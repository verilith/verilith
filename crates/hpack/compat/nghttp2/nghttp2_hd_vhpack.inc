/*
 * nghttp2's HPACK inflater on vhpack's verified decoder.
 *
 * compat/nghttp2/patch.py makes nghttp2_hd.c include this file in place of
 * its own inflater (the functions below). The deflater, the static table
 * and the token lookup stay nghttp2's. Every decoding decision is made by
 * vhpack_feed; this file wraps the decoded name and value in rcbufs, as
 * nghttp2's own inflater emits them, and keeps nghttp2's state and error
 * conventions (ctx.bad, NGHTTP2_ERR_HEADER_COMP, NGHTTP2_ERR_INVALID_STATE).
 */
#include <stdint.h>

void *vhpack_new(void);
void vhpack_free(void *d);
typedef struct {
  size_t consumed;
  const uint8_t *name;
  size_t namelen;
  const uint8_t *value;
  size_t valuelen;
  uint64_t ids[2];
  uint32_t idx;
  int never;
} vhpack_field;
int vhpack_feed(void *d, const uint8_t *in, size_t inlen, int fin,
                vhpack_field *f);
int vhpack_change_settings(void *d, uint32_t n);
void vhpack_end_block(void *d);
size_t vhpack_table_len(const void *d);
size_t vhpack_table_size(const void *d);
size_t vhpack_table_max(const void *d);
int vhpack_table_entry(const void *d, size_t i, const uint8_t **name,
                       size_t *namelen, const uint8_t **value,
                       size_t *valuelen);

/* Puts n bytes from p in *keep (capacity *cap), NUL-terminated as
   nghttp2_rcbuf_new2 does. *keep is reused if this inflater holds its only
   reference and it is big enough; otherwise it is released and a new one
   is made. */
static int vh_fill(nghttp2_rcbuf **keep, size_t *cap, const uint8_t *p,
                   size_t n, nghttp2_mem *mem) {
  nghttp2_rcbuf *rc = *keep;
  int rv;

  if (rc == NULL || rc->ref != 1 || *cap < n) {
    size_t c = n < 128 ? 128 : n;
    nghttp2_rcbuf_decref(rc);
    *keep = NULL;
    rv = nghttp2_rcbuf_new(&rc, c + 1, mem);
    if (rv != 0) {
      return rv;
    }
    *cap = c;
    *keep = rc;
  }
  if (n) {
    memcpy(rc->base, p, n);
  }
  rc->base[n] = '\0';
  rc->len = n;
  return 0;
}

/* rcbufs for dynamic table entries, so a field indexed from the table is
   not copied each time: slot id % VH_SLOTS holds entry id's name and
   value (made when first needed; an id always names the same entry). Only
   short strings are kept, so stale slots hold little memory. */
#define VH_SLOTS 64
#define VH_SLOT_MAX 256
typedef struct {
  uint64_t id;
  nghttp2_rcbuf *name, *value;
  int32_t token;
} vh_slot;

static void vh_slots_free(vh_slot *c) {
  size_t i;
  if (c == NULL) {
    return;
  }
  for (i = 0; i < VH_SLOTS; i++) {
    nghttp2_rcbuf_decref(c[i].name);
    nghttp2_rcbuf_decref(c[i].value);
  }
}

/* The slot for entry id, emptied if it held another. */
static vh_slot *vh_slot_for(vh_slot *c, uint64_t id) {
  vh_slot *sl = &c[id % VH_SLOTS];
  if (sl->id != id) {
    nghttp2_rcbuf_decref(sl->name);
    nghttp2_rcbuf_decref(sl->value);
    sl->id = id;
    sl->name = NULL;
    sl->value = NULL;
  }
  return sl;
}

int nghttp2_hd_inflate_init(nghttp2_hd_inflater *inflater, nghttp2_mem *mem) {
  int rv;

  rv = hd_context_init(&inflater->ctx, mem);
  if (rv != 0) {
    return rv;
  }
  inflater->settings_hd_table_bufsize_max = NGHTTP2_HD_DEFAULT_MAX_BUFFER_SIZE;
  inflater->min_hd_table_bufsize_max = UINT32_MAX;
  inflater->nv_name_keep = NULL;
  inflater->nv_value_keep = NULL;
  inflater->namercbuf = NULL;
  inflater->valuercbuf = NULL;
  inflater->vh_name_cap = 0;
  inflater->vh_value_cap = 0;
  inflater->opcode = NGHTTP2_HD_OPCODE_NONE;
  inflater->state = NGHTTP2_HD_STATE_INFLATE_START;
  inflater->vh = vhpack_new();
  inflater->vh_slots = nghttp2_mem_calloc(mem, VH_SLOTS, sizeof(vh_slot));
  if (inflater->vh == NULL || inflater->vh_slots == NULL) {
    vhpack_free(inflater->vh);
    nghttp2_mem_free(mem, inflater->vh_slots);
    hd_context_free(&inflater->ctx);
    return NGHTTP2_ERR_NOMEM;
  }
  return 0;
}

void nghttp2_hd_inflate_free(nghttp2_hd_inflater *inflater) {
  hd_inflate_keep_free(inflater);
  vh_slots_free(inflater->vh_slots);
  nghttp2_mem_free(inflater->ctx.mem, inflater->vh_slots);
  inflater->vh_slots = NULL;
  vhpack_free(inflater->vh);
  inflater->vh = NULL;
  hd_context_free(&inflater->ctx);
}

int nghttp2_hd_inflate_change_table_size(
  nghttp2_hd_inflater *inflater, size_t settings_max_dynamic_table_size) {
  if (settings_max_dynamic_table_size > UINT32_MAX ||
      vhpack_change_settings(inflater->vh,
                             (uint32_t)settings_max_dynamic_table_size) != 0) {
    return NGHTTP2_ERR_INVALID_STATE;
  }
  inflater->settings_hd_table_bufsize_max = settings_max_dynamic_table_size;
  return 0;
}

nghttp2_ssize nghttp2_hd_inflate_hd_nv(nghttp2_hd_inflater *inflater,
                                       nghttp2_hd_nv *nv_out,
                                       int *inflate_flags, const uint8_t *in,
                                       size_t inlen, int in_final) {
  vhpack_field f;
  int rv;
  uint32_t ni, vi;
  vh_slot *sl;
  nghttp2_mem *mem = inflater->ctx.mem;

  if (inflater->ctx.bad) {
    return NGHTTP2_ERR_HEADER_COMP;
  }
  /* Unlike nghttp2's inflater, the last field's rcbufs stay in
     nv_name_keep and nv_value_keep until they can be reused (vh_fill), or
     until free. */
  *inflate_flags = NGHTTP2_HD_INFLATE_NONE;

  switch (vhpack_feed(inflater->vh, in, inlen, in_final, &f)) {
  case 0: /* more input needed */
    return (nghttp2_ssize)f.consumed;
  case 1: /* the block ended cleanly */
    *inflate_flags |= NGHTTP2_HD_INFLATE_FINAL;
    return (nghttp2_ssize)f.consumed;
  case 2: /* a field */
    break;
  default:
    inflater->ctx.bad = 1;
    return NGHTTP2_ERR_HEADER_COMP;
  }

  /* Static table names and values are nghttp2's own static rcbufs, as in
     nghttp2_hd_table_get; short dynamic table ones are cached (vh_slot);
     the rest are copies. */
  ni = f.idx & 0xff;
  vi = f.idx >> 8;
  rv = 0;
  if (ni >= 1 && ni <= NGHTTP2_STATIC_TABLE_LENGTH) {
    nv_out->name = (nghttp2_rcbuf *)&static_table[ni - 1].name;
    nv_out->token = static_table[ni - 1].token;
  } else if (f.ids[0] != 0 && f.namelen <= VH_SLOT_MAX) {
    sl = vh_slot_for(inflater->vh_slots, f.ids[0]);
    if (sl->name == NULL) {
      rv = nghttp2_rcbuf_new2(&sl->name, f.name, f.namelen, mem);
      sl->token = rv == 0 ? lookup_token(f.name, f.namelen) : -1;
    }
    nv_out->name = sl->name;
    nv_out->token = sl->token;
  } else {
    rv = vh_fill(&inflater->nv_name_keep, &inflater->vh_name_cap, f.name,
                 f.namelen, mem);
    nv_out->name = inflater->nv_name_keep;
    nv_out->token = rv == 0 ? lookup_token(f.name, f.namelen) : -1;
  }
  if (rv == 0) {
    if (vi >= 1 && vi <= NGHTTP2_STATIC_TABLE_LENGTH) {
      nv_out->value = (nghttp2_rcbuf *)&static_table[vi - 1].value;
    } else if (f.ids[1] != 0 && f.valuelen <= VH_SLOT_MAX) {
      sl = vh_slot_for(inflater->vh_slots, f.ids[1]);
      if (sl->value == NULL) {
        rv = nghttp2_rcbuf_new2(&sl->value, f.value, f.valuelen, mem);
      }
      nv_out->value = sl->value;
    } else {
      rv = vh_fill(&inflater->nv_value_keep, &inflater->vh_value_cap, f.value,
                   f.valuelen, mem);
      nv_out->value = inflater->nv_value_keep;
    }
  }
  if (rv != 0) {
    hd_inflate_keep_free(inflater);
    inflater->ctx.bad = 1;
    return NGHTTP2_ERR_NOMEM;
  }
  nv_out->flags = f.never ? NGHTTP2_NV_FLAG_NO_INDEX : NGHTTP2_NV_FLAG_NONE;
  *inflate_flags |= NGHTTP2_HD_INFLATE_EMIT;
  return (nghttp2_ssize)f.consumed;
}

int nghttp2_hd_inflate_end_headers(nghttp2_hd_inflater *inflater) {
  /* nv_name_keep and nv_value_keep stay for the next block: vh_fill reuses
     them once nothing else holds them, and free releases them. */
  vhpack_end_block(inflater->vh);
  return 0;
}

size_t nghttp2_hd_inflate_get_num_table_entries(nghttp2_hd_inflater *inflater) {
  return vhpack_table_len(inflater->vh) + NGHTTP2_STATIC_TABLE_LENGTH;
}

const nghttp2_nv *
nghttp2_hd_inflate_get_table_entry(nghttp2_hd_inflater *inflater, size_t idx) {
  const uint8_t *name, *value;
  size_t namelen, valuelen;

  if (idx == 0) {
    return NULL;
  }
  --idx;
  if (idx < NGHTTP2_STATIC_TABLE_LENGTH) {
    return &static_table[idx].cnv;
  }
  if (vhpack_table_entry(inflater->vh, idx - NGHTTP2_STATIC_TABLE_LENGTH,
                         &name, &namelen, &value, &valuelen) != 0) {
    return NULL;
  }
  inflater->vh_nv.name = (uint8_t *)name;
  inflater->vh_nv.namelen = namelen;
  inflater->vh_nv.value = (uint8_t *)value;
  inflater->vh_nv.valuelen = valuelen;
  inflater->vh_nv.flags = NGHTTP2_NV_FLAG_NONE;
  return &inflater->vh_nv;
}

size_t
nghttp2_hd_inflate_get_dynamic_table_size(nghttp2_hd_inflater *inflater) {
  return vhpack_table_size(inflater->vh);
}

size_t
nghttp2_hd_inflate_get_max_dynamic_table_size(nghttp2_hd_inflater *inflater) {
  return vhpack_table_max(inflater->vh);
}
