// A thin wrapper over ls-qpack for the benchmark: an encoder and a decoder
// with the calls a server makes, in the way lsquic makes them.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "lsqpack.h"
#include "lsxpack_header.h"

void *lsq_enc_new(unsigned max_cap, unsigned cap, unsigned blocked, unsigned char *sdtc, size_t *sdtc_sz) {
    struct lsqpack_enc *e = calloc(1, sizeof(*e));
    lsqpack_enc_preinit(e, NULL);
    if (0 != lsqpack_enc_init(e, NULL, max_cap, cap, blocked, LSQPACK_ENC_OPT_STAGE_2, sdtc, sdtc_sz))
        return NULL;
    return e;
}

void lsq_enc_free(void *e) {
    lsqpack_enc_cleanup(e);
    free(e);
}

// Encodes `n` fields (offsets into `buf`, four per field: name offset,
// name length, value offset, value length) into a contiguous header block
// in `hb` and encoder stream bytes in `es`. Returns 0 on success.
int lsq_encode(void *e, uint64_t stream, unsigned seqno, const char *buf, const uint32_t *offs, size_t n,
               unsigned char *hb, size_t hb_cap, size_t *hb_sz, unsigned char *es, size_t es_cap, size_t *es_sz) {
    if (0 != lsqpack_enc_start_header(e, stream, seqno))
        return -1;
    size_t pmax = lsqpack_enc_header_block_prefix_size(e);
    size_t hoff = pmax, eoff = 0;
    for (size_t i = 0; i < n; i++) {
        struct lsxpack_header x;
        lsxpack_header_set_offset2(&x, buf, offs[4 * i], offs[4 * i + 1], offs[4 * i + 2], offs[4 * i + 3]);
        size_t esz = es_cap - eoff, hsz = hb_cap - hoff;
        if (LQES_OK != lsqpack_enc_encode(e, es + eoff, &esz, hb + hoff, &hsz, &x, 0))
            return -2;
        eoff += esz;
        hoff += hsz;
    }
    ssize_t p = lsqpack_enc_end_header(e, hb, pmax, NULL);
    if (p < 0)
        return -3;
    memmove(hb + p, hb + pmax, hoff - pmax);
    *hb_sz = (size_t)p + hoff - pmax;
    *es_sz = eoff;
    return 0;
}

int lsq_enc_decoder_in(void *e, const unsigned char *b, size_t n) {
    return lsqpack_enc_decoder_in(e, b, n);
}

// The decoder: each header block decodes into an arena; `count` and
// `bytes` add up what was decoded, as a check.
struct lsq_block {
    struct lsxpack_header x;
    char *arena;
    size_t cap, used;
    size_t count, bytes;
};

struct lsq_dec {
    struct lsqpack_dec dec;
    struct lsq_block blk;
};

static void unblocked(void *ctx) {
    (void)ctx;
}

static struct lsxpack_header *prepare_decode(void *ctx, struct lsxpack_header *x, size_t space) {
    struct lsq_block *b = ctx;
    if (space > LSXPACK_MAX_STRLEN)
        return NULL;
    if (b->used + space > b->cap) {
        size_t nc = (b->used + space) * 2;
        char *na = realloc(b->arena, nc);
        if (!na)
            return NULL;
        b->arena = na;
        b->cap = nc;
    }
    if (x) {
        // More room for the header being decoded: keep its state.
        x->buf = b->arena;
        x->val_len = (lsxpack_strlen_t)space;
        return x;
    }
    x = &b->x;
    lsxpack_header_prepare_decode(x, b->arena, b->used, space);
    return x;
}

static int process_header(void *ctx, struct lsxpack_header *x) {
    struct lsq_block *b = ctx;
    b->used += x->name_len + x->val_len;
    b->count++;
    b->bytes += x->name_len + x->val_len;
    return 0;
}

static const struct lsqpack_dec_hset_if HSET = {
    .dhi_unblocked = unblocked,
    .dhi_prepare_decode = prepare_decode,
    .dhi_process_header = process_header,
};

void *lsq_dec_new(unsigned cap, unsigned blocked) {
    struct lsq_dec *d = calloc(1, sizeof(*d));
    lsqpack_dec_init(&d->dec, NULL, cap, blocked, &HSET, 0);
    d->blk.cap = 4096;
    d->blk.arena = malloc(d->blk.cap);
    return d;
}

void lsq_dec_free(void *p) {
    struct lsq_dec *d = p;
    lsqpack_dec_cleanup(&d->dec);
    free(d->blk.arena);
    free(d);
}

// Feeds encoder stream bytes; writes any Insert Count Increment to `out`.
int lsq_dec_enc_in(void *p, const unsigned char *b, size_t n, unsigned char *out, size_t *out_sz) {
    struct lsq_dec *d = p;
    if (0 != lsqpack_dec_enc_in(&d->dec, b, n))
        return -1;
    *out_sz = 0;
    if (lsqpack_dec_ici_pending(&d->dec)) {
        ssize_t k = lsqpack_dec_write_ici(&d->dec, out, LSQPACK_LONGEST_ICI);
        if (k < 0)
            return -1;
        *out_sz = (size_t)k;
    }
    return 0;
}

// Decodes a whole header block: 0 done, 1 blocked, -1 error. The section
// acknowledgment, if any, goes to `out`.
int lsq_decode(void *p, uint64_t stream, const unsigned char *b, size_t n, unsigned char *out, size_t *out_sz,
               size_t *count, size_t *bytes) {
    struct lsq_dec *d = p;
    d->blk.used = d->blk.count = d->blk.bytes = 0;
    const unsigned char *q = b;
    *out_sz = LSQPACK_LONGEST_HEADER_ACK;
    enum lsqpack_read_header_status s = lsqpack_dec_header_in(&d->dec, &d->blk, stream, n, &q, n, out, out_sz);
    *count = d->blk.count;
    *bytes = d->blk.bytes;
    if (s == LQRHS_DONE)
        return 0;
    if (s == LQRHS_BLOCKED)
        return 1;
    return -1;
}

const char *lsq_dec_arena(void *p, size_t *len) {
    struct lsq_dec *d = p;
    *len = d->blk.used;
    return d->blk.arena;
}
