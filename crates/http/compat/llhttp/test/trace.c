/* Prints what an llhttp user sees for one input: the callbacks, gathered
 * the way Node.js gathers them (spans joined across calls). Linked once with llhttp and once with vhttp's llhttp drop-in,
 * the two traces can be compared.
 *
 *   trace (req|res) (whole|bytes|SEED) FILE
 *
 * `bytes` feeds one byte per llhttp_execute call; a number feeds random
 * pieces from that seed. With PAUSE=k in the environment, the k-th
 * callback (counting from 1) pauses the parser, which then resumes where
 * it stopped: the trace must not change. With LENIENT=flags, the parser
 * runs with those lenient flags. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "llhttp.h"

#define CAP (1 << 20)

static char out[CAP * 4];
static size_t outn;
static char url[CAP], status[CAP], field[CAP], value[CAP];
static size_t urln, statusn, fieldn, valuen;
static int in_value, have_pair;
static unsigned long long body_len, body_hash;
static long pause_at, ncb;

/* The callback's result: pauses once, at callback number pause_at. */
static int ret(void) { return ++ncb == pause_at ? HPE_PAUSED : 0; }

static void emit(const char* fmt, ...) __attribute__((format(printf, 1, 2)));
#include <stdarg.h>
static void emit(const char* fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  outn += vsnprintf(out + outn, sizeof(out) - outn, fmt, ap);
  va_end(ap);
  if (outn > sizeof(out) - 1024) outn = sizeof(out) - 1024;
}

static void append(char* buf, size_t* n, const char* at, size_t len) {
  if (*n + len > CAP) len = CAP - *n;
  memcpy(buf + *n, at, len);
  *n += len;
}

static void flush_pair(void) {
  if (!have_pair) return;
  emit("h %.*s: [%.*s]\n", (int)fieldn, field, (int)valuen, value);
  fieldn = valuen = 0;
  have_pair = 0;
  in_value = 0;
}

static int on_message_begin(llhttp_t* p) {
  (void)p;
  emit("begin\n");
  urln = statusn = fieldn = valuen = 0;
  have_pair = in_value = 0;
  body_len = 0;
  body_hash = 1469598103934665603ULL;
  return ret();
}
static int on_url(llhttp_t* p, const char* at, size_t len) {
  (void)p;
  append(url, &urln, at, len);
  return ret();
}
static int on_status(llhttp_t* p, const char* at, size_t len) {
  (void)p;
  append(status, &statusn, at, len);
  return ret();
}
static int on_header_field(llhttp_t* p, const char* at, size_t len) {
  (void)p;
  if (in_value) flush_pair();
  have_pair = 1;
  append(field, &fieldn, at, len);
  return ret();
}
static int on_header_value(llhttp_t* p, const char* at, size_t len) {
  (void)p;
  in_value = 1;
  append(value, &valuen, at, len);
  return ret();
}
static int on_headers_complete(llhttp_t* p) {
  flush_pair();
  if (p->type == HTTP_REQUEST)
    emit("url %.*s\n", (int)urln, url);
  else
    emit("status %d %.*s\n", p->status_code, (int)statusn, status);
  emit("hc method=%d v=%d.%d upgrade=%d keepalive=%d\n", p->type == HTTP_REQUEST ? p->method : -1,
       p->http_major, p->http_minor, p->upgrade, llhttp_should_keep_alive(p));
  return 0;
}
static int on_body(llhttp_t* p, const char* at, size_t len) {
  (void)p;
  for (size_t i = 0; i < len; i++) {
    body_hash ^= (unsigned char)at[i];
    body_hash *= 1099511628211ULL;
  }
  body_len += len;
  return ret();
}
static int on_chunk_header(llhttp_t* p) {
  emit("chunk %llu\n", (unsigned long long)p->content_length);
  return ret();
}
static int on_message_complete(llhttp_t* p) {
  (void)p;
  flush_pair();
  emit("body %llu %016llx\nmc\n", body_len, body_hash);
  return ret();
}

int main(int argc, char** argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: trace (req|res) (whole|bytes|SEED) FILE\n");
    return 2;
  }
  FILE* f = fopen(argv[3], "rb");
  if (!f) return 2;
  static char in[CAP];
  size_t n = fread(in, 1, sizeof(in), f);
  fclose(f);

  llhttp_settings_t s;
  llhttp_settings_init(&s);
  s.on_message_begin = on_message_begin;
  s.on_url = on_url;
  s.on_status = on_status;
  s.on_header_field = on_header_field;
  s.on_header_value = on_header_value;
  s.on_headers_complete = on_headers_complete;
  s.on_body = on_body;
  s.on_chunk_header = on_chunk_header;
  s.on_message_complete = on_message_complete;
  llhttp_t p;
  llhttp_init(&p, strcmp(argv[1], "req") == 0 ? HTTP_REQUEST : HTTP_RESPONSE, &s);
  /* LENIENT=flags (llhttp_t's lenient_flags, e.g. 0x7ff for all). */
  if (getenv("LENIENT")) p.lenient_flags = (uint16_t)strtol(getenv("LENIENT"), NULL, 0);

  if (getenv("PAUSE")) pause_at = atol(getenv("PAUSE"));
  unsigned seed = 0;
  int mode = 0; /* 0 whole, 1 bytes, 2 random */
  if (strcmp(argv[2], "bytes") == 0) mode = 1;
  else if (strcmp(argv[2], "whole") != 0) { mode = 2; seed = (unsigned)atoi(argv[2]); }

  size_t off = 0;
  llhttp_errno_t err = HPE_OK;
  int resumed = 0;
  while (off < n || resumed) {
    resumed = 0;
    size_t len = n - off;
    if (mode == 1 && off < n) len = 1;
    if (mode == 2) {
      seed = seed * 1103515245u + 12345u;
      len = 1 + (seed >> 8) % 64;
      if (len > n - off) len = n - off;
    }
    err = llhttp_execute(&p, in + off, len);
    if (err == HPE_PAUSED) {
      /* Resume from where it stopped. */
      size_t at = (size_t)(llhttp_get_error_pos(&p) - in);
      llhttp_resume(&p);
      off = at;
      resumed = 1; /* call execute again, even with no bytes left */
      err = HPE_OK;
      continue;
    }
    if (err != HPE_OK) {
      size_t at = off + (size_t)(llhttp_get_error_pos(&p) - (in + off));
      emit("stop %s @%zu\n", llhttp_errno_name(err), at);
      break;
    }
    off += len;
  }
  if (err == HPE_OK) {
    err = llhttp_finish(&p);
    /* finish may call on_message_complete, which may be the one to pause */
    if (err != HPE_OK && err != HPE_PAUSED) emit("finish %s\n", llhttp_errno_name(err));
    else emit("eof\n");
  }
  fwrite(out, 1, outn, stdout);
  return 0;
}
