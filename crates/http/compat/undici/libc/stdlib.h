/* The libc subset llhttp's api.c needs, for wasm32 without a libc. */
#include <stddef.h>
void *malloc(size_t n);
void free(void *p);
_Noreturn void abort(void);
