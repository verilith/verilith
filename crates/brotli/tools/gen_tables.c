/* Prints the RFC 7932 tables vbrotli embeds, from google/brotli's sources.
   Build: cc -I$BROTLI/c -I$BROTLI/c/include tools/gen_tables.c $BROTLI/c/common/transform.c $BROTLI/c/common/context.c -o gen && ./gen */
#include <stdio.h>
#include "common/transform.h"
#include "common/context.h"
int main(void) {
  const BrotliTransforms* t = BrotliGetTransforms();
  int i;
  printf("pub const PREFIX_SUFFIX: [u8; %d] = [", (int)t->prefix_suffix_size);
  for (i = 0; i < t->prefix_suffix_size; i++) printf("%s%d", i ? ", " : "", t->prefix_suffix[i]);
  printf("];\n\npub const PS_MAP: [u16; 50] = [");
  for (i = 0; i < 50; i++) printf("%s%d", i ? ", " : "", t->prefix_suffix_map[i]);
  printf("];\n\npub const TRANSFORMS: [u8; %d] = [", t->num_transforms * 3);
  for (i = 0; i < t->num_transforms * 3; i++) printf("%s%d", i ? ", " : "", t->transforms[i]);
  printf("];\n\npub const CONTEXT_LUT: [u8; 2048] = [");
  for (i = 0; i < 2048; i++) printf("%s%d", i ? ", " : "", _kBrotliContextLookupTable[i]);
  printf("];\n");
  return 0;
}
