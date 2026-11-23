/* What expat's own test suite (tests/runtests.c) links from inside libexpat
 * besides its public API, for building that suite against verilith-xml's
 * expat ABI. These are libexpat's internals (its hash table, allocator,
 * tokenizer and accounting), which verilith-xml does not have: each stub
 * fails the test that calls it. scripts/test-expat.sh lists the tests that need them. */
#include "minicheck.h"


#define INTERNAL(name) \
  void *name(void) { _fail(__FILE__, __LINE__, "libexpat internal: " #name); return 0; }

INTERNAL(_INTERNAL_trim_to_complete_utf8_characters)
INTERNAL(testingAccountingGetCountBytesDirect)
INTERNAL(testingAccountingGetCountBytesIndirect)
INTERNAL(unsignedCharToPrintable)
INTERNAL(expat_malloc)
INTERNAL(expat_realloc)
INTERNAL(expat_free)
INTERNAL(hashTableInit)
INTERNAL(hashTableClear)
INTERNAL(hashTableDestroy)
INTERNAL(hashTableIterInit)
INTERNAL(hashTableIterNext)
INTERNAL(lookup)
INTERNAL(lookupWithLength)
INTERNAL(keyeq)
INTERNAL(keylen)
INTERNAL(isCDataCommentOrPIStart)
INTERNAL(isPredefinedEntityName)
INTERNAL(scanEntityText)
INTERNAL(xmlSetHashSalt)
