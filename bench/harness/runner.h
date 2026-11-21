/* The runner side of the vbench protocol, for C and C++ drivers.
 *
 * A driver registers its cases with vb_case() and then calls vb_main(),
 * which answers the harness (harness/vbench.py) on stdin/stdout:
 *
 *   info               -> "counters 0|1"
 *   cases              -> one "NAME\tBYTES" line per case, then "."
 *   run NAME ITERS     -> "NS\tINSTRUCTIONS\tCYCLES\tCHECK"
 *                         (one timed loop of ITERS calls; counts are -1
 *                          when the machine has no usable counters)
 *   quit
 *
 * BYTES is the input size of one call (0 if it has none), used only to
 * print MB/s. CHECK is the value the last call returned; the harness
 * compares it between the two contenders.
 */
#ifndef VB_RUNNER_H
#define VB_RUNNER_H
#include <stddef.h>
#include <stdint.h>
#include "counters.h"
#ifdef __cplusplus
extern "C" {
#endif
typedef uint64_t (*vb_fn)(void *ctx);
void vb_case(const char *name, uint64_t bytes, vb_fn fn, void *ctx);
int vb_main(void);
/* Whole file, malloc'd, with 64 zero bytes of padding after it. Exits on error. */
unsigned char *vb_read_file(const char *path, size_t *len);
/* $VBENCH_DATA, or "data". */
const char *vb_data_dir(void);
/* Sorted names of the regular files in DIR (not starting with '.'); returns count. */
size_t vb_list_dir(const char *dir, char ***names);
#ifdef __cplusplus
}
#endif
#endif
