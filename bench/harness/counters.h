/* Timer and hardware counters shared by every runner, C and Rust alike, so
 * each contender is timed and counted by the same code.
 *
 * Instructions retired (user + kernel on macOS, user only on Linux) and
 * cycles, for the whole calling process:
 *   Linux: perf_event_open (needs perf_event_paranoid <= 2 and a PMU; most
 *          cloud VMs have none, and then the counts are reported as -1).
 *   macOS: proc_pid_rusage(RUSAGE_INFO_V4) ri_instructions / ri_cycles. No
 *          root needed. These are the counters behind `/usr/bin/time -l`.
 */
#ifndef VB_COUNTERS_H
#define VB_COUNTERS_H
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
/* Call once at startup. Also raises the thread's QoS on macOS so the
 * scheduler keeps it on a performance core. Returns 1 if counters work. */
int vb_counters_init(void);
/* Monotonic time in nanoseconds. */
uint64_t vb_now_ns(void);
/* Instructions and cycles so far; -1 when unavailable. */
void vb_counters_read(int64_t *instructions, int64_t *cycles);
#ifdef __cplusplus
}
#endif
#endif
