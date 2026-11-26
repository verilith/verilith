// Verilith extensions to the wasm-c-api (include after wasm.h).
#ifndef VERILITH_H
#define VERILITH_H

#include <stdbool.h>
#include <stdint.h>

#include "wasm.h"

#ifdef __cplusplus
extern "C" {
#endif

// Caps the linear memory of instances created in `store` from now on at
// `bytes`, rounded down to whole 64 KiB pages. A module whose memory starts
// above the cap fails to instantiate, and memory.grow past it returns -1.
void verilith_store_limit_memory(wasm_store_t* store, uint64_t bytes);

// Meters instances created in `store` from now on: each starts with `fuel`
// units. Each branch, call and return costs one unit, and a call that runs
// out traps with the message "all fuel consumed". Unmetered by default.
void verilith_store_set_fuel(wasm_store_t* store, uint64_t fuel);

// Sets the fuel `instance` has left (which also meters an unmetered
// instance). Returns false if a call into the instance is running.
bool verilith_instance_set_fuel(const wasm_instance_t* instance, uint64_t fuel);

// Stores the fuel `instance` has left in `*out`. Returns false if the
// instance is unmetered or a call into it is running.
bool verilith_instance_get_fuel(const wasm_instance_t* instance, uint64_t* out);

#ifdef __cplusplus
}
#endif

#endif
