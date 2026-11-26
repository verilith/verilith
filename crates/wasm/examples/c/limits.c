// Fuel and memory limits (Verilith extensions, see include/verilith.h).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#include "wasm.h"
#include "verilith.h"

#define own

// (module
//   (memory 1)  ; not exported
//   (func (export "spin") (loop br 0))
//   (func (export "grow") (param i32) (result i32) local.get 0 memory.grow))
static const char wasm[] = {
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x09, 0x02, 0x60, 0x00, 0x00, 0x60, 0x01, 0x7f, 0x01, 0x7f,
  0x03, 0x03, 0x02, 0x00, 0x01,
  0x05, 0x03, 0x01, 0x00, 0x01,
  0x07, 0x0f, 0x02, 0x04, 's', 'p', 'i', 'n', 0x00, 0x00, 0x04, 'g', 'r', 'o', 'w', 0x00, 0x01,
  0x0a, 0x10, 0x02, 0x07, 0x00, 0x03, 0x40, 0x0c, 0x00, 0x0b, 0x0b, 0x06, 0x00, 0x20, 0x00, 0x40, 0x00, 0x0b,
};

static int32_t grow(const wasm_func_t* f, int32_t n) {
  wasm_val_t args_val[] = { WASM_I32_VAL(n) };
  wasm_val_t results_val[] = { WASM_INIT_VAL };
  wasm_val_vec_t args = WASM_ARRAY_VEC(args_val);
  wasm_val_vec_t results = WASM_ARRAY_VEC(results_val);
  own wasm_trap_t* trap = wasm_func_call(f, &args, &results);
  if (trap) {
    printf("> Unexpected trap!\n");
    exit(1);
  }
  return results_val[0].of.i32;
}

int main(int argc, const char* argv[]) {
  printf("Initializing...\n");
  wasm_engine_t* engine = wasm_engine_new();
  wasm_store_t* store = wasm_store_new(engine);
  verilith_store_set_fuel(store, 10000000);
  verilith_store_limit_memory(store, 4 * 65536);

  printf("Compiling module...\n");
  wasm_byte_vec_t binary = { sizeof wasm, (wasm_byte_t*)wasm };
  own wasm_module_t* module = wasm_module_new(store, &binary);
  if (!module) {
    printf("> Error compiling module!\n");
    return 1;
  }

  printf("Instantiating module...\n");
  wasm_extern_vec_t imports = WASM_EMPTY_VEC;
  own wasm_instance_t* instance = wasm_instance_new(store, module, &imports, NULL);
  if (!instance) {
    printf("> Error instantiating module!\n");
    return 1;
  }
  own wasm_extern_vec_t exports;
  wasm_instance_exports(instance, &exports);
  if (exports.size < 2) {
    printf("> Error accessing exports!\n");
    return 1;
  }
  const wasm_func_t* spin = wasm_extern_as_func(exports.data[0]);
  const wasm_func_t* growf = wasm_extern_as_func(exports.data[1]);
  if (!spin || !growf) {
    printf("> Error accessing exports!\n");
    return 1;
  }

  printf("Calling an infinite loop...\n");
  wasm_val_vec_t none = WASM_EMPTY_VEC;
  own wasm_trap_t* trap = wasm_func_call(spin, &none, &none);
  if (!trap) {
    printf("> Error: the loop returned!\n");
    return 1;
  }
  own wasm_message_t message;
  wasm_trap_message(trap, &message);
  printf("Trap: %s\n", message.data);
  if (strcmp(message.data, "all fuel consumed") != 0) {
    printf("> Wrong trap!\n");
    return 1;
  }
  wasm_byte_vec_delete(&message);
  wasm_trap_delete(trap);
  uint64_t fuel = 1;
  if (!verilith_instance_get_fuel(instance, &fuel) || fuel != 0) {
    printf("> Fuel not used up!\n");
    return 1;
  }

  printf("Refuelling and growing memory up to the limit...\n");
  verilith_instance_set_fuel(instance, 1000);
  int32_t got[4] = { grow(growf, 2), grow(growf, 1), grow(growf, 1), grow(growf, 0) };
  printf("memory.grow: %d %d %d %d\n", got[0], got[1], got[2], got[3]);
  if (got[0] != 1 || got[1] != 3 || got[2] != -1 || got[3] != 4) {
    printf("> Wrong results!\n");
    return 1;
  }

  wasm_extern_vec_delete(&exports);
  wasm_instance_delete(instance);
  wasm_module_delete(module);

  printf("Shutting down...\n");
  wasm_store_delete(store);
  wasm_engine_delete(engine);

  printf("Done.\n");
  return 0;
}
