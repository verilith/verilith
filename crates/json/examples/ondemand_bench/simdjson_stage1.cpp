// simdjson's stage 1 alone (On Demand `iterate` with nothing read) and its
// UTF-8 validation alone, per file, to compare with `examples/split.rs`
// (S1=1) and `examples/utf8_speed.rs`.
// c++ -O3 -mcpu=native -std=c++17 -I$SIMDJSON/singleheader simdjson_stage1.cpp \
//     $SIMDJSON/singleheader/simdjson.cpp -o simdjson_stage1 && ./simdjson_stage1 FILE...
#include "simdjson.h"
#include <chrono>
#include <cstdio>
using namespace simdjson;
int main(int argc, char **argv) {
  printf("file\tMB\tstage1 us\tstage1 GB/s\tutf8 us\tutf8 GB/s\tstructurals\n");
  for (int a = 1; a < argc; a++) {
    padded_string json = padded_string::load(argv[a]);
    ondemand::parser op;
    dom::parser dp;
    double best[2] = {1e9, 1e9};
    bool ok = true;
    auto t0 = std::chrono::steady_clock::now();
    for (int n = 0; n < 50 || std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count() < 2.0; n++)
      for (int i = 0; i < 2; i++) {
        auto t = std::chrono::steady_clock::now();
        if (i == 0) { ondemand::document d = op.iterate(json); (void)d; }
        else ok &= validate_utf8(json.data(), json.size());
        double e = std::chrono::duration<double>(std::chrono::steady_clock::now() - t).count();
        if (e < best[i]) best[i] = e;
      }
    // The DOM parser's stage 1 is the same one; it exposes the count.
    (void)dp.parse(json);
    double mb = json.size() / 1e6;
    printf("%s\t%.2f\t%.1f\t%.2f\t%.1f\t%.2f\t%u%s\n", argv[a], mb, best[0] * 1e6, mb / 1e3 / best[0],
           best[1] * 1e6, mb / 1e3 / best[1], dp.implementation->n_structural_indexes, ok ? "" : " BAD UTF-8");
  }
}
