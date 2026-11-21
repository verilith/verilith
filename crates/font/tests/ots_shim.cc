// Exercises the OTS-style C++ interface: ots_shim FONT.
#include <cstdio>
#include <cstring>
#include <vector>

#include "ots-memory-stream.h"

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  FILE *f = fopen(argv[1], "rb");
  if (!f) return 2;
  std::vector<uint8_t> in(1 << 20);
  in.resize(fread(in.data(), 1, in.size(), f));
  fclose(f);

  ots::OTSContext context;
  ots::ExpandingMemoryStream out(in.size(), in.size() * 8);
  if (!context.Process(&out, in.data(), in.size())) {
    fprintf(stderr, "font refused\n");
    return 1;
  }
  const size_t n = static_cast<size_t>(out.Tell());
  if (n < 12) return 1;

  // The same through a fixed buffer, and a buffer that is too small.
  std::vector<uint8_t> fixed(n);
  ots::MemoryStream exact(fixed.data(), fixed.size());
  if (!context.Process(&exact, in.data(), in.size()) ||
      memcmp(fixed.data(), out.get(), n) != 0) {
    return 1;
  }
  ots::MemoryStream small(fixed.data(), n - 1);
  if (context.Process(&small, in.data(), in.size()) || small.Tell() != 0) {
    return 1;
  }
  // A refused font writes nothing.
  ots::ExpandingMemoryStream none(16, 1 << 20);
  if (context.Process(&none, in.data(), 10) || none.Tell() != 0) return 1;
  puts("ots shim ok");
  return 0;
}
