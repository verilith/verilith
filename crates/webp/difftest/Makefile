# Differential testing against libwebp. LIBWEBP_SRC is a libwebp checkout,
# LIBWEBP_BUILD its CMake build directory (libwebp.a, libsharpyuv.a).
LIBWEBP_SRC ?= $(HOME)/ext/libwebp
LIBWEBP_BUILD ?= $(HOME)/ext/lwbuild
# The workspace's target directory.
TARGET ?= $(or $(CARGO_TARGET_DIR),$(CURDIR)/../../../target)
VWEBP := $(TARGET)/release/libverilith_webp.a
LIBS := $(LIBWEBP_BUILD)/libwebp.a $(LIBWEBP_BUILD)/libsharpyuv.a -lpthread -lm -ldl

all: diff

$(VWEBP):
	cd .. && cargo build --release

diff: diff.c $(VWEBP)
	$(CC) -O2 -g -I$(LIBWEBP_SRC)/src -o $@ diff.c $(VWEBP) $(LIBS)

# libFuzzer: libwebp and the harness instrumented; build vwebp with
# coverage too (see ../scripts/fuzz.sh).
fuzz_diff: diff.c
	clang -O1 -g -DFUZZ -fsanitize=fuzzer,address -I$(LIBWEBP_SRC)/src -o $@ diff.c $(VWEBP) $(LIBS)

bench: bench.c $(VWEBP)
	$(CC) -O3 -g -I$(LIBWEBP_SRC)/src -o $@ bench.c $(VWEBP) $(LIBS)

cve_demo: cve_demo.c $(VWEBP)
	$(CC) -O2 -g -I$(LIBWEBP_SRC)/src -o $@ cve_demo.c $(VWEBP) $(LIBS)

cve_demo_asan: cve_demo.c $(VWEBP)
	clang -O1 -g -fsanitize=address -I$(LIBWEBP_SRC)/src -o $@ cve_demo.c $(VWEBP) $(LIBS)

clean:
	rm -f diff fuzz_diff cve_demo cve_demo_asan bench
