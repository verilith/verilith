# Differential testing against libjpeg-turbo. LIBJPEG_SRC is a libjpeg-turbo
# checkout (3.1.2 is the version vjpeg is compared with), LIBJPEG_BUILD its
# CMake build directory (libjpeg.a, jconfig.h).
LIBJPEG_SRC ?= $(HOME)/ext/libjpeg-turbo
LIBJPEG_BUILD ?= $(HOME)/ext/ljtbuild
# The workspace's target directory.
TARGET ?= $(or $(CARGO_TARGET_DIR),$(CURDIR)/../../../target)
VJPEG := $(TARGET)/release/libverilith_jpeg.a
INC := -I$(LIBJPEG_SRC)/src -I$(LIBJPEG_BUILD)
LIBS := $(LIBJPEG_BUILD)/libjpeg.a -lpthread -lm -ldl

all: diff

$(VJPEG):
	cd .. && cargo build --release

diff: diff.c $(VJPEG)
	$(CC) -O2 -g $(INC) -o $@ diff.c $(VJPEG) $(LIBS)

# libFuzzer: build libjpeg-turbo and vjpeg with coverage too (see
# ../scripts/fuzz.sh).
fuzz_diff: diff.c
	clang -O1 -g -DFUZZ -fsanitize=fuzzer,address $(INC) -o $@ diff.c $(VJPEG) $(LIBS)

# The TurboJPEG API: the same driver against libturbojpeg and against vjpeg
# built with --features turbojpeg-abi. `make tjcheck FILES="a.jpg b.jpg"`.
TJ := ../target/tj/release/libverilith_jpeg.a
$(TJ):
	cd .. && cargo build --release --features turbojpeg-abi --target-dir target/tj
tjdiff_ref: tjdiff.c
	$(CC) -O2 $(INC) -o $@ tjdiff.c $(LIBJPEG_BUILD)/libturbojpeg.a -lm
tjdiff_ours: tjdiff.c $(TJ)
	$(CC) -O2 $(INC) -o $@ tjdiff.c $(TJ) -lpthread -lm -ldl
tjcheck: tjdiff_ref tjdiff_ours
	./tjdiff_ref $(FILES) > tj_ref.txt
	./tjdiff_ours $(FILES) > tj_ours.txt
	cmp tj_ref.txt tj_ours.txt && echo "TurboJPEG API: same on $$(wc -l < tj_ref.txt) files"

clean:
	rm -f diff fuzz_diff tjdiff_ref tjdiff_ours tj_ref.txt tj_ours.txt
