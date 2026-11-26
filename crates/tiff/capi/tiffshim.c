/* The variadic half of verilith-tiff's libtiff API (src/capi.rs has the
 * rest): TIFFGetField and friends, TIFFSetField, and the error and warning
 * reporters, which stable Rust cannot define. Trusted glue, not verified:
 * each function takes its arguments off the va_list and calls src/capi.rs.
 *
 * Built by build.rs. With VTIFF_ABI (the tiff-abi feature) the functions
 * are also defined under libtiff's names. */
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

typedef struct tiff TIFF;
typedef void *thandle_t;
typedef void (*TIFFErrorHandler)(const char *, const char *, va_list);
typedef void (*TIFFErrorHandlerExt)(thandle_t, const char *, const char *, va_list);

/* In src/capi.rs. */
extern int vtiff_field_args(uint32_t tag);
extern int vtiff_get_field(TIFF *tif, uint32_t tag, void *a, void *b, void *c, int defaulted);
extern int vtiff_set_field(TIFF *tif, uint32_t tag);

static void unix_error(const char *module, const char *fmt, va_list ap) {
	if (module != NULL) fprintf(stderr, "%s: ", module);
	vfprintf(stderr, fmt, ap);
	fprintf(stderr, ".\n");
}

static void unix_warning(const char *module, const char *fmt, va_list ap) {
	if (module != NULL) fprintf(stderr, "%s: ", module);
	fprintf(stderr, "Warning, ");
	vfprintf(stderr, fmt, ap);
	fprintf(stderr, ".\n");
}

static TIFFErrorHandler error_handler = unix_error;
static TIFFErrorHandler warning_handler = unix_warning;
static TIFFErrorHandlerExt error_handler_ext = NULL;
static TIFFErrorHandlerExt warning_handler_ext = NULL;

static void vreport(int warning, thandle_t fd, const char *module, const char *fmt, va_list ap) {
	TIFFErrorHandler h = warning ? warning_handler : error_handler;
	TIFFErrorHandlerExt e = warning ? warning_handler_ext : error_handler_ext;
	if (h) {
		va_list c;
		va_copy(c, ap);
		h(module, fmt, c);
		va_end(c);
	}
	if (e) {
		va_list c;
		va_copy(c, ap);
		e(fd, module, fmt, c);
		va_end(c);
	}
}

static void report(int warning, thandle_t fd, const char *module, const char *fmt, ...) {
	va_list ap;
	va_start(ap, fmt);
	vreport(warning, fd, module, fmt, ap);
	va_end(ap);
}

/* Called from src/capi.rs with a finished message. */
void vtiff_report(int warning, thandle_t fd, const char *module, const char *msg) {
	report(warning, fd, module, "%s", msg);
}

static int vget(TIFF *tif, uint32_t tag, va_list ap, int defaulted) {
	void *p[3] = {0, 0, 0};
	int n = vtiff_field_args(tag);
	for (int i = 0; i < n && i < 3; i++) p[i] = va_arg(ap, void *);
	return vtiff_get_field(tif, tag, p[0], p[1], p[2], defaulted);
}

#define DEFINE(prefix)                                                                    \
	int prefix##TIFFGetField(TIFF *tif, uint32_t tag, ...) {                              \
		va_list ap;                                                                       \
		va_start(ap, tag);                                                                \
		int r = vget(tif, tag, ap, 0);                                                    \
		va_end(ap);                                                                       \
		return r;                                                                         \
	}                                                                                     \
	int prefix##TIFFGetFieldDefaulted(TIFF *tif, uint32_t tag, ...) {                     \
		va_list ap;                                                                       \
		va_start(ap, tag);                                                                \
		int r = vget(tif, tag, ap, 1);                                                    \
		va_end(ap);                                                                       \
		return r;                                                                         \
	}                                                                                     \
	int prefix##TIFFVGetField(TIFF *tif, uint32_t tag, va_list ap) {                      \
		va_list c;                                                                        \
		va_copy(c, ap);                                                                   \
		int r = vget(tif, tag, c, 0);                                                     \
		va_end(c);                                                                        \
		return r;                                                                         \
	}                                                                                     \
	int prefix##TIFFVGetFieldDefaulted(TIFF *tif, uint32_t tag, va_list ap) {             \
		va_list c;                                                                        \
		va_copy(c, ap);                                                                   \
		int r = vget(tif, tag, c, 1);                                                     \
		va_end(c);                                                                        \
		return r;                                                                         \
	}                                                                                     \
	int prefix##TIFFSetField(TIFF *tif, uint32_t tag, ...) { return vtiff_set_field(tif, tag); } \
	int prefix##TIFFVSetField(TIFF *tif, uint32_t tag, va_list ap) {                      \
		(void)ap;                                                                         \
		return vtiff_set_field(tif, tag);                                                 \
	}                                                                                     \
	void prefix##TIFFError(const char *module, const char *fmt, ...) {                    \
		va_list ap;                                                                       \
		va_start(ap, fmt);                                                                \
		vreport(0, NULL, module, fmt, ap);                                                \
		va_end(ap);                                                                       \
	}                                                                                     \
	void prefix##TIFFErrorExt(thandle_t fd, const char *module, const char *fmt, ...) {   \
		va_list ap;                                                                       \
		va_start(ap, fmt);                                                                \
		vreport(0, fd, module, fmt, ap);                                                  \
		va_end(ap);                                                                       \
	}                                                                                     \
	void prefix##TIFFWarning(const char *module, const char *fmt, ...) {                  \
		va_list ap;                                                                       \
		va_start(ap, fmt);                                                                \
		vreport(1, NULL, module, fmt, ap);                                                \
		va_end(ap);                                                                       \
	}                                                                                     \
	void prefix##TIFFWarningExt(thandle_t fd, const char *module, const char *fmt, ...) { \
		va_list ap;                                                                       \
		va_start(ap, fmt);                                                                \
		vreport(1, fd, module, fmt, ap);                                                  \
		va_end(ap);                                                                       \
	}                                                                                     \
	TIFFErrorHandler prefix##TIFFSetErrorHandler(TIFFErrorHandler h) {                    \
		TIFFErrorHandler old = error_handler;                                             \
		error_handler = h;                                                                \
		return old;                                                                       \
	}                                                                                     \
	TIFFErrorHandler prefix##TIFFSetWarningHandler(TIFFErrorHandler h) {                  \
		TIFFErrorHandler old = warning_handler;                                           \
		warning_handler = h;                                                              \
		return old;                                                                       \
	}                                                                                     \
	TIFFErrorHandlerExt prefix##TIFFSetErrorHandlerExt(TIFFErrorHandlerExt h) {           \
		TIFFErrorHandlerExt old = error_handler_ext;                                      \
		error_handler_ext = h;                                                            \
		return old;                                                                       \
	}                                                                                     \
	TIFFErrorHandlerExt prefix##TIFFSetWarningHandlerExt(TIFFErrorHandlerExt h) {         \
		TIFFErrorHandlerExt old = warning_handler_ext;                                    \
		warning_handler_ext = h;                                                          \
		return old;                                                                       \
	}

DEFINE(vtiff_)
#ifdef VTIFF_ABI
DEFINE()
#endif
