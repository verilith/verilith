/* Only llhttp__debug (llhttp.c's debug builds) prints; nothing here calls
   it, and the linker drops it. */
extern void *stderr;
int fprintf(void *f, const char *fmt, ...);
