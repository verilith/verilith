/* Reads each file named on the command line, parses it with
 * cJSON_ParseWithLengthOpts(require_null_terminated = 1) and prints
 * "ACCEPT <file>" or "REJECT <file>". Links against either vjson or cJSON. */
#include <stdio.h>
#include <stdlib.h>
#include "cJSON.h"

int main(int argc, char **argv) {
    for (int a = 1; a < argc; a++) {
        FILE *f = fopen(argv[a], "rb");
        if (!f) { perror(argv[a]); return 2; }
        fseek(f, 0, SEEK_END);
        long n = ftell(f);
        fseek(f, 0, SEEK_SET);
        char *buf = malloc(n + 1);
        if (fread(buf, 1, n, f) != (size_t)n) { return 2; }
        buf[n] = 0;
        fclose(f);
        cJSON *j = cJSON_ParseWithLengthOpts(buf, n + 1, NULL, 1);
        printf("%s %s\n", j ? "ACCEPT" : "REJECT", argv[a]);
        cJSON_Delete(j);
        free(buf);
    }
    return 0;
}
