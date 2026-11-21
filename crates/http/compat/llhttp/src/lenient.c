/* llhttp's own generated parser (llhttp.c), under other names, for parsers
 * with lenient flags set. vhttp's drop-in parses strictly; the lenient
 * modes (Node.js's --insecure-http-parser and httpValidation) accept
 * messages the verified machines reject by design, so with the
 * `llhttp-lenient` feature the drop-in hands such parsers to this copy.
 * Compile it next to llhttp.c. */
#define llhttp__internal_init vhttp_lenient_init
#define llhttp__internal_execute vhttp_lenient_execute
#include "llhttp.c"

/* Puts a parser that `llhttp__internal_init` (vhttp's) cleared at
 * llhttp's start state. */
void vhttp_lenient_start(llhttp__internal_t* state) {
  state->_current = (void*) (intptr_t) s_n_llhttp__internal__n_start;
}
