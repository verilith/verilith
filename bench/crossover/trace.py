"""gdb script: records the instructions of the second call of `probe`.

    gdb -q -batch -x trace.py --args target/release/crossover <kernel> <n>

Writes one instruction per line (the function it is in, a tab, then the
instruction in Intel syntax, gdb's disassembly) to the
file named by the environment variable TRACE_OUT. Steps into every call,
the platform's memcpy included, and stops when `probe` returns.
"""
import os
import gdb

gdb.execute("set pagination off")
gdb.execute("set disassembly-flavor intel")
gdb.execute("set confirm off")
gdb.execute("set language c")
gdb.execute("break *probe")
gdb.execute("run")
gdb.execute("continue")  # the second call
frame = gdb.selected_frame()
sp0 = int(gdb.parse_and_eval("$sp"))
out = []
arch = frame.architecture()
while True:
    pc = int(gdb.parse_and_eval("$pc"))
    ins = arch.disassemble(pc)[0]["asm"]
    fn = gdb.block_for_pc(pc)
    name = fn.function.name if fn is not None and fn.function is not None else "?"
    # `probe`'s own dispatch is the same for every kernel: left out.
    if not name.endswith("probe"):
        out.append(name + "\t" + ins)
    if ins.startswith("ret") and int(gdb.parse_and_eval("$sp")) == sp0:
        break
    gdb.execute("stepi", to_string=True)
    if len(out) > 200000:
        raise SystemExit("trace too long")
with open(os.environ["TRACE_OUT"], "w") as f:
    f.write("\n".join(out) + "\n")
gdb.execute("kill")
