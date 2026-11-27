#!/usr/bin/env python3
"""Static constant-time check of compiled code: x86-64 and AArch64 ELF.

    scripts/ctcheck.py CONFIG BINARY [--arch x86_64|aarch64] [-v]

For each function CONFIG names, this reads its machine code from BINARY
and runs a taint analysis over every path through it (an abstract
interpretation to a fixpoint, so loops are covered for any trip count):

- every value loaded from memory the function was handed is SECRET, unless
  CONFIG says that range is public (an expanded key's round count); the
  arguments in registers (pointers and lengths) and constants are public;
- taint follows the data through every instruction, through registers,
  flags, vector and mask registers, and the stack (tracked byte by byte at
  known offsets, and as a whole where an offset is not known);
- calls (direct, through the GOT, and tail calls) into functions of the
  binary are followed, on both architectures, with each callee's frame a
  stack region of its own; memcpy, memset and memmove are summarized, and
  `<crate>::ct::declassify` makes its result public;
- data symbols are secret too, except the CPU-feature caches the dispatch
  reads (`PUBLIC_DATA`, and any CONFIG names in "public_data");
- it is a failure if a conditional branch depends on a secret (the flags it
  tests, or the register of a CBZ/TBZ), if any memory address does (base or
  index register), if an indirect jump or a call the check does not know
  is reached, or if an instruction outside the list of data-independent-
  timing instructions (Intel's DOIT list, Arm's DIT list) has a secret
  operand.

This is the leakage model of the constant-time literature (Barthe et al.,
"System-level non-interference for constant-time cryptography", CCS 2014):
the trace of branch decisions and memory addresses. The analysis is
conservative: where it cannot tell, it assumes secret. What it trusts is
listed in each crate's TRUST.md: capstone's decoding and its lists of
which registers and flags an instruction reads and writes, the summaries
of memcpy, memset and memmove (in `CALLS`), and the CPU's promise that the
listed instructions take time independent of their data.

CONFIG is JSON:
  {"functions": [{"name": "<demangled symbol>", "public": [[arg, off, len]],
                  "expect": "pass" | "<kind of failure a control must show>"}]}
"""
import argparse
import json
import re
import subprocess
import sys

import capstone
from capstone import arm64_const as A64
from capstone import x86_const as X86
from elftools.elf.elffile import ELFFile

P = ("P",)  # public
S = ("S",)  # secret


def ptr(base, off):
    """A public pointer into `base` (an argument, a stack frame, constants)."""
    return ("A", base, off)


def const(n):
    """A public value known to be `n` (a length, mostly)."""
    return ("K", n & 0xFFFF_FFFF_FFFF_FFFF)


def is_ptr(v):
    return v[0] == "A"


def taint(v):
    return S if v == S else P


def join(a, b):
    if a == b:
        return a
    if a == S or b == S:
        return S
    if a[0] == "A" and b[0] == "A" and a[1] == b[1]:
        return ptr(a[1], None)
    return P


def joins(vs):
    r = None
    for v in vs:
        r = v if r is None else join(r, v)
    return P if r is None else r


def is_stack(region):
    return isinstance(region, str) and region.startswith("stack")


def frozen(st):
    """A hashable copy of a state, to memoize the analysis of a callee."""
    return (tuple(sorted(st.regs.items())), tuple(sorted(st.mem.items(), key=repr)), tuple(sorted(st.dflt.items())))


# The stack objects of the function being checked that are variables
# (allocas: arrays and locals whose address is taken), as offsets from the
# stack pointer at entry, from LLVM's stack-frame-layout remark; None if
# the check was not given them. Spill slots (the register allocator's) are
# only ever addressed at a constant offset from the frame, never through an
# index or a pointer, so a store whose offset is not known cannot reach
# them.
# The same for each stack region: "stack#d" is the frame of the function
# at call depth d (the checked function is depth 0; a call is followed into
# the callee, which gets the next region).
REGION_VARS = {}
FRAMES = None
# Data symbols whose contents are public: the CPU-feature caches the
# dispatch reads (CPUID bits), and any the config names ("public_data").
PUBLIC_DATA = {"std_detect::detect::cache::CACHE"}
MAX_DEPTH = 12
import os
TRACE = {int(x, 16) for x in os.environ.get("CTCHECK_TRACE", "").split(",") if x}


def in_frame(region, off):
    """Whether a stack byte is in this function's own frame: below the stack
    pointer at entry (offset 0 of "stack", where the return address is), or
    anywhere in a frame realigned from it. A store or load at an offset the
    check does not know (an array indexed by a register) is assumed to stay
    in the frame; the code is memory safe (Verus and Rust prove it), and the
    only stack objects it can index are its own locals. The caller's frame
    above the return address (the arguments passed on the stack) is kept.
    """
    if not region.startswith("stack#"):
        return True
    vs = REGION_VARS.get(region)
    if vs is not None:
        return off in vs
    return off < 0


class State:
    """Registers (missing means public), flags, and the stack, bytewise."""

    __slots__ = ("regs", "mem", "dflt")

    def __init__(self):
        self.regs = {}
        self.mem = {}  # (region, offset) -> (value, byte index within it)
        self.dflt = {}  # region -> taint of bytes never written exactly

    def copy(self):
        s = State()
        s.regs = dict(self.regs)
        s.mem = dict(self.mem)
        s.dflt = dict(self.dflt)
        return s

    def get(self, r):
        return self.regs.get(r, P)

    def set(self, r, v):
        if v == P:
            self.regs.pop(r, None)
        else:
            self.regs[r] = v

    def default(self, region):
        return self.dflt.get(region, P)

    def load(self, region, off, n):
        if off is None:
            vs = [v for (rg, o), (v, _) in self.mem.items() if rg == region and in_frame(region, o)]
            return taint(joins([self.default(region)] + [taint(v) for v in vs]))
        cells = [self.mem.get((region, off + i)) for i in range(n)]
        if all(c is not None for c in cells):
            v0 = cells[0][0]
            if all(c[0] == v0 and c[1] == i for i, c in enumerate(cells)) and n == 8:
                return v0
            return taint(joins([taint(c[0]) for c in cells]))
        d = self.default(region) if any(in_frame(region, off + i) for i in range(n)) else P
        return taint(joins([d] + [taint(c[0]) for c in cells if c is not None]))

    def store(self, region, off, n, v):
        if off is None:
            t = taint(v)
            if t == S:
                for k, (cv, _) in list(self.mem.items()):
                    if k[0] == region and in_frame(region, k[1]):
                        self.mem[k] = (S, None)
                self.dflt[region] = S
            return
        for i in range(n):
            self.mem[(region, off + i)] = (v, i) if n == 8 else (taint(v), None)

    def havoc_stack(self, v):
        """A store of `v` through a pointer that might be into the stack."""
        if taint(v) == S:
            for k in list(self.mem):
                if is_stack(k[0]) and in_frame(k[0], k[1]):
                    self.mem[k] = (S, None)
            for rg in set([k[0] for k in self.mem] + list(self.dflt)):
                if is_stack(rg):
                    self.dflt[rg] = S
            self.dflt["stack*"] = S

    def join_with(self, o):
        """self := self join o; returns whether self changed."""
        changed = False
        for r in set(self.regs) | set(o.regs):
            v = join(self.get(r), o.get(r))
            if v != self.get(r):
                changed = True
                self.set(r, v)
        for rg in set(self.dflt) | set(o.dflt):
            v = taint(join(self.default(rg), o.default(rg)))
            if v != self.default(rg):
                changed = True
                self.dflt[rg] = v
        for k in set(self.mem) | set(o.mem):
            a = self.mem.get(k, (self.default(k[0]), None))
            b = o.mem.get(k, (o.default(k[0]), None))
            c = a if a == b else (taint(join(a[0], b[0])), None)
            if self.mem.get(k) != c:
                changed = True
                self.mem[k] = c
        return changed


class Check:
    def __init__(self, fn, public, verbose):
        self.fn = fn
        self.public = public  # [(arg register, offset, length)]
        self.verbose = verbose
        self.violations = {}

    def bad(self, insn, kind, why):
        key = (insn.address, kind)
        if key not in self.violations:
            self.violations[key] = f"{insn.address:#x}  {insn.mnemonic} {insn.op_str}  [{kind}: {why}]"

    def load_from(self, st, base, off, n, insn):
        """The value at a pointer `base`+`off`, `n` bytes."""
        if base == S:
            return S
        if base[0] == "F" and base[1] in PUBLIC_DATA:
            return P  # through the GOT entry of a public data symbol
        if not is_ptr(base):
            return S  # memory we know nothing about: assume secret
        region, boff = base[1], base[2]
        if is_stack(region):
            return st.load(region, boff if off is None or boff is None else boff + off, n) if off is not None else st.load(region, None, n)
        if region == "const":
            return P
        if region == "got":
            return ("F", self.elf.got_target(boff)) if boff is not None else P
        if region == "data" and boff is not None and off is not None and self.elf.public_data_at(boff + off, n):
            return P
        if boff is not None and off is not None:
            a = boff + off
            for (arg, lo, ln) in self.public:
                if arg == region and lo <= a and a + n <= lo + ln:
                    return P
        return S

    def mem_op(self, st, kind, dst, src, n, insn):
        """The effect of memcpy/memmove(dst, src, n) or memset(dst, c, n):
        byte for byte where the length and the addresses are known."""
        if kind == "memset":
            v = taint(src)
            if n[0] == "K" and is_ptr(dst) and dst[2] is not None and n[1] <= 4096:
                for i in range(n[1]):
                    self.store_to(st, dst, i, 1, v, insn)
            else:
                self.store_to(st, dst if is_ptr(dst) else P, None, 1, v, insn)
            return
        if n[0] == "K" and is_ptr(dst) and dst[2] is not None and n[1] <= 4096:
            cells = []
            for i in range(n[1]):
                if is_ptr(src) and src[2] is not None and is_stack(src[1]):
                    c = st.mem.get((src[1], src[2] + i))
                    cells.append(c if c is not None else (st.default(src[1]) if in_frame(src[1], src[2] + i) else P, None))
                else:
                    cells.append((self.load_from(st, src, i, 1, insn) if is_ptr(src) and src[2] is not None else S, None))
            if is_stack(dst[1]):
                for i, c in enumerate(cells):
                    st.mem[(dst[1], dst[2] + i)] = c
            else:
                for i, c in enumerate(cells):
                    self.store_to(st, dst, i, 1, taint(c[0]), insn)
            return
        sv = P if is_ptr(src) and src[1] == "const" else S
        self.store_to(st, dst if is_ptr(dst) else P, None, 1, sv, insn)

    def store_to(self, st, base, off, n, v, insn):
        if base == S:
            return
        if not is_ptr(base):
            st.havoc_stack(v)
            return
        region, boff = base[1], base[2]
        if is_stack(region):
            st.store(region, None if (boff is None or off is None) else boff + off, n, v)
        elif taint(v) == S:
            for (arg, lo, ln) in self.public:
                if arg == region:
                    self.bad(insn, "store", "a secret written over public input")


# ---------------------------------------------------------------------------
# The binary
# ---------------------------------------------------------------------------


class Elf:
    def __init__(self, path, arch):
        self.path = path
        self.f = open(path, "rb")
        self.elf = ELFFile(self.f)
        self.arch = arch
        nm = "llvm-nm"
        for cand in ["llvm-nm", "rust-nm"]:
            try:
                subprocess.run([cand, "--version"], capture_output=True, check=True)
                nm = cand
                break
            except (OSError, subprocess.CalledProcessError):
                continue
        out = subprocess.run([nm, "-C", "-S", "--defined-only", path], capture_output=True, text=True, check=True).stdout
        self.syms = {}  # name -> (addr, size)
        self.data_syms = {}
        self.by_addr = {}
        for line in out.splitlines():
            m = re.match(r"([0-9a-f]+) ([0-9a-f]+) (\w) (.*)", line)
            if not m:
                m2 = re.match(r"([0-9a-f]+) (\w) (.*)", line)
                if m2:
                    self.by_addr.setdefault(int(m2.group(1), 16), m2.group(3))
                continue
            a, sz, ty, name = int(m.group(1), 16), int(m.group(2), 16), m.group(3), m.group(4)
            name = re.sub(r"::h[0-9a-f]{16}$", "", name)
            name = re.sub(r" \(\.llvm\.\d+\)$", "", name)
            if ty in "tTwW":
                self.syms.setdefault(name, (a, sz))
            else:
                self.data_syms.setdefault(name, (a, sz))
            self.by_addr.setdefault(a, name)
        self.sections = [(s["sh_addr"], s["sh_addr"] + s["sh_size"], s) for s in self.elf.iter_sections() if s["sh_addr"]]
        self.got = {}
        for sec in self.elf.iter_sections():
            if sec.header["sh_type"] in ("SHT_RELA", "SHT_REL"):
                symtab = self.elf.get_section(sec["sh_link"]) if sec["sh_link"] else None
                for r in sec.iter_relocations():
                    name = None
                    if r["r_info_sym"] and symtab is not None:
                        name = symtab.get_symbol(r["r_info_sym"]).name
                    elif "r_addend" in r.entry:
                        name = self.by_addr.get(r["r_addend"])
                    if name:
                        self.got[r["r_offset"]] = name
        dm = demangle_all(set(self.got.values()))
        self.got = {k: dm[v] for k, v in self.got.items()}

    def demangle(self, name):
        if not (name.startswith("_ZN") or name.startswith("_R")):
            return name
        try:
            return subprocess.run(["llvm-cxxfilt", name], capture_output=True, text=True).stdout.strip() or name
        except OSError:
            return name

    def section_of(self, a):
        for lo, hi, s in self.sections:
            if lo <= a < hi:
                return s
        return None

    def kind_of(self, a):
        s = self.section_of(a)
        if s is None:
            return "data"
        if s.name in (".got", ".got.plt"):
            return "got"
        flags = s["sh_flags"]
        if not flags & 1:  # not writable
            return "const"
        return "data"

    def data_ptr(self, v):
        """A pointer loaded from the GOT entry of a data symbol, as a
        pointer to it (anything else unchanged)."""
        if v[0] == "F" and v[1] in self.data_syms:
            return ("A", "data", self.data_syms[v[1]][0])
        return v

    def public_data_at(self, a, n):
        for name in PUBLIC_DATA:
            if name in self.data_syms:
                lo, sz = self.data_syms[name]
                if lo <= a and a + n <= lo + sz:
                    return True
        return False

    def got_target(self, a):
        return self.got.get(a, "?")

    def code(self, name):
        cands = [n for n in self.syms if n == name]
        if not cands:
            raise SystemExit(f"ctcheck: no function {name!r} in {self.path}")
        a, sz = self.syms[cands[0]]
        s = self.section_of(a)
        off = a - s["sh_addr"] + s["sh_offset"]
        self.f.seek(off)
        return a, self.f.read(sz)

    def read_u64(self, name):
        """The value of a `static` u64 in the binary."""
        a, _ = self.data_syms[name]
        s = self.section_of(a)
        self.f.seek(a - s["sh_addr"] + s["sh_offset"])
        return int.from_bytes(self.f.read(8), "little")

    def name_at(self, a):
        n = self.by_addr.get(a)
        return re.sub(r"::h[0-9a-f]{16}$", "", n) if n else "?"


# Calls the check knows. A noreturn function ends the path (its arguments
# were checked at the branch that leads to it); the others are summaries.
NORETURN = re.compile(
    r"(panic|unwrap_failed|expect_failed|handle_alloc_error|handle_error|index_fail|len_fail|"
    r"index_order_fail|out_of_bounds|abort|unreachable|capacity_overflow|assert_failed)"
)
CALLS = {"memcpy", "memmove", "memset"}
# A crate's declassification point: its result is public.
DECLASSIFY = re.compile(r"^verilith_\w+::ct::declassify$")
DECL = "declassify"
# Functions of no secret input whose result is public: the standard
# library's CPU-feature detection (on AArch64 it reads the auxiliary
# vector), which the dispatch calls once to fill its cache.
# (It takes no arguments, so none is checked.)
PUBLIC_CALLS = {"std_detect::detect::cache::detect_and_initialize"}


def callee_kind(name):
    if name is None:
        return None
    base = name.split("@")[0]
    if base in CALLS:
        return base
    if DECLASSIFY.match(base):
        return DECL
    if base in PUBLIC_CALLS:
        return "public"
    if NORETURN.search(base):
        return "noreturn"
    return None


# ---------------------------------------------------------------------------
# x86-64
# ---------------------------------------------------------------------------

GPR64 = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"] + [f"r{i}" for i in range(8, 16)]
X86_CANON = {}
for r, names in {
    "rax": ["eax", "ax", "al", "ah"], "rbx": ["ebx", "bx", "bl", "bh"], "rcx": ["ecx", "cx", "cl", "ch"],
    "rdx": ["edx", "dx", "dl", "dh"], "rsi": ["esi", "si", "sil"], "rdi": ["edi", "di", "dil"],
    "rbp": ["ebp", "bp", "bpl"], "rsp": ["esp", "sp", "spl"],
}.items():
    X86_CANON[r] = (r, 64)
    for n in names:
        X86_CANON[n] = (r, 32 if n.startswith("e") else 8)
for i in range(8, 16):
    X86_CANON[f"r{i}"] = (f"r{i}", 64)
    X86_CANON[f"r{i}d"] = (f"r{i}", 32)
    X86_CANON[f"r{i}w"] = (f"r{i}", 16)
    X86_CANON[f"r{i}b"] = (f"r{i}", 8)
for i in range(32):
    for p in ("xmm", "ymm", "zmm"):
        X86_CANON[f"{p}{i}"] = (f"v{i}", {"xmm": 128, "ymm": 256, "zmm": 512}[p])
for i in range(8):
    X86_CANON[f"k{i}"] = (f"k{i}", 64)
for f in ("rflags", "eflags", "flags"):
    X86_CANON[f] = ("flags", 64)

X86_ARGS = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
X86_CALLER_SAVED = ["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "flags"] + [f"v{i}" for i in range(32)] + [f"k{i}" for i in range(8)]

# Instructions whose time does not depend on their data (Intel's list of
# data operand independent timing instructions, and moves), by mnemonic,
# as capstone names them.
X86_DOIT = re.compile(
    r"^(v?)("
    r"mov|movabs|movzx|movsx|movsxd|movd|movq|movdq[au]|movdq[au](8|16|32|64)|movap[sd]|movup[sd]|movnt\w*|"
    r"movbe|bswap|lea|xchg|push|pop|cmov\w+|set\w+|"
    r"add|adc|sub|sbb|and|andn|or|xor|not|neg|inc|dec|cmp|test|bt|btc|btr|bts|"
    r"shl|shr|sar|rol|ror|rcl|rcr|shld|shrd|shlx|shrx|sarx|rorx|"
    r"imul|mul|mulx|"
    r"p?xor[dq]?|p?or[dq]?|p?and[dq]?|p?andn[dq]?|xorp[sd]|orp[sd]|andp[sd]|andnp[sd]|"
    r"pternlog[dq]|"
    r"padd[bwdq]|psub[bwdq]|pshufb|pshuf[dw]|pshufhw|pshuflw|shufp[sd]|shuf[if]\d+x\d+|"
    r"psll[wdq]|psrl[wdq]|psra[wdq]|psll(v[dq])?|psrl(v[dq])?|psl{2}dq|psrldq|palignr|alignr?[dq]?|"
    r"punpck\w+|pack[us]s\w+|unpck\w+|pblend\w+|blendp[sd]|pinsr[bwdq]|pextr[bwdq]|insert\w+|extract\w+|"
    r"broadcast\w+|pbroadcast\w+|perm\w+|"
    r"aesenc|aesenclast|aesdec|aesdeclast|aesimc|aeskeygenassist|"
    r"pclmulqdq|pclmul\w+|"
    r"sha256rnds2|sha256msg1|sha256msg2|sha1rnds4|sha1nexte|sha1msg1|sha1msg2|"
    r"ptest|pcmpeq[bwdq]|pcmpgt[bwdq]|pmovzx\w+|pmovsx\w+|"
    r"kmov[bwdq]|kor[bwdq]|kand[bwdq]|kxor[bwdq]|"
    r"zeroupper|nop|endbr64|data16"
    r")$"
)

X86_ZERO_IDIOMS = re.compile(r"^(v?p?xor[dq]?|v?xorp[sd]|sub|xor|v?psub[bwdq])$")


def x86_reg(cs, r):
    return X86_CANON.get(cs.reg_name(r))


def x86_check(elf, fn, public, verbose, entry_stack_args):
    cs = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    cs.detail = True
    addr0, code0 = elf.code(fn)
    chk = Check(fn, public, verbose)
    chk.elf = elf
    chk.ninsns = 0
    memo = {}

    st0 = State()
    for k, r in enumerate(X86_ARGS):
        st0.set(r, ptr(f"arg{k}", 0))
    st0.set("rsp", ptr("stack#0", 0))
    for k in range(entry_stack_args):
        st0.store("stack#0", 8 + 8 * k, 8, ptr(f"arg{6 + k}", 0))
    REGION_VARS.clear()
    REGION_VARS["stack#0"] = FRAMES.get(fn) if FRAMES is not None else None
    run_fn = None

    def mem_addr(st, op, insn):
        m = op.mem
        if m.base == X86.X86_REG_RIP:
            a = insn.address + insn.size + m.disp
            k = elf.kind_of(a)
            return ptr(k if k in ("const", "got") else "data", a), 0
        if m.segment not in (0, X86.X86_REG_DS, X86.X86_REG_SS):
            return ptr("tls", None), None
        bv = st.get(x86_reg(cs, m.base)[0]) if m.base else P
        iv = st.get(x86_reg(cs, m.index)[0]) if m.index else None
        if bv == S or iv == S:
            return S, None
        bv = elf.data_ptr(bv)
        if iv is not None:
            return (ptr(bv[1], None) if is_ptr(bv) else P), None
        if is_ptr(bv):
            return ptr(bv[1], bv[2]), m.disp
        return P, None

    def addr_ok(st, op, insn):
        m = op.mem
        for r in (m.base, m.index):
            if r and r != X86.X86_REG_RIP and st.get(x86_reg(cs, r)[0]) == S:
                chk.bad(insn, "address", f"{cs.reg_name(r)} is secret")

    def write_reg(st, name, v, insn, vex):
        c = X86_CANON.get(name)
        if c is None:
            return
        r, w = c
        if r in ("rip",):
            return
        full = (w in (32, 64) and not r.startswith("v")) or (r.startswith("v") and vex) or r.startswith("k") or r == "flags"
        masked = "{k" in insn.op_str and "{z}" not in insn.op_str
        if full and not masked:
            st.set(r, v)
        else:
            st.set(r, join(st.get(r), taint(v)) if not is_ptr(v) else taint(join(st.get(r), v)))

    def enter(name, st, insn, depth, tail):
        """Follows a call (or, `tail`, a jump) into `name`; the state after
        it returns, or None if it does not."""
        if name not in elf.syms or depth + 1 > MAX_DEPTH:
            chk.bad(insn, "call", f"to {name or 'an unknown function'}")
            return None
        sp = st.get("rsp")
        if not is_ptr(sp) or sp[2] is None:
            chk.bad(insn, "call", "with the stack pointer not known")
            return None
        region = f"stack#{depth + 1}"
        st2 = State()
        st2.regs = dict(st.regs)
        st2.mem = {k: v for k, v in st.mem.items() if k[0] != region}
        st2.dflt = {k: v for k, v in st.dflt.items() if k != region}
        st2.set("rsp", ptr(region, 0))
        # The arguments on the stack: at the caller's stack pointer, which
        # is 8 above the callee's (the return address between).
        for i in range(8, 8 + 64):
            c = st.mem.get((sp[1], sp[2] + (i if tail else i - 8)))
            if c is not None:
                st2.mem[(region, i)] = c
        REGION_VARS[region] = FRAMES.get(name) if FRAMES is not None else None
        key = (name, region, frozen(st2))
        if key in memo:
            out = memo[key]
        else:
            memo[key] = None
            out = run_fn(name, st2, depth + 1)
            memo[key] = out
        if out is None:
            return None
        out = out.copy()
        out.mem = {k: v for k, v in out.mem.items() if k[0] != region}
        out.dflt.pop(region, None)
        out.set("rsp", sp)
        return out

    def run(fn, st0, depth):
        addr, code = elf.code(fn) if depth else (addr0, code0)
        insns = {i.address: i for i in cs.disasm(code, addr)}
        chk.ninsns += len(insns)
        order = sorted(insns)
        nxt = {a: order[k + 1] if k + 1 < len(order) else None for k, a in enumerate(order)}
        region = f"stack#{depth}"
        states = {addr: st0}
        work = [addr]
        exits = []

        while work:
            a = work.pop()
            insn = insns.get(a)
            if insn is None:
                continue
            st = states[a].copy()
            if TRACE and a in TRACE:
                print(f"trace {a:#x} depth {depth} {insn.mnemonic} {insn.op_str}: " + ", ".join(f"{k}={v}" for k, v in sorted(st.regs.items()) if not k.startswith("v")), file=sys.stderr)
            succ = []  # [(address, state)]
            mn = insn.mnemonic
            ops = insn.operands
            vex = mn.startswith("v") or mn.startswith("k")
            eflags = insn.eflags if hasattr(insn, "eflags") else 0
            reads_flags = bool(eflags & (X86.X86_EFLAGS_TEST_OF | X86.X86_EFLAGS_TEST_SF | X86.X86_EFLAGS_TEST_ZF
                                         | X86.X86_EFLAGS_TEST_PF | X86.X86_EFLAGS_TEST_CF | X86.X86_EFLAGS_TEST_AF
                                         | X86.X86_EFLAGS_TEST_DF))
            writes_flags = bool(eflags & ~(X86.X86_EFLAGS_TEST_OF | X86.X86_EFLAGS_TEST_SF | X86.X86_EFLAGS_TEST_ZF
                                           | X86.X86_EFLAGS_TEST_PF | X86.X86_EFLAGS_TEST_CF | X86.X86_EFLAGS_TEST_AF
                                           | X86.X86_EFLAGS_TEST_DF))
            imp_r = [cs.reg_name(r) for r in insn.regs_read]
            imp_w = [cs.reg_name(r) for r in insn.regs_write]
            if any(r in ("rflags", "eflags", "flags") for r in imp_r):
                reads_flags = True
            if any(r in ("rflags", "eflags", "flags") for r in imp_w):
                writes_flags = True

            for op in ops:
                if op.type == X86.X86_OP_MEM and mn not in ("lea", "nop") and not mn.startswith("prefetch"):
                    addr_ok(st, op, insn)
                elif op.type == X86.X86_OP_MEM and mn.startswith("prefetch"):
                    addr_ok(st, op, insn)
            fall = nxt.get(a)
            if mn == "ret":
                exits.append(st)
            elif mn in ("ud2", "int3", "hlt"):
                pass
            elif mn == "jmp":
                if ops[0].type == X86.X86_OP_IMM and ops[0].imm not in insns:
                    out = enter(elf.name_at(ops[0].imm), st, insn, depth, True)  # a tail call
                    if out is not None:
                        exits.append(out)
                elif ops[0].type == X86.X86_OP_IMM:
                    succ.append((ops[0].imm, st))
                else:
                    # A tail call through the GOT (or a register holding a
                    # function's address from it); anything else is an
                    # indirect jump we cannot follow.
                    if ops[0].type == X86.X86_OP_MEM:
                        base, off = mem_addr(st, ops[0], insn)
                        v = chk.load_from(st, base, off, 8, insn)
                    else:
                        v = st.get(x86_reg(cs, ops[0].reg)[0])
                    if v[0] == "F" and v[1] != "?" and callee_kind(v[1]) is None:
                        out = enter(v[1], st, insn, depth, True)
                        if out is not None:
                            exits.append(out)
                    elif v[0] == "F" and v[1] != "?":
                        chk.bad(insn, "call", f"tail call to {v[1]}, not followed")
                    else:
                        chk.bad(insn, "indirect", "indirect jump")
            elif mn.startswith("j"):  # jcc, jrcxz
                if reads_flags and st.get("flags") == S:
                    chk.bad(insn, "branch", "on secret flags")
                for r in imp_r:
                    c = X86_CANON.get(r)
                    if c and c[0] != "flags" and st.get(c[0]) == S:
                        chk.bad(insn, "branch", f"on secret {r}")
                succ.append((ops[0].imm, st))
                succ.append((fall, st.copy()))
            elif mn == "call":
                op = ops[0]
                name = None
                if op.type == X86.X86_OP_IMM:
                    name = elf.name_at(op.imm)
                elif op.type == X86.X86_OP_MEM:
                    base, off = mem_addr(st, op, insn)
                    v = chk.load_from(st, base, off, 8, insn)
                    name = v[1] if v[0] == "F" else None
                elif op.type == X86.X86_OP_REG:
                    v = st.get(x86_reg(cs, op.reg)[0])
                    name = v[1] if v[0] == "F" else None
                kind = callee_kind(name)
                if kind is None:
                    out = enter(name, st, insn, depth, False) if name else None
                    if name is None:
                        chk.bad(insn, "call", "to an unknown function")
                    if out is not None:
                        succ.append((fall, out))
                elif kind == "noreturn":
                    pass
                else:
                    for r in ("rdi", "rsi", "rdx"):
                        if st.get(r) == S and kind not in (DECL, "public"):
                            chk.bad(insn, "call", f"{kind} with secret {r}")
                    dst = st.get("rdi")
                    if kind in ("memcpy", "memmove", "memset"):
                        chk.mem_op(st, kind, dst, st.get("rsi"), st.get("rdx"), insn)
                    for r in X86_CALLER_SAVED:
                        st.set(r, S)
                    if kind in ("memcpy", "memmove", "memset"):
                        st.set("rax", dst)
                    else:
                        st.set("rax", P)  # declassified
                    succ.append((fall, st))
            else:
                # Data.
                srcs = []
                loads = []
                for op in ops:
                    if op.type == X86.X86_OP_REG and op.access & capstone.CS_AC_READ:
                        c = x86_reg(cs, op.reg)
                        if c:
                            srcs.append(st.get(c[0]))
                    elif op.type == X86.X86_OP_MEM and mn != "lea" and op.access & capstone.CS_AC_READ:
                        base, off = mem_addr(st, op, insn)
                        loads.append(chk.load_from(st, base, off, op.size, insn))
                for r in imp_r:
                    c = X86_CANON.get(r)
                    if c and c[0] not in ("flags", "rsp", "rip"):
                        srcs.append(st.get(c[0]))
                if reads_flags:
                    srcs.append(st.get("flags"))
                vals = srcs + loads
                res = taint(joins(vals))
                regops = [op for op in ops if op.type == X86.X86_OP_REG]
                if any(v == S for v in vals) and not X86_DOIT.match(mn) and mn not in ("nop",):
                    chk.bad(insn, "variable-time", "secret operand of an instruction not known to be data-independent")
                # Special forms that keep a pointer, or clear a register.
                special = None
                if X86_ZERO_IDIOMS.match(mn) and len(regops) >= 2 and len(set(x86_reg(cs, o.reg) for o in regops[-2:])) == 1 \
                        and all(o.type == X86.X86_OP_REG for o in ops):
                    special = P
                    res = P
                if mn in ("mov", "movabs") and len(ops) == 2 and ops[0].size == 8:
                    if ops[1].type == X86.X86_OP_REG:
                        special = st.get(x86_reg(cs, ops[1].reg)[0])
                    elif ops[1].type == X86.X86_OP_MEM:
                        special = loads[0] if loads else S
                    elif ops[1].type == X86.X86_OP_IMM:
                        special = const(ops[1].imm)
                if mn == "mov" and len(ops) == 2 and ops[0].size == 4 and ops[0].type == X86.X86_OP_REG \
                        and ops[1].type == X86.X86_OP_IMM:
                    special = const(ops[1].imm & 0xFFFF_FFFF)
                if mn == "lea":
                    base, off = mem_addr(st, ops[1], insn)
                    if base == S:
                        special = S
                    elif is_ptr(base):
                        special = ptr(base[1], None if off is None or base[2] is None else base[2] + off)
                    else:
                        special = P
                if mn in ("add", "sub") and len(ops) == 2 and ops[0].type == X86.X86_OP_REG and ops[0].size == 8:
                    d = st.get(x86_reg(cs, ops[0].reg)[0])
                    if d[0] == "K" and ops[1].type == X86.X86_OP_IMM:
                        special = const(d[1] + (ops[1].imm if mn == "add" else -ops[1].imm))
                    if is_ptr(d):
                        if ops[1].type == X86.X86_OP_IMM:
                            k = ops[1].imm if mn == "add" else -ops[1].imm
                            special = ptr(d[1], None if d[2] is None else d[2] + k)
                        else:
                            o = srcs[-1] if ops[1].type == X86.X86_OP_REG else (loads[0] if loads else S)
                            special = S if o == S else ptr(d[1], None)
                        res = taint(special)
                if mn == "and" and ops[0].type == X86.X86_OP_REG and x86_reg(cs, ops[0].reg)[0] == "rsp":
                    special = ptr(f"stack@{a:x}", 0)
                    res = P
                if mn == "push":
                    v = srcs[0] if ops[0].type == X86.X86_OP_REG else (loads[0] if loads else P)
                    sp = st.get("rsp")
                    sp2 = ptr(sp[1], None if sp[2] is None else sp[2] - 8) if is_ptr(sp) else sp
                    chk.store_to(st, sp2, 0, 8, v, insn)
                    st.set("rsp", sp2)
                elif mn == "pop":
                    sp = st.get("rsp")
                    v = chk.load_from(st, sp, 0, 8, insn)
                    st.set("rsp", ptr(sp[1], None if sp[2] is None else sp[2] + 8) if is_ptr(sp) else sp)
                    write_reg(st, cs.reg_name(ops[0].reg), v, insn, True)
                elif mn == "xchg" and all(o.type == X86.X86_OP_REG for o in ops):
                    r0, r1 = x86_reg(cs, ops[0].reg)[0], x86_reg(cs, ops[1].reg)[0]
                    v0, v1 = st.get(r0), st.get(r1)
                    st.set(r0, v1 if ops[0].size == 8 else taint(v1))
                    st.set(r1, v0 if ops[0].size == 8 else taint(v0))
                else:
                    for op in ops:
                        if op.type == X86.X86_OP_REG and op.access & capstone.CS_AC_WRITE:
                            write_reg(st, cs.reg_name(op.reg), special if special is not None else res, insn, vex)
                        elif op.type == X86.X86_OP_MEM and op.access & capstone.CS_AC_WRITE and mn != "lea":
                            base, off = mem_addr(st, op, insn)
                            v = special if special is not None else res
                            chk.store_to(st, base, off, op.size, v, insn)
                    for r in imp_w:
                        c = X86_CANON.get(r)
                        if c and c[0] not in ("flags", "rip"):
                            if c[0] == "rsp":
                                if mn not in ("push", "pop"):
                                    sp = st.get("rsp")
                                st.set("rsp", ptr(sp[1], None) if is_ptr(sp) else S)
                                continue
                            write_reg(st, r, res, insn, vex)
                    if mn.startswith("rep") or mn.startswith("stos") or mn.startswith("movs"):
                        for r in ("rdi", "rsi", "rcx"):
                            if st.get(r) == S:
                                chk.bad(insn, "address", f"string op with secret {r}")
                        st.havoc_stack(S)
                if writes_flags:
                    st.set("flags", res if special is None or not is_ptr(special) else P)
                succ.append((fall, st))

            for (t, s2) in succ:
                if t is None or t not in insns:
                    if t is not None:
                        chk.bad(insn, "indirect", f"jump outside the function to {t:#x}")
                    continue
                if t not in states:
                    states[t] = s2.copy()
                    work.append(t)
                elif states[t].join_with(s2):
                    work.append(t)
        if not exits:
            return None
        out = exits[0].copy()
        for e in exits[1:]:
            out.join_with(e)
        return out

    run_fn = run
    run(fn, st0, 0)
    return chk, chk.ninsns


# ---------------------------------------------------------------------------
# AArch64
# ---------------------------------------------------------------------------

A64_CANON = {}
for i in range(31):
    A64_CANON[f"x{i}"] = (f"x{i}", 64)
    A64_CANON[f"w{i}"] = (f"x{i}", 32)
A64_CANON["sp"] = ("sp", 64)
A64_CANON["wsp"] = ("sp", 32)
A64_CANON["xzr"] = ("zr", 64)
A64_CANON["wzr"] = ("zr", 32)
A64_CANON["fp"] = ("x29", 64)
A64_CANON["lr"] = ("x30", 64)
for i in range(32):
    for p, w in (("v", 128), ("q", 128), ("d", 64), ("s", 32), ("h", 16), ("b", 8)):
        A64_CANON[f"{p}{i}"] = (f"v{i}", w)
A64_CANON["nzcv"] = ("flags", 4)

# Aliases of UBFM/SBFM/EXTR that capstone reports as reading their
# destination, which they only write.
A64_PURE_DEST = {"lsr", "lsl", "asr", "ror", "ubfx", "sbfx", "ubfiz", "sbfiz",
                 "uxtb", "uxth", "uxtw", "sxtb", "sxth", "sxtw"}

A64_CALLER_SAVED = [f"x{i}" for i in range(19)] + ["flags"] + [f"v{i}" for i in list(range(8)) + list(range(16, 32))]

# Arm's list of instructions with data-independent timing (FEAT_DIT), and
# loads and stores (whose timing depends on the address, checked apart).
A64_DIT = re.compile(
    r"^("
    r"mov|movz|movn|movk|mvn|fmov|umov|smov|ins|dup|movi|mvni|"
    r"ldr\w*|ldur\w*|ldp\w*|ldnp|str\w*|stur\w*|stp\w*|stnp|ld1\w*|st1\w*|ld1r|"
    r"add|adds|sub|subs|adc|adcs|sbc|sbcs|neg|negs|ngc|cmp|cmn|tst|and|ands|orr|orn|eor|eon|bic|bics|"
    r"lsl|lsr|asr|ror|lslv|lsrv|asrv|rorv|extr|ubfm|sbfm|bfm|ubfx|sbfx|bfi|bfxil|ubfiz|sbfiz|uxt[bhw]|sxt[bhw]|"
    r"mul|madd|msub|mneg|umull|smull|umulh|smulh|umaddl|smaddl|"
    r"csel|csinc|csinv|csneg|cset|csetm|cinc|cinv|cneg|ccmp|ccmn|"
    r"rev|rev16|rev32|rev64|rbit|clz|cls|"
    r"aese|aesd|aesmc|aesimc|pmull|pmull2|"
    r"sha256h|sha256h2|sha256su0|sha256su1|sha512h|sha512h2|sha512su0|sha512su1|"
    r"ext|tbl|tbx|zip1|zip2|uzp1|uzp2|trn1|trn2|xtn|xtn2|"
    r"shl|ushr|sshr|sli|sri|ushl|sshl|shrn|ushll|ushll2|sshll|usra|ssra|"
    r"addp|addv|"
    r"cmeq|cmhi|cmhs|cmgt|cmge|cmtst|bsl|bit|bif|not|"
    r"eor3|bcax|xar|rax1|"
    r"nop|hint|bti|paciasp|autiasp|pacibsp|autibsp|msr|mrs"
    r")$"
)


def a64_reg(cs, r):
    return A64_CANON.get(cs.reg_name(r))


def a64_check(elf, fn, public, verbose, entry_stack_args):
    cs = capstone.Cs(capstone.CS_ARCH_ARM64, capstone.CS_MODE_ARM)
    cs.detail = True
    chk = Check(fn, public, verbose)
    chk.elf = elf
    chk.ninsns = 0
    memo = {}
    st0 = State()
    for k in range(8):
        st0.set(f"x{k}", ptr(f"arg{k}", 0))
    st0.set("sp", ptr("stack#0", 0))
    for k in range(entry_stack_args):
        st0.store("stack#0", 8 * k, 8, ptr(f"arg{8 + k}", 0))
    REGION_VARS.clear()
    REGION_VARS["stack#0"] = FRAMES.get(fn) if FRAMES is not None else None

    def rv(st, r):
        c = a64_reg(cs, r)
        if c is None:
            return P
        if c[0] == "zr":
            return P
        return st.get(c[0])

    def wr(st, r, v, insn):
        c = a64_reg(cs, r)
        if c is None or c[0] == "zr":
            return
        name, w = c
        if name.startswith("v"):
            # Writes to a SIMD&FP register zero its upper bits, except the
            # element forms (INS, LD1 lane, ...), which merge.
            if "[" in insn.op_str.split(",")[0] or insn.mnemonic in ("ins", "mov") and "[" in insn.op_str.split(",")[0]:
                st.set(name, taint(join(st.get(name), v)))
            else:
                st.set(name, taint(v))
        else:
            st.set(name, v if w == 64 else taint(v))

    def mem_base(st, op):
        m = op.mem
        bv = rv(st, m.base) if m.base else P
        iv = rv(st, m.index) if m.index else None
        if bv == S or iv == S:
            return S, None
        bv = elf.data_ptr(bv)
        if iv is not None:
            return (ptr(bv[1], None) if is_ptr(bv) else P), None
        if is_ptr(bv):
            return ptr(bv[1], bv[2]), m.disp
        return P, None

    def enter(name, st, insn, depth):
        """Follows a call (`bl`, `blr`, or a tail `b`) into `name`; the
        state after it returns, or None if it does not. The callee's stack
        arguments are at the caller's stack pointer."""
        if name not in elf.syms or depth + 1 > MAX_DEPTH:
            chk.bad(insn, "call", f"to {name or 'an unknown function'}")
            return None
        sp = st.get("sp")
        if not is_ptr(sp) or sp[2] is None:
            chk.bad(insn, "call", "with the stack pointer not known")
            return None
        region = f"stack#{depth + 1}"
        st2 = State()
        st2.regs = dict(st.regs)
        st2.mem = {k: v for k, v in st.mem.items() if k[0] != region}
        st2.dflt = {k: v for k, v in st.dflt.items() if k != region}
        st2.set("sp", ptr(region, 0))
        st2.set("x30", P)
        for i in range(64):
            c = st.mem.get((sp[1], sp[2] + i))
            if c is not None:
                st2.mem[(region, i)] = c
        REGION_VARS[region] = FRAMES.get(name) if FRAMES is not None else None
        key = (name, region, frozen(st2))
        if key in memo:
            out = memo[key]
        else:
            memo[key] = None
            out = run(name, st2, depth + 1)
            memo[key] = out
        if out is None:
            return None
        out = out.copy()
        out.mem = {k: v for k, v in out.mem.items() if k[0] != region}
        out.dflt.pop(region, None)
        out.set("sp", sp)
        return out

    def run(fn, st0, depth):
        addr, code = elf.code(fn)
        insns = {i.address: i for i in cs.disasm(code, addr)}
        chk.ninsns += len(insns)
        order = sorted(insns)
        nxt = {a: order[k + 1] if k + 1 < len(order) else None for k, a in enumerate(order)}
        states = {addr: st0}
        work = [addr]
        exits = []
        while work:
            a = work.pop()
            insn = insns.get(a)
            if insn is None:
                continue
            st = states[a].copy()
            if TRACE and a in TRACE:
                print(f"trace {a:#x} depth {depth} {insn.mnemonic} {insn.op_str}: " + ", ".join(f"{k}={v}" for k, v in sorted(st.regs.items()) if not k.startswith("v")), file=sys.stderr)
            succ = []
            mn = insn.mnemonic
            ops = insn.operands
            fall = nxt.get(a)
            rd, wrt = insn.regs_access()
            rd_names = [cs.reg_name(r) for r in rd]
            wr_names = [cs.reg_name(r) for r in wrt]
            reads_flags = "nzcv" in rd_names or insn.cc not in (A64.ARM64_CC_INVALID, A64.ARM64_CC_AL, A64.ARM64_CC_NV)
            writes_flags = insn.update_flags or "nzcv" in wr_names
            mems = [op for op in ops if op.type == A64.ARM64_OP_MEM]
            for op in mems:
                m = op.mem
                for r in (m.base, m.index):
                    if r and rv(st, r) == S:
                        chk.bad(insn, "address", f"{cs.reg_name(r)} is secret")
            if mn == "ret":
                exits.append(st)
            elif mn in ("brk", "udf", "hlt"):
                pass
            elif mn == "b" and insn.cc in (A64.ARM64_CC_INVALID, A64.ARM64_CC_AL):
                if ops[0].imm not in insns:
                    out = enter(elf.name_at(ops[0].imm), st, insn, depth)  # a tail call
                    if out is not None:
                        exits.append(out)
                else:
                    succ.append((ops[0].imm, st))
            elif mn.startswith("b.") or (mn == "b" and reads_flags):
                if st.get("flags") == S:
                    chk.bad(insn, "branch", "on secret flags")
                succ.append((ops[-1].imm, st))
                succ.append((fall, st.copy()))
            elif mn in ("cbz", "cbnz", "tbz", "tbnz"):
                if rv(st, ops[0].reg) == S:
                    chk.bad(insn, "branch", f"on secret {cs.reg_name(ops[0].reg)}")
                succ.append((ops[-1].imm, st))
                succ.append((fall, st.copy()))
            elif mn in ("br", "braa", "brab"):
                chk.bad(insn, "indirect", "indirect jump")
            elif mn in ("bl", "blr"):
                name = None
                if mn == "bl":
                    name = elf.name_at(ops[0].imm)
                    if name == "?" or name.startswith("$"):
                        name = elf.got.get(ops[0].imm, name)
                else:
                    v = rv(st, ops[0].reg)
                    name = v[1] if v[0] == "F" else None
                kind = callee_kind(name)
                if kind is None:
                    out = enter(name, st, insn, depth) if name and name != "?" else None
                    if not name or name == "?":
                        chk.bad(insn, "call", "to an unknown function")
                    if out is not None:
                        out.set("x30", P)
                        succ.append((fall, out))
                elif kind != "noreturn":
                    for r in ("x0", "x1", "x2"):
                        if st.get(r) == S and kind not in (DECL, "public"):
                            chk.bad(insn, "call", f"{kind} with secret {r}")
                    dst = st.get("x0")
                    if kind in ("memcpy", "memmove", "memset"):
                        chk.mem_op(st, kind, dst, st.get("x1"), st.get("x2"), insn)
                    for r in A64_CALLER_SAVED:
                        st.set(r, S)
                    st.set("x0", dst if kind in ("memcpy", "memmove", "memset") else P)
                    succ.append((fall, st))
            else:
                srcs = []
                loads = []
                stores = []
                for k, op in enumerate(ops):
                    if k == 0 and mn in A64_PURE_DEST and op.access & capstone.CS_AC_WRITE:
                        continue  # capstone marks these aliases' destination as read too
                    if op.type == A64.ARM64_OP_REG and op.access & capstone.CS_AC_READ:
                        srcs.append(rv(st, op.reg))
                    elif op.type == A64.ARM64_OP_REG and mn.startswith("st") and not (op.access & capstone.CS_AC_WRITE):
                        srcs.append(rv(st, op.reg))
                if reads_flags:
                    srcs.append(st.get("flags"))
                is_load = mn.startswith("ld")
                is_store = mn.startswith("st")
                if is_load or is_store:
                    m = [op for op in ops if op.type == A64.ARM64_OP_MEM][0]
                    base, off = mem_base(st, m)
                    regs = [op for op in ops if op.type == A64.ARM64_OP_REG]
                    post = insn.writeback and any(op.type == A64.ARM64_OP_IMM for op in ops) and \
                        insn.op_str.rstrip().split("]")[-1].strip().startswith(",")
                    ea_off = 0 if post else off
                    n_each = 16 if any(cs.reg_name(r.reg).startswith("q") for r in regs) else \
                        (8 if any(cs.reg_name(r.reg)[0] in "xd" for r in regs) else 4)
                    if mn.startswith("ld1") or mn.startswith("st1"):
                        n_each = 16
                    if mn in ("ldrb", "strb", "ldurb", "sturb", "ldrsb", "ldursb"):
                        n_each = 1
                    if mn in ("ldrh", "strh", "ldurh", "sturh", "ldrsh", "ldursh"):
                        n_each = 2
                    if is_load:
                        k = 0
                        for r in regs:
                            if r.access & capstone.CS_AC_WRITE or not (r.access & capstone.CS_AC_READ):
                                if cs.reg_name(r.reg) == cs.reg_name(m.mem.base):
                                    continue
                                v = chk.load_from(st, base, None if ea_off is None else ea_off + k * n_each, n_each, insn)
                                if not (mn.startswith("ld1") and "[" in insn.op_str.split("},")[0].split("{")[-1]):
                                    pass
                                wr(st, r.reg, v, insn)
                                k += 1
                    else:
                        k = 0
                        data_regs = [r for r in regs if cs.reg_name(r.reg) != cs.reg_name(m.mem.base) or
                                     not insn.writeback]
                        for r in data_regs:
                            v = rv(st, r.reg)
                            chk.store_to(st, base, None if ea_off is None else ea_off + k * n_each, n_each, v, insn)
                            k += 1
                    if insn.writeback:
                        bname = a64_reg(cs, m.mem.base)[0]
                        bv = st.get(bname)
                        imm = [op.imm for op in ops if op.type == A64.ARM64_OP_IMM]
                        inc = imm[0] if post and imm else m.mem.disp
                        if is_ptr(bv):
                            st.set(bname, ptr(bv[1], None if bv[2] is None else bv[2] + inc))
                    # A load's or store's time depends on its address (checked
                    # above), not on the data it moves.
                else:
                    vals = srcs
                    if any(v == S for v in vals) and not A64_DIT.match(mn):
                        chk.bad(insn, "variable-time", "secret operand of an instruction not known to be data-independent")
                    res = taint(joins(vals))
                    special = None
                    regops = [op for op in ops if op.type == A64.ARM64_OP_REG]
                    if mn in ("mov",) and len(ops) == 2 and ops[1].type == A64.ARM64_OP_REG and \
                            a64_reg(cs, ops[0].reg) and a64_reg(cs, ops[0].reg)[1] == 64:
                        special = rv(st, ops[1].reg)
                    if mn in ("mov", "movz", "movn", "movk", "movi", "mvni") and len(ops) >= 2 and ops[1].type == A64.ARM64_OP_IMM:
                        special = P if mn != "movk" else res
                    if mn in ("add", "sub") and len(ops) == 3 and ops[2].type == A64.ARM64_OP_IMM and regops:
                        b = rv(st, ops[1].reg)
                        if is_ptr(b):
                            k = ops[2].imm
                            if ops[2].shift.value:
                                k <<= ops[2].shift.value
                            k = k if mn == "add" else -k
                            special = ptr(b[1], None if b[2] is None else b[2] + k)
                    if mn in ("add", "sub") and len(ops) == 3 and ops[2].type == A64.ARM64_OP_REG:
                        b = rv(st, ops[1].reg)
                        o = rv(st, ops[2].reg)
                        if is_ptr(b) and o != S:
                            special = ptr(b[1], None)
                    if mn in ("adrp", "adr"):
                        t = ops[1].imm
                        k = elf.kind_of(t)
                        special = ptr(k if k in ("const", "got") else "data", t)
                    if mn in ("eor",) and len(regops) == 3 and cs.reg_name(regops[1].reg) == cs.reg_name(regops[2].reg):
                        special = P
                        res = P
                    if mn == "movi" or mn == "mvni":
                        special = P
                    if mn == "adrp" or mn == "adr":
                        pass
                    written = False
                    for op in ops:
                        if op.type == A64.ARM64_OP_REG and op.access & capstone.CS_AC_WRITE:
                            wr(st, op.reg, special if special is not None else res, insn)
                            written = True
                    # Capstone gives some aliases (LSR, LSL, ... of UBFM) no operand
                    # access: their destination is still written.
                    if not written:
                        for r in wrt:
                            if cs.reg_name(r) != "nzcv":
                                wr(st, r, special if special is not None else res, insn)
                    if mn in ("add",) and special is not None and is_ptr(special) and special[1] == "got":
                        pass
                    if writes_flags:
                        st.set("flags", res)
                succ.append((fall, st))

            for (t, s2) in succ:
                if t is None or t not in insns:
                    if t is not None:
                        chk.bad(insn, "indirect", f"jump outside the function to {t:#x}")
                    continue
                if t not in states:
                    states[t] = s2.copy()
                    work.append(t)
                elif states[t].join_with(s2):
                    work.append(t)
        if not exits:
            return None
        out = exits[0].copy()
        for e in exits[1:]:
            out.join_with(e)
        return out

    run(fn, st0, 0)
    return chk, chk.ninsns


def demangle_all(names):
    """Demangles Rust symbols, in one call of llvm-cxxfilt."""
    names = list(names)
    try:
        out = subprocess.run(["llvm-cxxfilt"], input="\n".join(names), capture_output=True, text=True).stdout.split("\n")
    except OSError:
        out = names
    return {n: re.sub(r"::h[0-9a-f]{16}$", "", (out[i] if i < len(out) and out[i] else n)) for i, n in enumerate(names)}


def read_frames(path):
    """LLVM's stack-frame-layout remarks (rustc -C remark=stack-frame-layout):
    each function's variables, as sets of byte offsets from the stack
    pointer at entry."""
    raw = {}
    cur = None
    for line in open(path, errors="replace"):
        m = re.search(r"Function: (\S+)", line)
        if m:
            name = re.sub(r"\.llvm\.\d+$", "", m.group(1))
            cur = raw.setdefault(name, set())
            continue
        m = re.search(r"Offset: \[SP([+-]\d+)\], Type: (\w+), Align: \d+, Size: (\d+)", line)
        if m and cur is not None and m.group(2) == "Variable":
            off, size = int(m.group(1)), int(m.group(3))
            cur.update(range(off, off + size))
    names = demangle_all(raw)
    frames = {}
    for k, v in raw.items():
        frames.setdefault(names[k], set()).update(v)
    return frames


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("config")
    ap.add_argument("binary")
    ap.add_argument("--arch", default=None)
    ap.add_argument("--frames", default=None, help="the build's stack-frame-layout remarks")
    ap.add_argument("-v", action="store_true")
    args = ap.parse_args()
    with open(args.binary, "rb") as f:
        machine = ELFFile(f)["e_machine"]
    arch = args.arch or {"EM_X86_64": "x86_64", "EM_AARCH64": "aarch64"}[machine]
    elf = Elf(args.binary, arch)
    cfg_text = open(args.config).read()
    # "${NAME}" in the config is the value of the static u64 NAME in the
    # binary (a layout fact the binary was built with, such as a field's
    # offset).
    cfg_text = re.sub(r"\$\{(\w+)\}", lambda m: str(elf.read_u64(m.group(1))), cfg_text)
    cfg = json.loads(cfg_text)
    frames = read_frames(args.frames) if args.frames else None
    if frames is not None and not frames:
        raise SystemExit(f"ctcheck: no stack-frame-layout remarks in {args.frames} (was the crate compiled?)")
    PUBLIC_DATA.update(cfg.get("public_data", []))
    failed = False
    for f in cfg["functions"]:
        if f.get("arch", arch) != arch:
            continue
        public = [(f"arg{a}", int(o), int(n)) for a, o, n in f.get("public", [])]
        # A function the remarks do not name is checked without them (every
        # byte of its frame may be reached through an index).
        global FRAMES
        FRAMES = frames
        run = x86_check if arch == "x86_64" else a64_check
        chk, n = run(elf, f["name"], public, args.v, f.get("stack_args", 0))
        kinds = sorted(set(k for (_, k) in chk.violations))
        expect = f.get("expect", "pass")
        if expect == "pass":
            ok = not chk.violations
        elif expect == "any":
            ok = bool(kinds)
        else:
            ok = expect in kinds
        status = "ok  " if ok else "FAIL"
        what = "no leak" if not chk.violations else ", ".join(kinds)
        label = f["name"] + (" [round count secret]" if expect != "pass" and not f.get("public") and "note" in f else "")
        print(f"{status} {arch} {label} ({n} instructions): {what}" + ("" if expect == "pass" else f" (control, must show {expect})"))
        if (not ok or args.v) and chk.violations:
            for (_, _), msg in sorted(chk.violations.items()):
                print("       " + msg)
        failed |= not ok
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
