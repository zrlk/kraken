#!/usr/bin/env python3
"""Litmus tests for herd's `NoRet` atomics with a zero-register destination.

diycross7 only emits the no-result atomics as `ST<op>` (`Amo.StAdd`, ...; see
`gen.sh`); its `Amo.Swp`, `Amo.Cas` and `Amo.LdAdd` edges always return the
old value to a register, which is also how they observe the read. This script
writes the zero-destination forms (`LD<op>{,A,L,AL} Ws,WZR`, `SWP{,A,L,AL}
Ws,WZR`, `CAS{,A,L,AL} WZR,Wt`, `STADDL`), with the same atomics returning to
a register as controls, into the shapes LB, MP, S, WRC and 2+2W, each with
the atomic's read as the source of the ordering under test (`DMB LD`,
`DSB LD`, `DMB SY`, `DSB SY`, a later release store, nothing).

The read value is discarded, so each test observes it through the final
value of the atomic's location instead: the atomic's write immediately
follows, in coherence order, the write it read from.
- `LDADD`/`STADDL` add 1 (2 -> 3), `LDCLR` clears bit 0 (3 -> 2);
- `SWP` writes 1: a final 1 means it read the other thread's 2;
- `CAS WZR,W4` (`W4 = 3`) succeeds only on 0: the location starts at 5 and
  the other thread writes 0, so a final 3 means it read that 0.

Usage: gen_zr.py <directory>
"""
import os
import sys

# name -> (setup lines, instruction with {a} for the address register,
#          initial value, value the other thread writes, observed final value)
ATOMS = {}
for sfx in ["", "a", "l", "al"]:
    S = sfx.upper()
    ATOMS[f"ldadd{sfx}.zr"] = (["MOV W0,#1"], f"LDADD{S} W0,WZR,[{{a}}]", 0, 2, 3)
    ATOMS[f"swp{sfx}.zr"] = (["MOV W0,#1"], f"SWP{S} W0,WZR,[{{a}}]", 0, 2, 1)
    ATOMS[f"cas{sfx}.zr"] = (["MOV W4,#3"], f"CAS{S} WZR,W4,[{{a}}]", 5, 0, 3)
ATOMS["ldclr.zr"] = (["MOV W0,#1"], "LDCLR W0,WZR,[{a}]", 0, 3, 2)
ATOMS["staddl"] = (["MOV W0,#1"], "STADDL W0,[{a}]", 0, 2, 3)
# controls: the old value returned to a register (an ordinary RMW read)
ATOMS["ldadd.reg"] = (["MOV W0,#1"], "LDADD W0,W5,[{a}]", 0, 2, 3)
ATOMS["ldadda.reg"] = (["MOV W0,#1"], "LDADDA W0,W5,[{a}]", 0, 2, 3)
ATOMS["swpa.reg"] = (["MOV W0,#1"], "SWPA W0,W5,[{a}]", 0, 2, 1)
ATOMS["casa.reg"] = (["MOV W4,#3", "MOV W6,#0"], "CASA W6,W4,[{a}]", 5, 0, 3)

SMALL = ["ldadd.zr", "ldadda.zr", "swpa.zr", "cas.zr", "casa.zr", "staddl",
         "ldadd.reg", "ldadda.reg", "casa.reg"]

# fence name -> (lines between the atomic and the next access, store mnemonic)
FENCES = {
    "po": ([], "STR"),
    "dmb.ld": (["DMB LD"], "STR"),
    "dsb.ld": (["DSB LD"], "STR"),
    "dmb.sy": (["DMB SY"], "STR"),
    "dsb.sy": (["DSB SY"], "STR"),
    "dmb.st": (["DMB ST"], "STR"),
    "popl": ([], "STLR"),
}


def write_val(v, reg, addr):
    return [f"STR WZR,[{addr}]"] if v == 0 else [f"MOV {reg},#{v}", f"STR {reg},[{addr}]"]


def table(threads):
    n = max(len(t) for t in threads)
    cols = [t + [""] * (n - len(t)) for t in threads]
    widths = [max(len(x) for x in c + [f"P{i}"]) for i, c in enumerate(cols)]
    rows = [" " + " | ".join(f"P{i}".ljust(w) for i, w in enumerate(widths)) + " ;"]
    for r in range(n):
        rows.append(" " + " | ".join(cols[i][r].ljust(widths[i]) for i in range(len(cols))) + " ;")
    return "\n".join(rows)


def litmus(name, doc, init, threads, cond):
    return f'AArch64 {name}\n"{doc}"\n{{\n{init}\n}}\n{table(threads)}\nexists ({cond})\n'


def gen(out):
    tests = {}

    def add(name, doc, init, threads, cond):
        tests[name] = litmus(name, doc, init, threads, cond)

    for an, (setup, ins, x0, vin, obs) in ATOMS.items():
        small = an in SMALL
        init0 = "x=5; " if x0 else ""
        inity = "y=5; " if x0 else ""
        # LB: atomic read of x (from P1's write), then F, then a write of y
        for fn, (fl, st) in FENCES.items():
            add(f"LB+{an}-{fn}+dmb.sy", f"{an}; {fn}; write || read; DMB SY; write",
                f"{init0}\n0:X1=x; 0:X3=y;\n1:X1=y; 1:X3=x;",
                [setup + [ins.format(a="X1")] + fl + ["MOV W7,#1", f"{st} W7,[X3]"],
                 ["LDR W0,[X1]", "DMB SY"] + write_val(vin, "W2", "X3")],
                f"[x]={obs} /\\ 1:X0=1")
        # MP: a write of x, DMB SY, a write of y || atomic read of y, F, read of x
        for fn in ["po", "dmb.ld", "dsb.ld", "dmb.sy", "dsb.sy"]:
            fl = FENCES[fn][0]
            add(f"MP+dmb.sy+{an}-{fn}", f"write; DMB SY; write || {an}; {fn}; read",
                f"{inity}\n0:X1=x; 0:X3=y;\n1:X1=y; 1:X3=x;",
                [["MOV W0,#1", "STR W0,[X1]", "DMB SY"] + write_val(vin, "W2", "X3"),
                 setup + [ins.format(a="X1")] + fl + ["LDR W7,[X3]"]],
                f"[y]={obs} /\\ 1:X7=0")
        # S: a write of x, DMB SY, a write of y || atomic read of y, F, a write of x
        for fn in ["po", "dmb.ld", "dsb.ld", "dmb.sy", "popl"]:
            fl, st = FENCES[fn]
            add(f"S+dmb.sy+{an}-{fn}", f"write; DMB SY; write || {an}; {fn}; write",
                f"{inity}\n0:X1=x; 0:X3=y;\n1:X1=y; 1:X3=x;",
                [["MOV W0,#2", "STR W0,[X1]", "DMB SY"] + write_val(vin, "W2", "X3"),
                 setup + [ins.format(a="X1")] + fl + ["MOV W7,#1", f"{st} W7,[X3]"]],
                f"[y]={obs} /\\ [x]=2")
        if not small:
            continue
        for fn in ["po", "dmb.ld", "dsb.ld", "dmb.sy"]:
            fl, st = FENCES[fn]
            # WRC: write x || atomic read of x, F, write y || read y, DMB SY, read x
            add(f"WRC+{an}-{fn}+dmb.sy", f"write || {an}; {fn}; write || read; DMB SY; read",
                f"{init0}\n0:X1=x;\n1:X1=x; 1:X3=y;\n2:X1=y; 2:X3=x;",
                [write_val(vin, "W2", "X1"),
                 setup + [ins.format(a="X1")] + fl + ["MOV W7,#1", f"{st} W7,[X3]"],
                 ["LDR W0,[X1]", "DMB SY", "LDR W2,[X3]"]],
                f"[x]={obs} /\\ 2:X0=1 /\\ 2:X2={x0}")
            # 2+2W: atomic read of x, F, write y || write y, DMB SY, write x
            add(f"2+2W+{an}-{fn}+dmb.sy", f"{an}; {fn}; write || write; DMB SY; write",
                f"{init0}\n0:X1=x; 0:X3=y;\n1:X1=y; 1:X3=x;",
                [setup + [ins.format(a="X1")] + fl + ["MOV W7,#1", f"{st} W7,[X3]"],
                 ["MOV W2,#2", "STR W2,[X1]", "DMB SY"] + write_val(vin, "W8", "X3")],
                f"[x]={obs} /\\ [y]=2")

    for name, text in tests.items():
        with open(os.path.join(out, name + ".litmus"), "w") as f:
            f.write(text)
    return len(tests)


if __name__ == "__main__":
    print(f"gen_zr.py: {gen(sys.argv[1])} tests")
