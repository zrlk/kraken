#!/usr/bin/env python3
"""Linux-side checks of a linked `--host raw` unit (untrusted).

Usage: Scc/Test/rawcheck.py x64|arm RAW_ELF LINUX_ELF [RAW_S RAW_LD]

RAW_ELF is `scc --host raw` output linked with `Scc/Test/elf/raw.ld`;
LINUX_ELF is the same program's `scc --host linux` output, linked as usual.
Checks, each printed as `ok`, `FAIL` or `skip`:

* header: a 64-bit little-endian static executable of the ISA, entry at
  `scc_rt_main`; no `PT_INTERP`, no `PT_DYNAMIC`; no `.dynamic`, `.interp`,
  `.rel*`/`.rela*`, `.got`, `.plt` section; no undefined symbol;
* text: `.text` starts at `scc_text_start`, granule-aligned (64 KiB);
* no system call instruction (`syscall`, `svc`) in the text;
* symbol order: `scc_text_start` <= `scc_kabi_start` = the first kernel
  routine trampoline; the trampolines in slot order, each right after the
  previous one (its `.size`); `scc_kabi_end` right after the last, and at or
  before every other function of the text;
* no block entry below `scc_kabi_end`: every text symbol there (but the
  AArch64 mapping symbols) is `scc_text_start`, `scc_kabi_start` or a
  trampoline (the tables reader's rule for the trampolines needs it);
* descriptor: `scc_gc_desc` has the magic and version 1, and its next five
  self-relative words resolve to `scc_text_start`, `scc_text_end`,
  `scc_gc_maps`, `scc_gc_succs` and `scc_gc_rseq`; `skip` when the unit has no
  `scc_gc_desc`. The granule word (the 8 bytes before `scc_text_end`,
  `scc_gc_desc - .`) must point at it when the text ends on a granule
  boundary; `skip` otherwise;
* user code: every `wc_*` function and `scc_rt_morestack` is the Linux one,
  instruction by instruction: equal bytes, except a pc-relative reference
  out of the function, whose target must instead lie in the same function at
  the same offset (by address: objdump's chosen name is ambiguous where
  several symbols share an address).
  On AArch64 the assembler text's local labels carry the function's index
  (`.L<n>_<f>`), which differs between the two (the raw program has fewer
  functions); the labels place no bytes, so the bytes are compared as on x64.

With RAW_S (the unit's assembler text) and RAW_LD (the link script,
`Scc/Test/elf/raw.ld`), two position-independence checks follow:

* relocations: RAW_S assembled to an object (`as`; `clang -c` on AArch64)
  has only PC- or page-relative relocations (x86-64: `R_X86_64_PC32`,
  `PLT32`, `PC64`; AArch64: `ADR_PREL_PG_HI21`, `ADR_PREL_LO21`,
  `ADD_ABS_LO12_NC`, `LDST*_ABS_LO12_NC`, `CALL26`, `JUMP26`, `CONDBR19`,
  `TSTBR14`, `LD_PREL_LO19`, `PREL32`, `PREL64`); every other one (absolute
  words `R_X86_64_64`/`32`/`32S`, `R_AARCH64_ABS64`/`ABS32`, `MOVW_UABS*`,
  `GOTPCREL`, ...) fails, listed with its site;
* two bases: RAW_S linked as RAW_ELF is (the same commands as
  `Scc/Test/elf.sh`), but with the text at two other granule-aligned bases
  (0x10000, 0x7a30000), gives the same `.text` and `.rodata` bytes: with no
  relocation applied by a loader, no byte depends on where the unit sits.
  The differing words are listed.

Exit status 0 when nothing fails. Needs `llvm-objdump` (on `PATH`, or the
newest `/usr/lib/llvm-*/bin/llvm-objdump`).
"""

import glob
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile

SLOTS = ["scc_rt_alloc", "scc_rt_alloc_tcb", "scc_rt_print", "scc_rt_park",
         "scc_rt_unpark", "scc_rt_abort", "scc_rt_exit_thread",
         "scc_rt_exit_process", "scc_rt_stack_take", "scc_rt_stack_release",
         "scc_rt_grow", "scc_rt_thread_reserve", "scc_rt_thread_init",
         "scc_rt_spawn"]
GRANULE = 65536
MAGIC = 0x3153444347434353
MACHINE = {"x64": 62, "arm": 183}


class Elf:
    def __init__(self, path):
        self.data = open(path, "rb").read()
        d = self.data
        if d[:4] != b"\x7fELF" or d[4] != 2 or d[5] != 1:
            raise ValueError(f"{path}: not a 64-bit little-endian ELF")
        (self.type, self.machine, _, self.entry, phoff, shoff, _, _, phentsize, phnum,
         shentsize, shnum, shstrndx) = struct.unpack_from("<HHIQQQIHHHHHH", d, 16)
        self.phdrs = [struct.unpack_from("<IIQQQQQQ", d, phoff + i * phentsize)
                      for i in range(phnum)]
        shs = [struct.unpack_from("<IIQQQQIIQQ", d, shoff + i * shentsize)
               for i in range(shnum)]
        strtab = shs[shstrndx]

        def name(off, tab):
            end = d.index(b"\0", tab[4] + off)
            return d[tab[4] + off:end].decode()
        self.sections = {}
        for s in shs:
            self.sections[name(s[0], strtab)] = s
        self.symbols = []  # (name, value, size, type, shndx)
        for s in shs:
            if s[1] == 2:  # SHT_SYMTAB
                st = shs[s[6]]
                for i in range(s[5] // 24):
                    n, info, _, shndx, value, size = struct.unpack_from("<IBBHQQ", d, s[4] + 24 * i)
                    self.symbols.append((name(n, st), value, size, info & 15, shndx))

    def sym(self, n):
        for s in self.symbols:
            if s[0] == n and s[4] != 0:
                return s[1]
        return None

    def read(self, addr, n):
        for s in self.sections.values():
            if s[1] == 1 and s[3] <= addr and addr + n <= s[3] + s[5]:
                off = s[4] + addr - s[3]
                return self.data[off:off + n]
        return None


def objdump():
    p = shutil.which("llvm-objdump")
    if p:
        return p
    cands = sorted(glob.glob("/usr/lib/llvm-*/bin/llvm-objdump"),
                   key=lambda s: int(re.search(r"llvm-(\d+)", s).group(1)))
    return cands[-1] if cands else None


INS = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(.*)$")
TGT = re.compile(r"(?:0x)?([0-9a-f]+) <([^>]+)>")


def disasm(path, arch):
    """address -> (bytes, text, target address or None, target name or None)."""
    tool = objdump()
    out = subprocess.run([tool, "-d", path],
                         capture_output=True, text=True, check=True).stdout
    ins = {}
    for line in out.splitlines():
        m = INS.match(line)
        if not m:
            continue
        a = int(m.group(1), 16)
        bs = bytes.fromhex(m.group(2).replace(" ", ""))
        text = m.group(3).strip()
        t = TGT.search(text)
        ins[a] = (bs, text, int(t.group(1), 16) if t else None, t.group(2) if t else None)
    return ins


def functions(elf):
    """Text functions: name -> (start, end); a size-0 symbol ends at the next one."""
    text = elf.sections.get(".text")
    if text is None:
        return {}
    lo, hi = text[3], text[3] + text[5]
    fs = sorted({(v, n, z) for (n, v, z, t, sh) in elf.symbols
                 if t == 2 and lo <= v < hi})
    out = {}
    for i, (v, n, z) in enumerate(fs):
        nxt = fs[i + 1][0] if i + 1 < len(fs) else hi
        out[n] = (v, v + z if z else nxt)
    return out


PCREL = {
    "x64": {"R_X86_64_PC32", "R_X86_64_PLT32", "R_X86_64_PC64"},
    "arm": {"R_AARCH64_" + t for t in
            ["ADR_PREL_PG_HI21", "ADR_PREL_LO21", "ADD_ABS_LO12_NC",
             "LDST8_ABS_LO12_NC", "LDST16_ABS_LO12_NC", "LDST32_ABS_LO12_NC",
             "LDST64_ABS_LO12_NC", "LDST128_ABS_LO12_NC", "CALL26", "JUMP26",
             "CONDBR19", "TSTBR14", "LD_PREL_LO19", "PREL32", "PREL64"]},
}
BASES = [0x10000, 0x7a30000]
A64_CC = ["clang", "--target=aarch64-linux-gnu", "-march=armv8.4-a"]


def assemble(arch, src, obj):
    cmd = ["as", "-o", obj, src] if arch == "x64" else A64_CC + ["-c", "-o", obj, src]
    subprocess.run(cmd, check=True, capture_output=True)


def link(arch, src, script, out, tmp):
    """`Scc/Test/elf.sh`'s link of a raw unit."""
    if arch == "x64":
        obj = os.path.join(tmp, "u.o")
        assemble(arch, src, obj)
        cmd = ["ld", "-static", "-T", script, "-z", "max-page-size=65536",
               "-z", "noexecstack", "-o", out, obj]
    else:
        cmd = A64_CC + ["-nostdlib", "-static", "-fuse-ld=lld",
                        f"-Wl,-T,{script},-z,max-page-size=65536,--build-id=none",
                        "-o", out, src]
    subprocess.run(cmd, check=True, capture_output=True)


RELHDR = re.compile(r"^RELOCATION RECORDS FOR \[(.*)\]:")
RELREC = re.compile(r"^([0-9a-f]+)\s+(\S+)\s*(.*)$")


def relocations(arch, src, tmp):
    """(section, offset, type, value) of each relocation of `src` assembled."""
    obj = os.path.join(tmp, "r.o")
    assemble(arch, src, obj)
    out = subprocess.run([objdump(), "-r", obj],
                         capture_output=True, text=True, check=True).stdout
    sec, rels = None, []
    for line in out.splitlines():
        m = RELHDR.match(line)
        if m:
            sec = m.group(1)
            continue
        m = RELREC.match(line)
        if m and sec is not None:
            rels.append((sec, int(m.group(1), 16), m.group(2), m.group(3).strip()))
    return rels


def where(fns, addr):
    """(function name, offset) of the non-empty function containing addr, or None."""
    hits = [(s, n) for n, (s, e) in fns.items() if s <= addr < e]
    if not hits:
        return None
    s, n = max(hits)
    return (n, addr - s)


def main(argv):
    if len(argv) not in (4, 6) or argv[1] not in MACHINE:
        print(__doc__.split("\n\n")[1])
        return 2
    arch, rawp, linp = argv[1], argv[2], argv[3]
    raw, lin = Elf(rawp), Elf(linp)
    results = []

    def check(name, ok, detail=""):
        results.append(ok)
        word = "ok" if ok is True else ("skip" if ok is None else "FAIL")
        print(f"{word:4}  {name}{': ' + detail if detail else ''}")

    # header
    check("header: static executable of the ISA", raw.type == 2 and raw.machine == MACHINE[arch],
          f"type {raw.type}, machine {raw.machine}")
    check("header: entry is scc_rt_main", raw.sym("scc_rt_main") == raw.entry,
          f"entry {raw.entry:#x}")
    bad_ph = [p[0] for p in raw.phdrs if p[0] in (2, 3)]
    check("header: no PT_INTERP, no PT_DYNAMIC", not bad_ph, str(bad_ph))
    bad_sec = [n for n in raw.sections if n in (".dynamic", ".interp", ".got", ".plt", ".got.plt")
               or n.startswith(".rel")]
    check("header: no dynamic or relocation section", not bad_sec, ", ".join(bad_sec))
    und = [s[0] for s in raw.symbols if s[4] == 0 and s[0]]
    check("header: no undefined symbol", not und, ", ".join(und))

    # text placement
    text = raw.sections[".text"]
    ts = raw.sym("scc_text_start")
    check("text: starts at scc_text_start, granule-aligned",
          ts == text[3] and text[3] % GRANULE == 0, f".text {text[3]:#x}, scc_text_start {ts}")

    # no system call
    ins = disasm(rawp, arch)
    sys_ins = [hex(a) for a, (_, t, _, _) in ins.items()
               if re.match(r"(syscall|svc)\b", t)]
    check("text: no system call instruction", not sys_ins, ", ".join(sys_ins[:5]))

    # symbol order
    ks, ke = raw.sym("scc_kabi_start"), raw.sym("scc_kabi_end")
    fns = functions(raw)
    tr = [fns.get(n) for n in SLOTS]
    order = ts is not None and ks is not None and ke is not None and None not in tr and \
        ts <= ks and tr[0][0] == ks and \
        all(tr[i + 1][0] == tr[i][1] for i in range(len(tr) - 1)) and tr[-1][1] == ke
    others = [v for n, (v, _) in fns.items() if n not in SLOTS]
    order = order and all(ke <= v for v in others)
    check("symbols: scc_text_start <= scc_kabi_start < trampolines (slot order) < scc_kabi_end"
          " <= every function", order,
          f"text {ts}, kabi [{ks}, {ke}), first function {min(others) if others else None}")
    # no block entry below scc_kabi_end: every text symbol there (any type but the AArch64
    # mapping symbols `$x`/`$d`) is a start label or a trampoline (local block labels are inside
    # their function, after its symbol)
    allowed = {"scc_text_start", "scc_kabi_start"} | set(SLOTS)
    tsec = raw.sections.get(".text")
    below = sorted({n for (n, v, _, t, sh) in raw.symbols
                    if n and not n.startswith("$") and t in (0, 1, 2) and sh not in (0, 0xfff1)
                    and tsec is not None and ke is not None
                    and tsec[3] <= v < ke and n not in allowed})
    check("symbols: no block entry below scc_kabi_end", ke is not None and not below,
          ", ".join(below))

    # descriptor: at scc_gc_desc, magic and version 1, then self-relative words that must
    # resolve to scc_text_start, scc_text_end, scc_gc_maps, scc_gc_succs, scc_gc_rseq; the
    # granule word (8 bytes before scc_text_end, `scc_gc_desc - .`) only once the granule
    # pass has run (its `wordPrefix` labels), else skip
    te = raw.sym("scc_text_end")
    da = raw.sym("scc_gc_desc")
    if da is None:
        check("descriptor", None, "no scc_gc_desc in this unit")
    else:
        hdr = raw.read(da, 16)
        ok = hdr is not None and struct.unpack("<QQ", hdr) == (MAGIC, 1)
        want = ["scc_text_start", "scc_text_end", "scc_gc_maps", "scc_gc_succs", "scc_gc_rseq"]
        bad = []
        for k, n in enumerate(want):
            a = da + 16 + 8 * k
            w = raw.read(a, 8)
            if w is None or raw.sym(n) is None or a + struct.unpack("<q", w)[0] != raw.sym(n):
                bad.append(n)
        check("descriptor: magic, version 1, self-relative words resolve", ok and not bad,
              f"at {da:#x}" + (f"; wrong: {', '.join(bad)}" if bad else ""))
        granule = te is not None and te % GRANULE == 0  # the granule pass ends the text on a boundary
        if not granule:
            check("descriptor: granule word", None, "no granule pass in this unit")
        else:
            gw = raw.read(te - 8, 8) if te else None
            check("descriptor: granule word points at it", gw is not None and
                  te - 8 + struct.unpack("<q", gw)[0] == da, "")

    # user code against Linux
    lins = disasm(linp, arch)
    lfns = functions(lin)
    names = sorted(n for n in fns if n.startswith("wc_") or n == "scc_rt_morestack")
    bad = []
    for n in names:
        if n not in lfns:
            bad.append(f"{n}: not in the Linux text")
            continue
        (rs, re_), (ls, le) = fns[n], lfns[n]
        if re_ - rs != le - ls:
            bad.append(f"{n}: size {re_ - rs} vs {le - ls}")
            continue
        for off in range(0, re_ - rs):
            r, l = ins.get(rs + off), lins.get(ls + off)
            if r is None and l is None:
                continue
            if r is None or l is None:
                bad.append(f"{n}+{off:#x}: instruction boundary differs")
                break
            rout = r[2] is not None and not (rs <= r[2] < re_)
            lout = l[2] is not None and not (ls <= l[2] < le)
            if rout or lout:
                # compare targets by the function containing them, not by the
                # name objdump picks (several symbols may share address 0)
                rt = where(fns, r[2]) if rout else None
                lt = where(lfns, l[2]) if lout else None
                if not (rout and lout and rt is not None and rt == lt
                        and len(r[0]) == len(l[0])):
                    bad.append(f"{n}+{off:#x}: {r[1]} vs {l[1]}")
                    break
            elif r[0] != l[0]:
                bad.append(f"{n}+{off:#x}: {r[0].hex()} vs {l[0].hex()}")
                break
    note = " (AArch64: local label names differ by the function index; bytes equal)" \
        if arch == "arm" else ""
    check(f"user code: {len(names)} functions equal to Linux{note}", not bad and bool(names),
          "; ".join(bad) or ", ".join(names))

    if len(argv) == 6:
        srcp, ldp = argv[4], argv[5]
        with tempfile.TemporaryDirectory() as tmp:
            # relocations
            rels = relocations(arch, srcp, tmp)
            absr = [r for r in rels if r[2] not in PCREL[arch]]
            check(f"relocations: {len(rels)}, all PC- or page-relative", not absr,
                  "; ".join(f"{t} at {s}+{o:#x} -> {v}" for s, o, t, v in absr))
            # two bases
            script = open(ldp).read()
            if script.count(". = 0;") != 1:
                check("two bases: same .text and .rodata bytes", False,
                      f"{ldp}: no single `. = 0;` to move")
            else:
                outs = []
                for b in BASES:
                    sp = os.path.join(tmp, f"raw{b:x}.ld")
                    open(sp, "w").write(script.replace(". = 0;", f". = {b:#x};"))
                    ep = os.path.join(tmp, f"u{b:x}")
                    link(arch, srcp, sp, ep, tmp)
                    outs.append(Elf(ep))
                diffs, base_ok = [], True
                for sn in (".text", ".rodata"):
                    a, b = (o.sections.get(sn) for o in outs)
                    if a is None or b is None:
                        if a is not b:
                            diffs.append(f"{sn}: present in one link only")
                        continue
                    if (a[3] - BASES[0]) != (b[3] - BASES[1]):
                        base_ok = False
                    ba, bb = (o.data[s[4]:s[4] + s[5]] for o, s in zip(outs, (a, b)))
                    if len(ba) != len(bb):
                        diffs.append(f"{sn}: size {len(ba)} vs {len(bb)}")
                        continue
                    words = sorted({i // 8 * 8 for i in range(len(ba)) if ba[i] != bb[i]})
                    diffs += [f"{sn}+{w:#x}" for w in words]
                check(f"two bases ({', '.join(hex(b) for b in BASES)}): same .text and .rodata bytes",
                      not diffs and base_ok,
                      (f"{len(diffs)} differing word(s): " + ", ".join(diffs)) if diffs
                      else ("" if base_ok else "sections not moved by the base"))

    return 0 if all(r is not False for r in results) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
