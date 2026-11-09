#!/usr/bin/env python3
"""Check the P2b granule layout of an scc executable (untrusted test harness).

Compiles a `.w` program with scc, assembles and links it the way
`Scc/Test/run.sh` does (x64: GNU `as` + `ld -static`; arm: `$A64_CC` from
`Scc/Test/a64link.sh`, unpinned), runs it (arm under `qemu-aarch64`), compares
the exit status with `T.code` when present, and checks with
readelf/nm/objdump that

  (a) `.text` starts at a multiple of G = 64 KiB;
  (b) for every granule G·k .. G·(k+1) that `.text` touches, `.text` reaches
      the granule end and its last 8 bytes hold the little-endian 64-bit
      value `desc - .`, where `desc` is the descriptor symbol (`--desc`) and
      `.` the address of the word;
  (c) no instruction straddles the reserved bytes: no decoded instruction
      starts before `G·(k+1) - 8` and ends after it.

(c) reads a linear-sweep disassembly; the reserved word itself decodes as
data, so an x64 sweep may resynchronise a few instructions after a granule
end.  That only affects decoding after the word, never the instruction that
precedes it.

Usage: granule_check.py [--arch x64|arm|both] [--desc SYM] [--keep DIR] T.w
Exit status 0 iff every check passes on every requested arch.
"""

import argparse
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile

G = 1 << 16
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SCC = os.path.join(ROOT, ".lake", "build", "bin", "scc")
A64_CC = ("clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static "
          "-fuse-ld=lld").split()
TOOLS = {
    "x64": {"readelf": "readelf", "nm": "nm", "objdump": ["objdump", "-d", "--insn-width=16"]},
    "arm": {"readelf": "llvm-readelf-21", "nm": "llvm-nm-21", "objdump": ["llvm-objdump-21", "-d"]},
}


def sh(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw).stdout


def build(arch, src, work):
    s = os.path.join(work, f"{arch}.s")
    exe = os.path.join(work, arch)
    sh([SCC, "--arch", arch, "-o", s, src])
    if arch == "x64":
        o = os.path.join(work, "x64.o")
        sh(["as", "-o", o, s])
        sh(["ld", "-static", "-o", exe, o])
    else:
        sh(A64_CC + ["-o", exe, s])
    return exe


def run(arch, exe):
    cmd = [exe] if arch == "x64" else ["qemu-aarch64", exe]
    return subprocess.run(cmd, capture_output=True).returncode


def text_section(arch, exe):
    out = sh([TOOLS[arch]["readelf"], "-S", "-W", exe])
    for line in out.splitlines():
        m = re.search(r"\]\s+\.text\s+PROGBITS\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
        if m:
            return tuple(int(x, 16) for x in m.groups())
    raise RuntimeError("no .text section")


def symbols(arch, exe):
    res = {}
    for line in sh([TOOLS[arch]["nm"], exe]).splitlines():
        parts = line.split()
        if len(parts) == 3:
            res[parts[2]] = int(parts[0], 16)
    return res


def symbol(arch, exe, name):
    return symbols(arch, exe).get(name)


def insns(arch, exe):
    """(start, length) of every decoded instruction in `.text`."""
    res = []
    pat = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+|[0-9a-f]{8}\s)")
    for line in sh(TOOLS[arch]["objdump"] + ["-j", ".text", exe]).splitlines():
        m = pat.match(line)
        if not m:
            continue
        addr, enc = int(m.group(1), 16), m.group(2).split()
        n = 4 if arch == "arm" and len(enc) == 1 and len(enc[0]) == 8 else len(enc)
        res.append((addr, n))
    return res


def check(arch, src, desc, keep):
    work = keep or tempfile.mkdtemp(prefix="granule_")
    os.makedirs(work, exist_ok=True)
    fails = []
    try:
        exe = build(arch, src, work)
        code_file = os.path.splitext(src)[0] + ".code"
        rc = run(arch, exe)
        if os.path.exists(code_file):
            want = int(open(code_file).read().strip())
            if rc != want:
                fails.append(f"exit status {rc}, expected {want}")
        addr, off, size = text_section(arch, exe)
        end = addr + size
        first, last = addr // G, (end - 1) // G
        print(f"[{arch}] .text 0x{addr:x}..0x{end:x} ({size} B), granules {first}..{last} "
              f"({last - first + 1} touched), exit {rc}")
        # (a)
        if addr % G:
            fails.append(f"(a) .text at 0x{addr:x} is not {G}-aligned")
        # (b)
        d = symbol(arch, exe, desc)
        if d is None:
            fails.append(f"(b) no descriptor symbol '{desc}'")
        blob = open(exe, "rb").read()
        bad_b = []
        for k in range(first, last + 1):
            w = G * (k + 1) - 8
            if w < addr or w + 8 > end:
                bad_b.append(f"granule {k}: word at 0x{w:x} outside .text")
                continue
            got = struct.unpack_from("<q", blob, off + (w - addr))[0]
            if d is None or got != d - w:
                bad_b.append(f"granule {k}: word at 0x{w:x} = 0x{got & (2**64 - 1):016x}")
        if bad_b:
            fails.append(f"(b) {len(bad_b)} of {last - first + 1} granule words wrong: "
                         + "; ".join(bad_b[:4]) + (" ..." if len(bad_b) > 4 else ""))
        # Which routine each granule boundary falls in (information only).
        syms = sorted((v, k) for k, v in symbols(arch, exe).items() if addr <= v < end)
        for k in range(first, last):
            b = G * (k + 1)
            owner = max(((v, n) for v, n in syms if v <= b), default=(addr, "?"))[1]
            print(f"[{arch}] boundary 0x{b:x} inside {owner}")
        # (c)
        bad_c = []
        words = [G * (k + 1) - 8 for k in range(first, last + 1)]
        decoded = insns(arch, exe)
        if not decoded:
            fails.append("(c) disassembly produced no instructions")
        for s, n in decoded:
            for w in words:
                if s < w < s + n:
                    bad_c.append(f"insn 0x{s:x}+{n} straddles 0x{w:x}")
        if bad_c:
            fails.append(f"(c) {len(bad_c)} straddling instruction(s): " + "; ".join(bad_c[:4]))
    except subprocess.CalledProcessError as e:
        fails.append(f"build failed: {' '.join(e.cmd[:3])}...: {e.stderr.strip()[:300]}")
    finally:
        if not keep:
            shutil.rmtree(work, ignore_errors=True)
    for f in fails:
        print(f"[{arch}] FAIL {f}")
    if not fails:
        print(f"[{arch}] ok (a) (b) (c)")
    return not fails


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--arch", default="both", choices=["x64", "arm", "both"])
    ap.add_argument("--desc", default="scc_desc", help="descriptor symbol (default scc_desc)")
    ap.add_argument("--keep", help="keep build products in this directory")
    ap.add_argument("src")
    a = ap.parse_args()
    if not os.path.exists(SCC):
        sys.exit(f"{SCC} missing: run `lake build scc scc_x64 scc_arm` first")
    archs = ["x64", "arm"] if a.arch == "both" else [a.arch]
    ok = all([check(arch, os.path.abspath(a.src), a.desc,
                    a.keep and os.path.join(a.keep, arch)) for arch in archs])
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
