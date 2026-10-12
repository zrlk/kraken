#!/usr/bin/env python3
"""Translation validation, part 2: which object, and the data the proofs assume.

A. Object identity: the six C procedures in `aacsbr.rela.o` (the object tv.py
   compares against; `ld -r` merge of the `-ffunction-sections` build) against
   `aacsbr.pic.o` and `aacsbr.g.o` (one section per function): same bytes outside
   relocation fields, same relocation types, same resolved targets (symbol name
   or section+offset mapped to the symbol at that place).
B. Data: every `lab "X"` region of the proofs' footprints (sizes as stated in
   the Lean files, copied below) is resolved in the objects: inside its section,
   pairwise disjoint within each footprint (the separating conjunction is
   unsatisfiable otherwise), alignment facts the specs assume (`LayoutC`,
   `isAligned`), and the values the proofs assume (`LCPI14_4 = 1E20`,
   `LCPI17_11 = 0x3000001ff` as 16 little-endian bytes).
Exit 1 on any mismatch.
"""
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tv import Elf, relocs, OBJDIR, ROOT, tool  # noqa: E402

bad = []


def say(ok, msg):
  print(("ok    " if ok else "FAIL  ") + msg)
  if not ok:
    bad.append(msg)


# ------------------------------------------------------------- A ---------

def func_view(elf, rels, name):
  s = elf.sym(name)
  sec = elf.secs[s["shndx"]]
  b = elf.data[sec["off"] + s["value"] - sec["addr"]: sec["off"] + s["value"] - sec["addr"] + s["size"]]
  out = {}
  for o, (t, symidx, ad) in rels.get(sec["idx"], {}).items():
    if s["value"] <= o < s["value"] + s["size"]:
      # resolve to the symbol at the target (section-relative or named)
      rs = elf.syms[symidx]
      if rs["type"] == 3:  # STT_SECTION: find the symbol covering the target
        shndx = rs["shndx"]
        probe = ad + (4 if t != "R_X86_64_GOTOFF64" else 0)
        cands = sorted(x["name"] for x in elf.syms if x["shndx"] == shndx
                       and x["type"] in (0, 1, 2) and x["value"] <= probe < x["value"] + max(x["size"], 1))
        if cands:
          x = next(y for y in elf.syms if y["name"] == cands[0] and y["shndx"] == shndx)
          tgt = f"{cands[0]}{ad - x['value']:+#x}"
        else:
          tgt = f"{elf.secname(shndx)}+{ad:#x}"
      else:
        tgt = f"{rs['name']}{ad:+#x}"
      out[o - s["value"]] = (t, tgt)
  return b, out


def all_relocs(path):
  """target section index -> {offset: (type, symbol, addend)} (llvm-readelf -r,
  which reads CREL; the relocation section is identified by its file offset,
  since `-ffunction-sections` objects have many sections of one name)."""
  import re
  import subprocess
  e = Elf(path)
  outp = subprocess.run([tool("llvm-readelf"), "-r", path], capture_output=True,
                        text=True, check=True).stdout
  res, sec = {}, None
  for line in outp.splitlines():
    m = re.match(r"^Relocation section '(.+)' at offset (0x[0-9a-f]+) contains", line)
    if m:
      rs = next(s for s in e.secs if s["off"] == int(m[2], 16) and s["name"] == m[1])
      sec = rs["info"]
      res.setdefault(sec, {})
      continue
    m = re.match(r"^([0-9a-f]{16})\s+([0-9a-f]{16})\s+(R_\S+)\s+[0-9a-f]+\s+(\S+)\s*([+-])\s*([0-9a-f]+)$",
                 line)
    if m:
      ad = int(m[6], 16) * (-1 if m[5] == "-" else 1)
      res[sec][int(m[1], 16)] = (m[3], int(m[2], 16) >> 32, ad)
  return res


def part_a():
  print("== A. object identity (rela.o vs pic.o, g.o)")
  ref = os.path.join(OBJDIR, "aacsbr.rela.o")
  e0, r0 = Elf(ref), all_relocs(ref)
  for other in ("aacsbr.pic.o", "aacsbr.g.o"):
    p = os.path.join(OBJDIR, other)
    e1, r1 = Elf(p), all_relocs(p)
    for f in ("ff_aac_sbr_apply", "sbr_qmf_synthesis", "sbr_lf_gen", "sbr_hf_inverse_filter",
              "sbr_x_gen", "sbr_hf_assemble"):
      b0, x0 = func_view(e0, r0, f)
      b1, x1 = func_view(e1, r1, f)
      mask = set()
      for o, (t, _) in list(x0.items()) + list(x1.items()):
        mask.update(range(o, o + (8 if t.endswith("64") else 4)))
      same = len(b0) == len(b1) and all(b0[i] == b1[i] for i in range(len(b0)) if i not in mask)
      # pic.o calls other functions through relocations; rela.o (merged .text)
      # may have resolved some of them: compare only common offsets' targets,
      # and require the same offsets.
      diffs = [(hex(o), x0.get(o), x1.get(o)) for o in sorted(set(x0) | set(x1))
               if x0.get(o) != x1.get(o)]
      say(same and not diffs, f"{f}: rela.o vs {other}: {len(b0)} bytes, {len(x0)} relocs, "
          f"bytes {'equal' if same else 'DIFFER'}, reloc diffs {diffs[:4]}")


# ------------------------------------------------------------- B ---------

# Footprints, alignments and values are DERIVED from the Lean text (so they
# cannot go stale): every `(lab "X", N)` / `N ?@ lab "X"` region, every valued
# cell `Int.toBytes K V =@ lab "X"`, every `isAligned A (lab "X")`.
# Groups: the `def CstW` block of each Apply source (a single separating
# conjunction: strictly disjoint), and per file the union of all lab regions.
import glob
import re

SBR = os.path.join(ROOT, "Kraken/X64/Examples/Sbr")
# Apply's spec sources: ApplySpec.lean, plus optional extra files with a `def CstW`
# block (TV_APPLY_TEMPLATES, ':'-separated; e.g. a staged generator template).
APPLY_SRCS = [os.path.join(SBR, "ApplySpec.lean")] + [
    p for p in os.environ.get("TV_APPLY_TEMPLATES", "").split(":") if p and os.path.exists(p)]

NUM = r"(0x[0-9a-fA-F_]+|\d+)"
RE_REG = re.compile(r'\(lab "([\w.]+)",\s*' + NUM + r"\)")
RE_RES = re.compile(NUM + r'\s*\?@\s*\(?lab "([\w.]+)"\)?')
RE_VAL = re.compile(r"Int\.toBytes\s+" + NUM + r"\s+(\(?[\w.#]+\)?)\s*=@\s*\(?lab \"([\w.]+)\"")
RE_ALN = re.compile(r'isAligned\s+' + NUM + r'\s+\(lab "([\w.]+)"\)')


def num(s):
  return int(s.replace("_", ""), 0)


def bv_consts():
  """`def NAME : BitVec 64 := 0x...#64` anywhere under Sbr (e.g. dbl1E20)."""
  out = {}
  for f in glob.glob(os.path.join(SBR, "**/*.lean"), recursive=True):
    for m in re.finditer(r"def (\w+) : BitVec (\d+) := " + NUM + r"#\d+", open(f).read()):
      out[m[1]] = (num(m[3]), int(m[2]))
  return out


def value_bytes(k, expr, consts):
  e = expr.strip("()")
  m = re.fullmatch(r"(\w+)\.toInt", e)
  if m and m[1] in consts:
    v, bits = consts[m[1]]
    v = v - (1 << bits) if v >> (bits - 1) else v  # toInt
  else:
    v = num(e)
  return (v % (1 << (8 * k))).to_bytes(k, "little")


def scan(text, consts):
  regs, vals, aln = {}, {}, {}
  for m in RE_REG.finditer(text):
    regs[m[1]] = max(regs.get(m[1], 0), num(m[2]))
  for m in RE_RES.finditer(text):
    regs[m[2]] = max(regs.get(m[2], 0), num(m[1]))
  for m in RE_VAL.finditer(text):
    k = num(m[1])
    vals[m[3]] = value_bytes(k, m[2], consts)
    regs[m[3]] = max(regs.get(m[3], 0), k)
  for m in RE_ALN.finditer(text):
    aln[m[2]] = max(aln.get(m[2], 0), num(m[1]))
  return regs, vals, aln


def cstw_block(text):
  i = text.index("def CstW")
  j = text.find("\n\n", i)
  return text[i: j if j > 0 else len(text)]


def footprints():
  consts = bv_consts()
  fps = []  # (name, regs, vals, aln)
  for p in APPLY_SRCS:
    t = open(p).read()
    blk = cstw_block(t)
    if p.endswith("ApplySpec.lean"):  # alignments: the spec and the generated table
      t += open(os.path.join(SBR, "ApplyTable.lean")).read()
    r, v, _ = scan(blk, consts)
    # completeness: every label CstW mentions must have been parsed as a region
    missed = sorted(set(re.findall(r'lab "([\w.]+)"', blk)) - set(r))
    say(not missed, f"CstW of {os.path.relpath(p, ROOT)}: every label parsed as a region "
        f"({len(r)}); unparsed: {missed}")
    _, _, a = scan(t, consts)
    fps.append((f"Apply.CstW ({os.path.relpath(p, ROOT)})", r, v, a))
  for f in sorted(glob.glob(os.path.join(SBR, "**/*.lean"), recursive=True)):
    if f.endswith(("ApplySpec.lean", "ApplyTable.lean")):
      continue
    r, v, a = scan(open(f).read(), consts)
    if r or a:
      fps.append((f"{os.path.relpath(f, ROOT)} (all lab regions)", r, v, a))
  return fps


def find(label):
  for objn in ("aacsbr.rela.o", "sbrdsp.o", "float_dsp.o"):
    e = Elf(os.path.join(OBJDIR, objn))
    c = [x for x in e.syms if x["shndx"] and x["type"] != 3 and
         (x["name"] in (label, "." + label) or x["name"].endswith("." + label)
          or x["name"].lstrip(".").replace(".", "_") == label)]
    if c:
      return objn, e, c[0]
  return None, None, None


def part_b():
  print("== B. data (derived from the Lean text)")
  fps = footprints()
  if not fps or not fps[0][1]:
    say(False, "no CstW regions found in the Apply sources")
  for fp, regs, vals, aln in fps:
    placed = []
    for lab in sorted(set(regs) | set(aln)):
      n = regs.get(lab, 0)
      objn, e, s = find(lab)
      if s is None:
        print(f"ok    {fp}: {lab} ({n} B) is external (not in these objects; checked at link)")
        continue
      sec = e.secs[s["shndx"]]
      off = s["value"] - sec["addr"]
      say(off + n <= sec["size"], f"{fp}: {lab} = {s['name']} @ {objn}:{sec['name']}+{off:#x}, "
          f"{n} B inside {sec['name']} ({sec['size']:#x} B, align {sec['align']})")
      if n:
        placed.append((objn, sec["name"], off, n, lab))
      if lab in aln:
        a = aln[lab]
        say(sec["align"] >= a and off % a == 0, f"{fp}: {lab} aligned {a} (section align "
            f"{sec['align']}, offset {off:#x})")
      if lab in vals:
        got = e.data[sec["off"] + off: sec["off"] + off + len(vals[lab])]
        say(got == vals[lab], f"{fp}: {lab} value {got.hex()} expected {vals[lab].hex()}")
    nbad = len(bad)
    for i in range(len(placed)):
      for j in range(i + 1, len(placed)):
        a, b = placed[i], placed[j]
        if a[:2] == b[:2] and a[2] < b[2] + b[3] and b[2] < a[2] + a[3]:
          say(False, f"{fp}: {a[4]} and {b[4]} overlap in {a[0]}:{a[1]}")
    if len(bad) == nbad:
      print(f"ok    {fp}: {len(regs)} regions ({len(placed)} in these objects) pairwise disjoint, "
            f"{len(aln)} alignments, {len(vals)} values")
    for lab in aln:
      if find(lab)[2] is None:
        print(f"note  {fp}: {lab} external; alignment {aln[lab]} must come from its defining object at link")


if __name__ == "__main__":
  part_a()
  part_b()
  sys.exit(1 if bad else 0)
