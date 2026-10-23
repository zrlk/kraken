#!/usr/bin/env python3
"""Classify the instructions of scc's x64 listing that no block covers, for
a program's per-node instance (`Spike/Lib/Rows.lean`); the x64 counterpart
of `genrows_a64.py`.

`scc --code` tables the program's blocks (`<name>T`, `List Grp`, each
block's instructions with their sizes and its byte offset after its label)
and gives the assembler's instruction sizes (`<name>Asm.sizes`, one per
`.text` instruction or alignment directive, in text order). Every other
instruction of `.text` is a node of its own. This script emits, for those
instructions:

- `<name>R : List Grp`: each as a one-instruction block at its label, index
  and byte offset, with its size, in program order, so that
  `blocksIn <name>Cells <name>R` (checked by `kernel_rfl`) gives each row
  at its address as for the blocks;
- `<name>Rows : List Row`: its function, label, offset, kind (`RowK`) and
  whether the function is the runtime's;
- a coverage check: the blocks' and the rows' instructions are all of the
  program's, each once.

There is no x64 placement data (`scc --blocks` writes it on AArch64 only),
so no source nodes are listed.

Kinds: `label` (`leaq L(%rip), %r`), `flags` (a register operation whose
flags are undefined or unused: `flag_nd`), `switch` (`%rsp` written from a
register or masked: `sw_nd`, `swand_nd`), `dead` (`ud2`: `dead_nd`), `svc`
(`syscall`), `load` (`movq` from memory not off `%rbp`/`%rsp`, the thread
pointer's `%fs:k` included), `store` (`movq` to such memory), `rmw` (`lock
xadd`, `xchg` with memory), `other` (the script fails).

Usage: genrows_x64.py NAME LISTING.s CODE.lean OUT.lean CODEMOD
  NAME        the program's name in CODE.lean (`<name>Cells`, `<name>T`)
  LISTING.s   scc's x64 listing (scc --arch x64 -S prog.w)
  CODE.lean   scc --code's output for the same program
  OUT.lean    the generated module
  CODEMOD     the module CODE.lean is pasted as (imported by OUT.lean)

Python 3, standard library only; deterministic (program order throughout).
"""
import re
import sys

name, listing, codef, out, codemod = sys.argv[1:6]
code = open(codef).read()

LAB = r'[.A-Za-z_][\w.]*'

covered = set()
for g in re.finditer(r'⟨"(' + LAB + r')", \[(.*?)\]⟩', code, re.S):
    lab = g.group(1)
    for b in re.finditer(r'\((\d+), (\d+), \(parse\("(.*?)"\)\)\.zip \[([\d, ]*)\]\)', g.group(2), re.S):
        i = int(b.group(1))
        for k in range(len(b.group(3).split('\n'))):
            key = (lab, i + k)
            assert key not in covered, f'block instruction twice: {key}'
            covered.add(key)

m = re.search(r'def ' + name + r'Asm : Scc\.Sem\.X64\.Asm where\n  text := \w+\n  sizes := \[([\d, ]*)\]', code)
if not m:
    sys.exit(f'no {name}Asm sizes in {codef}')
sizes = [int(x) for x in m.group(1).split(', ')]

MEM = r'(-?\d+)?\((%\w+)\)'


def kind(ins):
    if re.fullmatch(r'leaq ' + LAB + r'\(%rip\), %\w+', ins):
        return 'label'
    if ins == 'syscall':
        return 'svc'
    if ins == 'ud2':
        return 'dead'
    if re.fullmatch(r'movq %\w+, %rsp', ins) or re.fullmatch(r'andq \$-?\d+, %rsp', ins):
        return 'switch'
    if re.fullmatch(r'movq %fs:\d+, %\w+', ins):
        return 'load'
    m = re.fullmatch(r'movq ' + MEM + r', %\w+', ins)
    if m and m.group(2) not in ('%rbp', '%rsp'):
        return 'load'
    m = re.fullmatch(r'movq %\w+, ' + MEM, ins)
    if m and m.group(2) not in ('%rbp', '%rsp'):
        return 'store'
    if re.fullmatch(r'(lock xaddq|xchgq) %\w+, ' + MEM, ins):
        return 'rmw'
    if re.fullmatch(r'(andq|orq|xorq|imulq|addq|subq) %\w+, %\w+', ins) or \
            re.fullmatch(r'(shlq|shrq|sarq) %cl, %\w+', ins) or re.fullmatch(r'xorl %(\w+), %\1', ins):
        return 'flags'
    return 'other'


rows = []      # (fn, label, index, byte offset, size, kind, instruction)
total = 0
fn = None
lab = None
idx = 0
off = 0
si = 0
section = '.text'
for line in open(listing).read().split('\n'):
    s = line.strip()
    if not s or s.startswith('#'):
        continue
    if s.startswith('.text'):
        section = '.text'
        continue
    if s.startswith(('.data', '.bss', '.rodata', '.section')):
        section = s
        continue
    if section != '.text':
        continue
    mt = re.fullmatch(r'\.type (' + LAB + r'), @function', s)
    if mt:
        fn = mt.group(1)
        continue
    if re.fullmatch(LAB + ':', s):
        lab = s[:-1]
        idx = 0
        off = 0
        continue
    if s.startswith('.p2align') or s.startswith('.balign'):
        if lab is not None and idx > 0:
            sys.exit(f'alignment inside a run after {lab}: the indices would count it')
        si += 1
        continue
    if s.startswith('.'):
        continue
    total += 1
    sz = sizes[si]
    si += 1
    if (lab, idx) not in covered:
        k = kind(s)
        if k == 'other':
            sys.exit(f'unclassified instruction outside the blocks: {lab}+{idx}: {s}')
        rows.append((fn or lab, lab, idx, off, sz, k, s))
    idx += 1
    off += sz

if si != len(sizes):
    sys.exit(f'sizes: {len(sizes)} entries, {si} cells in the listing')
if total != len(covered) + len(rows):
    sys.exit(f'coverage: {total} instructions, {len(covered)} in blocks, {len(rows)} rows')

o = []
o.append(f'''import Spike.Lib.Rows
import {codemod}

/-!
# The nodes of `{name}.w`'s x64 code outside its blocks

Generated by `Spike/Gen/genrows_x64.py` from scc's listing and `scc --code`'s
block tables (`{name}T`) and instruction sizes (`{name}Asm`). Every
instruction of `.text` is in a block of `{name}T` or a row here, once
(checked by the generator: {total} instructions, {len(covered)} in blocks,
{len(rows)} rows).

- `{name}R`: each row's instruction, with its size, as a one-instruction
  block at its label, index and byte offset; `{name}R_in` checks them
  against `{name}Cells` (`blocksIn`).
- `{name}Rows`: each row's function, label, offset, kind and runtime flag
  (`Spike.Lib.Rows.Row`).
-/

namespace SccCode

open Kraken Kraken.Promising.X64 Kraken.X64.Parser Scc.Cert.Rt.X64 Spike.Lib.Rows

/-- The instructions outside the blocks, one per block, in program order. -/
def {name}R : List Grp := [''')
groups = []
for r in rows:
    if groups and groups[-1][0] == r[1]:
        groups[-1][1].append(r)
    else:
        groups.append((r[1], [r]))
gl = []
for (l, items) in groups:
    bs = ',\n    '.join(f'({i}, {b}, (parse("{s}")).zip [{z}]) /- {k} -/' for (f, _, i, b, z, k, s) in items)
    gl.append(f'  ⟨"{l}", [{bs}]⟩')
o.append(',\n'.join(gl))
o.append(f''']

theorem {name}R_in : blocksIn {name}Cells {name}R := by kernel_rfl

/-- Each row's function, label, offset, kind and whether the function is
the runtime's (`scc_rt_*`, `_start`). -/
def {name}Rows : List Row := [''')
o.append(',\n'.join(
    f'  ⟨"{f}", "{l}", {i}, .{k}, {"true" if (f.startswith("scc_rt_") or f == "_start") else "false"}⟩'
    for (f, l, i, b, z, k, s) in rows))
o.append(f''']

-- The rows and the table agree on the places.
#guard {name}Rows.map (fun r => (r.l, r.k)) = {name}R.flatMap fun g => g.bs.map fun b => (g.l, b.1)

-- The blocks' and the rows' instructions number the program's cells.
#guard ({name}T ++ {name}R).foldl (fun n g => g.bs.foldl (fun n b => n + b.2.2.length) n) 0 =
  ({name}Cells.filter Scc.Cert.Rt.X64.notLab).length

end SccCode
''')
open(out, 'w').write('\n'.join(o))
print(f'{total} instructions: {len(covered)} in blocks, {len(rows)} rows')
