# Checking the `ff_aac_sbr_apply` proof

`ci.sh` re-checks the memory-safety proof of FFmpeg's `ff_aac_sbr_apply` (with its callees
`sbr_qmf_synthesis`, `sbr_lf_gen`, `sbr_hf_inverse_filter`, `sbr_x_gen`, `sbr_hf_assemble` and
the x86 `SBRDSPContext` routines) in `Kraken/X64/Examples/Sbr/`. The final theorem is
`Kraken.Examples.Sbr.ff_aac_sbr_apply_linked` (`Link.lean`); its docstring lists what is
assumed and what is open.

```
SBR_OBJ_DIR=/path/to/objects LLVM_BIN=/path/to/llvm/bin \
SBR_CAP_CMD="systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0" \
  scripts/sbr/ci.sh
```

Run it from anywhere inside the repository; everything is resolved from the repository root.

## Steps

| step | checks |
|---|---|
| build | `lake build` of each module of the proof, one at a time in dependency order (Spec, Dsp/*, the C procedures, ApplySpec, ApplyTable, the Apply shards, Apply, Link, Witness); fails on a nonzero exit, an `error`, or `declaration uses 'sorry'` |
| axioms | `#print axioms` (`Ax.lean`) of the final theorem, every procedure specification and the four satisfiability witnesses equals `baseline/axioms.txt`: each exactly `[propext, Classical.choice, Quot.sound]` |
| tv | `tv/tv.sh`, translation validation. The objects' hashes equal `baseline/objects.sha256`; the oleans are built from the current sources. The elaborated program texts (`tv/Export.lean`) are re-assembled with `llvm-mc` at the object addresses and compared with the objects byte for byte (relocations resolved, labels at their symbols, padding sized). `tv/tv_data.py` checks that the object variants agree and that every data region, alignment and constant the proofs assume holds in the objects. The row-crossing discipline (below). Finally each edit in `tv/mutations/` is applied to the exported text and must be caught |
| a2 | `tv/a2_discipline.py`, the row-crossing discipline: `HfAssemble.lean` (with `HfAssemble/*.lean`) crosses a row of `Y` only through `a2_row_spill` |
| heartbeats | `hbscan.py`: the generated per-block `maxHeartbeats` of the Apply shards equal `baseline/hb_table.txt`; no other `maxHeartbeats`/`maxRecDepth` option beyond `baseline/hb_baseline.txt` |
| srcscan | `srcscan.py`: no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, and none of the kernel-bypassing `debug.*` options (e.g. `debug.skipKernelTC`), `implemented_by`, `@[extern]`, `unsafe`, in `Kraken/X64/Examples/Sbr/`; elsewhere in `Kraken/` nothing beyond `baseline/srcscan_baseline.txt` (19 upstream uses, one an `unsafe def` in `Eval.lean`). `closure.py` prints which of those files the proof imports (`Rules/IntMisc.lean`, `Specs.lean`; the axioms step shows none of their `bv_decide` lemmas is used) |
| regen | `apply/check_regen.sh` and `hfasm/check_regen.sh`: the generators regenerate `ApplyTable.lean`, `Apply.lean`, `Apply/*.lean`, and `HfAssemble.lean`, `HfAssemble/{Base,Part1,Part2}.lean`, into a scratch directory; they must equal the checked-in files byte for byte (no Lean run) |
| tcb | `Tcb.lean`: the trusted closure of the final theorem, i.e. every declaration reachable from its statement through statements and definition bodies but not proofs, with its source lines per module, and a fingerprint of the closure's names, types and bodies. The fingerprint must equal `baseline/tcb_fingerprint.txt`. It changes exactly when the specification, the machine model or a program text changes; review such a change, then re-record the line printed as `FINGERPRINT` |

## What to review

The kernel checks every proof; what it cannot check is what the statement means. A
reviewer reads the trusted closure (`tcb` step), not the proofs:

- the specification: `Spec.lean` (callee contracts), `ApplySpec.lean` (`ApplySpec`,
  `ApplyPre`, `ApplyF`, `SbrWF`, `LayoutC`, `CstW`, `KeepD`; hand-written, definitions only),
  `Link.lean` (the final statement, `SbrPlaced`, `SbrSlots`, `SbrAssumed`), the `Dsp.lean` /
  `FloatDsp.lean` slot specifications;
- the machine model this work added to: `Kraken/X64/Semantics.lean`, `Syntax.lean`;
- not the program texts themselves but the checker that matches them to the objects:
  `tv/tv.py`, `tv/tv_data.py`, `tv/tv.sh`, `tv/Export.lean`, `tv/Fresh.lean`,
  `Kraken/X64/PrintIntel.lean`;
- these scripts: `Ax.lean` with `baseline/axioms.txt`, `srcscan.py`, `Tcb.lean`;
- for adequacy: whether the `SbrAssumed` contracts hold of the real routines (an over-strong
  one makes the theorem vacuous; see FD1) and the statements, not the proofs, of
  the satisfiability witnesses (`Witness.lean`, `Linked.lean`).

Block proofs, label tables and entry assertions, helper lemmas, the generated `Apply/*.lean`,
`HfAssemble/*.lean` and the tactics need no review for soundness.

## Environment

| variable | |
|---|---|
| `SBR_OBJ_DIR` | required: directory with `aacsbr.rela.o`, `aacsbr.pic.o`, `aacsbr.g.o`, `sbrdsp.o`, `float_dsp.o` (hashes in `baseline/objects.sha256`) |
| `LLVM_BIN` | directory of `llvm-objdump`, `llvm-objcopy`, `llvm-mc`, `llvm-readelf` (LLVM 21 was used); default: from `PATH` |
| `SBR_CAP_CMD` | optional command prefix for every `lake`/`lean` call, e.g. a memory cap. Without it lean runs uncapped. The largest module (`Apply.GainAsm`) peaks at about 9.5 GB, so modules must be built one at a time (`ci.sh` does); a plain parallel `lake build` of the Apply shards runs out of memory on ordinary machines |
| `SBR_OUT` | scratch and output, default `.lake/sbr-ci` |
| `SBR_SKIP_BUILD=1` | skip the build step (the tv step still refuses stale oleans) |

## The objects

FFmpeg n8_1, built with clang at `-O3 -mavx -msse4.2 -fPIC -mcmodel=medium
-fno-omit-frame-pointer -mtune=haswell -mprefer-vector-width=128 -fno-strict-aliasing
-ffunction-sections` (x86-64, optimized build of `libavcodec`):

- `aacsbr.pic.o`: `libavcodec/aacsbr.c` as compiled (one section per function);
- `aacsbr.rela.o`: the same object merged into one `.text` (`ld -r`), the addresses the
  Lean texts are named after (`ff_aac_sbr_apply.L66e0` …);
- `aacsbr.g.o`: the same compilation with debug information (DWARF);
- `sbrdsp.o`: `libavcodec/x86/sbrdsp.asm`, assembled with NASM for x86-64;
- `float_dsp.o`: `libavutil/x86/float_dsp.asm`, assembled with NASM 3.01 from the
  FFmpeg source root: `nasm -f elf64 -DPIC -g -F dwarf -I./ -P./config.asm
  libavutil/x86/float_dsp.asm -o float_dsp.o`.

`tv_data.py` checks that the six C procedures are identical in the three `aacsbr` objects.

## Expected output

The last lines of a passing run:

```
== CI summary
build       ok
axioms      ok
tv          ok
a2          ok
heartbeats  ok
srcscan     ok
regen       ok
tcb         ok
ci: exit 0
```

`tv` prints one line per program (18 programs, `findings=0 link=0`), `mutation m1` … `m8:
caught`, and `tv: exit 0`. Exit status 1 means a check failed; 2 means a setup problem
(objects missing or different, stale oleans).

## Why `Kraken.lean` does not import the proof

`Kraken.lean` (the default `lake build` target) does not import `Apply`, `Link` or `Witness`.
The Apply proof is split into about 35 shards, several of which need 8–9.5 GB each; the
default parallel build would run them together and exhaust memory. `ci.sh` builds the
whole proof, module by module.

## Optional: checking against a real binary

Off by default; the steps above and their output do not change. `SBR_REAL=1` adds a step
`real` (`real/check.sh`) that proves and checks the placement of the texts in a linked
executable:

```
SBR_REAL=1 SBR_BIN=/path/to/ffmpeg SBR_OBJ_DIR=… LLVM_BIN=… scripts/sbr/ci.sh
```

**The binary.** The FFmpeg 8.1 `ffmpeg` executable (x86-64 PIE, not stripped) of the same
optimized build as the objects above (same sources and compiler flags): it links
`aacsbr.o`, `sbrdsp.o` and `float_dsp.o` unchanged. The six C procedures are byte-identical
to `aacsbr.rela.o`, and the texts of `sbrdsp.o` and `float_dsp.o` to the binary's, outside
relocation fields. Its hash
is in `baseline/binary.sha256`. It is not in the repository; `SBR_BIN` points at it (with
`SBR_REAL=1` and no `SBR_BIN` the step fails).

**The Lean side** is the library `KrakenSbrReal` (`KrakenSbrReal/`, its own `lean_lib`, not
a default target; nothing in `Kraken/` imports it):

- `RealData.lean`, generated by `real/gen.py` from the binary and the texts `tv/Export.lean`
  prints: the address range from the QMF windows to `_GLOBAL_OFFSET_TABLE_` in address order
  (the twenty-six texts at their symbols, one cell per constant, string, callee and the GOT at
  the address the binary's instructions encode, labelled gaps between), with the size of
  every cell (the binary's instruction lengths).
- `Real.lean`: `rCE b` (that image at load bias `b`); `rPlaced b : SbrPlaced` for every `b`;
  `ff_aac_sbr_apply_real` (the linked theorem under `rCE b`, `SbrPlaced` discharged);
  `rlab_*` (each constant at `b` plus its link-time address); `rLab` (`LabAligned` for every
  page-aligned `b`); `rCst` and `real_hyps_sat_{sce,ps,cpe,a3}` under `rCE 0`.

**The check** (`real/check.sh`): the binary's hash; `gen.py`'s output equals the checked-in
`RealData.lean`; `lake build KrakenSbrReal` (and a source scan of it); `real/Ax.lean` equals
`baseline/axioms_real.txt`; `real/RealExport.lean` prints every cell of `rCE 0` with its
address, and `real/check.py` re-assembles every instruction there (llvm-mc, relocations
resolved against the Lean label addresses) and requires the binary's bytes, the binary's
instruction length as the cell size, the texts at their symbols, every referenced constant
pinned by an instruction, and the constants' values; finally four edits of the export must
each be caught. Adding a text: one entry in `real/real_lib.py`'s `TEXTS` and one in
`Real.rTexts`, then regenerate `RealData.lean` with `gen.py`.

`SbrSlots` stays a hypothesis: the slots are written at run time by the initialisation code.

## Line counts

`python3 scripts/sbr/loc.py [BASE [HEAD]] [--json FILE]` counts the Lean lines added between
`BASE` (default `28ca345`, the commit before the SBR work) and `HEAD`, by purpose: block
proofs, label tables and definitions, helper lemmas, program texts, procedure `spec`
compositions, proof-local tactics, comments; the headline files; the library (hand-written,
added to existing files, generated rules); tests; tooling. Each line of a new file is
attributed to the top-level declaration it belongs to. It needs only git and Python, and does
not build anything. The document's "Development effort" table is taken from its output.

## The `ff_aac_sbr_apply` generator

`ApplyTable.lean`, `Apply.lean` and `Apply/*.lean` are generated by `apply/gen.py`; edit its
inputs and regenerate (`python3 scripts/sbr/apply/gen.py`, writing into
`Kraken/X64/Examples/Sbr/`; `APPLY_OUT=<dir>` writes elsewhere). `ApplySpec.lean` is
hand-written and not generated. Inputs:

- `body.s`, `blocks.json`: the text cut into 434 blocks, by `apply/cut.py` from the
  disassembly `ff_aac_sbr_apply.s` and its relocation notes (`APPLY_PROG_DIR`);
- `templates/{head_table,mid,tail}.lean.in`: the fixed parts of `ApplyTable.lean`;
- `spec/<Shard>.py`: entry assertions and frames per block (`define(g)`);
- `override/<block>.lean`: the proof of each block (`theorem blk_<block>`);
- `lemmas/<Shard>.lean`, `lemmas/_table.lean`: shard helper lemmas and table lemmas;
- `../baseline/hb_table.txt`: per-block `maxHeartbeats`.

`gen.py`'s docstring lists the environment switches. The `regen` CI step checks that the
checked-in files are exactly the generator's output.

## The `sbr_hf_assemble` generator

`HfAssemble.lean` and `HfAssemble/{Base,Part1,Part2}.lean` are generated by `hfasm/build.sh`
(`gen.py`, then `split.py`, which balances the block theorems over the parts by the
heartbeats in `hfasm/hb_table.txt`); `HfAssemble/Cells.lean` is hand-written. Inputs:

- `body.s`: the text cut into 116 blocks, by `hfasm/mkbody.py` from the disassembly
  `sbr_hf_assemble.s` (`HFASM_PROG_DIR`);
- `spec.lean.in`, `proof_head.lean.in`: the fixed parts (the footprint and specification, the text);
- `spec_hf.py` (with `mregion.py`, `skel.py`): label assertions, frames, the generic block proofs;
- `override/<block>.lean`, `override/_lemmas.lean`, `lb01d_dev.lean`, `dev2.lean`: hand-written
  block proofs and lemmas;
- `hb_table.txt`: `<block> <measured> <budget>`; the budget becomes the block's `maxHeartbeats`.

`build.sh` writes into `Kraken/X64/Examples/Sbr/` (`HFASM_OUT` elsewhere; its header lists
the switches). The `regen` CI step checks that the checked-in files are its output.
