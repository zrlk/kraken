import Scc.Config
import Scc.Cert.Sha256
import Scc.Cert.SrcTerm

/-!
# Certificate skeletons (`scc --cert`)

`render` writes the Lean file `scc --cert FILE.lean` produces next to the
assembler text. It is a *skeleton*: it checks the program's acceptance and
its placement, not yet the compiler's correctness, whose theorem does not
exist yet (see the docstring it carries, `docstring`):

1. it embeds the WeakCore source and the emitted assembler text verbatim, as
   string literals, with their SHA-256 digests in a comment;
2. a reproducibility check, by evaluation (`#guard`, not a proof): the
   source, run through `scc`'s frontend, lowering and emitter at elaboration
   time, gives exactly the embedded text;
3. Kraken's parser reads the embedded text (at elaboration time), and
   `decide +kernel` proves the architecture's lowerability predicate of the
   parsed program: `Scc.Emit.X64.ProgramWCLowerable` on x64
   (`Scc/Emit/X64Lowerable.lean`), Kraken's `Program.WCLowerable` on AArch64
   (`Kraken/Promising/Lower/Lowerable.lean`);
4. the source program as a term (`Scc.Cert.SrcTerm.progTerm`), checked
   against the frontend's reading of the source by evaluation; whether it
   is in the fragment `Scc.Lower.Accepted0` (by `decide +kernel`, either
   way); and `placeOK` (`Scc/Cert/PlaceOKA64.lean`, `PlaceOKX64.lean`) of
   `Out.ofEmitted (lowerAll cfg prog_src)` (`Scc/Cert/PlaceDataA64.lean`,
   `PlaceDataX64.lean`; on x64 at the assembler's sizes and label offsets),
   at the canonical configuration with the program's thread entries and
   their stack budget (`Placement`). The kernel runs the lowering once, to
   check `out = outLit` against the literal `outLit` (`scc_lit%`,
   `Scc/Cert/OutLit.lean`; in three steps on literals,
   `Scc/Cert/OutStageA64.lean`, `OutStageX64.lean`, the lowering's itself in
   two, the depth limit and the lowering, `Scc/Cert/LowerStage.lean`),
   and decides the
   components on the literal in separate declarations (A1 to A8, A9
   where the ISA checks it, A11; each its own kernel check), or, for
   `Placement.fails`, the one failing component (`prog_not_placeOK`), with
   the loader's parse of the embedded text checked against that output by
   evaluation (`parsesTo`); for an accepted program, `prog_cert_ready`, the
   two together.

A program without a stack need table (non-tail recursion) cannot satisfy
`placeOK`'s A4: it gets no certificate, partial or not, but a file with its
source and the reason (`renderOutside`).

The file imports `Scc.Cert.X64` and `Scc.Cert.OutStageX64`, or
`Scc.Cert.Arm` and `Scc.Cert.OutStageA64` (the staged check of `out =
outLit`, over the literals' `ToExpr` instances `Scc.Cert.OutLitX64`,
`OutLitA64` and the placement data `Scc.Cert.PlaceDataX64`,
`PlaceDataA64`), and `Scc.Cert.SrcTerm` (one ISA per file). It checks
with `lake env lean FILE.lean` in the Kraken package, or
`scc --check FILE.lean`. This module itself imports no ISA.
-/

namespace Scc.Cert.Gen

open Scc

/-- A Lean string literal for `s`, one source line per line of `s` (string
gaps: `\` at the end of a line, the next line's leading spaces skipped).
Backslashes, quotes, tabs, carriage returns and other control characters are
escaped, and so is a space at the start of a line (a gap would skip it). -/
def quote (s : String) : String := Id.run do
  let esc (atStart : Bool) (c : Char) : String :=
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c == '\t' then "\\t"
    else if c == '\r' then "\\r"
    else if c == ' ' && atStart then "\\x20"
    else if c.toNat < 0x20 || c.toNat == 0x7f then
      let h := String.ofList (Nat.toDigits 16 c.toNat)
      "\\x" ++ (if h.length < 2 then "0" else "") ++ h
    else c.toString
  let lines := s.splitOn "\n"
  let mut out := "\"\\\n  "
  let mut i := 0
  for l in lines do
    let cs := l.toList
    out := out ++ String.join ((cs.zipIdx).map fun (c, j) => esc (j == 0) c)
    if i + 1 < lines.length then out := out ++ "\\n\\\n  "
    i := i + 1
  return out ++ "\""

/-- A one-line Lean string literal for `s` (a label name). -/
def quoteLine (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else c.toString) ++ "\""

/-- A Lean term for the configuration (its layout is the default one). -/
def cfgTerm (cfg : Config) : String :=
  let a := match cfg.arch with | .x64 => ".x64" | .arm => ".arm"
  let h := match cfg.host with | .linux => ".linux" | .raw => ".raw"
  let g := match cfg.gc with | .none => ".none"
  s!"(\{ arch := {a}, host := {h}, gc := {g} } : Scc.Config)"

/-- Per architecture: the support module, the namespace of `reproduces`, the
re-parse elaborator, the predicate and where it is defined, and the lines of
the text that the parsed program leaves out. -/
structure Isa where
  module : String
  /-- The placement data module and its namespace. -/
  place : String
  placeNs : String
  /-- The module relating scc's run to the run at the certificate's ranked witness
  (`lowerAll_eq_of_tables`), its namespace the same. -/
  placeW : String
  /-- The lowering's namespace (`lowerAll`) and the link's (`parsesTo`). -/
  lower : String
  link : String
  ns : String
  reparse : String
  predicate : String
  predicateDoc : String
  dropped : String
  /-- Whether `out = outLit` is checked in stages (`Scc/Cert/OutStageA64.lean`:
  the lowering, the emitter, and the rest, each on literals) instead of by one
  definitional equality. -/
  staged : Bool := false
  /-- The emitter's namespace (`emitItemsMaps`, `Item`) and the type of its
  safepoints. -/
  emit : String
  safepoint : String
  /-- A3 checks that the block table covers every instruction. -/
  cover : Bool := false
  /-- Whether the ISA's `placeOK` checks A9 (the lowered code blocks):
  `placeOK_of` then takes its proof after A8's. -/
  a9 : Bool := false
  /-- Whether the ISA's `placeOK` checks A12 (the code of every user
  function): `placeOK_of` then takes its proof after A11's. -/
  a12 : Bool := false
  /-- Whether A9 is proved by its keyed form (`a9_of_fast`, `Scc/Cert/A9StageA64.lean`,
  `Scc/Cert/A9StageX64.lean`)
  instead of by the kernel's evaluation of `a9` itself; with `a12`, A12 is
  proved from its two keyed parts (`a12_of_split`,
  `Scc/Cert/A12StageA64.lean`, `Scc/Cert/A12StageX64.lean`), each its own
  declaration. -/
  a9fast : Bool := false
  /-- Whether A2 is proved by its keyed form (`a2_of_fast`,
  `Scc/Cert/A2StageA64.lean`) instead of by the kernel's evaluation of `a2`
  itself. -/
  a2fast : Bool := false
  /-- Whether A2 is proved part by part (`a2_of_parts`, the loader's checks by
  `loadOk_ofR`, each part its own declaration, the `.quad` labels keyed by
  `Scc.Cert.Rt.X64.codeT_eq`, as the code check file's) instead of by the
  kernel's evaluation of `a2` itself: with the GC tables in `.rodata`, the whole
  of `a2` is the certificate's peak. -/
  a2split : Bool := false
  /-- Whether the block table is its own stage of `out_eq` (`blocks_eq`, on a
  literal, then `ofStage_eq_B`) instead of a part of the last step. -/
  blocksStaged : Bool := false
  /-- Whether the block table is its own stage of `out_eq` split per function
  on a large listing only (`Placement.parts` not 0), and part of the last
  step otherwise (`blocksStaged` is for every listing). -/
  blocksStagedLarge : Bool := false
  /-- The namespace of the block table's groups (`OGrp`). -/
  rt : String := ""
  /-- Whether `emitted_eq` is checked in stages (`emitItemsMaps_of_stages`:
  the emitter's checks, each function, and the rest, each a kernel check on
  literals) instead of by one definitional equality. -/
  emitStaged : Bool := false
  /-- Whether the emitter numbers local labels across functions (x64: each
  function's check takes the number its predecessor's leaves, `emitFuncs`,
  chained by `emitFuncs_cons`) instead of by the function's index
  (AArch64: `emitFuncAt` on `zipIdx`, chained by `mapM_ok_cons`). -/
  emitCounter : Bool := false
  /-- The module and namespace of the placement check for a program that
  takes its thread id or spawns (`placeOK2`: `Scc/Cert/SpawnX64.lean`,
  `Scc/Cert/SpawnA64.lean`), imported and stated with `Placement.spawn`. -/
  spawnMod : String := ""
  spawnNs : String := ""
  /-- The module of the tables' per-function slice (`tablesPart`:
  `Scc/Cert/MapsPartX64.lean`, `Scc/Cert/MapsPartA64.lean`). -/
  tablesMod : String := "Scc.Cert.MapsPart"

def isaOf : Arch → Isa
  | .x64 => {
      module := "Scc.Cert.X64", ns := "Scc.Cert.X64", reparse := "scc_x64_reparse%"
      place := "Scc.Cert.OutStageX64", placeNs := "Scc.Cert.PlaceOK.X64", staged := true,
      placeW := "Scc.Cert.OutStageWX64"
      emit := "Scc.Emit.X64", safepoint := "(String × List Int × List Int)"
      lower := "Scc.Lower.X64", link := "Scc.Cert.Link.X64"
      predicate := "Scc.Emit.X64.ProgramWCLowerable prog", a9 := true, a9fast := true, a12 := true
      emitStaged := true, emitCounter := true, blocksStagedLarge := true, rt := "Scc.Cert.Rt.X64"
      a2split := true
      spawnMod := "Scc.Cert.SpawnX64", spawnNs := "Scc.Cert.Spawn.X64"
      tablesMod := "Scc.Cert.MapsPartX64"
      predicateDoc := "`Scc.Emit.X64.ProgramWCLowerable` (`Scc/Emit/X64Lowerable.lean`: \
        every memory RMW is locked, no `movnti`)"
      dropped := "the assembler directive lines (sections, symbols, data, the stack-map \
        table); every instruction is parsed" }
  | .arm => {
      module := "Scc.Cert.Arm", ns := "Scc.Cert.Arm", reparse := "scc_arm_reparse%"
      place := "Scc.Cert.OutStageA64", placeNs := "Scc.Cert.PlaceOK.A64", staged := true,
      placeW := "Scc.Cert.OutStageWA64"
      emit := "Scc.Emit.A64", safepoint := "Scc.Emit.A64.Safepoint"
      lower := "Scc.Lower.A64", link := "Scc.Cert.Link.A64"
      predicate := "prog.WCLowerable", cover := true, a9 := true, a9fast := true, a12 := true
      emitStaged := true, blocksStaged := true, a2fast := true, rt := "Scc.Cert.Rt.A64"
      spawnMod := "Scc.Cert.SpawnA64", spawnNs := "Scc.Cert.Spawn.A64"
      tablesMod := "Scc.Cert.MapsPartA64"
      predicateDoc := "Kraken's `Program.WCLowerable` (`Kraken/Promising/Lower/Lowerable.lean`: \
        the AArch64 forms a WeakCore lowering may emit)"
      dropped := "the assembler directive lines (sections, symbols, data, the stack-map \
        table); every instruction is parsed" }

/-- What a certificate's acceptance and placement part needs to know of the
compilation (`render`, `placePart`): whether the program is in
`Scc.Lower.Accepted0`, and the stack need's configuration: whether the
lowering has a stack need table (`Scc.Lower.stackNeed`: none with non-tail
recursion, and then `placeOK`'s A4 cannot hold: `renderOutside`), the thread entries
(`Scc.Lower.threadEntries`) and their budget (the initial stack range less
the headroom), as the code check has them. -/
structure Placement where
  accepted : Bool := false
  /-- Whether the program is in the fragment the compiler theorems over
  `Scc.Lower.Accepted1` cover (`a64_scc_correctE_text_closedAt1`,
  `x64_scc_correctE_text_closedAt1`: a one-declaration program in
  `Accepted1`; `scc --cert` sets it so): the file then also proves
  `Accepted1` of it (`prog_accepted1`). -/
  accepted1 : Bool := false
  hasNeed : Bool := false
  entries : List String := ["scc_rt_main"]
  budget : Nat := 12288
  /-- A component of `placeOK` that fails on the output, if one is known:
  the file then proves `placeOK` `false` at that component
  (`prog_not_placeOK`) instead of `placeOK`. `scc --cert` leaves it `none` (its
  file states `placeOK`, and does not check when `placeOK` fails); the
  placement diagnostic (`Scc/Test/placediag.sh`, by evaluation of
  `Scc.Cert.PlaceOK.Checks.firstFail`) names the first failing component, and
  `scc --cert-fails N` sets it to that to write the file that proves the
  failure. Not a trusted input: it only selects which statement
  the file makes, and the kernel decides that statement either way (a wrong
  value gives a file that does not check). -/
  fails : Option Nat := none
  /-- The number of functions of the lowered IR: with `Isa.emitStaged`, one
  emitter check per function (`emitStage`). -/
  funcs : Nat := 0
  /-- The number of functions the block table splits the instruction list
  into (`Scc.Lower.Listing.parts`): with `Isa.blocksStaged`, one block check
  per function (`blocksStage`); 0, one check for all. -/
  parts : Nat := 0
  /-- Whether each function of the lowered IR is stack-checked
  (`Scc.IR.Func.checkStack`), in order: with A12 per function
  (`a12PerFn`), a run of functions that are not is one range check
  (`a12Skip`) instead of a check per function. Not a trusted input: a wrong
  value gives a file that does not check. Empty: every function checked. -/
  checked : List Bool := []
  /-- Whether the lowered IR's `scc_rt_main` passes the TCB to `main` or the
  IR has a `clone` (`Scc.Cert.Spawn.X64.tidOf`, `spawnsOf`; `scc --cert`
  sets it so): the file then states `placeOK2` (`Isa.spawnMod`) instead of
  `placeOK`, whose A11 and A12 do not admit such a program. Not a trusted
  input: it only selects which statement the file makes, and the kernel
  decides that statement either way. -/
  spawn : Bool := false

/-- The programs with a release theorem (`Spike/Test/Ret0Release{A64,X64}.lean`):
their certificate's docstring points at it (`docstring`). -/
def releaseNames : List String := ["ret0.w"]

/-- The module docstring of a certificate. -/
def docstring (cfg : Config) (name srcHash asmHash : String) (sized : Bool := false)
    (pl : Placement := {}) : String :=
  let accepted := pl.accepted
  let isa := isaOf cfg.arch
  let sizesItem := if sized then "
4. *Sizes, by `decide +kernel`:* `sizes` and `labelOffs` are the length of
   every instruction of `prog` in text order and the offsets of the labels,
   read off GNU `as`'s object file for `asm` (untrusted), and `sizes_ok`
   proves that they are consistent with `prog` laid out from 0
   (`Scc.Cert.X64.sizesOk`: one positive size per instruction, every listed
   label at its listed offset); the statement's loader lays the code out at
   these sizes." else ""
  let placeN := if sized then 5 else 4
  let acceptedText := if accepted then
      "`prog_accepted` proves that `prog_src` is in the fragment the first compiler theorem covers (`Scc.Lower.Accepted0`)."
    else
      "`prog_not_accepted` proves that `prog_src` is outside the fragment the first compiler theorem covers (`Scc.Lower.Accepted0`)."
  let acc1 := pl.accepted1
  -- The compiler theorem over `Accepted1` on this ISA; on x64 it also takes
  -- `main`'s frame bound (`MainFrame1Ok`), which the file does not decide.
  let isaName := if cfg.arch == .arm then "AArch64" else "x86-64"
  let thm1 := if cfg.arch == .arm then "a64_scc_correctE_text_closedAt1" else "x64_scc_correctE_text_closedAt1"
  let acceptedText := if acc1 then acceptedText ++ s!"
   `prog_accepted1` proves that it is in the fragment the {isaName} compiler
   theorem covers (`Scc.Lower.Accepted1`, `{thm1}`)." else acceptedText
  let sizedOut := if sized then ", at `sizes` and `labelOffs`" else ""
  let readyText := if pl.fails.isSome then ""
    else if accepted then "\n   `prog_cert_ready` states acceptance and placement together."
    else if acc1 then s!"\n   Placement holds; `prog_src` is outside `Accepted0` and in `Accepted1`: the\n   \
      {isaName} compiler theorem over `Accepted1` covers it."
    else "\n   Placement holds; `prog_src` is outside `Accepted0`, so no correctness claim\n   \
      (uncertified)."
  let stagedText := if isa.staged then
      s!" in three\n   kernel steps (`lowered_eq`, the lowering, from `frames_eq` and `ir_eq`; `emitted_eq`, \
        the emitter on the\n   literal IR{if isa.emitStaged then ", from its checks, each function\n   and the rest" else ""}; the rest on literals: `{isa.placeNs}.ofEmitted_of_stages`,\n   \
        `Scc/Cert/OutStage{if cfg.arch == .arm then "A64" else "X64"}.lean`)" else ""
  let coverItem := if isa.cover then "" else "
* that the block table covers every instruction: `placeOK` checks the rows
  the table has;"
  let frame1 := if cfg.arch == .arm then "" else " and on `main`'s frame bound
  (`Spike.Lib.LowerX64.MainFrame1Ok`, decided after the link)"
  let relationItem := if !accepted && acc1 && pl.fails.isNone then s!"
* the relation between the behaviour of `asm` and the WeakCore semantics of
  `source`: that is the {isaName} compiler theorem over `Accepted1`
  (`{thm1}`), given this file's decisions{frame1}."
    else if !(accepted && pl.fails.isNone) then "
* any relation between the behaviour of `asm` and the WeakCore semantics of
  `source`." else if releaseNames.contains name then "
* the relation between the behaviour of `asm` and the WeakCore semantics of
  `source`: that is the release theorem (`Spike/Test/Ret0Release{A64,X64}.lean`,
  `ret0_correct`), not this file; it rests on this file's evaluated steps
  (items 2 and 4, the frontend's parse of `source`) and on `parsesTo`." else "
* the relation between the behaviour of `asm` and the WeakCore semantics of
  `source`: that is the compiler theorem (`*_scc_correctE_text_closedAt`),
  given this file's decisions."
  let placeProof := match pl.fails with
    | some n => s!"`prog_not_placeOK` proves `placeOK` of it `false` at `placeCfg`:
   its component A{n} fails (`prog_placeOK_{n}`, decided on
   `outLit`)"
    | none =>
      if pl.spawn then s!"`prog_placeOK2` proves `placeOK2` of it at `placeCfg` (`{isa.spawnMod}`:
   `placeOK` with A11', A12' and A13 for a program that takes its thread id
   or spawns; decided on `outLit` in separate declarations, A1 to A9, A11',
   A12''s two parts and A13, combined by `placeOK2_of`)"
      else if isa.a12 then "`prog_placeOK` proves `placeOK` of it at `placeCfg` (decided on
   `outLit` in separate declarations, A1 to A8, A9 and A12 where the ISA
   checks them, A11, combined by `placeOK_of`)"
      else "`prog_placeOK` proves `placeOK` of it at `placeCfg` (decided on
   `outLit` in separate declarations, A1 to A8, A9 where the ISA checks
   it, A11, combined by `placeOK_of`)"
  let placeText := s!"`out` is `scc`'s output for
   `prog_src` as the placement check reads it (`{isa.placeNs}.Out.ofEmitted`
   of `{isa.lower}.lowerAll config prog_src`{sizedOut}), `out_eq` proves it
   equal to the literal `outLit` (its value, computed at elaboration time){stagedText},
   and {placeProof}: the canonical configuration with the program's thread
   entries and their stack budget. `prog_tablesOk` proves that the GC
   tables' stage of `lowerAll config prog_src` (scc's own run) succeeds, with
   the data `tblLit` that ends `outLit`'s `.rodata`. The proofs run the
   pipeline at `configW`, `config` with the ranked witness `gwLit` (the
   tables' stage `emitTablesW`: every function's witness its least fixpoint),
   and `prog_sameAsScc` proves that run is scc's. The
   loader's parse of `asm` is `out`'s code and data sections, the GC tables
   included (`parsesTo`, by evaluation: the trust boundary).{readyText}"
  s!"/-!
# scc certificate skeleton: `{name}`, `--arch {cfg.arch.name}`

Generated by `scc --cert`.  Check it with `scc --check FILE.lean`, or with
`lake env lean FILE.lean` in the Kraken package (exit status 0 when it
checks).

**It checks acceptance and placement; it is not yet a correctness proof.**
It does not state, let alone prove, that the assembler program behaves as
the WeakCore program does; the `correct` theorem at the end is a placeholder
for that future statement.

What the file establishes:

1. `source` and `asm` are the WeakCore source and the assembler text `scc`
   wrote, verbatim (SHA-256 of their UTF-8 bytes: source `{srcHash}`, asm
   `{asmHash}`).
2. *Reproducibility, by evaluation (a `#guard`, not a proof):* `source`, run
   through `scc`'s frontend, lowering and emitter at elaboration time
   (`{isa.ns}.reproduces`), gives exactly `asm`.  This trusts the Lean
   compiler and interpreter that run it, and says nothing about whether the
   pipeline is right.
3. *Lowerability, by `decide +kernel`:* `prog` is the program Kraken's parser
   reads from `asm` (run at elaboration time by `{isa.reparse}`), and
   `lowerable` proves {isa.predicateDoc} of it.{sizesItem}
{placeN}. *The source program as a term, by evaluation:* `prog_src` is the
   program `scc`'s frontend reads from `source` (`Scc.Cert.SrcTerm.reads`);
   the kernel does not run the frontend's parser, so the decisions below are
   about this term.
{placeN + 1}. *Acceptance, by `decide +kernel`:* {acceptedText}
{placeN + 2}. *Placement, by `decide +kernel`:* {placeText}

What it does not establish:

* anything about {isa.dropped}: they are not part of `prog`;
* that `prog` is what the parser reads, beyond trusting the elaborator that
  ran it (the parse is not replayed in the kernel);
* the sub-word store obligation (`SubWordOwned`, `Scc/Emit/X64Lowerable.lean`;
  on AArch64 the lowering emits no sub-word store);{coverItem}{relationItem}
-/"

/-- The labels `sizes_ok` checks in one kernel run (`sizesPart`). -/
def sizesChunk : Nat := 64

/-- The size table part of an x64 certificate, if any (`render`). The
kernel checks the linear `sizesOkFast`, which implies `sizesOk`
(`Scc.Cert.X64.sizesOk_of_fast`), in pieces (`sizesOkFast_of_chunks`): the
walk over the program on literals, then the listed labels' offsets,
`sizesChunk` labels per kernel run, chained by `offsAll_drop`. -/
def sizesPart : Option (List Nat × List (String × Nat)) → String
  | none => ""
  | some (sizes, offs) =>
    let offsT := ", ".intercalate (offs.map fun (l, o) => s!"({quoteLine l}, {o})")
    let c := sizesChunk
    let k := (offs.length + c - 1) / c
    let chunks := String.join ((List.range k).map fun i => s!"
/-- The listed labels {c * i} to {c * i + c - 1} are at their offsets (kernel-checked). -/
theorem sizes_offs_{i} :
    ((labelOffs.drop {c * i}).take {c}).all (Scc.Cert.X64.offOk walkLit.1) = true := by
  decide +kernel
")
    let chain := String.join ((List.range k).map (s!"Scc.Cert.X64.offsAll_drop {c} sizes_offs_{·} <|\n    ")) ++
      "by decide +kernel"
    s!"
/-- The length of every instruction of `prog`, in text order, as GNU `as`
assembled `asm` (untrusted). -/
def sizes : List Nat := {sizes}

/-- The offsets in `.text` of the labels of `asm`, as GNU `as` placed them
(untrusted). -/
def labelOffs : List (String × Nat) := [{offsT}]

/-- The walk over `prog` and `sizes` from 0, at elaboration time. -/
def walkVal : Option (List (String × Nat) × Nat) := Scc.Cert.X64.sizeWalk (Int64.ofNat 0) prog sizes 0

/-- The walk's labels with their offsets and its end offset, as a literal
(untrusted, checked by `walk_eq`). -/
def walkLit : List (String × Nat) × Nat := (scc_lit% walkVal).get!

/-- The walk gives `walkLit`: every size positive, every `nopalign` aligned
(kernel-checked). -/
theorem walk_eq : Scc.Cert.X64.sizeWalk (Int64.ofNat 0) prog sizes 0 = some walkLit := by kernel_rfl

/-- The code ends below `2 ^ 64` (kernel-checked). -/
theorem sizes_end : walkLit.2 < 2 ^ 64 := by decide +kernel
{chunks}
/-- Every listed label is at its offset (`sizes_offs_i`, chained). -/
theorem sizes_offs : (labelOffs.drop 0).all (Scc.Cert.X64.offOk walkLit.1) = true :=
  {chain}

/-- The size table is consistent with `prog` laid out from 0 (kernel-checked,
in the pieces above). -/
theorem sizes_ok : Scc.Cert.X64.sizesOk 0 prog sizes labelOffs = true :=
  Scc.Cert.X64.sizesOk_of_fast (Scc.Cert.X64.sizesOkFast_of_chunks walk_eq sizes_end sizes_offs)
"

/-- The pre-check part of a staged `emitted_eq` (`emitStage`). -/
def emitStagePre (e : String) : String := s!"/-- The emitter's checks and argument areas on the literal IR, at
elaboration time. -/
def areasVal : Option (List (Scc.IR.Sym × Nat)) := ({e}.emitPre loweredLit.1).toOption

/-- The argument areas, as a literal (untrusted, checked by `pre_eq`). -/
def areasLit : List (Scc.IR.Sym × Nat) := (scc_lit% areasVal).get!

/-- The emitter's checks pass and give `areasLit` (kernel-checked). -/
theorem pre_eq : {e}.emitPre loweredLit.1 = .ok areasLit := by kernel_rfl
"

/-- A staged `emitted_eq` where the emitter numbers local labels across
functions (`Isa.emitCounter`, x64): function `i`'s check (`emit_eq_i`)
starts at the number function `i - 1`'s literal leaves, and `emitFuncs_cons`
chains them. -/
def emitStageCounter (isa : Isa) (n : Nat) : String :=
  let e := isa.emit
  let r := s!"(List {e}.Item × Nat × List {isa.safepoint})"
  let start (i : Nat) := if i == 0 then "0" else s!"emitLit_{i - 1}.2.1"
  let funcs := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s items, next label number and safepoints, at elaboration
time. -/
def emitVal_{i} : Option {r} :=
  ({e}.emitFuncAt loweredLit.1 areasLit loweredLit.1.funcs[{i}]! {start i}).toOption

/-- Function {i}'s items, next label number and safepoints, as a literal
(untrusted, checked by `emit_eq_{i}`). -/
def emitLit_{i} : {r} :=
  (scc_lit% emitVal_{i}).get!

/-- The emitter gives `emitLit_{i}` on function {i} (kernel-checked). -/
theorem emit_eq_{i} :
    {e}.emitFuncAt loweredLit.1 areasLit loweredLit.1.funcs[{i}]! {start i} = .ok emitLit_{i} := by
  kernel_rfl
")
  let lits := ",\n    ".intercalate ((List.range n).map fun i => s!"(emitLit_{i}.1, emitLit_{i}.2.2)")
  let fns := ",\n    ".intercalate ((List.range n).map (s!"loweredLit.1.funcs[{·}]!"))
  let chain := String.join ((List.range n).map (s!"{e}.emitFuncs_cons emit_eq_{·} <|\n    ")) ++ "rfl"
  emitStagePre e ++ s!"
/-- The functions of the literal IR (kernel-checked). -/
theorem fns_eq : loweredLit.1.funcs = [
    {fns}] := by kernel_rfl
{funcs}
/-- The functions' items and safepoints, in order. -/
def emitLits : List (List {e}.Item × List {isa.safepoint}) := [
    {lits}]

/-- The emitter gives each function's literal (`emit_eq_i`, chained). -/
theorem funcs_eq : {e}.emitFuncs loweredLit.1 areasLit loweredLit.1.funcs 0 = .ok emitLits := by
  rw [fns_eq]
  exact {chain}

/-- The rest of the emitter gives `emittedLit` from the functions' literals
(kernel-checked). -/
theorem post_eq : {e}.emitPost loweredLit.1 emitLits = .ok emittedLit := by kernel_rfl

/-- The emitter gives `emittedLit` on the literal IR (`emitItemsMaps_of_stages`:
the stages above). -/
theorem emitted_eq : {e}.emitItemsMaps loweredLit.1 = .ok emittedLit :=
  {e}.emitItemsMaps_of_stages pre_eq funcs_eq post_eq
"

/-- `emitted_eq` (staged `out_eq`): by one kernel run of the emitter, or,
with `Isa.emitStaged`, from the emitter's stages (`emitItemsMaps_of_stages`):
its checks (`pre_eq`, giving the argument areas `areasLit`), each of the `n`
functions (`emit_eq_i`, giving `emitLit_i`), chained over the functions
(`funcs_eq`), and the rest (`post_eq`), each a kernel check on literals, so
that the kernel keeps one function's terms alive at a time. With
`Isa.emitCounter` the functions' checks are `emitStageCounter`'s. -/
def emitStage (isa : Isa) (n : Nat) : String :=
  if !isa.emitStaged then s!"/-- The emitter gives `emittedLit` on the literal IR (kernel-checked: the
kernel runs the emitter, here). -/
theorem emitted_eq : {isa.emit}.emitItemsMaps loweredLit.1 = .ok emittedLit := by kernel_rfl
" else
  let e := isa.emit
  if isa.emitCounter then emitStageCounter isa n else
  let r := s!"(List {e}.Item × List {isa.safepoint})"
  let fn (i : Nat) := s!"(loweredLit.1.funcs[{i}]!, {i})"
  let funcs := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s items and safepoints, at elaboration time. -/
def emitVal_{i} : Option {r} :=
  ({e}.emitFuncAt loweredLit.1 areasLit {fn i}).toOption

/-- Function {i}'s items and safepoints, as a literal (untrusted, checked by
`emit_eq_{i}`). -/
def emitLit_{i} : {r} :=
  (scc_lit% emitVal_{i}).get!

/-- The emitter gives `emitLit_{i}` on function {i} (kernel-checked). -/
theorem emit_eq_{i} :
    {e}.emitFuncAt loweredLit.1 areasLit {fn i} = .ok emitLit_{i} := by
  kernel_rfl
")
  let lits := ",\n    ".intercalate ((List.range n).map (s!"emitLit_{·}"))
  let fns := ",\n    ".intercalate ((List.range n).map fn)
  let chain := String.join ((List.range n).map (s!"Scc.Cert.OutLit.mapM_ok_cons emit_eq_{·} <|\n    ")) ++ "rfl"
  emitStagePre e ++ s!"
/-- The functions of the literal IR, with their indices (kernel-checked). -/
theorem zip_eq : loweredLit.1.funcs.zipIdx = [
    {fns}] := by kernel_rfl
{funcs}
/-- The functions' items and safepoints, in order. -/
def emitLits : List {r} := [
    {lits}]

/-- The emitter gives each function's literal (`emit_eq_i`, chained). -/
theorem funcs_eq : loweredLit.1.funcs.zipIdx.mapM ({e}.emitFuncAt loweredLit.1 areasLit) =
    .ok emitLits := by
  rw [zip_eq]
  exact {chain}

/-- The rest of the emitter gives `emittedLit` from the functions' literals
(kernel-checked). -/
theorem post_eq : {e}.emitPost loweredLit.1 emitLits = .ok emittedLit := by kernel_rfl

/-- The emitter gives `emittedLit` on the literal IR (`emitItemsMaps_of_stages`:
the stages above). -/
theorem emitted_eq : {e}.emitItemsMaps loweredLit.1 = .ok emittedLit :=
  {e}.emitItemsMaps_of_stages pre_eq funcs_eq post_eq
"

/-- The block table's stage of `out_eq` (`Isa.blocksStaged`): `blocks_eq`,
the items' block table as `blocksLit`, which is `outLit`'s own (so that
`out_eq` compares the table with itself, not with a second literal). With
`n` functions (`Placement.parts`, not 0) the items' functions are a literal
(`split_eq`), each function's groups a slice of `blocksLit` checked by a
kernel run of their own (`grps_eq_i`), chained by `mapM_some_cons` and
`blocksOfStage_of_split` (`Scc/Cert/OutStageA64.lean`,
`Scc/Cert/OutStageX64.lean`), so that the kernel keeps one function's offsets
fixpoint alive at a time; with `n = 0`, one check for all. `rt` is the
groups' namespace, `pre` the arguments before the IR (x86-64: the sizes). -/
def blocksStage (ns rt pre : String) (n : Nat) : String :=
  let g := s!"List {rt}.OGrp"
  let f := s!"(String × List {ns}.Data.It)"
  let at_ := s!"{pre}loweredLit.1 emittedLit.1"
  let lit := s!"
/-- The block table: `outLit`'s (checked by `blocks_eq`). -/
def blocksLit : {g} := outLit.place.blocks
"
  if n == 0 then s!"{lit}
/-- The items give the block table `blocksLit` (kernel-checked: the offsets
fixpoint of every function, here). -/
theorem blocks_eq : {ns}.blocksOfStage {at_} = some blocksLit := by kernel_rfl
" else
  let off (i : Nat) := if i == 0 then "0" else " + ".intercalate ((List.range i).map (s!"grpsLen_{·}"))
  let fns := String.join ((List.range n).map fun i => s!"
/-- The number of function {i}'s block groups, at elaboration time. -/
def grpsLenVal_{i} : Nat := (({ns}.grpsOf splitLit[{i}]!).getD []).length

/-- The number of function {i}'s block groups (untrusted, checked by
`grps_eq_{i}`). -/
def grpsLen_{i} : Nat := scc_lit% grpsLenVal_{i}

/-- Function {i}'s block groups: their slice of `blocksLit`. -/
def grpsLit_{i} : {g} := (blocksLit.drop ({off i})).take grpsLen_{i}

/-- Function {i}'s block groups are `grpsLit_{i}` (kernel-checked: its offsets
fixpoint). -/
theorem grps_eq_{i} : {ns}.grpsOf splitLit[{i}]! = some grpsLit_{i} := by kernel_rfl
")
  let lits := ", ".intercalate ((List.range n).map (s!"grpsLit_{·}"))
  let elems := ",\n    ".intercalate ((List.range n).map (s!"splitLit[{·}]!"))
  let chain := String.join ((List.range n).map (s!"{ns}.mapM_some_cons grps_eq_{·} <|\n    ")) ++ "rfl"
  s!"{lit}
/-- The functions of the literal items, at elaboration time. -/
def splitVal : List {f} := {ns}.splitStage {at_}

/-- The functions of the literal items, as a literal (untrusted, checked by
`split_eq`). -/
def splitLit : List {f} := scc_lit% splitVal

/-- The literal is its {n} functions (kernel-checked). -/
theorem split_parts : splitLit = [
    {elems}] := by kernel_rfl

/-- The items' functions are `splitLit` (kernel-checked). -/
theorem split_eq : {ns}.splitStage {at_} = splitLit := by kernel_rfl
{fns}
/-- The slices are all of `blocksLit` (kernel-checked). -/
theorem grps_flat : [{lits}].flatten = blocksLit := by kernel_rfl

/-- The items give the block table `blocksLit` (the functions' checks above,
chained). -/
theorem blocks_eq : {ns}.blocksOfStage {at_} = some blocksLit := by
  rw [← grps_flat]
  exact {ns}.blocksOfStage_of_split split_eq <| by
    rw [split_parts]
    exact {chain}
"

/-- The runs of `checked`: each with its first function, its end and
whether its functions are stack-checked (a run of stack-checked functions
is one function long). -/
def a12Runs (checked : List Bool) : List (Nat × Nat × Bool) :=
  (checked.zipIdx.foldl (fun acc (c, i) => match acc with
    | (k, _, false) :: rest => if c then (i, i + 1, true) :: acc else (k, i + 1, false) :: rest
    | _ => (i, i + 1, c) :: acc) []).reverse

/-- A12 one function at a time (`Scc/Cert/A12StageA64.lean`,
`Scc/Cert/A12StageX64.lean`), for a large listing: A12's tables at `t` as a
literal (`a12TabsLit`, checked once by `prog_placeOK{sfx}_12t`), then for
each of the IR's `n` stack-checked functions its code conjunct
(`prog_placeOK{sfx}_12c_i`) and its phase conjunct
(`prog_placeOK{sfx}_12p_i`), each its own kernel check on the literal
tables, and for each run of functions that are not stack-checked one range
check (`prog_placeOK{sfx}_12s_i`, `a12Skip`) for both parts, chained by
`a12From_cons` and `a12codeFrom_skip`/`a12phFrom_skip` to a decided end; `a12_of_tabs` gives
`prog_placeOK{sfx}_12`. `checked` is each function's `checkStack` (empty:
all). The literal's name is `a12TabsLit{sfx}` (`sfx` is `At` in
`Scc/Test/certify.sh`'s file). -/
def a12PerFn (ns t sfx : String) (n : Nat) (checked : List Bool := []) : String :=
  let tl := s!"a12TabsLit{sfx}"
  let runs := a12Runs (if checked.length == n then checked else List.replicate n true)
  let each := String.join (runs.map fun (i, j, c) => if c then s!"
/-- A12's code conjunct of function {i} (kernel-checked). -/
theorem prog_placeOK{sfx}_12c_{i} : {ns}.a12codeAtL outLit {tl} {i} = true := by
  decide +kernel

/-- A12's phase conjunct of function {i} (kernel-checked). -/
theorem prog_placeOK{sfx}_12p_{i} : {ns}.a12phAtL outLit {tl} {i} = true := by
  decide +kernel
" else s!"
/-- Functions {i} to {j - 1} are not stack-checked (kernel-checked). -/
theorem prog_placeOK{sfx}_12s_{i} : {ns}.a12Skip outLit {i} {j} = true := by
  decide +kernel
")
  let chain (p skip : String) := String.join (runs.map fun (i, _, c) =>
    if c then s!"{ns}.a12From_cons rfl prog_placeOK{sfx}_12{p}_{i} <|\n    "
    else s!"{ns}.{skip} prog_placeOK{sfx}_12s_{i} <|\n    ")
  s!"
/-- A12's tables, at elaboration time. -/
def a12TabsVal{sfx} : Option {ns}.A12Tabs := {ns}.a12Tabs outLit {t}

/-- A12's tables as a literal (untrusted, checked by `prog_placeOK{sfx}_12t`). -/
def {tl} : {ns}.A12Tabs := (scc_lit% a12TabsVal{sfx}).get!

/-- `{tl}` is A12's tables (kernel-checked). -/
theorem prog_placeOK{sfx}_12t : {ns}.a12TabsOk outLit {t} {tl} = true := by
  decide +kernel
{each}
/-- No function after the {n} above, for the code part (kernel-checked). -/
theorem prog_placeOK{sfx}_12c_end : {ns}.a12From outLit ({ns}.code12L outLit {tl}) {n} = true := by
  decide +kernel

/-- No function after the {n} above, for the phase part (kernel-checked). -/
theorem prog_placeOK{sfx}_12p_end : {ns}.a12From outLit ({ns}.ph12O outLit {tl}) {n} = true := by
  decide +kernel

/-- A12 of `outLit`: the code of every user function (its functions' checks,
chained). -/
theorem prog_placeOK{sfx}_12 : {ns}.a12 outLit {t} = true :=
  {ns}.a12_of_tabs prog_placeOK{sfx}_12t
    ({chain "c" "a12codeFrom_skip"}prog_placeOK{sfx}_12c_end)
    ({chain "p" "a12phFrom_skip"}prog_placeOK{sfx}_12p_end)
"

/-- A function's slice, as `tablesPart` names it: `Scc.Cert.MapsX64.sliceFn`
(x86-64: on the sizes) or `Scc.Cert.MapsA64.sliceFn` (AArch64: on the
argument areas) of the literal IR and the emitter's items and safepoints. -/
def tablesSlice : Arch → String
  | .x64 => "Scc.Cert.MapsX64.sliceFn loweredLit.1 emittedLit.1 emittedLit.2 sizes"
  | .arm => "Scc.Cert.MapsA64.sliceFn loweredLit.1 areasLit emittedLit.1 emittedLit.2"

/-- The IR's function symbols, as `tablesPart` names them: a tail jump's
possible targets (`Succs.tail`), the list scc's whole-text tables use
(`Scc.Cert.Maps.fnNames` of every function's tags: its entry label, its name). -/
def tablesNames : String := "loweredLit.1.funcs.map (·.name)"

/-- The tables part of a certificate (`Scc/Cert/MapsPart.lean`),
for the `n` functions of the lowered IR (`Placement.funcs`; with
`Isa.emitStaged`, whose stage gives `areasLit`): `tables_ok`, every
function's rebased slice computes and has a liveness witness and tables that
pass `fnOk`. Per function `i`, three kernel checks on literals, each its own
declaration so that the kernel holds one part's terms at a time: the slice
(`tables_s_i`, `sliceLit_i`), the witness (`tables_w_i`, `wLit_i`: a
post-fixpoint of slot liveness on the body) and the tables (`tables_c_i`,
`tLit_i`, `computeW`'s from the witness; `tables_g_i`, of the format's
shape); `fnOk_of_lit` joins them (`tables_fn_i`), `fnsOkFrom_cons` chains the
functions and `fnsOk_of_from` gives `tables_ok`. A jump out of a slice's
body names its target (`Succs.tail`), and `tables_t_i` checks that it is one
of the IR's function symbols (`tailsLit`, `tails_eq`: `loweredLit`'s names,
the list scc's whole-text checker uses; a jump out of a body to anything else
fails `fnOk`), so the per-function tables merged are the whole text's by
construction.
The witness and tables theorems name only the slice's and the names' literals,
so that a runtime routine's (the same in every program, rebased; its tail
targets by name) can come from a fixed module instead; `tables_ok`'s statement
names no literal, and it is stated of the IR's own function count
(`loweredLit.1.funcs.length`, checked against the chain's length by
`kernel_rfl`), not of `n`, which only generates the per-function parts. -/
def tablesPart (arch : Arch) (n : Nat) : String :=
  let sl := tablesSlice arch
  let names := tablesNames
  let m := "Scc.Cert.Maps"
  let r := s!"(Nat × List {m}.Item × {m}.FnTags)"
  let each := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s rebased slice (entry address, items, tags), at elaboration
time. -/
def sliceVal_{i} : Option {r} := ({sl} {i}).toOption

/-- Function {i}'s rebased slice, as a literal (untrusted, checked by
`tables_s_{i}`). -/
def sliceLit_{i} : {r} := (scc_lit% sliceVal_{i}).get!

/-- Function {i}'s slice is `sliceLit_{i}` (kernel-checked). -/
theorem tables_s_{i} : {sl} {i} = .ok sliceLit_{i} := by kernel_rfl

/-- Function {i}'s liveness witness, at elaboration time (scc's: the least
fixpoint). -/
def wVal_{i} : Array (List Int) := ({m}.witness [sliceLit_{i}.2.2] sliceLit_{i}.2.1).headD #[]

/-- Function {i}'s liveness witness, as a literal (untrusted, checked by
`tables_w_{i}`). -/
def wLit_{i} : Array (List Int) := scc_lit% wVal_{i}

/-- `wLit_{i}` is a post-fixpoint of slot liveness on function {i}'s body
(kernel-checked). -/
theorem tables_w_{i} : {m}.liveOk ({m}.bodyOf sliceLit_{i}.2.2 sliceLit_{i}.2.1) wLit_{i} = true := by
  decide +kernel

/-- Function {i}'s tables from `wLit_{i}`, at elaboration time. -/
def tVal_{i} : Option {m}.Tables :=
  ({m}.computeW [sliceLit_{i}.2.2] sliceLit_{i}.2.1 [wLit_{i}]).toOption

/-- Function {i}'s tables, as a literal (untrusted, checked by `tables_c_{i}`). -/
def tLit_{i} : {m}.Tables := (scc_lit% tVal_{i}).get!

/-- The tables `computeW` builds from `wLit_{i}` on function {i}'s slice are
`tLit_{i}` (kernel-checked). -/
theorem tables_c_{i} : {m}.computeW [sliceLit_{i}.2.2] sliceLit_{i}.2.1 [wLit_{i}] = .ok tLit_{i} := by
  kernel_rfl

/-- `tLit_{i}` has the format's shape (kernel-checked). -/
theorem tables_g_{i} : tLit_{i}.g1Ok = true := by decide +kernel

/-- `tLit_{i}`'s tail names are among `tailsLit`: every jump out of function
{i}'s body enters a function of the IR (kernel-checked). -/
theorem tables_t_{i} : tLit_{i}.tailsIn tailsLit = true := by decide +kernel

/-- Function {i} passes `fnOk` (its parts above). -/
theorem tables_fn_{i} : {m}.fnOk ({names}) ({sl} {i}) wLit_{i} tLit_{i} = true :=
  {m}.fnOk_of_lit tails_eq tables_s_{i} tables_w_{i} tables_c_{i} tables_g_{i} tables_t_{i}
")
  let ws := ",\n    ".intercalate ((List.range n).map fun i => s!"(wLit_{i}, tLit_{i})")
  let chain := String.join ((List.range n).map (s!"{m}.fnsOkFrom_cons tables_fn_{·} <|\n    ")) ++ "rfl"
  s!"
/-! ## The tables, per function

The statement of `Scc/Cert/MapsPart.lean`. Proved here, for each function `i` of
the lowered IR (`loweredLit`), on its slice of the emitter's text
(`emittedLit`) rebased to its entry label, with its tags from the IR (the tags
are trusted from the IR: they are not checked against the code): the slice
computes; the witness `wLit_i` is a post-fixpoint of slot liveness on the
body (`liveOk`); `tLit_i` is the tables `computeW` builds from it (each
safepoint's maps from the witness, the successors of the body's blocks and of
its exits) and has the format's shape (`Tables.g1Ok`). A jump out of a
slice's body names its target, which is one of the IR's function symbols
(`tailsLit`, `tails_eq`); scc's whole-text checker requires the same names,
so the per-function tables merged are the whole text's tail successors
included.

Not proved here (W1, checked by scc, untrusted): that `wLit_i` is the least
fixpoint (`tLit_i` is `compute`'s tables; any post-fixpoint lists every slot
the least one does, `liveSlots_le`), that the tables scc emits are the
per-function tables put back at their entries and merged in address order,
and that a runtime routine's tables are the constant ones scc's runtime
expects.
-/
{each}
/-- Every function's witness and tables, from function 0 on, pass `fnOk`
(`tables_fn_i`, chained). -/
theorem tables_from : {m}.fnsOkFrom ({names}) ({sl}) 0 [
    {ws}] = true :=
  {chain}

/-- **The tables of the IR's functions** (see the section's docstring),
stated of the IR's own function count (`loweredLit.1.funcs.length`, so every
tail name enters a function whose tables are among those checked): each
function's rebased slice computes and has a witness and tables that pass
`fnOk`. -/
theorem tables_ok : {m}.FnsOk ({names}) ({sl}) loweredLit.1.funcs.length :=
  {m}.fnsOk_of_from tables_from (by kernel_rfl)
"

/-- The ranked witness part of a certificate (`render`), before `configW`: the GC tables'
ranked witness scc computes for `source` (`gcWitOf`, at `config`), one literal per function
of the lowered IR (`n`, `Placement.funcs`), so that each function's least-fixpoint check
(`gcStage`'s `gc_least_i`) names its own; `gwLit` lists them, and `configW` carries it
(`Scc.Config.gcWit`). Untrusted: `emitTablesW` refuses any witness that is not every function's
least fixpoint. -/
def gwPart (isa : Isa) (n : Nat) : String :=
  let w := "(Array (List Int) × List (List Nat))"
  let each := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s ranked witness, as a literal (untrusted, checked by `gc_least_{i}`). -/
def gwLit_{i} : {w} := scc_lit% gwVal_{i}
")
  let vals := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s ranked witness, at elaboration time. -/
def gwVal_{i} : {w} := gwVal.getD {i} default
")
  let lits := ", ".intercalate ((List.range n).map (s!"gwLit_{·}"))
  s!"
/-- The GC tables' ranked witness of `source`, at elaboration time (scc's:
`{isa.ns}.gcWitOf`, the reference liveness and its ranks per IR function). -/
def gwVal : Scc.Cert.Maps.GcWit := ({isa.ns}.gcWitOf config source).toOption.getD []
{vals}{each}
/-- The ranked witness, one entry per function of the lowered IR, in order. -/
def gwLit : Scc.Cert.Maps.GcWit := [{lits}]
"

/-- The GC tables' stage of a staged `out_eq` (`Isa.staged`, `Isa.emitStaged`), after the
emitter's: `tablesOf` of the literal IR and items at `configW`'s witness (`emitTablesW`) is
`(titsLit, tblLit)`, from its stages (`emitTablesW_of_stages`), each a kernel check on literals:
the items, the `scc_stackmap` table and each function's tags (`fnTags*_of_stages`); each
function's least-fixpoint check of its witness (`gc_least_i`, chained by `leastFrom_cons`); the
stubs, each function's maps and exit successors and their sort (`computeW_of_stages`,
`computeWR_of_least`); the label map and the serialiser. `tables_eq` is the stage `out_eq`
takes (`tblLit` ends `outLit`'s `.rodata`); `prog_tablesW` states it of
`lowerAll configW prog_src` (`tables_of_stages`), and `prog_sameAsScc` relates that run to
scc's (`lowerAll_eq_of_tables`), which `out_eq` and `prog_tablesOk` (`placePart`) are about.
`n` is the IR's function count. -/
def gcStage (isa : Isa) (arch : Arch) (n : Nat) : String :=
  let m := "Scc.Cert.Maps"
  let mx := match arch with | .x64 => "Scc.Cert.MapsX64" | .arm => "Scc.Cert.MapsA64"
  let its := match arch with
    | .x64 => s!"emittedLit.1 ({mx}.unitSizes emittedLit.1)"
    | .arm => "emittedLit.1"
  let tagsPre := match arch with
    | .x64 => s!"{mx}.tagsOf loweredLit.1 gcItemsLit gcStblLit"
    | .arm => s!"{mx}.tagsOf loweredLit.1 areasLit gcItemsLit gcStblLit"
  let fnArg (i : Nat) := match arch with
    | .x64 => s!"loweredLit.1.funcs[{i}]!"
    | .arm => s!"(loweredLit.1.funcs[{i}]!, {i})"
  let fnsGoal := match arch with
    | .x64 => s!"loweredLit.1.funcs.mapM ({tagsPre})"
    | .arm => s!"loweredLit.1.funcs.zipIdx.mapM ({tagsPre})"
  let fnsRw := match arch with | .x64 => "fns_eq" | .arm => "zip_eq"
  let tagsThm := match arch with
    | .x64 => s!"{mx}.fnTagsX64 loweredLit.1 emittedLit.1 ({mx}.unitSizes emittedLit.1) = .ok (gcItemsLit, gcFnsLit) :=
  {mx}.fnTagsX64_of_stages gc_items_eq gc_stbl_eq gc_fns_eq"
    | .arm => s!"{mx}.fnTagsA64 loweredLit.1 emittedLit.1 = .ok (gcItemsLit, gcFnsLit) :=
  {mx}.fnTagsA64_of_stages pre_eq gc_items_eq gc_stbl_eq gc_fns_eq"
  let sec := match arch with | .x64 => ".dir" | .arm => ".raw"
  let mapM := "Scc.Cert.OutLit.mapM_ok_cons"
  let each := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s tags, at elaboration time. -/
def gcFnVal_{i} : Option {m}.FnTags := ({tagsPre} {fnArg i}).toOption

/-- Function {i}'s tags, as a literal (untrusted, checked by `gc_fn_eq_{i}`). -/
def gcFnLit_{i} : {m}.FnTags := (scc_lit% gcFnVal_{i}).get!

/-- Function {i}'s tags are `gcFnLit_{i}` (kernel-checked). -/
theorem gc_fn_eq_{i} : {tagsPre} {fnArg i} = .ok gcFnLit_{i} := by kernel_rfl
")
  let fnLits := ", ".intercalate ((List.range n).map (s!"gcFnLit_{·}"))
  let fnChain := String.join ((List.range n).map (s!"{mapM} gc_fn_eq_{·} <|\n    ")) ++ "rfl"
  let least := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s ranked witness is the least fixpoint of slot liveness on its body
(kernel-checked: `leastOk`, a post-fixpoint, every slot justified at its rank, the ranks below
the fuel). -/
theorem gc_least_{i} : {m}.leastOk ({m}.bodyOf gcFnLit_{i} gcItemsLit) gwLit_{i}.1 gwLit_{i}.2 = true := by
  decide +kernel
")
  let leastChain := String.join ((List.range n).map (s!"{m}.leastFrom_cons gc_least_{·} <|\n    ")) ++ "rfl"
  let maps := String.join ((List.range n).map fun i => s!"
/-- Function {i}'s root maps from its witness, at elaboration time. -/
def gcMsVal_{i} : Option (List {m}.RootMap) := ({m}.fnMapsW gcFnLit_{i} gcItemsLit gwLit_{i}.1).toOption

/-- Function {i}'s root maps, as a literal (untrusted, checked by `gc_ms_eq_{i}`). -/
def gcMsLit_{i} : List {m}.RootMap := (scc_lit% gcMsVal_{i}).get!

/-- Function {i}'s root maps are `gcMsLit_{i}` (kernel-checked). -/
theorem gc_ms_eq_{i} : {m}.fnMapsW gcFnLit_{i} gcItemsLit gwLit_{i}.1 = .ok gcMsLit_{i} := by kernel_rfl

/-- Function {i}'s exit successors, at elaboration time. -/
def gcOsVal_{i} : Option (List {m}.Succs) :=
  ({m}.outSuccs gcFnLit_{i} gcItemsLit (gcMsLit_{i}.map fun (r : {m}.RootMap) => r.pt.addr)).toOption

/-- Function {i}'s exit successors, as a literal (untrusted, checked by `gc_os_eq_{i}`). -/
def gcOsLit_{i} : List {m}.Succs := (scc_lit% gcOsVal_{i}).get!

/-- Function {i}'s exit successors are `gcOsLit_{i}` (kernel-checked). -/
theorem gc_os_eq_{i} :
    {m}.outSuccs gcFnLit_{i} gcItemsLit (gcMsLit_{i}.map fun (r : {m}.RootMap) => r.pt.addr) = .ok gcOsLit_{i} := by
  kernel_rfl

/-- Function {i}'s block successors, at elaboration time. -/
def gcFsVal_{i} : List {m}.Succs := {m}.fnSuccs gcFnLit_{i} gcItemsLit

/-- Function {i}'s block successors, as a literal (untrusted, checked by `gc_fs_eq_{i}`). -/
def gcFsLit_{i} : List {m}.Succs := scc_lit% gcFsVal_{i}

/-- Function {i}'s block successors are `gcFsLit_{i}` (kernel-checked). -/
theorem gc_fs_eq_{i} : {m}.fnSuccs gcFnLit_{i} gcItemsLit = gcFsLit_{i} := by kernel_rfl
")
  let fsLits := ", ".intercalate ((List.range n).map (s!"gcFsLit_{·}"))
  let fsRws := ", ".intercalate ((List.range n).map (s!"gc_fs_eq_{·}"))
  let msLits := ", ".intercalate ((List.range n).map (s!"gcMsLit_{·}"))
  let osLits := ", ".intercalate ((List.range n).map (s!"gcOsLit_{·}"))
  let msChain := String.join ((List.range n).map (s!"{mapM} gc_ms_eq_{·} <|\n    ")) ++ "rfl"
  let osChain := String.join ((List.range n).map (s!"{mapM} gc_os_eq_{·} <|\n    ")) ++ "rfl"
  s!"
/-! ### The GC tables

`tablesOf` of the literal IR and items at `configW`'s ranked witness (`emitTablesW`), in stages
(`emitTablesW_of_stages`): the items, the `scc_stackmap` table and the tags; every function's
witness the least fixpoint (`leastOk`); the tables from the witnesses, each function's maps,
exit successors and block successors apart (`computeW_of_stagesF`, `computeWR_of_least`); the
label map and the serialiser. -/

-- The witness in `configW` is scc's for the literal IR and items (evaluation, not a proof:
-- `gc_least_i` checks what the certificate relies on).
#guard decide (({mx}.gcWitness loweredLit.1 emittedLit.1).toOption = some gwLit)

/-- The tables' items, at elaboration time. -/
def gcItemsVal : Option (List {m}.Item) := ({mx}.itemsOf {its}).toOption

/-- The tables' items, as a literal (untrusted, checked by `gc_items_eq`). -/
def gcItemsLit : List {m}.Item := (scc_lit% gcItemsVal).get!

/-- The tables' items are `gcItemsLit` (kernel-checked). -/
theorem gc_items_eq : {mx}.itemsOf {its} = .ok gcItemsLit := by kernel_rfl

/-- The `scc_stackmap` table, at elaboration time. -/
def gcStblVal : Option (List (Nat × List Int × List Int)) := ({mx}.stackTable emittedLit.1 gcItemsLit).toOption

/-- The `scc_stackmap` table, as a literal (untrusted, checked by `gc_stbl_eq`). -/
def gcStblLit : List (Nat × List Int × List Int) := (scc_lit% gcStblVal).get!

/-- The `scc_stackmap` table is `gcStblLit` (kernel-checked). -/
theorem gc_stbl_eq : {mx}.stackTable emittedLit.1 gcItemsLit = .ok gcStblLit := by kernel_rfl
{each}
/-- The functions' tags, in order. -/
def gcFnsLit : List {m}.FnTags := [{fnLits}]

/-- The tags of every function (`gc_fn_eq_i`, chained). -/
theorem gc_fns_eq : {fnsGoal} = .ok gcFnsLit := by
  rw [{fnsRw}]
  exact {fnChain}

/-- The items and the tags (`fnTags*_of_stages`). -/
theorem gc_tags_eq : {tagsThm}
{least}
/-- Every function's ranked witness is its least fixpoint (`gc_least_i`, chained). -/
theorem gc_least : {m}.leastFrom gcItemsLit gcFnsLit gwLit = true :=
  {leastChain}

/-- No conditional branch leaves a body but to a stub (kernel-checked). -/
theorem gc_stubs : {m}.stubsOk gcFnsLit gcItemsLit = .ok () := by kernel_rfl

/-- One witness per function (kernel-checked). -/
theorem gc_len : (gwLit.map (·.1)).length = gcFnsLit.length := by kernel_rfl
{maps}
/-- Every function's root maps (`gc_ms_eq_i`, chained). -/
theorem gc_ms : (gcFnsLit.zip (gwLit.map (·.1))).mapM (fun (t, w) => {m}.fnMapsW t gcItemsLit w) =
    .ok [{msLits}] :=
  {msChain}

/-- Every function's exit successors (`gc_os_eq_i`, chained). -/
theorem gc_os : (gcFnsLit.zip [{msLits}]).mapM (fun (p : {m}.FnTags × List {m}.RootMap) =>
    {m}.outSuccs p.1 gcItemsLit (p.2.map fun (r : {m}.RootMap) => r.pt.addr)) = .ok [{osLits}] :=
  {osChain}

/-- Every function's block successors (`gc_fs_eq_i`, together). -/
theorem gc_fs : gcFnsLit.flatMap (fun t => {m}.fnSuccs t gcItemsLit) = [{fsLits}].flatten := by
  simp only [gcFnsLit, List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil,
    {fsRws}]

/-- The tables from the witnesses, at elaboration time. -/
def gcTVal : Option {m}.Tables := ({m}.computeW gcFnsLit gcItemsLit (gwLit.map (·.1))).toOption

/-- The tables, as a literal (untrusted, checked by `gc_w_eq`). -/
def gcTLit : {m}.Tables := (scc_lit% gcTVal).get!

/-- The tables from the witnesses are `gcTLit` (`computeW_of_stagesF`; the sort kernel-checked). -/
theorem gc_w_eq : {m}.computeW gcFnsLit gcItemsLit (gwLit.map (·.1)) = .ok gcTLit :=
  ({m}.computeW_of_stagesF gc_stubs gc_len gc_ms gc_os gc_fs).trans (by kernel_rfl)

/-- The tables from the ranked witness (`computeWR_of_least`). -/
theorem gc_wr_eq : {m}.computeWR gcFnsLit gcItemsLit gwLit = .ok gcTLit :=
  {m}.computeWR_of_least gc_least gc_w_eq

/-- The IR's function symbols, a tail jump's possible targets, at elaboration
time. -/
def tailsVal : List String := {tablesNames}

/-- The IR's function symbols, as a literal (untrusted, checked by
`tails_eq`). -/
def tailsLit : List String := scc_lit% tailsVal

/-- The function symbols are `tailsLit` (kernel-checked). -/
theorem tails_eq : {tablesNames} = tailsLit := by kernel_rfl

/-- **The merged tables' shape and tail names** (kernel-checked): `gcTLit`, the tables
`computeWR` builds from the ranked witness and the serialiser writes into `tblLit`, has the
format's shape (`Tables.g1Ok`), and every tail successor it names is one of the IR's
function symbols (`tailsLit`). The tables' stage does not check these on the merged
tables; the certificate does, here. -/
theorem prog_tables_merged : gcTLit.g1Ok && gcTLit.tailsIn tailsLit = true := by
  decide +kernel

/-- The label map, at elaboration time. -/
def gcLabsVal : List (Nat × String) := {m}.labelMap gcItemsLit

/-- The label map, as a literal (untrusted, checked by `gc_labs_eq`). -/
def gcLabsLit : List (Nat × String) := scc_lit% gcLabsVal

/-- The label map is `gcLabsLit` (kernel-checked). -/
theorem gc_labs_eq : {m}.labelMap gcItemsLit = gcLabsLit := by kernel_rfl

/-- The tables' data, at elaboration time. -/
def tblVal : Option (List Kraken.DataImage.Item) :=
  ({m}.tableItems gcTLit ({m}.labelIn gcLabsLit) (\{} : {m}.DescLabels)
    (fun g => ({m}.labelAddr gcItemsLit g).isSome)).toOption

/-- The tables' data, as a literal (untrusted, checked by `gc_ser_eq`): the end of `outLit`'s
`.rodata`. -/
def tblLit : List Kraken.DataImage.Item := (scc_lit% tblVal).get!

/-- The serialiser gives `tblLit` (kernel-checked). -/
theorem gc_ser_eq : {m}.tableItems gcTLit ({m}.labelIn gcLabsLit) (\{} : {m}.DescLabels)
    (fun g => ({m}.labelAddr gcItemsLit g).isSome) = .ok tblLit := by kernel_rfl

/-- The lowering has a stack growth (kernel-checked). -/
theorem gc_growth : loweredLit.1.growth.isSome = true := by decide +kernel

/-- The tables' items the listing appends to the emitter's. -/
def titsLit : List {isa.emit}.Item := {sec} \".section .rodata\" :: tblLit.map {mx}.dataItem

/-- The tables' stage at `configW`'s witness gives `(titsLit, tblLit)` (`emitTablesW_of_stages`:
the stages above). -/
theorem tables_eq : {isa.lower}.tablesOf loweredLit.1 emittedLit.1 configW.gcWit = .ok (titsLit, tblLit) :=
  {mx}.emitTablesW_of_stages gc_growth gc_tags_eq gc_wr_eq gc_labs_eq gc_ser_eq
"

/-- The acceptance and placement part of a certificate (`render`): the
source program as a term, its acceptance, `out`, the parse check, the
placement decisions and, for an accepted program, `prog_cert_ready`. -/
def placePart (cfg : Config) (prog : CoreTerm.Prog) (pl : Placement) (sized : Bool) : String :=
  let accepted := pl.accepted
  let isa := isaOf cfg.arch
  let ns := isa.placeNs
  let accept1 := if pl.accepted1 then s!"
/-- `prog_src` is in the fragment the {if cfg.arch == .arm then "AArch64" else "x86-64"} compiler theorem covers
(`{if cfg.arch == .arm then "a64" else "x64"}_scc_correctE_text_closedAt1`; kernel-checked). -/
theorem prog_accepted1 : Scc.Lower.Accepted1 prog_src = true := by decide +kernel
" else ""
  let outArgs := if sized then " sizes labelOffs" else ""
  let asmArg := if sized then "⟨asm, sizes, labelOffs⟩" else "asm"
  let can := "placeCfg"
  let es := ", ".intercalate (pl.entries.map quoteLine)
  let t := s!"({ns}.tablesOf {can} outLit)"
  -- With the keyed forms, A9 and A12's two parts are three declarations
  -- (`Scc/Cert/A12StageA64.lean`): the kernel's memory is held per
  -- declaration, so the peak is the largest of the three, not their sum.
  let split := isa.a9 && isa.a9fast && isa.a12
  let a9Pf :=
    if isa.a9fast then s!"\n  {ns}.a9_of_fast (by decide +kernel)" else " by\n  decide +kernel"
  let a9Thm := if isa.a9 then s!"
/-- A9 of `outLit`: the lowered code blocks (kernel-checked). -/
theorem prog_placeOK_9 : {ns}.a9 outLit {t} = true :={a9Pf}
" else ""
  let a9Arg := if isa.a9 then " prog_placeOK_9" else ""
  let a2Pf := if isa.a2fast then s!"\n  {ns}.a2_of_fast (by decide +kernel)"
    else if isa.a2split then s!"\n  {ns}.a2_of_parts ({isa.link}.loadOk_ofR prog_placeOK_2w prog_placeOK_2l prog_placeOK_2q
    prog_placeOK_2r) prog_placeOK_2a prog_placeOK_2i"
    else " by\n  decide +kernel"
  -- A2 part by part (`Isa.a2split`): each part its own declaration, so the peak is the
  -- largest part's
  let lΛ := s!"{t}.Λ"
  let syms := s!"(Scc.Sem.loadSyms {lΛ} outLit.secs.rodata)"
  let codeEnd := s!"(Scc.Sem.X64.codeEnd {lΛ}.code.lo outLit.prog)"
  let a2Parts := if isa.a2split && !isa.a2fast then s!"
/-- A2's code sizes against the assembler's label offsets (kernel-checked). -/
theorem prog_placeOK_2w : {isa.link}.sizeOkW (Int64.ofNat {lΛ}.code.lo) outLit.prog outLit.labelOffs = true := by
  decide +kernel

/-- A2's code labels, each once (kernel-checked). -/
theorem prog_placeOK_2l : {isa.link}.labelsNodupL (Int64.ofNat {lΛ}.code.lo) outLit.prog = true := by
  decide +kernel

/-- A2's `.quad` labels resolve (kernel-checked, the code labels keyed:
`Scc.Cert.Rt.X64.codeT_eq`; the GC tables' key words name code labels out of code order). -/
theorem prog_placeOK_2q :
    Scc.Sem.quadsResolve {lΛ} outLit.secs.rodata (Scc.Sem.X64.codeLabel {lΛ}.code.lo outLit.prog) = true := by
  rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- A2's `.rodata` and data symbols against the layout and the code (kernel-checked). -/
theorem prog_placeOK_2r : (Scc.Sem.rodataFits {lΛ} outLit.secs.rodata && Scc.Sem.symsAgree {lΛ} outLit.secs.rodata &&
    Scc.Sem.symsAbove {lΛ}.code.lo {codeEnd} {syms} &&
    {isa.link}.symsAround {lΛ}.code.lo outLit.prog {syms} &&
    {isa.link}.noClash {lΛ}.code.lo outLit.prog {syms} &&
    decide ({codeEnd} < 2 ^ 64)) = true := by
  decide +kernel

/-- A2's abort labels in the cells (kernel-checked). -/
theorem prog_placeOK_2a : {isa.link}.abortsIn outLit.prog {lΛ} = true := by
  decide +kernel

/-- A2's image (kernel-checked). -/
theorem prog_placeOK_2i : {isa.link}.imageIn outLit.prog outLit.secs {lΛ} = true := by
  decide +kernel
" else ""
  let a12Parts := if split then s!"
/-- A12's code part of `outLit` (kernel-checked). -/
theorem prog_placeOK_12c : {ns}.a12code outLit = true := by
  decide +kernel

/-- A12's phase part of `outLit` (kernel-checked). -/
theorem prog_placeOK_12p : {ns}.a12ph outLit {t} = true := by
  decide +kernel
" else ""
  let a12Pf := if split then s!"\n  {ns}.a12_of_split prog_placeOK_12c prog_placeOK_12p" else " by\n  decide +kernel"
  -- A12 per function on a listing whose block table is split (`blocksStage`): on one
  -- whose block table is one check (x86-64), that check is the peak, and A12 per
  -- function only adds time
  let perFn := split && isa.blocksStaged && pl.parts != 0 && pl.funcs != 0 && !pl.spawn
  let a12Thm := if isa.a12 then
    if perFn then a12PerFn ns t "" pl.funcs pl.checked else s!"{a12Parts}
/-- A12 of `outLit`: the code of every user function (kernel-checked). -/
theorem prog_placeOK_12 : {ns}.a12 outLit {t} = true :={a12Pf}
" else ""
  let a12Arg := if isa.a12 then " prog_placeOK_12" else ""
  let blocksSt := isa.blocksStaged || (isa.blocksStagedLarge && pl.parts != 0)
  let outLast := if blocksSt then s!"{blocksStage ns isa.rt (if sized then "sizes " else "") pl.parts}
/-- `out` is `outLit` (kernel-checked in five steps, `ofEmitted_of_stages`
and `ofStage_eq_B`: the lowering, the emitter, the GC tables and the block table above,
and here the stack need table and the `.text` filter on the literals; the
decisions below read `outLit`). -/
theorem out_eq : out = outLit := by
  rw [out_eqW, {ns}.ofEmitted_of_stages{outArgs} (ir := loweredLit.1) (setup := loweredLit.2)
    (items := emittedLit.1) (sps := emittedLit.2) lowered_eq emitted_eq tables_eq, {ns}.ofStage_eq_B blocks_eq]
  kernel_rfl
" else s!"
/-- `out` is `outLit` (kernel-checked in four steps, `ofEmitted_of_stages`:
the lowering, the emitter and the GC tables above, and here the stack need table, the
`.text` filter and the block table on the literals; the decisions below
read `outLit`). -/
theorem out_eq : out = outLit := by
  rw [out_eqW, {ns}.ofEmitted_of_stages{outArgs} lowered_eq emitted_eq tables_eq]
  kernel_rfl
"
  let tablesW := s!"
/-- The GC tables of the pipeline at `configW` (the ranked witness `gwLit`, `emitTablesW`):
the items `titsLit` and the data `tblLit` (`tables_of_stages`: the lowering, the emitter and
the tables' stages above). -/
theorem prog_tablesW : ({isa.lower}.lowerAll configW prog_src).tables = .ok (titsLit, tblLit) :=
  {ns}.tables_of_stages lowered_eq emitted_eq tables_eq

/-- **scc's run is the certificate's**: the pipeline at scc's configuration `config` gives
what it gives at `configW` (`{isa.placeW}.lowerAll_eq_of_tables`: the tables' stage at the
witness succeeds, `prog_tablesW`, and whatever `emitTablesW` gives is the reference
`emitTables`' result). -/
theorem prog_sameAsScc : {isa.lower}.lowerAll config prog_src = {isa.lower}.lowerAll configW prog_src :=
  {isa.placeW}.lowerAll_eq_of_tables rfl prog_src gwLit prog_tablesW

/-- `out` is the placement view of the run at `configW` (`prog_sameAsScc`). -/
theorem out_eqW : out = {ns}.Out.ofEmitted ({isa.lower}.lowerAll configW prog_src){outArgs} :=
  congrArg (fun e => {ns}.Out.ofEmitted e{outArgs}) prog_sameAsScc
"
  let tablesOk := s!"
/-- **The GC tables of `scc`'s output** for `prog_src`: the tables' stage of
`{isa.lower}.lowerAll config prog_src` (scc's configuration: the reference stage
`emitTables`) succeeds, with the items `titsLit` the listing appends and the data `tblLit`
that ends `outLit`'s `.rodata` (`prog_sameAsScc`, `prog_tablesW`). -/
theorem prog_tablesOk : ({isa.lower}.lowerAll config prog_src).tables = .ok (titsLit, tblLit) := by
  rw [prog_sameAsScc]; exact prog_tablesW

/-- info: 'SccCertificate.prog_sameAsScc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prog_sameAsScc

/-- info: 'SccCertificate.prog_tablesOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prog_tablesOk

/-- info: 'SccCertificate.prog_tables_merged' depends on axioms: [propext] -/
#guard_msgs in #print axioms prog_tables_merged
"
  let outEq := if isa.staged then s!"
/-- The lowering of `prog_src`, at elaboration time. -/
def loweredVal : Option (Scc.IR.Program × Bool) := {ns}.lowered1 configW prog_src

/-- The lowering's IR and setup flag, as a literal (untrusted, checked by
`lowered_eq`). -/
def loweredLit : Scc.IR.Program × Bool := (scc_lit% loweredVal).get!

/-- The emission of the literal IR, at elaboration time. -/
def emittedVal : Option (List {isa.emit}.Item × List {isa.safepoint}) :=
  ({isa.emit}.emitItemsMaps loweredLit.1).toOption

/-- The emitter's items and safepoints, as a literal (untrusted, checked by
`emitted_eq`). -/
def emittedLit : List {isa.emit}.Item × List {isa.safepoint} := (scc_lit% emittedVal).get!

/-- The stack budget's depth limit, at elaboration time. -/
def framesVal : Option Nat := Scc.Cert.LowerStage.frames1 configW prog_src

/-- The depth limit as a literal (untrusted, checked by `frames_eq`). -/
def framesLit : Nat := (scc_lit% framesVal).get!

/-- The budget gives the depth limit `framesLit` (kernel-checked: the kernel
runs the lowering for the frames, here). -/
theorem frames_eq : Scc.Cert.LowerStage.frames1 configW prog_src = some framesLit := by kernel_rfl

/-- The lowering gives `loweredLit` (kernel-checked: the kernel runs the
lowering, here). -/
theorem ir_eq : Scc.Cert.LowerStage.ir1 configW prog_src = some loweredLit := by kernel_rfl

/-- The lowering gives `loweredLit` (`lowered1_of_stages`: the budget and
the lowering above). -/
theorem lowered_eq : {ns}.lowered1 configW prog_src = some loweredLit :=
  {ns}.lowered1_of_stages frames_eq ir_eq

{emitStage isa pl.funcs}{gcStage isa cfg.arch pl.funcs}{tablesW}{outLast}{tablesOk}" else "
/-- `out` is `outLit` (kernel-checked: the kernel runs the lowering once,
here, and the decisions below read the literal). -/
theorem out_eq : out = outLit := by kernel_rfl
"
  let accept := if accepted then s!"
/-- `prog_src` is in the fragment the first compiler theorem covers
(kernel-checked). -/
theorem prog_accepted : Scc.Lower.Accepted0 prog_src = true := by decide +kernel
" else s!"
/-- `prog_src` is outside the fragment the first compiler theorem covers
(kernel-checked): no `prog_cert_ready` is stated. -/
theorem prog_not_accepted : Scc.Lower.Accepted0 prog_src = false := by decide +kernel
"
  -- A1 to A9: `placeOK`'s and `placeOK2`'s alike.
  let sns := isa.spawnNs
  let common := s!"
/-- A1 of `outLit` (kernel-checked; each component is its own declaration,
so that the kernel keeps one component's terms alive at a time). -/
theorem prog_placeOK_1 : {ns}.a1 outLit {t} = true := by
  decide +kernel

{a2Parts}
/-- A2 of `outLit` (kernel-checked). -/
theorem prog_placeOK_2 : {ns}.a2 outLit {t} = true :={a2Pf}

/-- A4 of `outLit` (kernel-checked). -/
theorem prog_placeOK_4 : {ns}.a4 {can} outLit {t} = true := by
  decide +kernel

/-- A7 of `outLit` (kernel-checked). -/
theorem prog_placeOK_7 : {ns}.a7 outLit {t} = true := by
  decide +kernel

/-- A3 of `outLit`: the block table at its places (kernel-checked). -/
theorem prog_placeOK_3 : {ns}.a3 outLit {t} = true :=
  {ns}.a3_of_parts (by decide +kernel) (by decide +kernel)

/-- A5 of `outLit`: the block table covered at its offsets (kernel-checked). -/
theorem prog_placeOK_5 : {ns}.a5 outLit {t} = true := by
  decide +kernel

/-- A6 of `outLit`: the block table in its phases (kernel-checked). -/
theorem prog_placeOK_6 : {ns}.a6 outLit {t} = true :=
  {ns}.a6_of_parts (by decide +kernel) (by decide +kernel)

/-- A8 of `outLit`: the runtime's data words (kernel-checked). -/
theorem prog_placeOK_8 : {ns}.a8 outLit {t} = true := by
  decide +kernel
{a9Thm}"
  let positive := s!"{common}
/-- A11 of `outLit`: the runtime's fixed code (kernel-checked). -/
theorem prog_placeOK_11 : {ns}.a11 outLit {t} = true := by
  decide +kernel
{a12Thm}
/-- **`placeOK` of `scc`'s output** for `prog_src`. -/
theorem prog_placeOK : {ns}.placeOK {can} out = true := by
  rw [out_eq]
  exact {ns}.placeOK_of prog_placeOK_1 prog_placeOK_2 prog_placeOK_3 prog_placeOK_4 prog_placeOK_5
    prog_placeOK_6 prog_placeOK_7 prog_placeOK_8{a9Arg} prog_placeOK_11{a12Arg}
"
  -- `placeOK2` (`Isa.spawnMod`) for a program that takes its thread id or
  -- spawns: A1 to A9 as `placeOK`'s, A11'
  -- for A11, A12' in its two parts and A13, each its own declaration.
  let positive2 := s!"{common}
/-- A11' of `outLit`: the runtime's fixed code, at the thread-id shape when
`main` takes its thread id (kernel-checked). -/
theorem prog_placeOK_11 : {sns}.a11' outLit {t} = true := by
  decide +kernel

/-- A12''s code part of `outLit` (kernel-checked). -/
theorem prog_placeOK_12c : {sns}.a12code' outLit = true := by
  decide +kernel

/-- A12''s phase part of `outLit` (kernel-checked). -/
theorem prog_placeOK_12p : {sns}.a12ph' outLit {t} = true := by
  decide +kernel

/-- A13 of `outLit`: the second thread's words and the spawn path's runtime
code (kernel-checked). -/
theorem prog_placeOK_13 : {sns}.a13 outLit {t} = true := by
  decide +kernel

/-- **`placeOK2` of `scc`'s output** for `prog_src`. -/
theorem prog_placeOK2 : {sns}.placeOK2 {can} out = true := by
  rw [out_eq]
  exact {sns}.placeOK2_of prog_placeOK_1 prog_placeOK_2 prog_placeOK_3 prog_placeOK_4 prog_placeOK_5
    prog_placeOK_6 prog_placeOK_7 prog_placeOK_8 prog_placeOK_9 prog_placeOK_11 prog_placeOK_12c
    prog_placeOK_12p prog_placeOK_13
"
  let negative (n : Nat) : String :=
    let cfgArg := if n == 4 then s!" {can}" else ""
    s!"
/-- A{n} of `outLit` fails (kernel-checked). -/
theorem prog_placeOK_{n} : {ns}.a{n}{cfgArg} outLit {t} = false := by
  decide +kernel

/-- **`placeOK` of `scc`'s output is `false`** for `prog_src` (A{n}): no
`prog_cert_ready` is stated. -/
theorem prog_not_placeOK : {ns}.placeOK {can} out = false := by
  rw [out_eq]
  exact {ns}.placeOK_eq_false_of_a{n} prog_placeOK_{n}
"
  -- The tables per function (`tablesPart`): on the staged emitter's literals
  -- (`areasLit`), x86-64 with its sizes.
  let tables := if isa.staged && isa.emitStaged && pl.funcs != 0 && (sized || cfg.arch == .arm) then
    tablesPart cfg.arch pl.funcs else ""
  let place := s!"
/-- The configuration of the placement check: the canonical one, with the
program's thread entries and their stack budget (`needOk`'s). -/
def placeCfg : Scc.Cert.PlaceOK.Config :=
  \{ Scc.Cert.PlaceOK.Config.canonical with needBudget := {pl.budget}, entries := [{es}] }

/-- `out` as a literal: its value computed at elaboration time (`scc_lit%`,
untrusted), trusted through `out_eq`. -/
def outLit : {ns}.Out := scc_lit% out
{outEq}{tables}{match pl.fails with | some n => negative n | none => if pl.spawn then positive2 else positive}"
  let ready := if accepted && pl.fails.isNone then
    if pl.spawn then s!"
/-- **Acceptance and placement** of `prog_src`'s compilation. -/
theorem prog_cert_ready : Scc.Lower.Accepted0 prog_src = true ∧ {sns}.placeOK2 {can} out = true :=
  ⟨prog_accepted, prog_placeOK2⟩
" else s!"
/-- **Acceptance and placement** of `prog_src`'s compilation. -/
theorem prog_cert_ready : Scc.Lower.Accepted0 prog_src = true ∧ {ns}.placeOK {can} out = true :=
  ⟨prog_accepted, prog_placeOK⟩
" else ""
  s!"
/-! ## Acceptance and placement -/

/-- The WeakCore program `scc`'s frontend reads from `source`, as a term
(the kernel does not run the frontend's parser). -/
def prog_src : CoreTerm.Prog :=
  {SrcTerm.progTerm prog}

-- The frontend reads `source` as `prog_src` (evaluation, not a proof).
#guard Scc.Cert.SrcTerm.reads source prog_src
{accept}{accept1}
/-- `scc`'s output for `prog_src` as the placement check reads it: the
lowering and the emission (`{isa.lower}.lowerAll`) with the placement data
computed from them. -/
def out : {ns}.Out := {ns}.Out.ofEmitted ({isa.lower}.lowerAll config prog_src){outArgs}

-- The loader's parse of `asm` is `out`'s code and data sections (evaluation,
-- not a proof: the trust boundary).
#guard {isa.link}.parsesTo {asmArg} out.prog out.secs
{place}{ready}"

/-- The line that marks a file `render` writes for a program outside the
certified fragment (`renderOutside`); `Scc/Test/run.sh` counts such files as
not certifiable. -/
def outsideMark : String :=
  "-- outside the certified fragment: no stack need table (non-tail recursion)"

/-- The file `render` writes for a program without a stack need table (non-tail
recursion): `placeOK`'s A4 cannot hold, so there is no certificate, and no
partial one either. It embeds the source and says why (`outsideMark`). -/
def renderOutside (cfg : Config) (name src : String) : String :=
  let srcHash := Sha256.ofString src
  s!"/-!
# scc: `{name}`, `--arch {cfg.arch.name}`: not certifiable

Generated by `scc --cert`. The program is outside the certified fragment:
the lowering has no stack need table (the program has non-tail recursion),
so `placeOK`'s A4 (the stack need) cannot hold, and the file states nothing.
-/

{outsideMark}

namespace SccCertificate

-- SHA-256 (UTF-8): {srcHash}
/-- The WeakCore source `{name}`, verbatim. -/
def source : String := {quote src}

end SccCertificate
"

/-- The listings' size, in lines, from which a certificate checks the block
table one function at a time (`blocksStage`): the literal of the functions
that this needs costs about 2 s, which on a listing of little more than the
runtime (about 1500 lines) outweighs what it saves; on larger ones the
single check's memory grows with the whole program. -/
def blocksSplitMin : Nat := 2000

/-- `pl` with the block table checked per function only on a listing of at
least `blocksSplitMin` lines. -/
def blocksParts (asm : String) (pl : Placement) : Placement :=
  if (asm.splitOn "\n").length ≥ blocksSplitMin then pl else { pl with parts := 0 }

/-- The certificate for a compilation of `src` (file name `name`) to `asm`
under `cfg`, of the program `prog` the frontend read from `src`, in the
fragment `Scc.Lower.Accepted0` or not, with its stack need's configuration
(`pl`). -/
def render (cfg : Config) (name src asm : String)
    (sizes : Option (List Nat × List (String × Nat))) (prog : CoreTerm.Prog) (pl : Placement) :
    String :=
  if !pl.hasNeed then renderOutside cfg name src else
  let isa := isaOf cfg.arch
  let srcHash := Sha256.ofString src
  let asmHash := Sha256.ofString asm
  let spawnImport := if pl.spawn then s!"\nimport {isa.spawnMod}" else ""
  s!"import {isa.module}
import {isa.place}{spawnImport}
import {isa.placeW}
import {isa.tablesMod}
import Scc.Cert.SrcTerm

{docstring cfg name srcHash asmHash sizes.isSome pl}

namespace SccCertificate

-- Deep terms: the reparse of a large `asm` (`prog`) and the kernel's
-- decisions below.
set_option maxRecDepth 100000

-- SHA-256 (UTF-8): {srcHash}
/-- The WeakCore source `{name}`, verbatim. -/
def source : String := {quote src}

-- SHA-256 (UTF-8): {asmHash}
/-- The assembler text `scc --arch {cfg.arch.name}` wrote, verbatim. -/
def asm : String := {quote asm}

/-- The configuration `scc` compiled with: every statement of the certificate is at it. -/
def config : Scc.Config := {cfgTerm cfg}
{gwPart isa pl.funcs}
/-- The configuration the certificate's proofs run the pipeline at: `config`, with the GC
tables' ranked witness `gwLit` (`Scc.Config.gcWit`: the tables' stage is `emitTablesW`'s from
it, which refuses unless every function's witness is its least fixpoint). `prog_sameAsScc`
proves the run at it is the run at `config`. -/
def configW : Scc.Config := \{ config with gcWit := some gwLit }

-- Reproducibility check (evaluation, not a proof): `source` compiles to
-- exactly `asm`.
#guard {isa.ns}.reproduces config source asm

/-- The program Kraken's parser reads from `asm` (computed at elaboration
time). -/
def prog : _root_.Program := {isa.reparse} asm

/-- `prog` satisfies the lowerability predicate (kernel-checked). -/
theorem lowerable : {isa.predicate} := by decide +kernel
{sizesPart sizes}{placePart cfg prog (blocksParts asm pl) sizes.isSome}
-- Placeholder for the future correctness statement (not stated yet):
-- theorem correct : Scc.Correct config source prog

end SccCertificate
"

end Scc.Cert.Gen
