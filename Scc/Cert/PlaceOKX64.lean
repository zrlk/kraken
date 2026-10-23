import Scc.Cert.PlaceOK
import Scc.Cert.LinkX64
import Scc.Cert.Rt.CodeX64
import Scc.Cert.Rt.WideX64
import Scc.Cert.Rt.X64Abort
import Scc.Cert.Rt.X64RtIn
import Scc.Cert.Rt.OffsX64
import Scc.Cert.Rt.CoverX64
import Scc.Cert.NeedX64
import Scc.Cert.Rt.RtWordsX64
import Spike.Lib.X64CodeSegs
import Spike.Lib.Rt.X64CodeIn
import Scc.Cert.Rt.PhasesX64
import Spike.Lib.LowerX64.Checks
import Spike.Lib.LowerX64.PhCheck
import Spike.Lib.X64AbortPh
import Scc.Cert.Rt.RtInitX64
import Spike.Lib.Rt.X64RtPhTab

/-!
# `PlaceOK` on x86-64

The x86-64 instance of the per-program placement check
(`Scc/Cert/PlaceOK.lean`), the twin of `Scc/Cert/PlaceOKA64.lean`: the
output's types, its tables and the ten components, each with its extraction
lemma from `PlaceOK` to the `Prop` the proofs use.

* **The output** `Out`: the code cells the canonical loader lays out (sized
  directives, `Scc.Sem.X64.cellsOf`), the data sections, the label offsets
  the assembler reported (`labelOffs`, checked against the cells' sizes by
  A2), and the placement data `PlaceData`: the block table (`scc --blocks`),
  the stack need table (`Scc.Lower.stackNeed`) and the shape of
  `scc_rt_main`'s tail.
* **The tables** `tablesOf cfg o`: the static link of the cells at the
  configuration's bases, code labels resolved in the cells at their byte
  addresses (`Scc.Sem.X64.codeLabel`); at `Config.canonical` it is
  `Link.X64.linkOf` (`tablesOf_canonical`). The link has no immediate table
  (`Layout.imms`): no component reads it (`loadOk_withImms` …).
* **The components**:
  - A1 the static link well-formed (`Link.wfB`; `wf_of_placeOK`), its
    layout facts (`PlaceOK.layoutOk`: `.rodata` clear of the stack pool,
    the regions of their own at their symbols and sizes, everything below
    `2 ^ 32`; `layoutOk_of_placeOK`, `below32_of_placeOK` …), and `_start`
    at the code base (`start_at_lo_of_placeOK`);
  - A2 the canonical loader's checks (the size table against `labelOffs`
    included), the abort labels in the cells and the image
    (`Link.X64.loadOk`, `abortsIn`, `imageIn`; `validLayout_of_placeOK`);
  - A3 the block table at its places (`Rt.X64.blocksIn` of
    `Rt.X64.toGrps`; `codeAt_of_placeOK`), and covering the cells: every
    non-label cell in the run after a label, each run tiled by its label's
    rows and single instructions, or single instructions where the label
    has no group (`Rt.X64.coverOk`; `cover_of_placeOK`, `inRow_of_placeOK`);
  - A4 the one-word fragment and the stack need (`WideX64.wideIn`,
    `NeedX64.needOk`; `wideSt_of_placeOK`, `needOk_of_placeOK`);
  - A7 (in part) the runtime's fixed code in one pass over the cells
    (`Rt.X64.rtIn`, `Scc/Cert/Rt/X64RtIn.lean`): `scc_rt_main`'s tail
    (`mainIn0`/`Abort.mainIn` by `PlaceData.tail`), `scc_rt_print`
    (`Print.printIn`), the abort stubs and `scc_rt_abort`
    (`Abort.abortIn`);
  - A5 the block table's static offsets: every row covered at its
    offsets, the offsets agreeing along the fall-through edges
    (`Rt.X64.offsetsOk`; `okBlk_of_placeOK`, `soLe_of_placeOK`,
    `sorel_next_of_placeOK`);
  - A8 the runtime's data words: each a data symbol of the link at its
    label, below `2 ^ 32`, 8-aligned, clear of the stack pool, in `.data` or
    the pinned region; the pool and
    the first stack in place, the words pairwise disjoint
    (`Rt.X64.rtWordsOk`; `lab_of_placeOK`, `wordsOk_of_placeOK` and their
    `_link` forms, `words_disj_of_placeOK`, `tcbSep_of_placeOK`); none
    with an initial word in the load (`Rt.X64.rtInitOk`;
    `rtInit_of_placeOK`); the first TCB's words clear of `.data` and
    the heap (`Rt.X64.rtOffOk`; `rtOff_of_placeOK`);
  - A6 the phases: every row of the block table but a site's `nop` off
    the marks' sites and in its entry's phase, every instruction covered,
    the phase table and the sites resolved in the cells, the sites
    distinct (`Rt.X64.phasesOk`; `rowPhOk_of_placeOK`, `label_of_placeOK`,
    `sites_nodup_of_placeOK`);
  - A9 the lowered code blocks' code: every `func0`-shaped function
    returning one operand of the lowered IR (`PlaceData.ir`, no IR failing) has its emitted prologue and
    body at its entry label, its frame recomputed from the IR
    (`Spike.Lib.LowerX64.fnCodeOk`; `fnCodeOk_of_placeOK`,
    `fnCode_of_placeOK`). Functions of other shapes (the runtime's, those
    with several blocks or other instructions) are not checked by it;
  - A11 the runtime's fixed code: `scc_rt_start`, `scc_rt_main` at the
    tail's `MainCode` (`mcOf`), `scc_rt_alloc_tcb`, `scc_rt_thread_init`
    and `scc_rt_stack_take`, in one pass over the cells
    (`Spike.Lib.X64.Rt.rtCodeOk`; `rtCodeOk_of_placeOK`). `false` on a
    `.setup` tail, so such a program fails `PlaceOK` for now
    (`placeOK_eq_false_of_a11`).

Where x86-64 differs from AArch64: the program is a list of sized cells and
every offset is in bytes (a block's offset from its label, a label's address
the sum of the sizes before it); the assembler's label offsets are an input
of the output, untrusted, checked by A2 (`sizeOkL` inside `loadOk`).
-/

namespace Scc.Cert.PlaceOK.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link.X64

/-- The shape of `scc_rt_main`'s tail: the `exit_group` tail right after
the call of `wc_main` (`.bare`, `mainIn0`), or after a setup block
(`.setup`, `Abort.mainIn`). -/
inductive MainShape where
  | bare
  | setup
  deriving DecidableEq, Repr

/-- **The x86-64 placement data**: the block table with its static offsets
(`scc --blocks`: the `block_spec` blocks per label with their cell counts,
byte offsets, regions and entry offsets, `Rt.X64.OGrp`; `Rt.X64.toGrps` is
the table), the stack need table (`NeedX64.Row`: label, frame, need), and
the shape of `scc_rt_main`'s tail. -/
structure PlaceData where
  blocks : List Rt.X64.OGrp
  need : List NeedX64.Row
  tail : MainShape
  /-- The lowered IR the program was emitted from (A9). -/
  ir : Option Scc.IR.Program := none

/-- **scc's x86-64 output**. -/
abbrev Out := PlaceOK.Out (List (Directive × Nat)) PlaceData

/-- **The x86-64 tables**: the ISA-generic ones (the static link). -/
abbrev Tables := PlaceOK.Tables

/-- **The tables of an output**: the static link at the configuration's
bases, code labels resolved in the cells at the code base. -/
def tablesOf (cfg : Config) (o : Out) : Tables :=
  linkTables cfg o.secs (codeLabel cfg.bases.codeLo o.prog)

/-- At the canonical configuration the link is `Link.X64.linkOf`. -/
theorem tablesOf_canonical (o : Out) : (tablesOf Config.canonical o).Λ = linkOf o.prog o.secs := rfl

/-! ## The components -/

/-- **The code in its region**: the program laid out from the code base
ends within the layout's code region (`Scc.Sem.X64.codeEnd`), so that nothing the
layout places after the code region overlaps it. -/
def codeFits (o : Out) (Λ : Scc.Sem.Layout) : Bool :=
  decide (Scc.Sem.X64.codeEnd Λ.code.lo o.prog ≤ Λ.code.lo + Λ.code.size)

/-- **A1**: the static link is well-formed, its layout facts hold
(`PlaceOK.layoutOk`, independent of the entry state), the code in its
region (`codeFits`), and `_start` is at
the code base (the loader's entry pc is `Λ.code.lo`, so the entry is
`_start`). -/
def a1 (o : Out) (t : Tables) : Bool :=
  PlaceOK.a1 t && layoutOk o.secs t.Λ && codeFits o t.Λ &&
    decide (codeLabel t.Λ.code.lo o.prog "_start" = some t.Λ.code.lo)

/-- **A2**: the canonical loader's checks of the link (the size table
against the assembler's label offsets included), its abort labels in the
cells, its image. -/
def a2 (o : Out) (t : Tables) : Bool :=
  loadOk t.Λ o.prog o.secs o.labelOffs && abortsIn o.prog t.Λ && imageIn o.prog o.secs t.Λ

/-- **A3**: every block of the table is code at its label and byte offset,
and every non-label cell is in a row or a single instruction of the table. -/
def a3 (o : Out) (_ : Tables) : Bool :=
  decide (Rt.X64.blocksIn o.prog (Rt.X64.toGrps o.place.blocks)) && Rt.X64.coverOk o.prog o.place.blocks

/-- **A5**: every row of the block table covered at its static offsets, and
the offsets agreeing along the fall-through edges. -/
def a5 (o : Out) (_ : Tables) : Bool :=
  Rt.X64.offsetsOk o.place.blocks

/-- **A4**: the one-word fragment; the stack need table on the cells,
within the budget at the thread entries. -/
def a4 (cfg : Config) (o : Out) (_ : Tables) : Bool :=
  WideX64.wideIn (o.prog.map (·.1)) && NeedX64.needOk o.prog o.place.need cfg.needBudget cfg.entries

/-- **The tail of `scc_rt_main` without a setup block**: the `exit_group`
tail right after `.Lscc_rt_main.x2` (the call's return), the result at
`-16(%rbp)` (`Spike.Lib.X64.Flow.exitIn`). -/
def mainIn0 (cells : List (Directive × Nat)) : Bool :=
  Spike.Lib.X64.Flow.exitIn cells ".Lscc_rt_main.x2" (-16) 4 4 5

/-- The groups of `scc_rt_main`'s tail in the shape the placement data
names (`RtIn.mainGrps0`/`mainGrps1`). -/
def mainGrps : MainShape → List Rt.X64.RGrp
  | .bare => Rt.X64.RtIn.mainGrps0
  | .setup => Rt.X64.RtIn.mainGrps1

/-- **A7** (the runtime's part): the tail of `scc_rt_main`, `scc_rt_print`,
the abort stubs and `scc_rt_abort`, checked in one pass over the cells, and
the overflow abort path's phase facts at A6's tables and the code labels
(`abortPhC`). -/
def a7 (o : Out) (t : Tables) : Bool :=
  Rt.X64.rtIn o.prog (Rt.X64.RtIn.rtTab (mainGrps o.place.tail)) &&
    Spike.Lib.X64.StubW.abortPhC t.Λ.code.lo t.Λ o.prog

/-- **A6**: every row of the block table in its entry's phase, off the
sites, and the runtime's phase facts but `scc_rt_main`'s (`rtPhOk` at
`rtPhTab none`). -/
def a6 (o : Out) (t : Tables) : Bool :=
  Rt.X64.phasesOk t.Λ.code.lo o.prog t.Λ o.place.blocks &&
    Rt.X64.rtPhOk t.Λ.code.lo o.prog t.Λ (Spike.Lib.X64.Rt.rtPhTab none)

/-- **A8**: the runtime's data words in the link, none of them with an
initial word in the load (`rtInitOk`), the first TCB's words clear of
`.data` and the heap (`rtOffOk`). -/
def a8 (o : Out) (t : Tables) : Bool :=
  Rt.X64.rtWordsOk t.Λ o.prog o.secs && Rt.X64.rtInitOk t.Λ o.prog o.secs && Rt.X64.rtOffOk t.Λ o.prog o.secs

/-- `scc_rt_main`'s facts (`Spike.Lib.X64.Rt.MainCode`) from the placement
data's shape of its tail: today's emitter writes one `scc_rt_main` without a
setup block (`bareMC`: frame 32, the result at `-16`, `wc_main`); after a
setup block the generic `mainUIn` does not apply yet (`none`). -/
def mcOf : MainShape → Option Spike.Lib.X64.Rt.MainCode
  | .bare => some Spike.Lib.X64.Rt.bareMC
  | .setup => none

/-- **A11**: the runtime's fixed code (`scc_rt_start`, `scc_rt_main` at
`mcOf`, `scc_rt_alloc_tcb`, `scc_rt_thread_init`, `scc_rt_stack_take`)
checked in one pass over the cells (`Spike.Lib.X64.Rt.rtCodeOk`).
`false` on a `.setup` tail until that shape's `MainCode` exists. The groups
name the runtime's local return points as today's single-thread emitter
numbers them (`.Lscc_rt_thread_init.x7`); the numbering is per program.
With it, `scc_rt_main`'s phase facts at `mcOf` (`rtPhOk` at `mainPhTab`). -/
def a11 (o : Out) (t : Tables) : Bool :=
  match mcOf o.place.tail with
  | some mc =>
    Spike.Lib.X64.Rt.rtCodeOk o.prog mc && Rt.X64.rtPhOk t.Λ.code.lo o.prog t.Λ (Spike.Lib.X64.Rt.mainPhTab mc)
  | none => false

/-- **A9** (the lowered code blocks' part, `fnCodeOk`): the prologue and
body of every `func0`-shaped function of the IR the output names, at its
frame recomputed from the IR, and their phase facts at A6's tables and the
code labels (`fnPhOk`); no IR fails. -/
def a9 (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => Spike.Lib.LowerX64.fnCodeOk o.prog ir && Spike.Lib.LowerX64.fnPhOk t.Λ.code.lo t.Λ o.prog ir
  | none => false

/-- **The ten components** on x86-64. -/
def checks (cfg : Config) : Checks Out Tables where
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4 cfg
  a5 := a5
  a6 := a6
  a7 := a7
  a8 := a8
  a9 := a9
  a11 := a11

/-- **`PlaceOK` on x86-64.** -/
def placeOK (cfg : Config) (o : Out) : Bool := (checks cfg).ok (tablesOf cfg) o

/-- **`PlaceOK` at a given layout** `Λ` in place of the static link (one
read off an executable, say); the configuration still gives A4's budget and
thread entries. -/
def placeOKAt (cfg : Config) (Λ : Scc.Sem.Layout) (o : Out) : Bool := (checks cfg).ok (fun _ => ⟨Λ⟩) o

/-- `PlaceOK` is `placeOKAt` at the static link. -/
theorem placeOK_eq_placeOKAt (cfg : Config) (o : Out) : placeOK cfg o = placeOKAt cfg (tablesOf cfg o).Λ o := rfl

/-- `PlaceOK` passes `placeOKAt` at the static link: the coercion callers of
the `placeOKAt` lemmas use (it spares the elaborator unfolding the link). -/
theorem atTables {cfg : Config} {o : Out} (h : placeOK cfg o = true) :
    placeOKAt cfg (tablesOf cfg o).Λ o = true := h

/-- `placeOKAt` reads neither the static-symbol table nor the immediate pool
of `Λ`: no check looks at them, so overriding them leaves the verdict unchanged. -/
theorem placeOKAt_static (cfg : Config) (Λ : Scc.Sem.Layout) (o : Out) (s) (i) :
    placeOKAt cfg { Λ with static := s, imms := i } o = placeOKAt cfg Λ o := rfl

/-! ## `PlaceOK` from its parts

A certificate decides each part below in its own declaration (or file:
the kernel's cost of one decision grows with the terms it shares), and
`placeOK_of` combines them without another decision. -/

section Parts

variable {cfg : Config} {o : Out}

theorem a1_of_parts (h1 : PlaceOK.a1 (tablesOf cfg o) = true) (h2 : layoutOk o.secs (tablesOf cfg o).Λ = true)
    (hc : codeFits o (tablesOf cfg o).Λ = true)
    (h3 : codeLabel (tablesOf cfg o).Λ.code.lo o.prog "_start" = some (tablesOf cfg o).Λ.code.lo) :
    a1 o (tablesOf cfg o) = true := by
  simp only [a1, h1, h2, hc, h3, decide_true, Bool.and_self]

theorem a2_of_parts (h1 : loadOk (tablesOf cfg o).Λ o.prog o.secs o.labelOffs = true)
    (h2 : abortsIn o.prog (tablesOf cfg o).Λ = true) (h3 : imageIn o.prog o.secs (tablesOf cfg o).Λ = true) :
    a2 o (tablesOf cfg o) = true := by
  simp only [a2, h1, h2, h3, Bool.and_self]

theorem a3_of_parts (h1 : decide (Rt.X64.blocksIn o.prog (Rt.X64.toGrps o.place.blocks)) = true)
    (h2 : Rt.X64.coverOk o.prog o.place.blocks = true) : a3 o (tablesOf cfg o) = true := by
  simp only [a3, h1, h2, Bool.and_self]

theorem a4_of_parts (h1 : WideX64.wideIn (o.prog.map (·.1)) = true)
    (h2 : NeedX64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true) :
    a4 cfg o (tablesOf cfg o) = true := by
  simp only [a4, h1, h2, Bool.and_self]

theorem a5_of_parts (h : Rt.X64.offsetsOk o.place.blocks = true) : a5 o (tablesOf cfg o) = true := h

theorem a6_of_parts
    (h : Rt.X64.phasesOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ o.place.blocks = true)
    (hrt : Rt.X64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.X64.Rt.rtPhTab none) = true) :
    a6 o (tablesOf cfg o) = true := by
  simp only [a6, h, hrt, Bool.and_self]

theorem a7_of_parts (h : Rt.X64.rtIn o.prog (Rt.X64.RtIn.rtTab (mainGrps o.place.tail)) = true)
    (hph : Spike.Lib.X64.StubW.abortPhC (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog = true) :
    a7 o (tablesOf cfg o) = true := by
  simp only [a7, h, hph, Bool.and_self]

theorem a8_of_parts (h : Rt.X64.rtWordsOk (tablesOf cfg o).Λ o.prog o.secs = true)
    (hi : Rt.X64.rtInitOk (tablesOf cfg o).Λ o.prog o.secs = true)
    (hc : Rt.X64.rtOffOk (tablesOf cfg o).Λ o.prog o.secs = true) :
    a8 o (tablesOf cfg o) = true := by
  simp only [a8, h, hi, hc, Bool.and_self]

theorem a11_of_parts {mc : Spike.Lib.X64.Rt.MainCode} (hs : mcOf o.place.tail = some mc)
    (h : Spike.Lib.X64.Rt.rtCodeOk o.prog mc = true)
    (hph : Rt.X64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.X64.Rt.mainPhTab mc) = true) :
    a11 o (tablesOf cfg o) = true := by
  simp only [a11, hs, h, hph, Bool.and_self]

theorem a9_of_parts {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    (h : Spike.Lib.LowerX64.fnCodeOk o.prog ir = true)
    (hph : Spike.Lib.LowerX64.fnPhOk (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog ir = true) :
    a9 o (tablesOf cfg o) = true := by
  simp only [a9, hir, h, hph, Bool.and_self]

/-- **`PlaceOK` from its components.** -/
theorem placeOK_of (h1 : a1 o (tablesOf cfg o) = true) (h2 : a2 o (tablesOf cfg o) = true)
    (h3 : a3 o (tablesOf cfg o) = true) (h4 : a4 cfg o (tablesOf cfg o) = true)
    (h5 : a5 o (tablesOf cfg o) = true) (h6 : a6 o (tablesOf cfg o) = true)
    (h7 : a7 o (tablesOf cfg o) = true) (h8 : a8 o (tablesOf cfg o) = true)
    (h9 : a9 o (tablesOf cfg o) = true) (h11 : a11 o (tablesOf cfg o) = true) : placeOK cfg o = true :=
  Checks.ok_of (C := checks cfg) h1 h2 h3 h4 h5 h6 h7 h8 h9 h11

/-- A wrong static link (A1: not well-formed, the entry stack not clear of it, or `_start` not at the code
base) fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a1 (h : a1 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- A program outside the one-word fragment or over its stack need (A4) fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a4 (h : a4 cfg o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- A wrong block table (A3) fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a3 (h : a3 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong static offsets (A5) fail `PlaceOK`. -/
theorem placeOK_eq_false_of_a5 (h : a5 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong phases (A6: the rows' or the runtime's) fail `PlaceOK`. -/
theorem placeOK_eq_false_of_a6 (h : a6 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- A missing IR or a lowered code block not in the cells (A9) fails
`PlaceOK`. -/
theorem placeOK_eq_false_of_a9 (h : a9 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong runtime code or abort path phases (A7) fail `PlaceOK`. -/
theorem placeOK_eq_false_of_a7 (h : a7 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- A wrong load (A2: the label offsets, the abort labels or the image) fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a2 (h : a2 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong runtime data words (A8) fail `PlaceOK`. -/
theorem placeOK_eq_false_of_a8 (h : a8 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong runtime fixed code or `scc_rt_main`'s phases (A11), or a tail without its `MainCode` yet
(`.setup`), fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a11 (h : a11 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- **`placeOKAt` from its components** (at a layout `Λ`, one read off an
executable, say). -/
theorem placeOKAt_of {Λ : Scc.Sem.Layout} (h1 : a1 o ⟨Λ⟩ = true) (h2 : a2 o ⟨Λ⟩ = true) (h3 : a3 o ⟨Λ⟩ = true)
    (h4 : a4 cfg o ⟨Λ⟩ = true) (h5 : a5 o ⟨Λ⟩ = true) (h6 : a6 o ⟨Λ⟩ = true) (h7 : a7 o ⟨Λ⟩ = true)
    (h8 : a8 o ⟨Λ⟩ = true) (h9 : a9 o ⟨Λ⟩ = true) (h11 : a11 o ⟨Λ⟩ = true) : placeOKAt cfg Λ o = true :=
  Checks.ok_of (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h1 h2 h3 h4 h5 h6 h7 h8 h9 h11

/-- A failing component fails `placeOKAt` (A1, say a code that overruns
the layout's code region, `codeFits`). -/
theorem placeOKAt_eq_false_of_a1 {Λ : Scc.Sem.Layout} (h : a1 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-! The same at a layout `Λ` (one read off an executable, say), for a
certificate driver's diagnostics. -/

theorem a1_of_partsAt {Λ : Scc.Sem.Layout} (h1 : PlaceOK.a1 ⟨Λ⟩ = true) (h2 : layoutOk o.secs Λ = true)
    (hc : codeFits o Λ = true)
    (h3 : codeLabel Λ.code.lo o.prog "_start" = some Λ.code.lo) :
    a1 o ⟨Λ⟩ = true := by
  simp only [a1, h1, h2, hc, h3, decide_true, Bool.and_self]

theorem a2_of_partsAt {Λ : Scc.Sem.Layout} (h1 : loadOk Λ o.prog o.secs o.labelOffs = true)
    (h2 : abortsIn o.prog Λ = true) (h3 : imageIn o.prog o.secs Λ = true) :
    a2 o ⟨Λ⟩ = true := by
  simp only [a2, h1, h2, h3, Bool.and_self]

theorem a3_of_partsAt {Λ : Scc.Sem.Layout} (h1 : decide (Rt.X64.blocksIn o.prog (Rt.X64.toGrps o.place.blocks)) = true)
    (h2 : Rt.X64.coverOk o.prog o.place.blocks = true) : a3 o ⟨Λ⟩ = true := by
  simp only [a3, h1, h2, Bool.and_self]

theorem a4_of_partsAt {Λ : Scc.Sem.Layout} (h1 : WideX64.wideIn (o.prog.map (·.1)) = true)
    (h2 : NeedX64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true) :
    a4 cfg o ⟨Λ⟩ = true := by
  simp only [a4, h1, h2, Bool.and_self]

theorem a5_of_partsAt {Λ : Scc.Sem.Layout} (h : Rt.X64.offsetsOk o.place.blocks = true) : a5 o ⟨Λ⟩ = true := h

theorem a6_of_partsAt {Λ : Scc.Sem.Layout}
    (h : Rt.X64.phasesOk Λ.code.lo o.prog Λ o.place.blocks = true)
    (hrt : Rt.X64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.X64.Rt.rtPhTab none) = true) :
    a6 o ⟨Λ⟩ = true := by
  simp only [a6, h, hrt, Bool.and_self]

theorem a7_of_partsAt {Λ : Scc.Sem.Layout} (h : Rt.X64.rtIn o.prog (Rt.X64.RtIn.rtTab (mainGrps o.place.tail)) = true)
    (hph : Spike.Lib.X64.StubW.abortPhC Λ.code.lo Λ o.prog = true) :
    a7 o ⟨Λ⟩ = true := by
  simp only [a7, h, hph, Bool.and_self]

theorem a8_of_partsAt {Λ : Scc.Sem.Layout} (h : Rt.X64.rtWordsOk Λ o.prog o.secs = true)
    (hi : Rt.X64.rtInitOk Λ o.prog o.secs = true)
    (hc : Rt.X64.rtOffOk Λ o.prog o.secs = true) :
    a8 o ⟨Λ⟩ = true := by
  simp only [a8, h, hi, hc, Bool.and_self]

theorem a11_of_partsAt {Λ : Scc.Sem.Layout} {mc : Spike.Lib.X64.Rt.MainCode} (hs : mcOf o.place.tail = some mc)
    (h : Spike.Lib.X64.Rt.rtCodeOk o.prog mc = true)
    (hph : Rt.X64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.X64.Rt.mainPhTab mc) = true) :
    a11 o ⟨Λ⟩ = true := by
  simp only [a11, hs, h, hph, Bool.and_self]

theorem a9_of_partsAt {Λ : Scc.Sem.Layout} {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    (h : Spike.Lib.LowerX64.fnCodeOk o.prog ir = true)
    (hph : Spike.Lib.LowerX64.fnPhOk Λ.code.lo Λ o.prog ir = true) :
    a9 o ⟨Λ⟩ = true := by
  simp only [a9, hir, h, hph, Bool.and_self]

/-- A program outside the one-word fragment or over its stack need (A4) fails `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a4 {Λ : Scc.Sem.Layout} (h : a4 cfg o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- A wrong block table (A3) fails `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a3 {Λ : Scc.Sem.Layout} (h : a3 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong static offsets (A5) fail `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a5 {Λ : Scc.Sem.Layout} (h : a5 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong phases (A6: the rows' or the runtime's) fail `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a6 {Λ : Scc.Sem.Layout} (h : a6 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- A missing IR or a lowered code block not in the cells (A9) fails
`placeOKAt`. -/
theorem placeOKAt_eq_false_of_a9 {Λ : Scc.Sem.Layout} (h : a9 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong runtime code or abort path phases (A7) fail `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a7 {Λ : Scc.Sem.Layout} (h : a7 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- A wrong load (A2: the label offsets, the abort labels or the image) fails `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a2 {Λ : Scc.Sem.Layout} (h : a2 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong runtime data words (A8) fail `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a8 {Λ : Scc.Sem.Layout} (h : a8 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong runtime fixed code or `scc_rt_main`'s phases (A11), or a tail without its `MainCode` yet
(`.setup`), fails `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a11 {Λ : Scc.Sem.Layout} (h : a11 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

end Parts

/-! ## Extraction lemmas -/

section Extract

variable {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out}

private theorem a1_of (h : placeOKAt cfg Λ o = true) : a1 o ⟨Λ⟩ = true :=
  Checks.a1_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a2_of (h : placeOKAt cfg Λ o = true) : a2 o ⟨Λ⟩ = true :=
  Checks.a2_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a3_of (h : placeOKAt cfg Λ o = true) : a3 o ⟨Λ⟩ = true :=
  Checks.a3_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a4_of (h : placeOKAt cfg Λ o = true) : a4 cfg o ⟨Λ⟩ = true :=
  Checks.a4_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a5_of (h : placeOKAt cfg Λ o = true) : a5 o ⟨Λ⟩ = true :=
  Checks.a5_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a6_of' (h : placeOKAt cfg Λ o = true) : a6 o ⟨Λ⟩ = true :=
  Checks.a6_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a6_of (h : placeOKAt cfg Λ o = true) :
    Rt.X64.phasesOk Λ.code.lo o.prog Λ o.place.blocks = true := by
  have h6 := a6_of' h; simp only [a6, Bool.and_eq_true] at h6; exact h6.1

/-- **A6**: the runtime's phase facts but `scc_rt_main`'s
(`Rt.X64.factOk_of_rtPhOk` gives each back). -/
theorem rtPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.X64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.X64.Rt.rtPhTab none) = true := by
  have h6 := a6_of' h; simp only [a6, Bool.and_eq_true] at h6; exact h6.2

private theorem a7_of' (h : placeOKAt cfg Λ o = true) : a7 o ⟨Λ⟩ = true :=
  Checks.a7_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a7_of (h : placeOKAt cfg Λ o = true) :
    Rt.X64.rtIn o.prog (Rt.X64.RtIn.rtTab (mainGrps o.place.tail)) = true := by
  have h7 := a7_of' h; simp only [a7, Bool.and_eq_true] at h7; exact h7.1

/-- **A7**: the overflow abort path's phase check at A6's tables and the
code labels (`abortPhC`). -/
theorem abortPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Spike.Lib.X64.StubW.abortPhC Λ.code.lo Λ o.prog = true := by
  have h7 := a7_of' h; simp only [a7, Bool.and_eq_true] at h7; exact h7.2

private theorem a8_of' (h : placeOKAt cfg Λ o = true) : a8 o ⟨Λ⟩ = true :=
  Checks.a8_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a8_of (h : placeOKAt cfg Λ o = true) : Rt.X64.rtWordsOk Λ o.prog o.secs = true := by
  have h8 := a8_of' h; simp only [a8, Bool.and_eq_true] at h8; exact h8.1.1

/-- **A8**: no runtime word has an initial word in the load
(`Rt.X64.initVal_rt_of_rtInitOk`: each starts at `0`). -/
theorem rtInit_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.X64.rtInitOk Λ o.prog o.secs = true := by
  have h8 := a8_of' h; simp only [a8, Bool.and_eq_true] at h8; exact h8.1.2

/-- **A8**: the first TCB's words are clear of `.data` and the heap
(`Rt.X64.clear_of_rtOffOk`). -/
theorem rtOff_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.X64.rtOffOk Λ o.prog o.secs = true := by
  have h8 := a8_of' h; simp only [a8, Bool.and_eq_true] at h8; exact h8.2

private theorem a9_of (h : placeOKAt cfg Λ o = true) : a9 o ⟨Λ⟩ = true :=
  Checks.a9_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-- **A9**: the output names its IR, and the IR's lowered code blocks are
in the cells (`fnCodeOk`). -/
theorem fnCodeOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ∃ ir, o.place.ir = some ir ∧ Spike.Lib.LowerX64.fnCodeOk o.prog ir = true := by
  have h9 := a9_of h
  simp only [a9] at h9
  split at h9
  · exact ⟨_, ‹_›, (Bool.and_eq_true _ _ ▸ h9).1⟩
  · exact absurd h9 Bool.false_ne_true

/-- **A9**'s phase part: the output's IR's lowered code blocks pass the
phase check at A6's tables and the code labels (`fnPhOk`). -/
theorem fnPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Spike.Lib.LowerX64.fnPhOk Λ.code.lo Λ o.prog ir = true := by
  have h9 := a9_of h
  simp only [a9, hir, Bool.and_eq_true] at h9
  exact h9.2

/-- **A9** at a lowered code block: `func0 name r`, a function of the
output's IR returning one operand, has its emitted prologue (at some cell
sizes) and body in the cells, at its frame recomputed from the IR. -/
theorem fnCode_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} (hf : Scc.Lower.Inv.func0 name r ∈ ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    (∃ zl zf z1 z2 zs, Spike.Lib.LowerX64.proInC o.prog (Spike.Lib.LowerX64.frOf ir (Scc.Lower.Inv.func0 name r))
        name (Scc.Emit.X64.labelOf name "entry") zl zf z1 z2 zs = true) ∧
      Spike.Lib.LowerX64.bodyIn o.prog (Spike.Lib.LowerX64.frOf ir (Scc.Lower.Inv.func0 name r))
        (Scc.Emit.X64.labelOf name "entry") 0 r.insts r.ret = true := by
  obtain ⟨ir', hir', hok⟩ := fnCodeOk_of_placeOKAt h
  rw [hir] at hir'; cases hir'
  have := Spike.Lib.LowerX64.fnCodeOk_func0 hok hf hI hw
  exact ⟨this.1, this.2.1⟩

/-- **A9** at a lowered code block with an instruction: `func0 name r`, a
function of the output's IR returning one operand, has its local overflow
block (`Spike.Lib.LowerX64.ovfBlk`) at `ovfL` in the cells. -/
theorem ovfCode_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} (hf : Scc.Lower.Inv.func0 name r ∈ ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w])
    (hne : r.insts ≠ []) :
    Rt.X64.blockAtB o.prog (Spike.Lib.LowerX64.ovfL (Spike.Lib.LowerX64.frOf ir (Scc.Lower.Inv.func0 name r))) 0
      Spike.Lib.LowerX64.ovfBlk = true := by
  obtain ⟨ir', hir', hok⟩ := fnCodeOk_of_placeOKAt h
  rw [hir] at hir'; cases hir'
  exact (Spike.Lib.LowerX64.fnCodeOk_func0 hok hf hI hw).2.2 hne
private theorem a11_of (h : placeOKAt cfg Λ o = true) : a11 o ⟨Λ⟩ = true :=
  Checks.a11_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-- **A1**: the static link is well-formed. -/
theorem wf_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.WF := by
  have := a1_of h; simp only [a1, Bool.and_eq_true] at this; exact wf_of_a1 this.1.1.1

/-- **A1**: the layout facts (`PlaceOK.layoutOk`). -/
theorem layoutOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) : layoutOk o.secs Λ = true := by
  have := a1_of h; simp only [a1, Bool.and_eq_true] at this; exact this.1.1.2

/-- **A1**: the code in its region (`codeFits`). -/
theorem codeFits_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Scc.Sem.X64.codeEnd Λ.code.lo o.prog ≤ Λ.code.lo + Λ.code.size := by
  have := a1_of h; simp only [a1, codeFits, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.2

/-- **A1**: the abort labels are the runtime's (`PlaceOK.abortStd`). -/
theorem abortLbl_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.abortLbl = Link.abortName :=
  abortLbl_of_layoutOk (layoutOk_of_placeOKAt h)

/-- **A1**: `.rodata` is clear of the stack pool. -/
theorem rodata_stackPool_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Λ.rodata.Disjoint Λ.stackPool :=
  rodata_stackPool_of_layoutOk (layoutOk_of_placeOKAt h)

/-- **A1**: the heap arena, the stack pool and the pinned region at their
symbols, of the sizes the output gives them. -/
theorem regionsTied_of_placeOKAt (h : placeOKAt cfg Λ o = true) : regionsTied o.secs Λ = true :=
  regionsTied_of_layoutOk (layoutOk_of_placeOKAt h)

/-- **A1**: `.rodata` and every region end at or below `2 ^ 32`. -/
theorem below32_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32 :=
  below32_of_layoutOk (layoutOk_of_placeOKAt h)

/-- The Linux entry stack is clear of the static link (from
`below32_of_placeOKAt`). -/
theorem clear_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Entry.linux.clear Λ = true :=
  clear_of_below32 (below32_of_placeOKAt h)

/-- The stack pool lies below the Linux entry stack (from
`below32_of_placeOKAt`). -/
theorem pool_below_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Λ.stackPool.lo + Λ.stackPool.size ≤ Entry.linux.stack.lo := by
  have := below32_of_placeOKAt h Λ.stackPool (by simp [Layout.regions])
  have hlo : Entry.linux.stack.lo = 2 ^ 47 - 4096 - 65536 := rfl
  omega

/-- **A1**: `_start` is a code label at the code base: the first
instruction of the cells, where the canonical loader's thread starts. -/
theorem start_at_lo_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    codeLabel Λ.code.lo o.prog "_start" = some Λ.code.lo := by
  have := a1_of h; simp only [a1, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2

/-- **A2**: the canonical loader's checks of the link. -/
theorem loadOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    loadOk Λ o.prog o.secs o.labelOffs = true := by
  have := a2_of h; simp only [a2, Bool.and_eq_true] at this; exact this.1.1

/-- **A2**: each abort label of the link is a code label of the cells. -/
theorem abortsIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : abortsIn o.prog Λ = true := by
  have := a2_of h; simp only [a2, Bool.and_eq_true] at this; exact this.1.2

/-- **A2**: the link's image holds each data symbol's item. -/
theorem imageIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : imageIn o.prog o.secs Λ = true := by
  have := a2_of h; simp only [a2, Bool.and_eq_true] at this; exact this.2

/-- **A2**: the loaded thread's layout is valid. -/
theorem validLayout_of_placeOKAt (h : placeOKAt cfg Λ o = true) (E : Entry) :
    Kraken.Executable.ValidLayout
      (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe :=
  validLayout_of_loadOk (loadOk_of_placeOKAt h) E

/-- **A3**: the block table is at its places in the cells. -/
theorem blocksIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.X64.blocksIn o.prog (Rt.X64.toGrps o.place.blocks) := by
  have := a3_of h; simp only [a3, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1

/-- **A3**: the table covers the cells (`Rt.X64.coverOk_sound`). -/
theorem cover_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.X64.coverOk o.prog o.place.blocks = true := by
  have := a3_of h; simp only [a3, Bool.and_eq_true] at this; exact this.2

/-- **A3**: every non-label cell is the `j`-th of the run after the first
label of a group's name, and in one of the group's rows or its single
instructions (then one the block lemmas do not cover, a load or store
through a base that is not a frame register, or a stack switch); or a
single instruction of the same kinds in the run of a label without a
group. -/
theorem inRow_of_placeOKAt (h : placeOKAt cfg Λ o = true) {i : Nat} {c : Directive × Nat}
    (hi : o.prog[i]? = some c) (hc : Rt.X64.notLab c = true) :
    (∃ g ∈ o.place.blocks, ∃ t j, Rt.X64.after g.l o.prog = some t ∧ (Rt.X64.cellRun t)[j]? = some c ∧
      ((∃ b ∈ g.bs, b.k ≤ j ∧ j < b.k + b.blk.length) ∨ (j ∈ g.ev ∧ Rt.X64.evOk c.1 = true))) ∨
    Rt.X64.evOk c.1 = true :=
  Rt.X64.inRow_of_coverOk (cover_of_placeOKAt h) hi hc

/-- **A3**: the code of every row of the table, at its label plus its
byte offset, in every layout of the cells. -/
theorem codeAt_of_placeOKAt (h : placeOKAt cfg Λ o = true) {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] (hp : Rt.X64.Lays exe o.prog) {st : State} (he : st.exe = exe)
    (hend : st.endPc = Rt.X64.endOf exe o.prog) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.X64.OBlk} (hb : b ∈ g.bs) :
    Spike.Lib.X64.CodeAt st ((_root_.Executable.labels exe).label g.l + Int64.ofNat b.off) b.blk :=
  have hm := Rt.X64.mem_toGrps hg hb
  Rt.X64.codeAt_of_blocksIn hp he hend (blocksIn_of_placeOKAt h) hm.1 hm.2

/-- **A5**: every row of the table is covered at its static offsets. -/
theorem okBlk_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.X64.OBlk} (hb : b ∈ g.bs) : Spike.Lib.X64.okBlk b.lo b.hi b.o b.blk = true :=
  Rt.X64.okBlk_of_offsetsOk (a5_of h) hg hb

/-- **A5**: a row of the table named by its label (`Rt.X64.rowIn`, a
lookup) is covered at its static offsets. -/
theorem okBlk_of_rowIn_placeOKAt (h : placeOKAt cfg Λ o = true) {l : Label} {b : Rt.X64.OBlk}
    (hr : Rt.X64.rowIn o.place.blocks l b = true) : Spike.Lib.X64.okBlk b.lo b.hi b.o b.blk = true :=
  Rt.X64.okBlk_of_rowIn (a5_of h) hr

/-- **A5**: along a fall-through edge between consecutive rows of a group,
the next row's offsets are implied by those the row leaves. -/
theorem soLe_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.X64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.X64.fallsThrough b.blk = true) : Rt.X64.SO.Le b'.o (Rt.X64.soAfter b.o b.blk) :=
  Rt.X64.soLe_of_offsetsOk (a5_of h) hg hi hk hf

/-- **A5**: along a fall-through edge, the registers at the offsets the
row's abstract run leaves are at the next row's. -/
theorem sorel_next_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.X64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.X64.fallsThrough b.blk = true) {R : Spike.Lib.Region} (lab : String → Int64) (pc : Int64)
    (σ : Spike.Lib.X64.AS)
    (hr : Spike.Lib.X64.SORel R (Spike.Lib.X64.arun lab b.blk ⟨pc, b.o, σ⟩).so
      (Spike.Lib.X64.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs) :
    Spike.Lib.X64.SORel R b'.o (Spike.Lib.X64.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs :=
  Rt.X64.sorel_next_of_offsetsOk (a5_of h) hg hi hk hf lab pc σ hr

/-- **A4**: the program is in the one-word fragment. -/
theorem wideIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : WideX64.wideIn (o.prog.map (·.1)) = true := by
  have := a4_of h; simp only [a4, Bool.and_eq_true] at this; exact this.1

/-- **A4**: the program's canonical threads are `WideSt`. -/
theorem wideSt_of_placeOKAt (h : placeOKAt cfg Λ o = true) (E : Entry) (base : Nat) (syms : List (String × Nat)) :
    WideX64.WideSt (threadAt E base o.prog syms) :=
  WideX64.wideSt_threadAt (wideIn_of_placeOKAt h) E base syms

/-- **A4**: the stack need table holds on the cells, within the budget. -/
theorem needOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    NeedX64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true := by
  have := a4_of h; simp only [a4, Bool.and_eq_true] at this; exact this.2

/-- **A7**: `scc_rt_print`'s code and labels. -/
theorem printIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.X64.Print.printIn o.prog = true :=
  Rt.X64.RtIn.printIn_of_rtIn (a7_of h)

/-- **A7**: the abort stubs and `scc_rt_abort`'s code and labels. -/
theorem abortIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.X64.Abort.abortIn o.prog = true :=
  Rt.X64.RtIn.abortIn_of_rtIn (a7_of h)

/-- **A7**: the tail of `scc_rt_main`, without a setup block. -/
theorem mainIn0_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hs : o.place.tail = .bare) : mainIn0 o.prog = true := by
  have h7 := a7_of h; simp only [hs, mainGrps] at h7; exact Rt.X64.RtIn.mainIn0_of_rtIn h7

/-- **A7**: the tail of `scc_rt_main`, after a setup block. -/
theorem mainIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hs : o.place.tail = .setup) :
    Rt.X64.Abort.mainIn o.prog = true := by
  have h7 := a7_of h; simp only [hs, mainGrps] at h7; exact Rt.X64.RtIn.mainIn_of_rtIn h7

/-- **A11**: the tail of `scc_rt_main` has its `MainCode` (today: no setup
block). -/
theorem tail_of_placeOKAt (h : placeOKAt cfg Λ o = true) : o.place.tail = .bare := by
  have h11 := a11_of h; revert h11; unfold a11
  cases o.place.tail <;> simp [mcOf]

/-- **A11**: the runtime's fixed code at the tail's `MainCode`
(`Spike.Lib.X64.Rt.rtCodeIn_of_ok` gives its facts back). -/
theorem rtCodeOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) {mc : Spike.Lib.X64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) : Spike.Lib.X64.Rt.rtCodeOk o.prog mc = true := by
  have h11 := a11_of h; simp only [a11, hs, Bool.and_eq_true] at h11; exact h11.1

/-- **A11**: `scc_rt_main`'s phase facts at the tail's `MainCode`
(`Rt.X64.factOk_of_rtPhOk` gives each back). -/
theorem mainPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) {mc : Spike.Lib.X64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) :
    Rt.X64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.X64.Rt.mainPhTab mc) = true := by
  have h11 := a11_of h; simp only [a11, hs, Bool.and_eq_true] at h11; exact h11.2

/-- **A11**: the runtime's fixed code at `bareMC`. -/
theorem rtCodeOk_bare_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Spike.Lib.X64.Rt.rtCodeOk o.prog Spike.Lib.X64.Rt.bareMC = true :=
  rtCodeOk_of_placeOKAt h (by rw [tail_of_placeOKAt h]; rfl)

/-- **A8**: the runtime's data words' checks. -/
theorem rtWordsOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.X64.rtWordsOk Λ o.prog o.secs = true :=
  a8_of h

/-- **A8**: a runtime word at its label in the loaded thread
(`Rt.X64.rtA`, the address the link's symbols give it). -/
theorem lab_of_placeOKAt (h : placeOKAt cfg Λ o = true) {x : String} (hx : x ∈ Rt.X64.rtNames) (E : Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.X64.rtA Λ o.prog o.secs x :=
  Rt.X64.label_of_rtWordsOk (loadOk_of_placeOKAt h) (a8_of h) hx E

/-- **A8**: the side conditions of the runtime's words (`Rt.X64.wordsOk`;
`Rt.X64.words_small_of_wordsOk` …). -/
theorem wordsOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.X64.wordsOk Λ (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stacks") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_next")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_lock") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_free_n") = true :=
  Rt.X64.wordsOk_of_rtWordsOk (a8_of h)

/-- **A6**: the phase check of the rows (`Rt.X64.phasesOk`). -/
theorem phasesOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.X64.phasesOk Λ.code.lo o.prog Λ o.place.blocks = true :=
  a6_of h

/-- **A6**: a row of the table, not a site's `nop`, at its group's address
`a` (its label's `codeLabel`) passes its phase check with `Rt.X64.okPcOf`
and `Rt.X64.phOf`. -/
theorem rowPhOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.X64.OBlk} (hb : b ∈ g.bs) (hs : b.blk ≠ Rt.X64.siteBlk) :
    ∃ a, codeLabel Λ.code.lo o.prog g.l = some a ∧
      Rt.X64.rowPhOk (Rt.X64.okPcOf Λ.code.lo o.prog Λ) (Rt.X64.phOf Λ.code.lo o.prog) a b = true :=
  Rt.X64.rowPhOk_of_phasesOk (a6_of h) hg hb hs

/-- **A6**: a row's group label at its address in the loaded thread, with
the loader's data symbols (the layout valid by A2). -/
theorem label_of_placeOKAt (h : placeOKAt cfg Λ o = true) {E : Entry} {l : String} {a : Nat}
    (ha : codeLabel Λ.code.lo o.prog l = some a) :
    (_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label l =
      Int64.ofNat a :=
  have := validLayout_of_placeOKAt h E
  Rt.X64.label_threadAt_of_codeLabel (above_of_loadOk (loadOk_of_placeOKAt h)) ha

/-- **A6**: the sites are distinct. -/
theorem sites_nodup_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ∃ ss, Rt.X64.sitesOf Λ.code.lo o.prog Λ = some ss ∧ ss.Nodup :=
  Rt.X64.sites_nodup_of_phasesOk (a6_of h)

/-- **A8**: the runtime's words are pairwise disjoint (`Rt.X64.WordSep`, in
`Rt.X64.rtWords`' order). -/
theorem words_disj_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    (Rt.X64.rtWords (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_next") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_lock")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_free_n")).Pairwise Rt.X64.WordSep :=
  Rt.X64.words_disj_of_wordsOk (wordsOk_of_placeOKAt h)

/-- **A8**: the TCB's words (`scc_rt_pinned + 8 j`, `j < 7`) are none of
the counters (`Rt.X64.tcbSep_of_wordsOk`). -/
theorem tcbSep_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ∀ j < 7, Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j) ∉
      [Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned_next", Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_lock",
        Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_free_n", Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_next"] :=
  Rt.X64.tcbSep_of_wordsOk (wordsOk_of_placeOKAt h)

end Extract

/-! ## The immediate table

The link of `tablesOf` has no immediate table; the lowering's layout is the
link with its immediates (`{Λ with imms := i}`). No component reads them. -/

section Imms

variable (Λ : Scc.Sem.Layout) (i : CoreTerm.Expr → String → Nat → Option Nat) (cells : List (Directive × Nat))
  (secs : DataSecs) (offs : List (String × Nat))

theorem wfB_withImms : Link.wfB { Λ with imms := i } = Link.wfB Λ := rfl
theorem clear_withImms : Entry.linux.clear { Λ with imms := i } = Entry.linux.clear Λ := rfl
theorem loadOk_withImms : loadOk { Λ with imms := i } cells secs offs = loadOk Λ cells secs offs := rfl
theorem abortsIn_withImms : abortsIn cells { Λ with imms := i } = abortsIn cells Λ := rfl
theorem imageIn_withImms : imageIn cells secs { Λ with imms := i } = imageIn cells secs Λ := rfl
theorem rtA_withImms (x : String) : Rt.X64.rtA { Λ with imms := i } cells secs x = Rt.X64.rtA Λ cells secs x := rfl
theorem rtWordsOk_withImms : Rt.X64.rtWordsOk { Λ with imms := i } cells secs = Rt.X64.rtWordsOk Λ cells secs := rfl

end Imms

section ImmsAt

variable (i : CoreTerm.Expr → String → Nat → Option Nat) {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out}

/-- **A1** at the link with an immediate table. -/
theorem wf_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ({ Λ with imms := i } : Scc.Sem.Layout).WF := by
  have := wf_of_placeOKAt h; exact wf_withImms this i

/-- **A1** at the link with an immediate table: the entry stack. -/
theorem clear_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Entry.linux.clear { Λ with imms := i } = true := by
  have := clear_of_placeOKAt h
  exact (clear_withImms _ i).trans this

/-- **A1** at the link with an immediate table: `_start` at the
code base. -/
theorem start_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    let Λ : Scc.Sem.Layout := { Λ with imms := i }
    codeLabel Λ.code.lo o.prog "_start" = some Λ.code.lo :=
  start_at_lo_of_placeOKAt h

/-- **A2** at the link with an immediate table: the loader's checks. -/
theorem loadOk_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    loadOk { Λ with imms := i } o.prog o.secs o.labelOffs = true := by
  have := loadOk_of_placeOKAt h
  exact (loadOk_withImms _ i _ _ _).trans this

/-- **A2** at the link with an immediate table: the abort labels. -/
theorem abortsIn_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    abortsIn o.prog { Λ with imms := i } = true := by
  have := abortsIn_of_placeOKAt h
  exact (abortsIn_withImms _ i _).trans this

/-- **A2** at the link with an immediate table: the image. -/
theorem imageIn_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    imageIn o.prog o.secs { Λ with imms := i } = true := by
  have := imageIn_of_placeOKAt h
  exact (imageIn_withImms _ i _ _).trans this

/-- **A8** at the link with an immediate table: the runtime's
data words' checks. -/
theorem rtWordsOk_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.X64.rtWordsOk { Λ with imms := i } o.prog o.secs = true := by
  have := rtWordsOk_of_placeOKAt h
  exact (rtWordsOk_withImms _ i _ _).trans this

/-- **A8** at the link with an immediate table: a runtime word
at its label in the loaded thread. -/
theorem lab_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) {x : String} (hx : x ∈ Rt.X64.rtNames)
    (E : Entry) :
    let Λ : Scc.Sem.Layout := { Λ with imms := i }
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.X64.rtA Λ o.prog o.secs x :=
  Rt.X64.label_of_rtWordsOk (loadOk_link_of_placeOKAt i h) (rtWordsOk_link_of_placeOKAt i h) hx E

end ImmsAt

/-! ## At the static link

Each extraction lemma above at `tablesOf`'s layout: `placeOK` is `placeOKAt` there
(`placeOK_eq_placeOKAt`). -/

section AtLink

variable (i : CoreTerm.Expr → String → Nat → Option Nat) {cfg : Config} {o : Out}

/-- `rtPh_of_placeOKAt` at the static link. -/
theorem rtPh_of_placeOK (h : placeOK cfg o = true) :
    Rt.X64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.X64.Rt.rtPhTab none) = true :=
  rtPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `abortPh_of_placeOKAt` at the static link. -/
theorem abortPh_of_placeOK (h : placeOK cfg o = true) :
    Spike.Lib.X64.StubW.abortPhC (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog = true :=
  abortPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtInit_of_placeOKAt` at the static link. -/
theorem rtInit_of_placeOK (h : placeOK cfg o = true) : Rt.X64.rtInitOk (tablesOf cfg o).Λ o.prog o.secs = true :=
  rtInit_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtOff_of_placeOKAt` at the static link. -/
theorem rtOff_of_placeOK (h : placeOK cfg o = true) : Rt.X64.rtOffOk (tablesOf cfg o).Λ o.prog o.secs = true :=
  rtOff_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `fnCodeOk_of_placeOKAt` at the static link. -/
theorem fnCodeOk_of_placeOK (h : placeOK cfg o = true) :
    ∃ ir, o.place.ir = some ir ∧ Spike.Lib.LowerX64.fnCodeOk o.prog ir = true :=
  fnCodeOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `fnPh_of_placeOKAt` at the static link. -/
theorem fnPh_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Spike.Lib.LowerX64.fnPhOk (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog ir = true :=
  fnPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir

/-- `fnCode_of_placeOKAt` at the static link. -/
theorem fnCode_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} (hf : Scc.Lower.Inv.func0 name r ∈ ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    (∃ zl zf z1 z2 zs, Spike.Lib.LowerX64.proInC o.prog (Spike.Lib.LowerX64.frOf ir (Scc.Lower.Inv.func0 name r))
        name (Scc.Emit.X64.labelOf name "entry") zl zf z1 z2 zs = true) ∧
      Spike.Lib.LowerX64.bodyIn o.prog (Spike.Lib.LowerX64.frOf ir (Scc.Lower.Inv.func0 name r))
        (Scc.Emit.X64.labelOf name "entry") 0 r.insts r.ret = true :=
  fnCode_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir hf hI hw

/-- `ovfCode_of_placeOKAt` at the static link. -/
theorem ovfCode_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} (hf : Scc.Lower.Inv.func0 name r ∈ ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w])
    (hne : r.insts ≠ []) :
    Rt.X64.blockAtB o.prog (Spike.Lib.LowerX64.ovfL (Spike.Lib.LowerX64.frOf ir (Scc.Lower.Inv.func0 name r))) 0
      Spike.Lib.LowerX64.ovfBlk = true :=
  ovfCode_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir hf hI hw hne

/-- `wf_of_placeOKAt` at the static link. -/
theorem wf_of_placeOK (h : placeOK cfg o = true) : (tablesOf cfg o).Λ.WF :=
  wf_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `layoutOk_of_placeOKAt` at the static link. -/
theorem layoutOk_of_placeOK (h : placeOK cfg o = true) : layoutOk o.secs (tablesOf cfg o).Λ = true :=
  layoutOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rodata_stackPool_of_placeOKAt` at the static link. -/
theorem rodata_stackPool_of_placeOK (h : placeOK cfg o = true) :
    (tablesOf cfg o).Λ.rodata.Disjoint (tablesOf cfg o).Λ.stackPool :=
  rodata_stackPool_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `regionsTied_of_placeOKAt` at the static link. -/
theorem regionsTied_of_placeOK (h : placeOK cfg o = true) : regionsTied o.secs (tablesOf cfg o).Λ = true :=
  regionsTied_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `below32_of_placeOKAt` at the static link. -/
theorem below32_of_placeOK (h : placeOK cfg o = true) :
    ∀ r ∈ (tablesOf cfg o).Λ.rodata :: (tablesOf cfg o).Λ.regions, r.lo + r.size ≤ 2 ^ 32 :=
  below32_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `clear_of_placeOKAt` at the static link. -/
theorem clear_of_placeOK (h : placeOK cfg o = true) : Entry.linux.clear (tablesOf cfg o).Λ = true :=
  clear_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `pool_below_of_placeOKAt` at the static link. -/
theorem pool_below_of_placeOK (h : placeOK cfg o = true) :
    (tablesOf cfg o).Λ.stackPool.lo + (tablesOf cfg o).Λ.stackPool.size ≤ Entry.linux.stack.lo :=
  pool_below_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `start_at_lo_of_placeOKAt` at the static link. -/
theorem start_at_lo_of_placeOK (h : placeOK cfg o = true) :
    codeLabel (tablesOf cfg o).Λ.code.lo o.prog "_start" = some (tablesOf cfg o).Λ.code.lo :=
  start_at_lo_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `loadOk_of_placeOKAt` at the static link. -/
theorem loadOk_of_placeOK (h : placeOK cfg o = true) :
    loadOk (tablesOf cfg o).Λ o.prog o.secs o.labelOffs = true :=
  loadOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `abortsIn_of_placeOKAt` at the static link. -/
theorem abortsIn_of_placeOK (h : placeOK cfg o = true) : abortsIn o.prog (tablesOf cfg o).Λ = true :=
  abortsIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `imageIn_of_placeOKAt` at the static link. -/
theorem imageIn_of_placeOK (h : placeOK cfg o = true) : imageIn o.prog o.secs (tablesOf cfg o).Λ = true :=
  imageIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `validLayout_of_placeOKAt` at the static link. -/
theorem validLayout_of_placeOK (h : placeOK cfg o = true) (E : Entry) :
    Kraken.Executable.ValidLayout
      (threadAt E (tablesOf cfg o).Λ.code.lo o.prog (loadSyms (tablesOf cfg o).Λ o.secs.rodata)).exe :=
  validLayout_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h E

/-- `blocksIn_of_placeOKAt` at the static link. -/
theorem blocksIn_of_placeOK (h : placeOK cfg o = true) :
    Rt.X64.blocksIn o.prog (Rt.X64.toGrps o.place.blocks) :=
  blocksIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `cover_of_placeOKAt` at the static link. -/
theorem cover_of_placeOK (h : placeOK cfg o = true) : Rt.X64.coverOk o.prog o.place.blocks = true :=
  cover_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `inRow_of_placeOKAt` at the static link. -/
theorem inRow_of_placeOK (h : placeOK cfg o = true) {i : Nat} {c : Directive × Nat}
    (hi : o.prog[i]? = some c) (hc : Rt.X64.notLab c = true) :
    (∃ g ∈ o.place.blocks, ∃ t j, Rt.X64.after g.l o.prog = some t ∧ (Rt.X64.cellRun t)[j]? = some c ∧
      ((∃ b ∈ g.bs, b.k ≤ j ∧ j < b.k + b.blk.length) ∨ (j ∈ g.ev ∧ Rt.X64.evOk c.1 = true))) ∨
    Rt.X64.evOk c.1 = true :=
  inRow_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hi hc

/-- `codeAt_of_placeOKAt` at the static link. -/
theorem codeAt_of_placeOK (h : placeOK cfg o = true) {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] (hp : Rt.X64.Lays exe o.prog) {st : State} (he : st.exe = exe)
    (hend : st.endPc = Rt.X64.endOf exe o.prog) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.X64.OBlk} (hb : b ∈ g.bs) :
    Spike.Lib.X64.CodeAt st ((_root_.Executable.labels exe).label g.l + Int64.ofNat b.off) b.blk :=
  codeAt_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hp he hend hg hb

/-- `okBlk_of_placeOKAt` at the static link. -/
theorem okBlk_of_placeOK (h : placeOK cfg o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.X64.OBlk} (hb : b ∈ g.bs) : Spike.Lib.X64.okBlk b.lo b.hi b.o b.blk = true :=
  okBlk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hb

/-- `okBlk_of_rowIn_placeOKAt` at the static link. -/
theorem okBlk_of_rowIn_placeOK (h : placeOK cfg o = true) {l : Label} {b : Rt.X64.OBlk}
    (hr : Rt.X64.rowIn o.place.blocks l b = true) : Spike.Lib.X64.okBlk b.lo b.hi b.o b.blk = true :=
  okBlk_of_rowIn_placeOKAt (Λ := (tablesOf cfg o).Λ) h hr

/-- `soLe_of_placeOKAt` at the static link. -/
theorem soLe_of_placeOK (h : placeOK cfg o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.X64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.X64.fallsThrough b.blk = true) : Rt.X64.SO.Le b'.o (Rt.X64.soAfter b.o b.blk) :=
  soLe_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hi hk hf

/-- `sorel_next_of_placeOKAt` at the static link. -/
theorem sorel_next_of_placeOK (h : placeOK cfg o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.X64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.X64.fallsThrough b.blk = true) {R : Spike.Lib.Region} (lab : String → Int64) (pc : Int64)
    (σ : Spike.Lib.X64.AS)
    (hr : Spike.Lib.X64.SORel R (Spike.Lib.X64.arun lab b.blk ⟨pc, b.o, σ⟩).so
      (Spike.Lib.X64.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs) :
    Spike.Lib.X64.SORel R b'.o (Spike.Lib.X64.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs :=
  sorel_next_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hi hk hf lab pc σ hr

/-- `wideIn_of_placeOKAt` at the static link. -/
theorem wideIn_of_placeOK (h : placeOK cfg o = true) : WideX64.wideIn (o.prog.map (·.1)) = true :=
  wideIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `wideSt_of_placeOKAt` at the static link. -/
theorem wideSt_of_placeOK (h : placeOK cfg o = true) (E : Entry) (base : Nat) (syms : List (String × Nat)) :
    WideX64.WideSt (threadAt E base o.prog syms) :=
  wideSt_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h E base syms

/-- `needOk_of_placeOKAt` at the static link. -/
theorem needOk_of_placeOK (h : placeOK cfg o = true) :
    NeedX64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true :=
  needOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `printIn_of_placeOKAt` at the static link. -/
theorem printIn_of_placeOK (h : placeOK cfg o = true) : Rt.X64.Print.printIn o.prog = true :=
  printIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `abortIn_of_placeOKAt` at the static link. -/
theorem abortIn_of_placeOK (h : placeOK cfg o = true) : Rt.X64.Abort.abortIn o.prog = true :=
  abortIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `mainIn0_of_placeOKAt` at the static link. -/
theorem mainIn0_of_placeOK (h : placeOK cfg o = true) (hs : o.place.tail = .bare) : mainIn0 o.prog = true :=
  mainIn0_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `mainIn_of_placeOKAt` at the static link. -/
theorem mainIn_of_placeOK (h : placeOK cfg o = true) (hs : o.place.tail = .setup) :
    Rt.X64.Abort.mainIn o.prog = true :=
  mainIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `tail_of_placeOKAt` at the static link. -/
theorem tail_of_placeOK (h : placeOK cfg o = true) : o.place.tail = .bare :=
  tail_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtCodeOk_of_placeOKAt` at the static link. -/
theorem rtCodeOk_of_placeOK (h : placeOK cfg o = true) {mc : Spike.Lib.X64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) : Spike.Lib.X64.Rt.rtCodeOk o.prog mc = true :=
  rtCodeOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `mainPh_of_placeOKAt` at the static link. -/
theorem mainPh_of_placeOK (h : placeOK cfg o = true) {mc : Spike.Lib.X64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) :
    Rt.X64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.X64.Rt.mainPhTab mc) = true :=
  mainPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `rtCodeOk_bare_of_placeOKAt` at the static link. -/
theorem rtCodeOk_bare_of_placeOK (h : placeOK cfg o = true) :
    Spike.Lib.X64.Rt.rtCodeOk o.prog Spike.Lib.X64.Rt.bareMC = true :=
  rtCodeOk_bare_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtWordsOk_of_placeOKAt` at the static link. -/
theorem rtWordsOk_of_placeOK (h : placeOK cfg o = true) : Rt.X64.rtWordsOk (tablesOf cfg o).Λ o.prog o.secs = true :=
  rtWordsOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `lab_of_placeOKAt` at the static link. -/
theorem lab_of_placeOK (h : placeOK cfg o = true) {x : String} (hx : x ∈ Rt.X64.rtNames) (E : Entry) :
    let Λ := (tablesOf cfg o).Λ
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.X64.rtA Λ o.prog o.secs x :=
  lab_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hx E

/-- `wordsOk_of_placeOKAt` at the static link. -/
theorem wordsOk_of_placeOK (h : placeOK cfg o = true) :
    let Λ := (tablesOf cfg o).Λ
    Rt.X64.wordsOk Λ (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stacks") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_next")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_lock") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_free_n") = true :=
  wordsOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `phasesOk_of_placeOKAt` at the static link. -/
theorem phasesOk_of_placeOK (h : placeOK cfg o = true) :
    Rt.X64.phasesOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ o.place.blocks = true :=
  phasesOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rowPhOk_of_placeOKAt` at the static link. -/
theorem rowPhOk_of_placeOK (h : placeOK cfg o = true) {g : Rt.X64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.X64.OBlk} (hb : b ∈ g.bs) (hs : b.blk ≠ Rt.X64.siteBlk) :
    let Λ := (tablesOf cfg o).Λ
    ∃ a, codeLabel Λ.code.lo o.prog g.l = some a ∧
      Rt.X64.rowPhOk (Rt.X64.okPcOf Λ.code.lo o.prog Λ) (Rt.X64.phOf Λ.code.lo o.prog) a b = true :=
  rowPhOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hb hs

/-- `label_of_placeOKAt` at the static link. -/
theorem label_of_placeOK (h : placeOK cfg o = true) {E : Entry} {l : String} {a : Nat}
    (ha : codeLabel (tablesOf cfg o).Λ.code.lo o.prog l = some a) :
    let Λ := (tablesOf cfg o).Λ
    (_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label l =
      Int64.ofNat a :=
  label_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h ha

/-- `sites_nodup_of_placeOKAt` at the static link. -/
theorem sites_nodup_of_placeOK (h : placeOK cfg o = true) :
    ∃ ss, Rt.X64.sitesOf (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ = some ss ∧ ss.Nodup :=
  sites_nodup_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `words_disj_of_placeOKAt` at the static link. -/
theorem words_disj_of_placeOK (h : placeOK cfg o = true) :
    let Λ := (tablesOf cfg o).Λ
    (Rt.X64.rtWords (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_next") (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_lock")
      (Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_free_n")).Pairwise Rt.X64.WordSep :=
  words_disj_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `tcbSep_of_placeOKAt` at the static link. -/
theorem tcbSep_of_placeOK (h : placeOK cfg o = true) :
    let Λ := (tablesOf cfg o).Λ
    ∀ j < 7, Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j) ∉
      [Rt.X64.rtA Λ o.prog o.secs "scc_rt_pinned_next", Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_lock",
        Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_free_n", Rt.X64.rtA Λ o.prog o.secs "scc_rt_stack_next"] :=
  tcbSep_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `wf_link_of_placeOKAt` at the static link. -/
theorem wf_link_of_placeOK (h : placeOK cfg o = true) :
    ({ (tablesOf cfg o).Λ with imms := i } : Scc.Sem.Layout).WF :=
  wf_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `clear_link_of_placeOKAt` at the static link. -/
theorem clear_link_of_placeOK (h : placeOK cfg o = true) :
    Entry.linux.clear { (tablesOf cfg o).Λ with imms := i } = true :=
  clear_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `start_link_of_placeOKAt` at the static link. -/
theorem start_link_of_placeOK (h : placeOK cfg o = true) :
    let Λ : Scc.Sem.Layout := { (tablesOf cfg o).Λ with imms := i }
    codeLabel Λ.code.lo o.prog "_start" = some Λ.code.lo :=
  start_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `loadOk_link_of_placeOKAt` at the static link. -/
theorem loadOk_link_of_placeOK (h : placeOK cfg o = true) :
    loadOk { (tablesOf cfg o).Λ with imms := i } o.prog o.secs o.labelOffs = true :=
  loadOk_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `abortsIn_link_of_placeOKAt` at the static link. -/
theorem abortsIn_link_of_placeOK (h : placeOK cfg o = true) :
    abortsIn o.prog { (tablesOf cfg o).Λ with imms := i } = true :=
  abortsIn_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `imageIn_link_of_placeOKAt` at the static link. -/
theorem imageIn_link_of_placeOK (h : placeOK cfg o = true) :
    imageIn o.prog o.secs { (tablesOf cfg o).Λ with imms := i } = true :=
  imageIn_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `rtWordsOk_link_of_placeOKAt` at the static link. -/
theorem rtWordsOk_link_of_placeOK (h : placeOK cfg o = true) :
    Rt.X64.rtWordsOk { (tablesOf cfg o).Λ with imms := i } o.prog o.secs = true :=
  rtWordsOk_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `lab_link_of_placeOKAt` at the static link. -/
theorem lab_link_of_placeOK (h : placeOK cfg o = true) {x : String} (hx : x ∈ Rt.X64.rtNames)
    (E : Entry) :
    let Λ : Scc.Sem.Layout := { (tablesOf cfg o).Λ with imms := i }
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.X64.rtA Λ o.prog o.secs x :=
  lab_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h hx E

/-- `codeFits_of_placeOKAt` at the static link. -/
theorem codeFits_of_placeOK (h : placeOK cfg o = true) :
    Scc.Sem.X64.codeEnd (tablesOf cfg o).Λ.code.lo o.prog ≤ (tablesOf cfg o).Λ.code.lo + (tablesOf cfg o).Λ.code.size :=
  codeFits_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `abortLbl_of_placeOKAt` at the static link (`rfl` there). -/
theorem abortLbl_of_placeOK (h : placeOK cfg o = true) : (tablesOf cfg o).Λ.abortLbl = Link.abortName :=
  abortLbl_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

end AtLink

end Scc.Cert.PlaceOK.X64
