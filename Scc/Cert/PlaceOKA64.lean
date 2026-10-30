import Scc.Cert.PlaceOK
import Scc.Cert.LinkA64
import Scc.Cert.Rt.CodeA64
import Scc.Cert.Rt.OffsA64
import Scc.Cert.Rt.CoverA64
import Scc.Cert.Rt.WideA64
import Scc.Cert.Rt.A64Abort
import Scc.Cert.Rt.A64RtIn
import Scc.Cert.NeedA64
import Scc.Cert.Ph1A64
import Scc.Cert.Rt.RtWordsA64
import Scc.Cert.Rt.PhasesA64
import Spike.Lib.Rt.A64CodeIn
import Spike.Lib.LowerA64.Checks
import Spike.Lib.LowerA64.PhCheck
import Spike.Lib.A64AbortPh
import Spike.Lib.A64TailPh
import Scc.Cert.Rt.RtInitA64
import Spike.Lib.Rt.A64RtPhTab
import Spike.Lib.Rt.A64CodeInSetup

/-!
# `PlaceOK` on AArch64

The AArch64 instance of the per-program placement check
(`Scc/Cert/PlaceOK.lean`): the output's types, its tables and the ten
components, each with its extraction lemma from `PlaceOK` to the `Prop` the
proofs use.

* **The output** `Out`: the parsed program (`Program`, the directive list
  the canonical loader reads, `Scc.Sem.A64.textProgram`), its data sections,
  and the placement data `PlaceData`: the block table (`scc --blocks`), the
  stack need table (`Scc.Lower.stackNeed`) and the shape of `scc_rt_main`'s
  tail.
* **The tables** `tablesOf cfg o`: the static link of the program at the
  configuration's bases, its code labels resolved in the program
  (`Link.A64.codeOf`); at `Config.canonical` it is `Link.A64.linkOf`
  (`tablesOf_canonical`). The link has no immediate table (`Layout.imms`):
  no component reads it (`loadOk_withImms` …).
* **The components**:
  - A1 the static link well-formed (`Link.wfB`; `wf_of_placeOK`), its
    layout facts (`PlaceOK.layoutOk`: `.rodata` clear of the stack pool,
    the regions of their own at their symbols and sizes, everything below
    `2 ^ 32`; `layoutOk_of_placeOK`, `below32_of_placeOK` …), and `_start`
    the first code label, at the code base (`start_at_lo_of_placeOK`);
  - A2 the canonical loader's checks, the abort labels in the program and
    the image (`Link.A64.loadOk`, `abortsIn`, `imageIn`;
    `validLayout_of_placeOK`, `load_of_placeOK`);
  - A3 the block table at its places (`Rt.A64.blocksIn` on the rows'
    table `Rt.A64.toGrps`; `codeAt_of_placeOK`), and covering the program:
    every instruction in the run after a label, each run tiled by its
    label's rows and single instructions (`Rt.A64.coverOk`;
    `cover_of_placeOK`, `inRow_of_placeOK`);
  - A4 the one-word fragment and the stack need (`WideA64.wideIn`,
    `NeedA64.needOk`; `wideSt_of_placeOK`, `needOk_of_placeOK`);
  - A7 (in part) the runtime's code: `scc_rt_main`'s tail by
    `PlaceData.tail`, `scc_rt_alloc`, `scc_rt_print`, the abort stubs and
    `scc_rt_abort`, in one pass over the program (`Rt.A64.rtIn` on
    `RtIn.rtTab`; `allocIn_of_placeOK`, `printIn_of_placeOK`,
    `abortIn_of_placeOK`, `mainIn0_of_placeOK`, `mainIn_of_placeOK`);
  - A5 the static offsets of the block table: every row covered at its
    offsets, the offsets agreeing along the fall-through edges
    (`Rt.A64.offsetsOk`; `okBlk_of_placeOK`, `soLe_of_placeOK`,
    `sorel_next_of_placeOK`);
  - A8 the runtime's data words: each a data symbol of the link at its
    label, below `2 ^ 32`, 8-aligned, clear of the stack pool, in `.data`
    or the pinned region; the pool and
    the first stack in place, the words pairwise disjoint
    (`Rt.A64.rtWordsOk`; `lab_of_placeOK`, `wordsOk_of_placeOK` and their
    `_link` forms, `words_disj_of_placeOK`, `tcbSep_of_placeOK`); none
    with an initial word in the load (`Rt.A64.rtInitOk`;
    `rtInit_of_placeOK`); the first TCB's words clear of `.data` and
    the heap (`Rt.A64.rtOffOk`; `rtOff_of_placeOK`);
  - A6 the phases: every row of the block table off the marks' sites and
    in its entry's phase, every instruction covered, the phase table and
    the sites resolved in the program, the sites distinct and the
    runtime's pinned pcs in their phases (`Rt.A64.phasesOk`;
    `rowPhOk_of_placeOK`, `label_of_placeOK`, `sites_nodup_of_placeOK`,
    `pin_of_placeOK`);
  - A9 the lowered code blocks' code: every `func0`-shaped function of the
    lowered IR (`PlaceData.ir`, no IR failing) has its emitted prologue and
    body at its entry label, its context recomputed from the IR
    (`Spike.Lib.LowerA64.fnCodeOk`; `fnCodeOk_of_placeOK`,
    `fnCode_of_placeOK`). Functions of other shapes (the runtime's, those
    with several blocks or other instructions) are not checked by it;
  - A11 the runtime's fixed code: `_start`, `scc_rt_start`, `scc_rt_main` at
    the tail's `MainCode` (`mcOf`), `scc_rt_alloc_tcb`, `scc_rt_thread_init`
    and `scc_rt_stack_take`, in one pass over the program
    (`Spike.Lib.A64.Rt.rtCodeOk`; `rtCodeOk_of_placeOK`). On a `.setup`
    tail, the same with `scc_rt_main` after a setup block
    (`Spike.Lib.A64.Rt.setupOk`: two calls, the setup words marshalled);
  - A12 the code of every user function: every stack-checked function of
    the IR, of any shape, has its prologue with its parameters' spills, a
    frame within one immediate, each block's emitted code at its label, the
    overflow block when it has a checked `+`, and its calls' and tail calls'
    frames within the stack need's rows (`Scc.Cert.Code1A64.fnCode1Ok`;
    `fnCode1_of_placeOKAt`); and their phase facts at A6's tables and the
    code labels: the prologue's, every label-free run of every block's,
    the overflow block's (`Scc.Cert.Ph1A64.fnPh1Ok`; `fnPh1_of_placeOKAt`).
-/

namespace Scc.Cert.PlaceOK.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link.A64

/-- The shape of `scc_rt_main`'s tail (`Abort.mainIn0`/`mainIn`): without a
setup block (`.sp0`), or after one (`.sp1`). -/
inductive MainShape where
  | bare
  | setup
  deriving DecidableEq, Repr

/-- **The AArch64 placement data**: the block table with its static offsets
(`scc --blocks`: the `block_spec` blocks per label with their regions and
entry offsets, `Rt.A64.OGrp`; `Rt.A64.toGrps` is the table), the stack need
table (`NeedA64.Row`: label, frame, need), and the shape of `scc_rt_main`'s
tail. -/
structure PlaceData where
  blocks : List Rt.A64.OGrp
  need : List NeedA64.Row
  tail : MainShape
  /-- The lowered IR the program was emitted from (A9). -/
  ir : Option Scc.IR.Program := none

/-- **scc's AArch64 output**. -/
abbrev Out := PlaceOK.Out Program PlaceData

/-- **The AArch64 tables**: the ISA-generic ones (the static link). -/
abbrev Tables := PlaceOK.Tables

/-- **The tables of an output**: the static link at the configuration's
bases, code labels resolved in the program at the code base. -/
def tablesOf (cfg : Config) (o : Out) : Tables :=
  linkTables cfg o.secs (codeOf cfg.bases.codeLo o.prog)

/-- At the canonical configuration the link is `Link.A64.linkOf`. -/
theorem tablesOf_canonical (o : Out) : (tablesOf Config.canonical o).Λ = linkOf o.prog o.secs := rfl

/-! ## The components -/

/-- **A2**: the canonical loader's checks of the link, its abort labels in
the program, its image. -/
def a2 (o : Out) (t : Tables) : Bool :=
  loadOk t.Λ o.prog o.secs && abortsIn o.prog t.Λ && imageIn o.prog o.secs t.Λ

/-- **A3**: every block of the table is code at its label and offset, and
every instruction of the program is in a row or a single instruction of the
table. -/
def a3 (o : Out) (_ : Tables) : Bool :=
  decide (Rt.A64.blocksIn o.prog (Rt.A64.toGrps o.place.blocks)) && Rt.A64.coverOk o.prog o.place.blocks

/-- **A5**: every row of the block table covered at its static offsets, and
the offsets agreeing along the fall-through edges. -/
def a5 (o : Out) (_ : Tables) : Bool :=
  Rt.A64.offsetsOk o.place.blocks

/-- **A4**: the one-word fragment; the stack need table on the program,
within the budget at the thread entries. -/
def a4 (cfg : Config) (o : Out) (_ : Tables) : Bool :=
  WideA64.wideIn o.prog && NeedA64.needOk o.prog o.place.need cfg.needBudget cfg.entries

/-- The groups of `scc_rt_main`'s tail in the shape the placement data
names (`RtIn.mainGrps0`/`mainGrps1`). -/
def mainGrps : MainShape → List Rt.A64.RGrp
  | .bare => Rt.A64.RtIn.mainGrps0
  | .setup => Rt.A64.RtIn.mainGrps1

/-- **A7** (the runtime's part): the tail of `scc_rt_main`, `scc_rt_alloc`,
`scc_rt_print` (its write block led by `dmb ish`), the abort stubs and
`scc_rt_abort`, checked in one pass over the program, and the overflow abort path's phase facts at A6's tables and the
code labels (`abortPhC`), and the same for `scc_rt_print`'s write tail, the
write/heap stubs and `scc_rt_alloc`, so none of their pcs is a thread site
(`tailOffC`). -/
def a7 (o : Out) (t : Tables) : Bool :=
  Rt.A64.rtIn o.prog (Rt.A64.RtIn.rtTab (mainGrps o.place.tail)) &&
    Spike.Lib.A64.StubW.abortPhC t.Λ.code.lo t.Λ o.prog &&
    Spike.Lib.A64.StubW.tailOffC t.Λ.code.lo t.Λ o.prog

/-- **A6**: every row of the block table in its entry's phase, off the
sites, and the runtime's phase facts but `scc_rt_main`'s (`rtPhOk` at
`rtPhTab none`). -/
def a6 (o : Out) (t : Tables) : Bool :=
  Rt.A64.phasesOk t.Λ.code.lo o.prog t.Λ o.place.blocks &&
    Rt.A64.rtPhOk t.Λ.code.lo o.prog t.Λ (Spike.Lib.A64.Rt.rtPhTab none)

/-- **The code in its region**: the program laid out from the code base
ends within the layout's code region (`Scc.Sem.A64.codeEnd`), so that nothing the
layout places after the code region overlaps it. -/
def codeFits (o : Out) (Λ : Scc.Sem.Layout) : Bool :=
  decide (Scc.Sem.A64.codeEnd Λ.code.lo o.prog ≤ Λ.code.lo + Λ.code.size)

/-- **A1**: the static link well-formed (`PlaceOK.a1`), its layout facts
(`PlaceOK.layoutOk`, independent of the entry state), the code in its
region (`codeFits`), and `_start` at the
code base (the loader's entry pc is `Λ.code.lo`, so the entry is
`_start`). -/
def a1 (o : Out) (t : Tables) : Bool :=
  PlaceOK.a1 t && layoutOk o.secs t.Λ && codeFits o t.Λ &&
    decide (codeOf t.Λ.code.lo o.prog "_start" = some t.Λ.code.lo)

/-- **The heap arena's symbols and size**: `scc_rt_heap` a data symbol of
the link at the arena's base and `scc_rt_heap_use` (the allocator's
counter) a data symbol at its address in the link's symbols (`heapUseOf`)
(`Rt.A64.symLab`: no code label of the name, no other address for it), the arena holding the allocator's cells
(`heapSizeOk`), and the static data below the arena (`dataBelowHeap`). -/
def heapOk (o : Out) (Λ : Scc.Sem.Layout) : Bool :=
  decide (Rt.A64.symLab Λ.code.lo o.prog (loadSyms Λ o.secs.rodata) Link.heapSym = some Λ.heap.lo) &&
    decide (Rt.A64.symLab Λ.code.lo o.prog (loadSyms Λ o.secs.rodata) heapUseSym = some (heapUseOf Λ)) &&
    heapSizeOk Λ && dataBelowHeap Λ

/-- **A8**: the runtime's data words in the link, none of them with an
initial word in the load (`rtInitOk`), the first TCB's words clear of
`.data` and the heap (`rtOffOk`); the heap arena's symbols and size
(`heapOk`). -/
def a8 (o : Out) (t : Tables) : Bool :=
  Rt.A64.rtWordsOk t.Λ o.prog o.secs && Rt.A64.rtInitOk t.Λ o.prog o.secs && Rt.A64.rtOffOk t.Λ o.prog o.secs &&
    heapOk o t.Λ

/-- **A9** (the lowered code blocks' part, `fnCodeOk`): the prologue and
body of every `func0`-shaped function of the IR the output names, at its
context recomputed from the IR, and their phase facts at A6's tables and
the code labels (`fnPhOk`); no IR fails. -/
def a9 (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => Spike.Lib.LowerA64.fnCodeOk o.prog ir && Spike.Lib.LowerA64.fnPhOk t.Λ.code.lo t.Λ o.prog ir
  | none => false

/-- `scc_rt_main`'s facts (`Spike.Lib.A64.Rt.MainCode`) from the placement
data's shape of its tail: today's emitter writes one `scc_rt_main` without a
setup block (`bareMC`: frame 48, the result at 8, `wc_main`); after a setup
block `scc_rt_main` calls twice, which `MainCode` does not describe (`none`;
A11 checks that shape by `Spike.Lib.A64.Rt.setupOk`). -/
def mcOf : MainShape → Option Spike.Lib.A64.Rt.MainCode
  | .bare => some Spike.Lib.A64.Rt.bareMC
  | .setup => none

/-- **A11**: the runtime's fixed code (`_start`, `scc_rt_start`,
`scc_rt_main` at `mcOf`, `scc_rt_alloc_tcb`, `scc_rt_thread_init`,
`scc_rt_stack_take`) checked in one pass over the program
(`Spike.Lib.A64.Rt.rtCodeOk`). The runtime's local labels are fixed: the
emitter numbers them by function index, and the runtime's functions come
first. With it, `scc_rt_main`'s phase facts at `mcOf` (`rtPhOk` at
`mainPhTab`). On a `.setup` tail, the same with `scc_rt_main` after a setup
block (`Spike.Lib.A64.Rt.setupOk`: `rtCodeOkS` and `mainPhTabS` at
`setupMC sw` for some `sw`). -/
def a11 (o : Out) (t : Tables) : Bool :=
  match mcOf o.place.tail with
  | some mc =>
    Spike.Lib.A64.Rt.rtCodeOk o.prog mc && Rt.A64.rtPhOk t.Λ.code.lo o.prog t.Λ (Spike.Lib.A64.Rt.mainPhTab mc)
  | none => Spike.Lib.A64.Rt.setupOk o.prog t.Λ.code.lo t.Λ

/-- **A12**: the code of every stack-checked function of the IR the output
names (`Scc.Cert.Code1A64.fnCode1Ok`, at the stack need's rows), whatever
its shape, and its phase facts at A6's tables and the code labels
(`Scc.Cert.Ph1A64.fnPh1Ok`); no IR fails. -/
def a12 (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => Scc.Cert.Code1A64.fnCode1Ok o.prog o.place.need ir && Scc.Cert.Ph1A64.fnPh1Ok t.Λ.code.lo t.Λ o.prog ir
  | none => false

/-- **The eleven components** on AArch64. -/
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
  a12 := a12

/-- **`PlaceOK` on AArch64.** -/
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

/-! ## Extraction lemmas -/

section Extract

variable {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out}

private theorem a1_of (h : placeOKAt cfg Λ o = true) : a1 o ⟨Λ⟩ = true :=
  Checks.a1_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-- **A1**: the static link is well-formed. -/
theorem wf_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.WF := by
  have := a1_of h; simp only [a1, Bool.and_eq_true] at this; exact wf_of_a1 this.1.1.1

/-- **A1**: the layout facts (`PlaceOK.layoutOk`). -/
theorem layoutOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) : layoutOk o.secs Λ = true := by
  have := a1_of h; simp only [a1, Bool.and_eq_true] at this; exact this.1.1.2

/-- **A1**: the code in its region (`codeFits`). -/
theorem codeFits_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Scc.Sem.A64.codeEnd Λ.code.lo o.prog ≤ Λ.code.lo + Λ.code.size := by
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
instruction of the program, where the canonical loader's thread starts. -/
theorem start_at_lo_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    codeOf Λ.code.lo o.prog "_start" = some Λ.code.lo := by
  have := a1_of h; simp only [a1, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2

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
    Rt.A64.phasesOk Λ.code.lo o.prog Λ o.place.blocks = true := by
  have h6 := a6_of' h; simp only [a6, Bool.and_eq_true] at h6; exact h6.1

/-- **A6**: the runtime's phase facts but `scc_rt_main`'s
(`Rt.A64.factOk_of_rtPhOk` gives each back). -/
theorem rtPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.A64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.A64.Rt.rtPhTab none) = true := by
  have h6 := a6_of' h; simp only [a6, Bool.and_eq_true] at h6; exact h6.2

private theorem a7_of' (h : placeOKAt cfg Λ o = true) : a7 o ⟨Λ⟩ = true :=
  Checks.a7_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a7_of (h : placeOKAt cfg Λ o = true) :
    Rt.A64.rtIn o.prog (Rt.A64.RtIn.rtTab (mainGrps o.place.tail)) = true := by
  have h7 := a7_of' h; simp only [a7, Bool.and_eq_true] at h7; exact h7.1.1

/-- **A7**: the overflow abort path's phase check at A6's tables and the
code labels (`abortPhC`). -/
theorem abortPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Spike.Lib.A64.StubW.abortPhC Λ.code.lo Λ o.prog = true := by
  have h7 := a7_of' h; simp only [a7, Bool.and_eq_true] at h7; exact h7.1.2

/-- **A7**: the phase check of `scc_rt_print`'s write tail, the write/heap
stubs and `scc_rt_alloc` at A6's tables and the code labels (`tailOffC`). -/
theorem tailOff_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Spike.Lib.A64.StubW.tailOffC Λ.code.lo Λ o.prog = true := by
  have h7 := a7_of' h; simp only [a7, Bool.and_eq_true] at h7; exact h7.2

private theorem a8_of' (h : placeOKAt cfg Λ o = true) : a8 o ⟨Λ⟩ = true :=
  Checks.a8_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a8_of (h : placeOKAt cfg Λ o = true) : Rt.A64.rtWordsOk Λ o.prog o.secs = true := by
  have h8 := a8_of' h; simp only [a8, Bool.and_eq_true] at h8; exact h8.1.1.1

/-- **A8**: no runtime word has an initial word in the load
(`Rt.A64.initVal_rt_of_rtInitOk`: each starts at `0`). -/
theorem rtInit_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.A64.rtInitOk Λ o.prog o.secs = true := by
  have h8 := a8_of' h; simp only [a8, Bool.and_eq_true] at h8; exact h8.1.1.2

/-- **A8**: the first TCB's words are clear of `.data` and the heap
(`Rt.A64.clear_of_rtOffOk`). -/
theorem rtOff_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.A64.rtOffOk Λ o.prog o.secs = true := by
  have h8 := a8_of' h; simp only [a8, Bool.and_eq_true] at h8; exact h8.1.2

/-- **A8**: the heap arena's symbols and size (`heapOk`). -/
theorem heapOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) : heapOk o Λ = true := by
  have h8 := a8_of' h; simp only [a8, Bool.and_eq_true] at h8; exact h8.2

private theorem a9_of (h : placeOKAt cfg Λ o = true) : a9 o ⟨Λ⟩ = true :=
  Checks.a9_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-- **A9**: the output names its IR, and the IR's lowered code blocks are
in the program (`fnCodeOk`). -/
theorem fnCodeOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ∃ ir, o.place.ir = some ir ∧ Spike.Lib.LowerA64.fnCodeOk o.prog ir = true := by
  have h9 := a9_of h
  simp only [a9] at h9
  split at h9
  · exact ⟨_, ‹_›, (Bool.and_eq_true _ _ ▸ h9).1⟩
  · exact absurd h9 Bool.false_ne_true

/-- **A9**'s phase part: the output's IR's lowered code blocks pass the
phase check at A6's tables and the code labels (`fnPhOk`). -/
theorem fnPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Spike.Lib.LowerA64.fnPhOk Λ.code.lo Λ o.prog ir = true := by
  have h9 := a9_of h
  simp only [a9, hir, Bool.and_eq_true] at h9
  exact h9.2

/-- **A9** at a lowered code block: `func0 name r`, the `fi`th function of
the output's IR, has its emitted prologue and body in the program, at its
context recomputed from the IR. -/
theorem fnCode_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {fi : Nat}
    (hf : (Scc.Lower.Inv.func0 name r, fi) ∈ ir.funcs.zipIdx)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    let c := Scc.Emit.A64.fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir Scc.Emit.A64.argRegs.length) fi
      (Scc.Lower.Inv.func0 name r)
    Spike.Lib.LowerA64.proInC o.prog c name (c.prefix ++ "0_entry") = true ∧
      Spike.Lib.LowerA64.bodyIn o.prog c (c.prefix ++ "0_entry") 0 r.insts r.ret = true := by
  obtain ⟨ir', hir', hok⟩ := fnCodeOk_of_placeOKAt h
  rw [hir] at hir'; cases hir'
  have := Spike.Lib.LowerA64.fnCodeOk_func0 hok hf hI hw
  exact ⟨this.1, this.2.1⟩

/-- **A9** at a lowered code block with an instruction: `func0 name r`, the
`fi`th function of the output's IR, has its local overflow block
(`Spike.Lib.LowerA64.ovfBlk`) at `abort_overflow` in the program. -/
theorem ovfCode_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {fi : Nat}
    (hf : (Scc.Lower.Inv.func0 name r, fi) ∈ ir.funcs.zipIdx)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w])
    (hne : r.insts ≠ []) :
    let c := Scc.Emit.A64.fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir Scc.Emit.A64.argRegs.length) fi
      (Scc.Lower.Inv.func0 name r)
    Rt.A64.blockAt o.prog (c.local "abort_overflow") 0 Spike.Lib.LowerA64.ovfBlk = true := by
  obtain ⟨ir', hir', hok⟩ := fnCodeOk_of_placeOKAt h
  rw [hir] at hir'; cases hir'
  exact (Spike.Lib.LowerA64.fnCodeOk_func0 hok hf hI hw).2.2 hne

private theorem a11_of (h : placeOKAt cfg Λ o = true) : a11 o ⟨Λ⟩ = true :=
  Checks.a11_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

private theorem a12_of (h : placeOKAt cfg Λ o = true) : a12 o ⟨Λ⟩ = true :=
  Checks.a12_of_ok (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h

/-- **A12**: the output's IR's stack-checked functions have their code in
the program, at the stack need's rows (`Scc.Cert.Code1A64.fnCode1Ok`; per
function `fnOk1_of_fnCode1Ok`, `fnOk1_facts`). -/
theorem fnCode1_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Scc.Cert.Code1A64.fnCode1Ok o.prog o.place.need ir = true := by
  have h12 := a12_of h
  simp only [a12, hir, Bool.and_eq_true] at h12
  exact h12.1

/-- **A12**'s phase part: the output's IR's stack-checked functions pass the
phase check at A6's tables and the code labels (`Scc.Cert.Ph1A64.fnPh1Ok`;
`fnPh1Ok_parts`, `fnPhF_of_fnPhAll1`, `fnPhF_facts`, `blocksPh_block`). -/
theorem fnPh1_of_placeOKAt (h : placeOKAt cfg Λ o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Scc.Cert.Ph1A64.fnPh1Ok Λ.code.lo Λ o.prog ir = true := by
  have h12 := a12_of h
  simp only [a12, hir, Bool.and_eq_true] at h12
  exact h12.2

/-- **A2**: the canonical loader's checks of the link. -/
theorem loadOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) : loadOk Λ o.prog o.secs = true := by
  have := a2_of h; simp only [a2, Bool.and_eq_true] at this; exact this.1.1

/-- **A2**: each abort label of the link is a code label of the program. -/
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

/-- **A3**: the block table is at its places in the program. -/
theorem blocksIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.A64.blocksIn o.prog (Rt.A64.toGrps o.place.blocks) := by
  have := a3_of h; simp only [a3, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1

/-- **A3**: the table covers the program (`Rt.A64.coverOk_sound`). -/
theorem cover_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.A64.coverOk o.prog o.place.blocks = true := by
  have := a3_of h; simp only [a3, Bool.and_eq_true] at this; exact this.2

/-- **A3**: every instruction of the program is the `j`-th of the run after
the first label of a group's name, and in one of the group's rows or its
single instructions (then one the block lemmas do not cover, or a stack
switch). -/
theorem inRow_of_placeOKAt (h : placeOKAt cfg Λ o = true) {i : Nat} {x : Instr} (hi : o.prog[i]? = some (.instr x)) :
    ∃ g ∈ o.place.blocks, ∃ t j, Rt.A64.after g.l o.prog = some t ∧ (Rt.A64.insRun t)[j]? = some (.instr x) ∧
      ((∃ b ∈ g.bs, b.k ≤ j ∧ j < b.k + b.blk.length) ∨ (j ∈ g.ev ∧ Rt.A64.evOk (.instr x) = true)) :=
  Rt.A64.inRow_of_coverOk (cover_of_placeOKAt h) hi

/-- **A3**: the code of every row of the table, at its label plus four
bytes per instruction before it, in every layout of the program. -/
theorem codeAt_of_placeOKAt (h : placeOKAt cfg Λ o = true) {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] (hp : Rt.A64.Lays exe o.prog) {st : State} (he : st.exe = exe)
    (hend : st.endPc = Rt.A64.endOf exe o.prog) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.A64.OBlk} (hb : b ∈ g.bs) :
    CodeAt st ((_root_.Executable.labels exe).label g.l + Int64.ofNat (4 * b.k)) b.blk :=
  have hm := Rt.A64.mem_toGrps hg hb
  Rt.A64.codeAt_of_blocksIn hp he hend (blocksIn_of_placeOKAt h) hm.1 hm.2

/-- **A5**: every row of the table is covered at its static offsets. -/
theorem okBlk_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.A64.OBlk} (hb : b ∈ g.bs) : Flow.okBlk b.lo b.hi b.o b.blk = true :=
  Rt.A64.okBlk_of_offsetsOk (a5_of h) hg hb

/-- **A5**: a row of the table named by its label (`Rt.A64.rowIn`, a
lookup) is covered at its static offsets. -/
theorem okBlk_of_rowIn_placeOKAt (h : placeOKAt cfg Λ o = true) {l : Label} {b : Rt.A64.OBlk}
    (hr : Rt.A64.rowIn o.place.blocks l b = true) : Flow.okBlk b.lo b.hi b.o b.blk = true :=
  Rt.A64.okBlk_of_rowIn (a5_of h) hr

/-- **A5**: along a fall-through edge between consecutive rows of a group,
the next row's offsets are implied by those the row leaves. -/
theorem soLe_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.A64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.A64.fallsThrough b.blk = true) : Rt.A64.SO.Le b'.o (Rt.A64.soAfter b.o b.blk) :=
  Rt.A64.soLe_of_offsetsOk (a5_of h) hg hi hk hf

/-- **A5**: along a fall-through edge, the registers at the offsets the
row's abstract run leaves are at the next row's. -/
theorem sorel_next_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.A64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.A64.fallsThrough b.blk = true) {R : Spike.Lib.Region} (lab : Label → Int64) (pc : Int64)
    (σ : Flow.AS) (hr : Flow.SORel R (Flow.arun lab b.blk ⟨pc, b.o, σ⟩).so (Flow.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs) :
    Flow.SORel R b'.o (Flow.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs :=
  Rt.A64.sorel_next_of_offsetsOk (a5_of h) hg hi hk hf lab pc σ hr


/-- **A4**: the program is in the one-word fragment. -/
theorem wideIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : WideA64.wideIn o.prog = true := by
  have := a4_of h; simp only [a4, Bool.and_eq_true] at this; exact this.1

/-- **A4**: the program's canonical threads are `WideSt`. -/
theorem wideSt_of_placeOKAt (h : placeOKAt cfg Λ o = true) (E : Entry) (base : Nat) (syms : List (String × Nat)) :
    WideA64.WideSt (threadAt E base o.prog syms) :=
  WideA64.wideSt_threadAt (wideIn_of_placeOKAt h) E base syms

/-- **A4**: the stack need table holds on the program, within the budget. -/
theorem needOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    NeedA64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true := by
  have := a4_of h; simp only [a4, Bool.and_eq_true] at this; exact this.2

/-- **A7**: `scc_rt_alloc`'s code and labels (`seg_alloc_ofW`'s code
premise). -/
theorem allocIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Spike.Lib.A64.Flow.allocIn o.prog = true :=
  Rt.A64.RtIn.allocIn_of_rtIn (a7_of h)

/-- **A7**: `scc_rt_print`'s code and labels. -/
theorem printIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.A64.Print.printIn o.prog = true :=
  Rt.A64.RtIn.printIn_of_rtIn (a7_of h)

/-- **A7**: the abort stubs and `scc_rt_abort`'s code and labels. -/
theorem abortIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.A64.Abort.abortIn o.prog = true :=
  Rt.A64.RtIn.abortIn_of_rtIn (a7_of h)

/-- **A7**: the tail of `scc_rt_main`, without a setup block. -/
theorem mainIn0_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hs : o.place.tail = .bare) :
    Rt.A64.Abort.mainIn0 o.prog = true := by
  have h7 := a7_of h; simp only [hs, mainGrps] at h7; exact Rt.A64.RtIn.mainIn0_of_rtIn h7

/-- **A7**: the tail of `scc_rt_main`, after a setup block. -/
theorem mainIn_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hs : o.place.tail = .setup) :
    Rt.A64.Abort.mainIn o.prog = true := by
  have h7 := a7_of h; simp only [hs, mainGrps] at h7; exact Rt.A64.RtIn.mainIn_of_rtIn h7

/-- **A11 at a `.setup` tail**: `scc_rt_main`'s code and phase facts after
a setup block (`Spike.Lib.A64.Rt.setupOk`). -/
theorem setupOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hs : o.place.tail = .setup) :
    Spike.Lib.A64.Rt.setupOk o.prog Λ.code.lo Λ = true := by
  have h11 := a11_of h; simp only [a11, hs, mcOf] at h11; exact h11

/-- **A11**: the runtime's fixed code at the tail's `MainCode`
(`Spike.Lib.A64.Rt.rtCodeIn_of_ok` gives its facts back). -/
theorem rtCodeOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) {mc : Spike.Lib.A64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) : Spike.Lib.A64.Rt.rtCodeOk o.prog mc = true := by
  have h11 := a11_of h; simp only [a11, hs, Bool.and_eq_true] at h11; exact h11.1

/-- **A11**: `scc_rt_main`'s phase facts at the tail's `MainCode`
(`Rt.A64.factOk_of_rtPhOk` gives each back). -/
theorem mainPh_of_placeOKAt (h : placeOKAt cfg Λ o = true) {mc : Spike.Lib.A64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) :
    Rt.A64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.A64.Rt.mainPhTab mc) = true := by
  have h11 := a11_of h; simp only [a11, hs, Bool.and_eq_true] at h11; exact h11.2

/-- **A11**: the runtime's fixed code at `bareMC`, on a bare tail. -/
theorem rtCodeOk_bare_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hs : o.place.tail = .bare) :
    Spike.Lib.A64.Rt.rtCodeOk o.prog Spike.Lib.A64.Rt.bareMC = true :=
  rtCodeOk_of_placeOKAt h (by rw [hs]; rfl)

/-- **A8**: the runtime's data words' checks. -/
theorem rtWordsOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Rt.A64.rtWordsOk Λ o.prog o.secs = true :=
  a8_of h

/-- **A8**: a runtime word at its label in the loaded thread
(`Rt.A64.rtA`, the address the link's symbols give it). -/
theorem lab_of_placeOKAt (h : placeOKAt cfg Λ o = true) {x : String} (hx : x ∈ Rt.A64.rtNames) (E : Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.A64.rtA Λ o.prog o.secs x :=
  Rt.A64.label_of_rtWordsOk (loadOk_of_placeOKAt h) (a8_of h) hx E

/-- **A8**: `scc_rt_heap` labels the heap arena's base in the loaded
thread. -/
theorem heapLab_of_placeOKAt (h : placeOKAt cfg Λ o = true) (E : Entry) :
    (_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label Link.heapSym =
      Int64.ofNat Λ.heap.lo := by
  have hh := heapOk_of_placeOKAt h
  simp only [heapOk, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact Rt.A64.label_threadAt_of_symLab (symsAround_of_loadOk (loadOk_of_placeOKAt h)) hh.1.1.1

/-- **A8**: `scc_rt_heap`'s label as a number is the heap arena's base
(the allocator's `Call.OK.heap` at `heap := Λ.heap.lo`). -/
theorem heapLab_toNat_of_placeOKAt (h : placeOKAt cfg Λ o = true) (E : Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      Link.heapSym).toBitVec.toNat = Λ.heap.lo := by
  rw [heapLab_of_placeOKAt h E]
  have hb := below32_of_placeOKAt h Λ.heap (by simp [Layout.regions])
  have e : (Int64.ofNat Λ.heap.lo).toBitVec = BitVec.ofNat 64 Λ.heap.lo := by simp
  rw [e, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- **A8**: `scc_rt_heap_use` labels the allocator's counter at its
address in the link's symbols (`heapUseOf`) in the loaded thread (the
allocator's `Call.OK.ctr` at `ctr := heapUseOf Λ`). -/
theorem heapUseLab_of_placeOKAt (h : placeOKAt cfg Λ o = true) (E : Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      heapUseSym).toBitVec = BitVec.ofNat 64 (heapUseOf Λ) := by
  have hh := heapOk_of_placeOKAt h
  simp only [heapOk, Bool.and_eq_true, decide_eq_true_eq] at hh
  rw [Rt.A64.label_threadAt_of_symLab (symsAround_of_loadOk (loadOk_of_placeOKAt h)) hh.1.1.2]
  simp

/-- **A8**: the heap arena holds the allocator's cells. -/
theorem heapSize_of_placeOKAt (h : placeOKAt cfg Λ o = true) : 16 * allocCells ≤ Λ.heap.size := by
  have hh := heapOk_of_placeOKAt h
  simp only [heapOk, Bool.and_eq_true] at hh
  exact heapSize_of_heapSizeOk hh.1.2

/-- **A8**: the static data below the heap arena. -/
theorem dataBelow_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.data.lo + Λ.data.size ≤ Λ.heap.lo := by
  have hh := heapOk_of_placeOKAt h
  simp only [heapOk, Bool.and_eq_true] at hh
  exact dataBelow_of_dataBelowHeap hh.2

/-- **A1**: the allocator's room above the arena's base (`Call.OK.room`
at `heap := Λ.heap.lo`). -/
theorem heapRoom_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.heap.lo + 2 ^ 46 ≤ 2 ^ 64 := by
  have hb := below32_of_placeOKAt h Λ.heap (by simp [Layout.regions])
  omega

/-- The allocator's limit as `scc_rt_alloc` loads it: `movz x10, #(allocCells >> 16), lsl #16`. -/
def allocCellsDir : Directive :=
  .instr ⟨.W64, .MOVZ (.low (.reg .X10) .W64) (.int64 (Int64.ofNat (allocCells >>> 16))) .LSL16⟩

/-- **`allocCells` is the allocator's limit** (A7): both compares of `scc_rt_alloc`'s code that
`allocIn_of_placeOKAt` places (`.1_cnt`'s `b4`, `.2_slow`'s `b6`) load `allocCellsDir`, a `movz`
whose shifted immediate is exactly `allocCells`. Changing either the runtime's literal or
`allocCells` alone breaks this by `rfl`. -/
theorem allocCells_eq_lit : Spike.Lib.A64.Alloc.b4[6]? = some allocCellsDir ∧
    Spike.Lib.A64.Alloc.b6[1]? = some allocCellsDir ∧
    allocCells >>> 16 < 2 ^ 16 ∧ (allocCells >>> 16) <<< 16 = allocCells :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- **A8**: the side conditions of the runtime's words (`Rt.A64.wordsOk`;
`Rt.A64.words_small_of_wordsOk` …). -/
theorem wordsOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.A64.wordsOk Λ (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stacks") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_next")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_lock") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_free_n") = true :=
  Rt.A64.wordsOk_of_rtWordsOk (a8_of h)

/-- **A6**: the phase check of the rows (`Rt.A64.phasesOk`). -/
theorem phasesOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Rt.A64.phasesOk Λ.code.lo o.prog Λ o.place.blocks = true :=
  a6_of h

/-- **A6**: a row of the table at its group's address `a` (its label's
`codeOf`) passes its phase check with `Rt.A64.okPcOf` and `Rt.A64.phOf`. -/
theorem rowPhOk_of_placeOKAt (h : placeOKAt cfg Λ o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.A64.OBlk} (hb : b ∈ g.bs) :
    ∃ a, codeOf Λ.code.lo o.prog g.l = some a ∧
      Rt.A64.rowPhOk (Rt.A64.okPcOf Λ.code.lo o.prog Λ) (Rt.A64.phOf Λ.code.lo o.prog) a b = true :=
  Rt.A64.rowPhOk_of_phasesOk (a6_of h) hg hb

/-- **A6**: a row's group label at its address in the loaded thread, for
any data symbols none of those below the code named like a code label
(`Link.A64.noClash`'s first half; none below the code at all:
`below_none_of_above`). -/
theorem label_of_placeOKAt {E : Entry} {syms : List (String × Nat)} {l : String} {a : Nat}
    (hs : ∀ p ∈ symsBelow Λ.code.lo syms, codeOf Λ.code.lo o.prog p.1 = none)
    (ha : codeOf Λ.code.lo o.prog l = some a) :
    (_root_.Executable.labels (threadAt E Λ.code.lo o.prog syms).exe).label l = Int64.ofNat a :=
  Rt.A64.label_threadAt_of_codeOf_below (fun p hp hl => by
    have := hs p hp; rw [hl, ha] at this; cases this) ha

/-- Data symbols none below the code satisfy `label_of_placeOKAt`'s premise
(the static link's, say). -/
theorem below_none_of_above {lo : Nat} {prog : Program} {syms : List (String × Nat)}
    (hs : ∀ p ∈ syms, lo ≤ p.2) : ∀ p ∈ symsBelow lo syms, codeOf lo prog p.1 = none := by
  rw [Scc.Cert.PlaceSyms.symsBelow_of_above hs]; simp

/-- **A6**: the sites are distinct (`Rt.A64.marksOkT`). -/
theorem sites_nodup_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ∃ ss, Rt.A64.sitesOf Λ.code.lo o.prog Λ = some ss ∧ ss.Nodup :=
  Rt.A64.sites_nodup_of_phasesOk (a6_of h)

/-- **A6**: a pin of the runtime (`Rt.A64.phPins`: a label, `k`
instructions after it, a phase index) resolves, and its pc is in its
phase. -/
theorem pin_of_placeOKAt (h : placeOKAt cfg Λ o = true) {l : String} {k v : Nat} (hp : (l, k, v) ∈ Rt.A64.phPins) :
    let lo := Λ.code.lo
    ∃ a, codeOf lo o.prog l = some a ∧ Rt.A64.phOf lo o.prog ((a + 4 * k) % 2 ^ 64) = v :=
  Rt.A64.pin_of_phasesOk (a6_of h) hp

/-- **A8**: the runtime's words are pairwise disjoint (`Rt.A64.WordSep`, in
`Rt.A64.rtWords`' order). -/
theorem words_disj_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    (Rt.A64.rtWords (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_next") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_lock")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_free_n")).Pairwise Rt.A64.WordSep :=
  Rt.A64.words_disj_of_wordsOk (wordsOk_of_placeOKAt h)

/-- **A8**: the TCB's words (`scc_rt_pinned + 8 j`, `j < 7`) are none of
the counters (`Rt.A64.tcbSep_of_wordsOk`). -/
theorem tcbSep_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ∀ j < 7, Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j) ∉
      [Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned_next", Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_lock",
        Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_free_n", Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_next"] :=
  Rt.A64.tcbSep_of_wordsOk (wordsOk_of_placeOKAt h)

end Extract

/-! ## The immediate table

The link of `tablesOf` has no immediate table; the lowering's layout is the
link with its immediates (`{Λ with imms := i}`). No component reads them. -/

section Imms

variable (Λ : Scc.Sem.Layout) (i : CoreTerm.Expr → String → Nat → Option Nat) (prog : Program) (secs : DataSecs)

theorem clear_withImms : Entry.linux.clear { Λ with imms := i } = Entry.linux.clear Λ := rfl
theorem wfB_withImms : Link.wfB { Λ with imms := i } = Link.wfB Λ := rfl
theorem loadOk_withImms : loadOk { Λ with imms := i } prog secs = loadOk Λ prog secs := rfl
theorem abortsIn_withImms : abortsIn prog { Λ with imms := i } = abortsIn prog Λ := rfl
theorem imageIn_withImms : imageIn prog secs { Λ with imms := i } = imageIn prog secs Λ := rfl
theorem rtA_withImms (x : String) : Rt.A64.rtA { Λ with imms := i } prog secs x = Rt.A64.rtA Λ prog secs x := rfl
theorem rtWordsOk_withImms : Rt.A64.rtWordsOk { Λ with imms := i } prog secs = Rt.A64.rtWordsOk Λ prog secs := rfl

end Imms

section ImmsAt

variable (i : CoreTerm.Expr → String → Nat → Option Nat) {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out}

/-- **A1** at the link with an immediate table. -/
theorem wf_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    ({ Λ with imms := i } : Scc.Sem.Layout).WF := by
  have := wf_of_placeOKAt h; exact wf_withImms this i

/-- **A1** at the link with an immediate table: the entry stack clear of it. -/
theorem clear_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    Entry.linux.clear { Λ with imms := i } = true := by
  have := clear_of_placeOKAt h
  exact (clear_withImms _ i).trans this

/-- **A1** at the link with an immediate table: `_start` at the
code base. -/
theorem start_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    let Λ : Scc.Sem.Layout := { Λ with imms := i }
    codeOf Λ.code.lo o.prog "_start" = some Λ.code.lo :=
  start_at_lo_of_placeOKAt h

/-- **A2** at the link with an immediate table: the loader's checks. -/
theorem loadOk_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) :
    loadOk { Λ with imms := i } o.prog o.secs = true := by
  have := loadOk_of_placeOKAt h
  exact (loadOk_withImms _ i _ _).trans this

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
    Rt.A64.rtWordsOk { Λ with imms := i } o.prog o.secs = true := by
  have := rtWordsOk_of_placeOKAt h
  exact (rtWordsOk_withImms _ i _ _).trans this

/-- **A8** at the link with an immediate table: a runtime word
at its label in the loaded thread. -/
theorem lab_link_of_placeOKAt (h : placeOKAt cfg Λ o = true) {x : String} (hx : x ∈ Rt.A64.rtNames)
    (E : Entry) :
    let Λ : Scc.Sem.Layout := { Λ with imms := i }
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.A64.rtA Λ o.prog o.secs x :=
  Rt.A64.label_of_rtWordsOk (loadOk_link_of_placeOKAt i h) (rtWordsOk_link_of_placeOKAt i h) hx E

end ImmsAt

/-! ## At the static link

Each extraction lemma above at `tablesOf`'s layout: `placeOK` is `placeOKAt` there
(`placeOK_eq_placeOKAt`). -/

section AtLink

variable (i : CoreTerm.Expr → String → Nat → Option Nat) {cfg : Config} {o : Out}

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
    codeOf (tablesOf cfg o).Λ.code.lo o.prog "_start" = some (tablesOf cfg o).Λ.code.lo :=
  start_at_lo_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtPh_of_placeOKAt` at the static link. -/
theorem rtPh_of_placeOK (h : placeOK cfg o = true) :
    Rt.A64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.A64.Rt.rtPhTab none) = true :=
  rtPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `abortPh_of_placeOKAt` at the static link. -/
theorem abortPh_of_placeOK (h : placeOK cfg o = true) :
    Spike.Lib.A64.StubW.abortPhC (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog = true :=
  abortPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `tailOff_of_placeOKAt` at the static link. -/
theorem tailOff_of_placeOK (h : placeOK cfg o = true) :
    Spike.Lib.A64.StubW.tailOffC (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog = true :=
  tailOff_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtInit_of_placeOKAt` at the static link. -/
theorem rtInit_of_placeOK (h : placeOK cfg o = true) : Rt.A64.rtInitOk (tablesOf cfg o).Λ o.prog o.secs = true :=
  rtInit_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rtOff_of_placeOKAt` at the static link. -/
theorem rtOff_of_placeOK (h : placeOK cfg o = true) : Rt.A64.rtOffOk (tablesOf cfg o).Λ o.prog o.secs = true :=
  rtOff_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `fnCodeOk_of_placeOKAt` at the static link. -/
theorem fnCodeOk_of_placeOK (h : placeOK cfg o = true) :
    ∃ ir, o.place.ir = some ir ∧ Spike.Lib.LowerA64.fnCodeOk o.prog ir = true :=
  fnCodeOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `fnPh_of_placeOKAt` at the static link. -/
theorem fnPh_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Spike.Lib.LowerA64.fnPhOk (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog ir = true :=
  fnPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir

/-- `fnCode1_of_placeOKAt` at the static link. -/
theorem fnCode1_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Scc.Cert.Code1A64.fnCode1Ok o.prog o.place.need ir = true :=
  fnCode1_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir

/-- `fnPh1_of_placeOKAt` at the static link. -/
theorem fnPh1_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir) :
    Scc.Cert.Ph1A64.fnPh1Ok (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog ir = true :=
  fnPh1_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir

/-- `fnCode_of_placeOKAt` at the static link. -/
theorem fnCode_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {fi : Nat}
    (hf : (Scc.Lower.Inv.func0 name r, fi) ∈ ir.funcs.zipIdx)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    let c := Scc.Emit.A64.fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir Scc.Emit.A64.argRegs.length) fi
      (Scc.Lower.Inv.func0 name r)
    Spike.Lib.LowerA64.proInC o.prog c name (c.prefix ++ "0_entry") = true ∧
      Spike.Lib.LowerA64.bodyIn o.prog c (c.prefix ++ "0_entry") 0 r.insts r.ret = true :=
  fnCode_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir hf hI hw

/-- `ovfCode_of_placeOKAt` at the static link. -/
theorem ovfCode_of_placeOK (h : placeOK cfg o = true) {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {fi : Nat}
    (hf : (Scc.Lower.Inv.func0 name r, fi) ∈ ir.funcs.zipIdx)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w])
    (hne : r.insts ≠ []) :
    let c := Scc.Emit.A64.fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir Scc.Emit.A64.argRegs.length) fi
      (Scc.Lower.Inv.func0 name r)
    Rt.A64.blockAt o.prog (c.local "abort_overflow") 0 Spike.Lib.LowerA64.ovfBlk = true :=
  ovfCode_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hir hf hI hw hne

/-- `loadOk_of_placeOKAt` at the static link. -/
theorem loadOk_of_placeOK (h : placeOK cfg o = true) : loadOk (tablesOf cfg o).Λ o.prog o.secs = true :=
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
    Rt.A64.blocksIn o.prog (Rt.A64.toGrps o.place.blocks) :=
  blocksIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `cover_of_placeOKAt` at the static link. -/
theorem cover_of_placeOK (h : placeOK cfg o = true) : Rt.A64.coverOk o.prog o.place.blocks = true :=
  cover_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `inRow_of_placeOKAt` at the static link. -/
theorem inRow_of_placeOK (h : placeOK cfg o = true) {i : Nat} {x : Instr} (hi : o.prog[i]? = some (.instr x)) :
    ∃ g ∈ o.place.blocks, ∃ t j, Rt.A64.after g.l o.prog = some t ∧ (Rt.A64.insRun t)[j]? = some (.instr x) ∧
      ((∃ b ∈ g.bs, b.k ≤ j ∧ j < b.k + b.blk.length) ∨ (j ∈ g.ev ∧ Rt.A64.evOk (.instr x) = true)) :=
  inRow_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hi

/-- `codeAt_of_placeOKAt` at the static link. -/
theorem codeAt_of_placeOK (h : placeOK cfg o = true) {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] (hp : Rt.A64.Lays exe o.prog) {st : State} (he : st.exe = exe)
    (hend : st.endPc = Rt.A64.endOf exe o.prog) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.A64.OBlk} (hb : b ∈ g.bs) :
    CodeAt st ((_root_.Executable.labels exe).label g.l + Int64.ofNat (4 * b.k)) b.blk :=
  codeAt_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hp he hend hg hb

/-- `okBlk_of_placeOKAt` at the static link. -/
theorem okBlk_of_placeOK (h : placeOK cfg o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.A64.OBlk} (hb : b ∈ g.bs) : Flow.okBlk b.lo b.hi b.o b.blk = true :=
  okBlk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hb

/-- `okBlk_of_rowIn_placeOKAt` at the static link. -/
theorem okBlk_of_rowIn_placeOK (h : placeOK cfg o = true) {l : Label} {b : Rt.A64.OBlk}
    (hr : Rt.A64.rowIn o.place.blocks l b = true) : Flow.okBlk b.lo b.hi b.o b.blk = true :=
  okBlk_of_rowIn_placeOKAt (Λ := (tablesOf cfg o).Λ) h hr

/-- `soLe_of_placeOKAt` at the static link. -/
theorem soLe_of_placeOK (h : placeOK cfg o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.A64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.A64.fallsThrough b.blk = true) : Rt.A64.SO.Le b'.o (Rt.A64.soAfter b.o b.blk) :=
  soLe_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hi hk hf

/-- `sorel_next_of_placeOKAt` at the static link. -/
theorem sorel_next_of_placeOK (h : placeOK cfg o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b b' : Rt.A64.OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length)
    (hf : Rt.A64.fallsThrough b.blk = true) {R : Spike.Lib.Region} (lab : Label → Int64) (pc : Int64)
    (σ : Flow.AS) (hr : Flow.SORel R (Flow.arun lab b.blk ⟨pc, b.o, σ⟩).so (Flow.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs) :
    Flow.SORel R b'.o (Flow.arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs :=
  sorel_next_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hi hk hf lab pc σ hr

/-- `wideIn_of_placeOKAt` at the static link. -/
theorem wideIn_of_placeOK (h : placeOK cfg o = true) : WideA64.wideIn o.prog = true :=
  wideIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `wideSt_of_placeOKAt` at the static link. -/
theorem wideSt_of_placeOK (h : placeOK cfg o = true) (E : Entry) (base : Nat) (syms : List (String × Nat)) :
    WideA64.WideSt (threadAt E base o.prog syms) :=
  wideSt_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h E base syms

/-- `needOk_of_placeOKAt` at the static link. -/
theorem needOk_of_placeOK (h : placeOK cfg o = true) :
    NeedA64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true :=
  needOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `allocIn_of_placeOKAt` at the static link. -/
theorem allocIn_of_placeOK (h : placeOK cfg o = true) : Spike.Lib.A64.Flow.allocIn o.prog = true :=
  allocIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `printIn_of_placeOKAt` at the static link. -/
theorem printIn_of_placeOK (h : placeOK cfg o = true) : Rt.A64.Print.printIn o.prog = true :=
  printIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `abortIn_of_placeOKAt` at the static link. -/
theorem abortIn_of_placeOK (h : placeOK cfg o = true) : Rt.A64.Abort.abortIn o.prog = true :=
  abortIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `mainIn0_of_placeOKAt` at the static link. -/
theorem mainIn0_of_placeOK (h : placeOK cfg o = true) (hs : o.place.tail = .bare) :
    Rt.A64.Abort.mainIn0 o.prog = true :=
  mainIn0_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `mainIn_of_placeOKAt` at the static link. -/
theorem mainIn_of_placeOK (h : placeOK cfg o = true) (hs : o.place.tail = .setup) :
    Rt.A64.Abort.mainIn o.prog = true :=
  mainIn_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `setupOk_of_placeOKAt` at the static link. -/
theorem setupOk_of_placeOK (h : placeOK cfg o = true) (hs : o.place.tail = .setup) :
    Spike.Lib.A64.Rt.setupOk o.prog (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ = true :=
  setupOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `rtCodeOk_of_placeOKAt` at the static link. -/
theorem rtCodeOk_of_placeOK (h : placeOK cfg o = true) {mc : Spike.Lib.A64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) : Spike.Lib.A64.Rt.rtCodeOk o.prog mc = true :=
  rtCodeOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `mainPh_of_placeOKAt` at the static link. -/
theorem mainPh_of_placeOK (h : placeOK cfg o = true) {mc : Spike.Lib.A64.Rt.MainCode}
    (hs : mcOf o.place.tail = some mc) :
    Rt.A64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.A64.Rt.mainPhTab mc) = true :=
  mainPh_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `rtCodeOk_bare_of_placeOKAt` at the static link. -/
theorem rtCodeOk_bare_of_placeOK (h : placeOK cfg o = true) (hs : o.place.tail = .bare) :
    Spike.Lib.A64.Rt.rtCodeOk o.prog Spike.Lib.A64.Rt.bareMC = true :=
  rtCodeOk_bare_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hs

/-- `rtWordsOk_of_placeOKAt` at the static link. -/
theorem rtWordsOk_of_placeOK (h : placeOK cfg o = true) : Rt.A64.rtWordsOk (tablesOf cfg o).Λ o.prog o.secs = true :=
  rtWordsOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `lab_of_placeOKAt` at the static link. -/
theorem lab_of_placeOK (h : placeOK cfg o = true) {x : String} (hx : x ∈ Rt.A64.rtNames) (E : Entry) :
    let Λ := (tablesOf cfg o).Λ
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.A64.rtA Λ o.prog o.secs x :=
  lab_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hx E

/-- `wordsOk_of_placeOKAt` at the static link. -/
theorem wordsOk_of_placeOK (h : placeOK cfg o = true) :
    let Λ := (tablesOf cfg o).Λ
    Rt.A64.wordsOk Λ (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stacks") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_next")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_lock") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_free_n") = true :=
  wordsOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `phasesOk_of_placeOKAt` at the static link. -/
theorem phasesOk_of_placeOK (h : placeOK cfg o = true) :
    Rt.A64.phasesOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ o.place.blocks = true :=
  phasesOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `rowPhOk_of_placeOKAt` at the static link. -/
theorem rowPhOk_of_placeOK (h : placeOK cfg o = true) {g : Rt.A64.OGrp} (hg : g ∈ o.place.blocks)
    {b : Rt.A64.OBlk} (hb : b ∈ g.bs) :
    let Λ := (tablesOf cfg o).Λ
    ∃ a, codeOf Λ.code.lo o.prog g.l = some a ∧
      Rt.A64.rowPhOk (Rt.A64.okPcOf Λ.code.lo o.prog Λ) (Rt.A64.phOf Λ.code.lo o.prog) a b = true :=
  rowPhOk_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hg hb

/-- `label_of_placeOKAt` at the static link. -/
theorem label_of_placeOK {E : Entry} {syms : List (String × Nat)} {l : String} {a : Nat}
    (hs : ∀ p ∈ symsBelow (tablesOf cfg o).Λ.code.lo syms, codeOf (tablesOf cfg o).Λ.code.lo o.prog p.1 = none)
    (ha : codeOf (tablesOf cfg o).Λ.code.lo o.prog l = some a) :
    (_root_.Executable.labels (threadAt E (tablesOf cfg o).Λ.code.lo o.prog syms).exe).label l = Int64.ofNat a :=
  label_of_placeOKAt (Λ := (tablesOf cfg o).Λ) hs ha

/-- `sites_nodup_of_placeOKAt` at the static link. -/
theorem sites_nodup_of_placeOK (h : placeOK cfg o = true) :
    ∃ ss, Rt.A64.sitesOf (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ = some ss ∧ ss.Nodup :=
  sites_nodup_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `pin_of_placeOKAt` at the static link. -/
theorem pin_of_placeOK (h : placeOK cfg o = true) {l : String} {k v : Nat} (hp : (l, k, v) ∈ Rt.A64.phPins) :
    let lo := (tablesOf cfg o).Λ.code.lo
    ∃ a, codeOf lo o.prog l = some a ∧ Rt.A64.phOf lo o.prog ((a + 4 * k) % 2 ^ 64) = v :=
  pin_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h hp

/-- `words_disj_of_placeOKAt` at the static link. -/
theorem words_disj_of_placeOK (h : placeOK cfg o = true) :
    let Λ := (tablesOf cfg o).Λ
    (Rt.A64.rtWords (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned_next")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_next") (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_lock")
      (Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_free_n")).Pairwise Rt.A64.WordSep :=
  words_disj_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `tcbSep_of_placeOKAt` at the static link. -/
theorem tcbSep_of_placeOK (h : placeOK cfg o = true) :
    let Λ := (tablesOf cfg o).Λ
    ∀ j < 7, Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * j) ∉
      [Rt.A64.rtA Λ o.prog o.secs "scc_rt_pinned_next", Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_lock",
        Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_free_n", Rt.A64.rtA Λ o.prog o.secs "scc_rt_stack_next"] :=
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
    codeOf Λ.code.lo o.prog "_start" = some Λ.code.lo :=
  start_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `loadOk_link_of_placeOKAt` at the static link. -/
theorem loadOk_link_of_placeOK (h : placeOK cfg o = true) :
    loadOk { (tablesOf cfg o).Λ with imms := i } o.prog o.secs = true :=
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
    Rt.A64.rtWordsOk { (tablesOf cfg o).Λ with imms := i } o.prog o.secs = true :=
  rtWordsOk_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h

/-- `lab_link_of_placeOKAt` at the static link. -/
theorem lab_link_of_placeOK (h : placeOK cfg o = true) {x : String} (hx : x ∈ Rt.A64.rtNames)
    (E : Entry) :
    let Λ : Scc.Sem.Layout := { (tablesOf cfg o).Λ with imms := i }
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label x).toBitVec =
      Rt.A64.rtA Λ o.prog o.secs x :=
  lab_link_of_placeOKAt (Λ := (tablesOf cfg o).Λ) i h hx E

/-- `codeFits_of_placeOKAt` at the static link. -/
theorem codeFits_of_placeOK (h : placeOK cfg o = true) :
    Scc.Sem.A64.codeEnd (tablesOf cfg o).Λ.code.lo o.prog ≤ (tablesOf cfg o).Λ.code.lo + (tablesOf cfg o).Λ.code.size :=
  codeFits_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

/-- `abortLbl_of_placeOKAt` at the static link (`rfl` there). -/
theorem abortLbl_of_placeOK (h : placeOK cfg o = true) : (tablesOf cfg o).Λ.abortLbl = Link.abortName :=
  abortLbl_of_placeOKAt (Λ := (tablesOf cfg o).Λ) h

end AtLink

/-! ## `PlaceOK` from its parts

A certificate decides each part below in its own declaration (or file:
the kernel's cost of one decision grows with the terms it shares), and
`placeOK_of` combines them without another decision. -/

section Parts

variable {cfg : Config} {o : Out}

theorem a1_of_parts (h1 : PlaceOK.a1 (tablesOf cfg o) = true)
    (h2 : layoutOk o.secs (tablesOf cfg o).Λ = true)
    (hc : codeFits o (tablesOf cfg o).Λ = true)
    (h3 : codeOf (tablesOf cfg o).Λ.code.lo o.prog "_start" = some (tablesOf cfg o).Λ.code.lo) :
    a1 o (tablesOf cfg o) = true := by
  simp only [a1, h1, h2, hc, h3, decide_true, Bool.and_self]

theorem a2_of_parts (h1 : loadOk (tablesOf cfg o).Λ o.prog o.secs = true)
    (h2 : abortsIn o.prog (tablesOf cfg o).Λ = true) (h3 : imageIn o.prog o.secs (tablesOf cfg o).Λ = true) :
    a2 o (tablesOf cfg o) = true := by
  simp only [a2, h1, h2, h3, Bool.and_self]

theorem a3_of_parts (h1 : decide (Rt.A64.blocksIn o.prog (Rt.A64.toGrps o.place.blocks)) = true)
    (h2 : Rt.A64.coverOk o.prog o.place.blocks = true) : a3 o (tablesOf cfg o) = true := by
  simp only [a3, h1, h2, Bool.and_self]

theorem a4_of_parts (h1 : WideA64.wideIn o.prog = true)
    (h2 : NeedA64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true) :
    a4 cfg o (tablesOf cfg o) = true := by
  simp only [a4, h1, h2, Bool.and_self]

theorem a5_of_parts (h : Rt.A64.offsetsOk o.place.blocks = true) : a5 o (tablesOf cfg o) = true := h

theorem a6_of_parts
    (h : Rt.A64.phasesOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ o.place.blocks = true)
    (hrt : Rt.A64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.A64.Rt.rtPhTab none) = true) :
    a6 o (tablesOf cfg o) = true := by
  simp only [a6, h, hrt, Bool.and_self]

theorem a7_of_parts (h : Rt.A64.rtIn o.prog (Rt.A64.RtIn.rtTab (mainGrps o.place.tail)) = true)
    (hph : Spike.Lib.A64.StubW.abortPhC (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog = true)
    (htl : Spike.Lib.A64.StubW.tailOffC (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog = true) :
    a7 o (tablesOf cfg o) = true := by
  simp only [a7, h, hph, htl, Bool.and_self]

theorem a8_of_parts (h : Rt.A64.rtWordsOk (tablesOf cfg o).Λ o.prog o.secs = true)
    (hi : Rt.A64.rtInitOk (tablesOf cfg o).Λ o.prog o.secs = true)
    (hc : Rt.A64.rtOffOk (tablesOf cfg o).Λ o.prog o.secs = true) (hh : heapOk o (tablesOf cfg o).Λ = true) :
    a8 o (tablesOf cfg o) = true := by
  simp only [a8, h, hi, hc, hh, Bool.and_self]

theorem a9_of_parts {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    (h : Spike.Lib.LowerA64.fnCodeOk o.prog ir = true)
    (hph : Spike.Lib.LowerA64.fnPhOk (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog ir = true) :
    a9 o (tablesOf cfg o) = true := by
  simp only [a9, hir, h, hph, Bool.and_self]

theorem a11_of_parts {mc : Spike.Lib.A64.Rt.MainCode} (hs : mcOf o.place.tail = some mc)
    (h : Spike.Lib.A64.Rt.rtCodeOk o.prog mc = true)
    (hph : Rt.A64.rtPhOk (tablesOf cfg o).Λ.code.lo o.prog (tablesOf cfg o).Λ (Spike.Lib.A64.Rt.mainPhTab mc) = true) :
    a11 o (tablesOf cfg o) = true := by
  simp only [a11, hs, h, hph, Bool.and_self]

theorem a12_of_parts {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    (h : Scc.Cert.Code1A64.fnCode1Ok o.prog o.place.need ir = true)
    (hph : Scc.Cert.Ph1A64.fnPh1Ok (tablesOf cfg o).Λ.code.lo (tablesOf cfg o).Λ o.prog ir = true) :
    a12 o (tablesOf cfg o) = true := by
  simp only [a12, hir, h, hph, Bool.and_self]

/-- **`PlaceOK` from its components.** -/
theorem placeOK_of (h1 : a1 o (tablesOf cfg o) = true) (h2 : a2 o (tablesOf cfg o) = true)
    (h3 : a3 o (tablesOf cfg o) = true) (h4 : a4 cfg o (tablesOf cfg o) = true)
    (h5 : a5 o (tablesOf cfg o) = true) (h6 : a6 o (tablesOf cfg o) = true)
    (h7 : a7 o (tablesOf cfg o) = true) (h8 : a8 o (tablesOf cfg o) = true)
    (h9 : a9 o (tablesOf cfg o) = true) (h11 : a11 o (tablesOf cfg o) = true)
    (h12 : a12 o (tablesOf cfg o) = true) : placeOK cfg o = true :=
  Checks.ok_of (C := checks cfg) h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12

/-- A wrong static link (A1: not well-formed, the entry stack not clear of it, or `_start` not at the code
base) fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a1 (h : a1 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- A wrong load (A2: the loader's checks, the abort labels or the image) fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a2 (h : a2 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
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

/-- A missing IR or a lowered code block not in the program (A9) fails
`PlaceOK`. -/
theorem placeOK_eq_false_of_a9 (h : a9 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong runtime code or abort path phases (A7) fail `PlaceOK`. -/
theorem placeOK_eq_false_of_a7 (h : a7 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong runtime data words (A8) fail `PlaceOK`. -/
theorem placeOK_eq_false_of_a8 (h : a8 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- Wrong runtime fixed code or `scc_rt_main`'s phases (A11) fail `PlaceOK`. -/
theorem placeOK_eq_false_of_a11 (h : a11 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- A user function's code not in the program, or a call over its stack need
row (A12), fails `PlaceOK`. -/
theorem placeOK_eq_false_of_a12 (h : a12 o (tablesOf cfg o) = false) : placeOK cfg o = false := by
  simp [placeOK, Checks.ok, checks, h]

/-- **`placeOKAt` from its components** (at a layout `Λ`, one read off an
executable, say). -/
theorem placeOKAt_of {Λ : Scc.Sem.Layout} (h1 : a1 o ⟨Λ⟩ = true) (h2 : a2 o ⟨Λ⟩ = true) (h3 : a3 o ⟨Λ⟩ = true)
    (h4 : a4 cfg o ⟨Λ⟩ = true) (h5 : a5 o ⟨Λ⟩ = true) (h6 : a6 o ⟨Λ⟩ = true) (h7 : a7 o ⟨Λ⟩ = true)
    (h8 : a8 o ⟨Λ⟩ = true) (h9 : a9 o ⟨Λ⟩ = true) (h11 : a11 o ⟨Λ⟩ = true) (h12 : a12 o ⟨Λ⟩ = true) :
    placeOKAt cfg Λ o = true :=
  Checks.ok_of (C := checks cfg) (tablesOf := fun _ => ⟨Λ⟩) h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12

/-- A failing component fails `placeOKAt` (A1, say a code that overruns
the layout's code region, `codeFits`). -/
theorem placeOKAt_eq_false_of_a1 {Λ : Scc.Sem.Layout} (h : a1 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-! The same at a layout `Λ` (one read off an executable, say), for a
certificate driver's diagnostics. -/

theorem a1_of_partsAt {Λ : Scc.Sem.Layout} (h1 : PlaceOK.a1 ⟨Λ⟩ = true)
    (h2 : layoutOk o.secs Λ = true)
    (hc : codeFits o Λ = true)
    (h3 : codeOf Λ.code.lo o.prog "_start" = some Λ.code.lo) :
    a1 o ⟨Λ⟩ = true := by
  simp only [a1, h1, h2, hc, h3, decide_true, Bool.and_self]

theorem a2_of_partsAt {Λ : Scc.Sem.Layout} (h1 : loadOk Λ o.prog o.secs = true)
    (h2 : abortsIn o.prog Λ = true) (h3 : imageIn o.prog o.secs Λ = true) :
    a2 o ⟨Λ⟩ = true := by
  simp only [a2, h1, h2, h3, Bool.and_self]

theorem a3_of_partsAt {Λ : Scc.Sem.Layout} (h1 : decide (Rt.A64.blocksIn o.prog (Rt.A64.toGrps o.place.blocks)) = true)
    (h2 : Rt.A64.coverOk o.prog o.place.blocks = true) : a3 o ⟨Λ⟩ = true := by
  simp only [a3, h1, h2, Bool.and_self]

theorem a4_of_partsAt {Λ : Scc.Sem.Layout} (h1 : WideA64.wideIn o.prog = true)
    (h2 : NeedA64.needOk o.prog o.place.need cfg.needBudget cfg.entries = true) :
    a4 cfg o ⟨Λ⟩ = true := by
  simp only [a4, h1, h2, Bool.and_self]

theorem a5_of_partsAt {Λ : Scc.Sem.Layout} (h : Rt.A64.offsetsOk o.place.blocks = true) : a5 o ⟨Λ⟩ = true := h

theorem a6_of_partsAt {Λ : Scc.Sem.Layout}
    (h : Rt.A64.phasesOk Λ.code.lo o.prog Λ o.place.blocks = true)
    (hrt : Rt.A64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.A64.Rt.rtPhTab none) = true) :
    a6 o ⟨Λ⟩ = true := by
  simp only [a6, h, hrt, Bool.and_self]

theorem a7_of_partsAt {Λ : Scc.Sem.Layout} (h : Rt.A64.rtIn o.prog (Rt.A64.RtIn.rtTab (mainGrps o.place.tail)) = true)
    (hph : Spike.Lib.A64.StubW.abortPhC Λ.code.lo Λ o.prog = true)
    (htl : Spike.Lib.A64.StubW.tailOffC Λ.code.lo Λ o.prog = true) :
    a7 o ⟨Λ⟩ = true := by
  simp only [a7, h, hph, htl, Bool.and_self]

theorem a8_of_partsAt {Λ : Scc.Sem.Layout} (h : Rt.A64.rtWordsOk Λ o.prog o.secs = true)
    (hi : Rt.A64.rtInitOk Λ o.prog o.secs = true)
    (hc : Rt.A64.rtOffOk Λ o.prog o.secs = true) (hh : heapOk o Λ = true) :
    a8 o ⟨Λ⟩ = true := by
  simp only [a8, h, hi, hc, hh, Bool.and_self]

theorem a9_of_partsAt {Λ : Scc.Sem.Layout} {ir : Scc.IR.Program} (hir : o.place.ir = some ir)
    (h : Spike.Lib.LowerA64.fnCodeOk o.prog ir = true)
    (hph : Spike.Lib.LowerA64.fnPhOk Λ.code.lo Λ o.prog ir = true) :
    a9 o ⟨Λ⟩ = true := by
  simp only [a9, hir, h, hph, Bool.and_self]

theorem a11_of_partsAt {Λ : Scc.Sem.Layout} {mc : Spike.Lib.A64.Rt.MainCode} (hs : mcOf o.place.tail = some mc)
    (h : Spike.Lib.A64.Rt.rtCodeOk o.prog mc = true)
    (hph : Rt.A64.rtPhOk Λ.code.lo o.prog Λ (Spike.Lib.A64.Rt.mainPhTab mc) = true) :
    a11 o ⟨Λ⟩ = true := by
  simp only [a11, hs, h, hph, Bool.and_self]

/-- A wrong load (A2: the loader's checks, the abort labels or the image) fails `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a2 {Λ : Scc.Sem.Layout} (h : a2 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

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

/-- A missing IR or a lowered code block not in the program (A9) fails
`placeOKAt`. -/
theorem placeOKAt_eq_false_of_a9 {Λ : Scc.Sem.Layout} (h : a9 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong runtime code or abort path phases (A7) fail `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a7 {Λ : Scc.Sem.Layout} (h : a7 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong runtime data words (A8) fail `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a8 {Λ : Scc.Sem.Layout} (h : a8 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

/-- Wrong runtime fixed code or `scc_rt_main`'s phases (A11) fail `placeOKAt`. -/
theorem placeOKAt_eq_false_of_a11 {Λ : Scc.Sem.Layout} (h : a11 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

theorem placeOKAt_eq_false_of_a12 {Λ : Scc.Sem.Layout} (h : a12 o ⟨Λ⟩ = false) : placeOKAt cfg Λ o = false := by
  simp [placeOKAt, Checks.ok, checks, h]

end Parts

end Scc.Cert.PlaceOK.A64
