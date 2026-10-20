/-
Msqueue2 part 6: **the two threads of `msqueue2.kl`
are pure**: in `SharedEnv.relPure Arch.armv8 rel` for release predicates pure
at the data words `[n1]` and `[n2]` (4 bytes; the enqueuer's only `str`s);
every other write is a release `casal`. Modelled on `EnvG/MsQueueRelPure.lean`.

`StartE2`, `StartD2` (the start states), `msqPureSpec2` and
`msqPureSpec2_init`.

The whole-image AArch64 proofs (name-preserving): each run is stated once as `…_at`, over any
ambient code (`[CodeEnv]`) in which the text is `Program.PlacedIn`, from its
entry label to the end address of its last block; the per-thread theorem is
`PartialTripleEnv.of_runAtT` of it (`EnvG/A64MaskRunAt.lean`), and the
whole-image theorems (`EnvG/A64WholeMsQueue*.lean`) run it in the image or a
mask of it.
-/
import Kraken.Promising.SLR.EnvG.MsQueue2VCGen
import Kraken.Promising.SLR.EnvG.MsQueueRelPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

set_option mvcgen.warning false
set_option experimental.vcgen true

section EnqAt

variable [CodeEnv]

/-- The enqueuer's purity table: `x13 = n2`, `x12 = n1` at `enq1`, `dmem`
maps no 8- or 4-byte word. -/
abbrev enqPureTable2 (n1 n2 : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    s.regs.X13.toBitVec = n2 ∧
    ((lb = "enq1" ∧ s.regs.X12.toBitVec = n1) ∨ lb = "enq1_loop" ∨ lb = "enq1_fix" ∨ lb = "enq1_end" ∨
      lb = "enq2" ∨ lb = "enq2_loop" ∨ lb = "enq2_fix" ∨ lb = "enq2_end" ∨ lb = "pdone")

/-- **`enq2_relPure` in any ambient code** in which `enq2Prog` is `PlacedIn`, from `enq1` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem enq2_relPure_at (rel : Loc → Pred) (n1 n2 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v)
    (hpl : Program.PlacedIn enq2Prog) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt enq2Prog l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (enqPureTable2 n1 n2 rel) "enq1" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "enq1"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (enqPureTable2 n1 n2 rel) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [enq2Prog]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hx13, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hd8, hT, hx13, SharedEnv.relPureQ, Arch.storeKind, hd, hd2,
    show Arch.armv8.plainStore = .plain from rfl]; done)
  -- the `casal`s are release RMWs: unconstrained
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  -- forward jumps
  all_goals try (exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx13],
    by simp (config := { decide := true })⟩, .inl (by decide)⟩)
  -- back edges: the variant decreased
  all_goals try (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp [hx13], by simp⟩,
    .inr fun ⟨_, hg⟩ => ?_⟩; subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *; omega)
  -- the `str`s fall through to the loop; `enq1_end` falls through to `enq2`
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hT, hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    simp (config := { decide := true }) [hd8, hd4, hx13]
  case vc1 => simp (config := { decide := true }) [hd8, hd4, hx13]
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hx13, hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    simp (config := { decide := true }) [hd8, hd4, hx13]

end EnqAt

section Enq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout enq2Prog)]

local instance enq2Prog.env : CodeEnv := ⟨layout enq2Prog⟩

/-- **The enqueuer is pure** (counted, partial): its `str`s write the data
words `[n1]`, `[n2]`, pure there; the `casal`s are releases. -/
theorem enq2_relPure (rel : Loc → Pred) (n1 n2 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
        s.regs.X13.toBitVec = n2 ∧ s.regs.X12.toBitVec = n1)
      enq2Prog (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed enq2Prog "enq1" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [enqPureTable2]) fun _ hlast =>
    enq2_relPure_at rel n1 n2 hd hd2 hpl.toPlacedIn hlast

end Enq

section DeqAt

variable [CodeEnv]

/-- The dequeuer's purity table: `dmem` maps no 8- or 4-byte word. -/
abbrev deqPureTable2 (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    (lb = "deq1a" ∨ lb = "deq1a_ne" ∨ lb = "deq1b" ∨ lb = "deq1b_ne" ∨ lb = "ddone1")

/-- **`deq2_relPure` in any ambient code** in which `deq2Prog` is `PlacedIn`, from `deq1a` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem deq2_relPure_at (rel : Loc → Pred)
    (hpl : Program.PlacedIn deq2Prog) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deq2Prog l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqPureTable2 rel) "deq1a" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "deq1a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (deqPureTable2 rel) deqRank2 ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deq2Prog]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hd8, SharedEnv.relPureQ]; done)
  -- the `casal`s are release RMWs: unconstrained
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  -- jumps down the rank
  all_goals try (exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4],
    by simp (config := { decide := true })⟩, .inl (by decide)⟩)
  -- back edges: the variant decreased
  all_goals try (refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp⟩,
    .inr (.inr fun ⟨_, hg⟩ => ?_)⟩; subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *; omega)
  -- `deq1a_ne` falls through to `deq1b`
  all_goals simp (config := { decide := true }) [hd8, hd4]

end DeqAt

section Deq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deq2Prog)]

local instance deq2Prog.env : CodeEnv := ⟨layout deq2Prog⟩

/-- **The dequeuer is pure** (counted, partial): it writes only by release
`casal`s. -/
theorem deq2_relPure (rel : Loc → Pred) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none))
      deq2Prog (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed deq2Prog "deq1a" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [deqPureTable2]) fun _ hlast =>
    deq2_relPure_at rel hpl.toPlacedIn hlast

end Deq

/-! ## Start states and the purity specifications -/

section Start

variable [layout : _root_.Layout]

/-- **The enqueuer's start state** (`0:X1=tail; 0:X12=n1; 0:X13=n2`): at the
start of `enq2Prog` with `x1 = t`, `x12 = n1`, `x13 = n2`; no private copy of
any 8- or 4-byte word (`dmem` empty there: the loads read the shared
memory). -/
structure StartE2 (t n1 n2 : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout enq2Prog
  decls : s.decls = {}
  endPc : s.endPc = (layout enq2Prog).addrOf enq2Prog.length
  pc : s.st.2 = (layout enq2Prog).addrOf 0
  x1 : s.st.1.regs.X1.toBitVec = t
  x12 : s.st.1.regs.X12.toBitVec = n1
  x13 : s.st.1.regs.X13.toBitVec = n2
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- **The dequeuer's start state** (`1:X0=head; 1:X1=tail`): at the start of
`deq2Prog` with `x0 = h`, `x1 = t`; no private copy of any 8- or 4-byte
word. -/
structure StartD2 (h t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout deq2Prog
  decls : s.decls = {}
  endPc : s.endPc = (layout deq2Prog).addrOf deq2Prog.length
  pc : s.st.2 = (layout deq2Prog).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = h
  x1 : s.st.1.regs.X1.toBitVec = t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

end Start

/-- The threads' purity specifications: the enqueuer at layout `l0` at
thread `0`, the dequeuer at layout `l1` elsewhere. -/
def msqPureSpec2 (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deq2Prog)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := l0) enq2Prog fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpec.ofProgram (layout := l1) deq2Prog fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states**, for release
predicates pure at the data words `[n1]`, `[n2]`. -/
theorem msqPureSpec2_init (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deq2Prog)] {rel : Loc → Pred} {h t n1 n2 : BitVec 64}
    (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v) (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v)
    {s0 s1 : isa.State} (h0 : StartE2 (layout := l0) t n1 n2 s0) (h1 : StartD2 (layout := l1) h t s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (msqPureSpec2 l0 l1 rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, -, hx12, hx13, hd8, hd4⟩ := h0
    letI : CodeEnv := ⟨l0 enq2Prog⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l0)
      (enq2_relPure (layout := l0) rel n1 n2 hd hd2).uncount rfl he hds hend hpc ⟨0, hd8, hd4, hx13, hx12⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, -, -, hd8, hd4⟩ := h1
    letI : CodeEnv := ⟨l1 deq2Prog⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l1)
      (deq2_relPure (layout := l1) rel).uncount rfl he hds hend hpc ⟨0, hd8, hd4⟩
  | _ + 2, _, hs => by cases hs

end Kraken.Promising.SLR.EnvG.MsQueue
