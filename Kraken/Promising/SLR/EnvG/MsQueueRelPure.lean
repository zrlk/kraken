/-
Part 7: **the two threads of `msqueue1.kl` are pure**:
in `SharedEnv.relPure Arch.armv8 rel` for release predicates pure at the
enqueued node's data word `[n1]` (4 bytes; the enqueuer's only `str`); every
other write is a release `casal` (unconstrained).

`StartE`, `StartD` (the start states), `msqPureSpec` and `msqPureSpec_init`.

The whole-image AArch64 proofs (name-preserving): each run is stated once as `…_at`, over any
ambient code (`[CodeEnv]`) in which the text is `Program.PlacedIn`, from its
entry label to the end address of its last block; the per-thread theorem is
`PartialTripleEnv.of_runAtT` of it (`EnvG/A64MaskRunAt.lean`), and the
whole-image theorems (`EnvG/A64WholeMsQueue*.lean`) run it in the image or a
mask of it.
-/
import Kraken.Promising.SLR.EnvG.MsQueueVCGen
import Kraken.Promising.SLR.EnvG.RelPureEnvA64

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

set_option mvcgen.warning false
set_option experimental.vcgen true

section EnqAt

variable [CodeEnv]

/-- The enqueuer's purity table: `x12 = n1` at `enq1`, `dmem` maps no 8- or
4-byte word. -/
abbrev enqPureTable (n1 : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "enq1" ∧ s.regs.X12.toBitVec = n1) ∨ lb = "enq1_loop" ∨ lb = "enq1_fix" ∨ lb = "enq1_end" ∨
      lb = "pdone")

/-- **`enq_relPure` in any ambient code** in which `enqProg` is `PlacedIn`, from `enq1` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem enq_relPure_at (rel : Loc → Pred) (n1 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v) (hpl : Program.PlacedIn enqProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt enqProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (enqPureTable n1 rel) "enq1" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "enq1"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (enqPureTable n1 rel) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [enqProg]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hd8, hT, SharedEnv.relPureQ, Arch.storeKind, hd,
    show Arch.armv8.plainStore = .plain from rfl]; done)
  -- the `casal`s are release RMWs: unconstrained
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  -- forward jumps
  all_goals try (exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4],
    by simp (config := { decide := true })⟩, .inl (by decide)⟩)
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hT, hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    simp (config := { decide := true }) [hd8, hd4]
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz old σ3 hnz hld1 hld2 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3
    omega
  case vc4 =>
    rename_i s σ0 old σ1 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h3 := hcas.2
    simp only [SharedEnv.tick_rmw] at h3
    omega
  all_goals done

end EnqAt

section Enq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout enqProg)]

local instance enqProg.env : CodeEnv := ⟨layout enqProg⟩

/-- **The enqueuer is pure** (counted, partial): its `str` writes the data
word `[n1]`, pure there; the `casal`s are releases. -/
theorem enq_relPure (rel : Loc → Pred) (n1 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
        s.regs.X12.toBitVec = n1)
      enqProg (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed enqProg "enq1" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [enqPureTable]) fun _ hlast =>
    enq_relPure_at rel n1 hd hpl.toPlacedIn hlast

end Enq

section DeqAt

variable [CodeEnv]

/-- The dequeuer's purity table: `dmem` maps no 8- or 4-byte word. -/
abbrev deqPureTable (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    (lb = "deq1a" ∨ lb = "deq1a_ne" ∨ lb = "ddone1")

/-- **`deq_relPure` in any ambient code** in which `deqProg` is `PlacedIn`, from `deq1a` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem deq_relPure_at (rel : Loc → Pred) (hpl : Program.PlacedIn deqProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deqProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqPureTable rel) "deq1a" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "deq1a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (deqPureTable rel) deqRank ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deqProg]
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
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hld1 hld2 hld3 _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hz hld1 hld2 hld3 _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3
    omega
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz old σ4 hld1 hld2 hld3 hcas _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hd8], by simp [hd4], by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2; have h4 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3 h4
    omega
  all_goals done

end DeqAt

section Deq

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqProg)]

local instance deqProg.env : CodeEnv := ⟨layout deqProg⟩

/-- **The dequeuer is pure** (counted, partial): it writes only by release
`casal`s. -/
theorem deq_relPure (rel : Loc → Pred) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none))
      deqProg (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed deqProg "deq1a" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [deqPureTable]) fun _ hlast =>
    deq_relPure_at rel hpl.toPlacedIn hlast

end Deq

/-! ## Start states and the purity specifications -/

section Start

variable [layout : _root_.Layout]

/-- **The enqueuer's start state** (`0:X1=tail; 0:X12=n1`): at the start of
`enqProg` with `x1 = t`, `x12 = n1`; no private copy of any 8- or 4-byte
word (`dmem`: the loads read the shared memory). -/
structure StartE (t n1 : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout enqProg
  decls : s.decls = {}
  endPc : s.endPc = (layout enqProg).addrOf enqProg.length
  pc : s.st.2 = (layout enqProg).addrOf 0
  x1 : s.st.1.regs.X1.toBitVec = t
  x12 : s.st.1.regs.X12.toBitVec = n1
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- **The dequeuer's start state** (`1:X0=head; 1:X1=tail`): at the start of
`deqProg` with `x0 = h`, `x1 = t`; no private copy of any 8- or 4-byte
word. -/
structure StartD (h t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout deqProg
  decls : s.decls = {}
  endPc : s.endPc = (layout deqProg).addrOf deqProg.length
  pc : s.st.2 = (layout deqProg).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = h
  x1 : s.st.1.regs.X1.toBitVec = t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

end Start

/-- The threads' purity specifications: the enqueuer at layout `l0` at
thread `0`, the dequeuer at layout `l1` elsewhere. -/
def msqPureSpec (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enqProg)]
    [Executable.ValidLayout (l1 deqProg)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := l0) enqProg fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpec.ofProgram (layout := l1) deqProg fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states**, for release
predicates pure at the data word `[n1]`. -/
theorem msqPureSpec_init (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enqProg)]
    [Executable.ValidLayout (l1 deqProg)] {rel : Loc → Pred} {h t n1 : BitVec 64}
    (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    {s0 s1 : isa.State} (h0 : StartE (layout := l0) t n1 s0) (h1 : StartD (layout := l1) h t s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (msqPureSpec l0 l1 rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, -, hx12, hd8, hd4⟩ := h0
    letI : CodeEnv := ⟨l0 enqProg⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l0)
      (enq_relPure (layout := l0) rel n1 hd).uncount rfl he hds hend hpc ⟨0, hd8, hd4, hx12⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, -, -, hd8, hd4⟩ := h1
    letI : CodeEnv := ⟨l1 deqProg⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l1)
      (deq_relPure (layout := l1) rel).uncount rfl he hds hend hpc ⟨0, hd8, hd4⟩
  | _ + 2, _, hs => by cases hs

end Kraken.Promising.SLR.EnvG.MsQueue
