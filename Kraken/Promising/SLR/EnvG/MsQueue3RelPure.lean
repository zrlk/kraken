/-
Part 6: **the three threads of `msqueue3.kl` are
pure**: in `SharedEnv.relPure Arch.armv8 rel` for release predicates pure at
the data words `[n1]` and `[n2]`. The enqueuer is msqueue2's
(`enq2_relPure`), the first dequeuer msqueue1's (`deq_relPure`); the second
dequeuer `deqBProg` writes only by release `casal`s (`deqB_relPure`).

`StartDB` (the second dequeuer's start state), `msqPureSpec3` and
`msqPureSpec3_init`.

The whole-image AArch64 proofs (name-preserving): each run is stated once as `…_at`, over any
ambient code (`[CodeEnv]`) in which the text is `Program.PlacedIn`, from its
entry label to the end address of its last block; the per-thread theorem is
`PartialTripleEnv.of_runAtT` of it (`EnvG/A64MaskRunAt.lean`), and the
whole-image theorems (`EnvG/A64WholeMsQueue*.lean`) run it in the image or a
mask of it.
-/
import Kraken.Promising.SLR.EnvG.MsQueue3VCGen
import Kraken.Promising.SLR.EnvG.MsQueue2RelPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.MsQueue

set_option mvcgen.warning false
set_option experimental.vcgen true

section DeqBAt

variable [CodeEnv]

/-- The second dequeuer's purity table: `dmem` maps no 8- or 4-byte word. -/
abbrev deqBPureTable (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    (lb = "deq2a" ∨ lb = "deq2a_ne" ∨ lb = "ddone2")

/-- **`deqB_relPure` in any ambient code** in which `deqBProg` is `PlacedIn`, from `deq2a` to
the end address `endA` of its last block (its script; `EnvG/A64MaskRunAt.lean`). -/
theorem deqB_relPure_at (rel : Loc → Pred)
    (hpl : Program.PlacedIn deqBProg) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt deqBProg l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, (deqBPureTable rel) "deq2a" s g → Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
      (fun x => (x.1.2 = endA ∧ True) ∨ False)
      ((s, (_root_.Executable.labels cenv).label "deq2a"), g) := by
  refine cfgEnv_partial_rank_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (deqBPureTable rel) (deqRank3 "deq2a_ne") ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env_rank [deqBProg]
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
  all_goals done

end DeqBAt

section DeqB

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqBProg)]

local instance deqBProg.env : CodeEnv := ⟨layout deqBProg⟩

/-- **The second dequeuer is pure** (counted, partial): it writes only by
release `casal`s. -/
theorem deqB_relPure (rel : Loc → Pred) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ (∀ a, Mem.loadInt s.dmem a 4 = none))
      deqBProg (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed deqBProg "deq2a" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [deqBPureTable]) fun _ hlast =>
    deqB_relPure_at rel hpl.toPlacedIn hlast

end DeqB

section Start

variable [layout : _root_.Layout]

/-- **The second dequeuer's start state** (`2:X0=head; 2:X1=tail`): at the
start of `deqBProg` with `x0 = h`, `x1 = t`; no private copy of any 8- or
4-byte word. -/
structure StartDB (h t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout deqBProg
  decls : s.decls = {}
  endPc : s.endPc = (layout deqBProg).addrOf deqBProg.length
  pc : s.st.2 = (layout deqBProg).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = h
  x1 : s.st.1.regs.X1.toBitVec = t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

end Start

/-- The threads' purity specifications: the enqueuer at layout `l0` at
thread `0`, the first dequeuer at layout `l1` at thread `1`, the second at
layout `l2` elsewhere. -/
def msqPureSpec3 (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deqProg)] [Executable.ValidLayout (l2 deqBProg)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := l0) enq2Prog fun _ _ => ∃ _ : Nat, True
  | 1 => RelPureSpec.ofProgram (layout := l1) deqProg fun _ _ => ∃ _ : Nat, True
  | _ + 2 => RelPureSpec.ofProgram (layout := l2) deqBProg fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states**, for release
predicates pure at the data words `[n1]`, `[n2]`. -/
theorem msqPureSpec3_init (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deqProg)] [Executable.ValidLayout (l2 deqBProg)] {rel : Loc → Pred}
    {h t n1 n2 : BitVec 64} (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v) {s0 s1 s2 : isa.State}
    (h0 : StartE2 (layout := l0) t n1 n2 s0) (h1 : StartD (layout := l1) h t s1)
    (h2 : StartDB (layout := l2) h t s2) :
    ∀ tid s, [s0, s1, s2][tid]? = some s → (msqPureSpec3 l0 l1 l2 rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, -, hx12, hx13, hd8, hd4⟩ := h0
    letI : CodeEnv := ⟨l0 enq2Prog⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l0)
      (enq2_relPure (layout := l0) rel n1 n2 hd hd2).uncount rfl he hds hend hpc ⟨0, hd8, hd4, hx13, hx12⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, -, -, hd8, hd4⟩ := h1
    letI : CodeEnv := ⟨l1 deqProg⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l1)
      (deq_relPure (layout := l1) rel).uncount rfl he hds hend hpc ⟨0, hd8, hd4⟩
  | 2, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, -, -, hd8, hd4⟩ := h2
    letI : CodeEnv := ⟨l2 deqBProg⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l2)
      (deqB_relPure (layout := l2) rel).uncount rfl he hds hend hpc ⟨0, hd8, hd4⟩
  | _ + 3, _, hs => by cases hs

end Kraken.Promising.SLR.EnvG.MsQueue
