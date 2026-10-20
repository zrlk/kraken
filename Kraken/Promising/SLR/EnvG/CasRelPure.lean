/-
**The CAS spinlock worker is pure**: `casTtasWorker`
(`EnvG/CasSmoke.lean`) in `SharedEnv.relPure Arch.armv8 rel`
(`EnvG/RelPureEnv.lean`), by one `cfgEnv_partial` table and `vcgen`, for
any release predicates `rel` that are pure at the lock for a non-zero low
word and pure at the counter. Its non-release writes are the `casa`'s `1`
(`w3 = 1` throughout the loop) and the counter's increment; the `stlr wzr`
is a release.

This is the purity half of `final_of_relWrites` (`hcell`/`Jinv`), through
`final_of_relPureSafely` (`EnvG/RelPureEnvA64.lean`): `casPureSpec` and
`casPureSpec_holds` below.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.CasSmoke

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.CasSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)]

local instance casTtasWorker.env : CodeEnv := ⟨layout casTtasWorker⟩

/-- The purity table: the frame everywhere, `w3 = 1` inside the loop. -/
abbrev casPureTable (l c : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
    Mem.loadInt s.dmem c 4 = none ∧
    (lb = "worker" ∨ ((lb = "try" ∨ lb = "spin") ∧ s.regs.X3.toBitVec.setWidth 32 = 1) ∨
      lb = "cs" ∨ lb = "done")

/-- **The CAS worker is pure** (counted, partial): the `casa` writes `1`,
pure at the lock; the increment writes the counter, pure; the `stlr` is a
release. -/
theorem casTtasWorker_relPure (rel : Loc → Pred) (l c : BitVec 64)
    (hl : ∀ v : Val, BitVec.setWidth 32 v ≠ 0 → Pred.Pure (rel ⟨l, 4⟩) v)
    (hc : ∀ v : Val, Pred.Pure (rel ⟨c, 4⟩) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
        Mem.loadInt s.dmem c 4 = none)
      casTtasWorker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (casPureTable l c rel) (hP := by funext s g; simp [casPureTable])
  cfg_cases_env [casTtasWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdl, hdc, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.relPureQ, Arch.storeKind, Reg64s.setXReg, rmwOpBits,
    show Arch.armv8.plainStore = .plain from rfl]

/-- **The worker's purity specification**: the end of its text. -/
def casPureSpec (rel : Loc → Pred) : RelPureSpec Arch.armv8 rel :=
  RelPureSpec.ofProgram casTtasWorker fun _ _ => ∃ _ : Nat, True

/-- **The purity specification holds at a start state.** -/
theorem casPureSpec_holds {rel : Loc → Pred} {l c : BitVec 64}
    (hl : ∀ v : Val, BitVec.setWidth 32 v ≠ 0 → Pred.Pure (rel ⟨l, 4⟩) v)
    (hc : ∀ v : Val, Pred.Pure (rel ⟨c, 4⟩) v) {s : isa.State} (h : StartState l c s) :
    (casPureSpec rel).Holds s :=
  RelPureSpec.holds_of_partialTripleEnv (casTtasWorker_relPure rel l c hl hc).uncount rfl h.exe h.decls h.endPc
    h.pc ⟨0, h.x0, h.x1, h.dl, h.dc⟩

end Kraken.Promising.SLR.EnvG.CasSmoke
