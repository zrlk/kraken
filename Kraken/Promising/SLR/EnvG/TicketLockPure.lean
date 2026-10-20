/-
**Part 5: purity and the dispenser phases of
the ticket lock worker by `vcgen`.**

`theorem1IIPureX_G₀_S_singleRmw` (`SLR/DispenserFresh.lean`) needs, besides
the per-thread `NPSafeP`, two facts about every reachable thread state:
purity (`EvTree.RelWrites`, as `final_of_relWritesJS`) and the
single-RMW dispenser shape (`SingleRmwDispenser`: before the hand-out the
next tree is `EvTree.BefX x N`, after it `EvTree.AftX x`). Both come from one
`vcgen` judgment per thread in an environment that tracks the phase:

- `dispPure A Q x N`: state `Bool` (`true`: after the hand-out). `ok` is
  `relPureQ`'s condition, no store to `x`, and an RMW on `x` only before the
  hand-out, writing `old + 1` below `N`; an RMW on `x` that writes moves to
  `true`, every other step keeps the phase. `Skips`.
- `TreeJ.disp`: the tree judgment `RelWrites ∧ All (∃ b, Post · b) ∧ (BefX`
  at `false`) `∧ (AftX` at `true)`.
- `DispSpec`, `dispSpec_step` (AArch64): `RelPureSpec`/`relPureSpec_step`
  with the phase as the environment state.
  (These four are in `EnvG/DispenserPureA64.lean`, same names.)
- `tkWorker_dispPure`: the worker in `dispPure` (table: `worker` before,
  `spin`/`done` after); `tkDispSpec`, `tkDispSpec_holds`.
-/
import Kraken.Promising.SLR.EnvG.DispenserPureA64
import Kraken.Promising.SLR.EnvG.TicketLockSmoke
import Kraken.Promising.SLR.DispenserRun
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.TicketLock

/-! ## The environment and the AArch64 specification

`dispPure`, `TreeJ.disp`, `DispSpec`, `dispSpec_step`, `DispSpec.ofProgram`
and `DispSpec.holds_of_partialTripleEnv` are in `EnvG/DispenserPureA64.lean`
(same names). -/

variable {A : Arch} {Q : Loc → Val → Prop} {x : Loc} {N : Nat}

/-! ## The worker -/

set_option mvcgen.warning false
set_option experimental.vcgen true

set_option hygiene false in
/-- **The purity-and-phase `vcgen` script of a ticket lock worker** (shared by
`tkWorker_dispPure` and `tkWorkerAl_dispPure`), after
`cfgEnv_partial` with the phase table, for the worker `wk`. Unhygienic: it
uses the theorem's hypotheses. -/
scoped macro "tk_pure_vcgen " "[" wk:Lean.Parser.Tactic.simpLemma "]" : tactic => `(tactic| (
  cfg_cases_env [$wk]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hx2, hdx, hdo, hdc, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [Arch.storeKind, Reg64s.setXReg, rmwOpBits, AtomicOp.apply,
    show Arch.armv8.plainStore = .plain from rfl]
  all_goals first
    | rfl
    | (intro old h; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)])
    | done))

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]

local instance tkWorker.envP : CodeEnv := ⟨layout tkWorker⟩

/-- The phase table: the frame everywhere, before the hand-out at `worker`,
after it at `spin` and `done`. -/
abbrev tkPureTable (Q : Loc → Val → Prop) (N : Nat) (x o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (dispPure Arch.armv8 Q ⟨x, 4⟩ (N + 1))).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
    Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
    ((lb = "worker" ∧ σ.1 = false) ∨ ((lb = "spin" ∨ lb = "done") ∧ σ.1 = true))

/-- **The ticket lock worker in `dispPure`** (counted, partial): the
`ldadda` writes `old + 1` to `next`, pure there, and moves to the second
phase; the counter's increment is pure; the `stlr` is a release; nothing else
writes `next`. -/
theorem tkWorker_dispPure (Q : Loc → Val → Prop) (N : Nat) (x o c : BitVec 64) (hN : N + 1 < 2 ^ 32)
    (hxo : x ≠ o) (hxc : x ≠ c) (hQx : ∀ v, Q ⟨x, 4⟩ v) (hQc : ∀ v, Q ⟨c, 4⟩ v) :
    PartialTripleEnv (SharedEnv.counted (dispPure Arch.armv8 Q ⟨x, 4⟩ (N + 1)))
      (fun s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
        Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
        σ.1 = false)
      tkWorker (fun _ σ => σ.1 = true) (fun _ _ _ => False) := by
  have hox := Ne.symm hxo
  have hcx := Ne.symm hxc
  apply MachineWP.cfgEnv_partial (tkPureTable Q N x o c) (hP := by funext s g; simp [tkPureTable])
  tk_pure_vcgen [tkWorker]

/-- **The worker's purity-and-phase specification**: the end of its text. -/
def tkDispSpec (Q : Loc → Val → Prop) (N : Nat) (x : BitVec 64) : DispSpec Arch.armv8 Q ⟨x, 4⟩ (N + 1) :=
  DispSpec.ofProgram tkWorker fun _ b => ∃ _ : Nat, b = true

/-- **The specification holds at a start state, before the hand-out.** -/
theorem tkDispSpec_holds {Q : Loc → Val → Prop} {N : Nat} {x o c : BitVec 64} (hN : N + 1 < 2 ^ 32)
    (hxo : x ≠ o) (hxc : x ≠ c) (hQx : ∀ v, Q ⟨x, 4⟩ v) (hQc : ∀ v, Q ⟨c, 4⟩ v) {s : isa.State}
    (h : StartState x o c s) : (tkDispSpec Q N x).Holds false s :=
  DispSpec.holds_of_partialTripleEnv (tkWorker_dispPure Q N x o c hN hxo hxc hQx hQc).uncount rfl h.exe h.decls
    h.endPc h.pc ⟨0, h.x0, h.x1, h.x2, h.dx, h.dO, h.dc, rfl⟩

end Worker

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.dispSpec_step
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkDispSpec_holds
