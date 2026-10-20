/-
**Item 2, part 3: purity and the dispenser
phases of the `ldaddal` ticket lock worker by `vcgen`**
(`EnvG/TicketLockPure.lean` for `tkWorkerAl`; `dispPure` is kind-neutral:
the `ldaddal` is a release-kind RMW, its written value `old + 1` is pure at
`next`).

- `tkWorkerAl_dispPure`, `tkAlDispSpec`, `tkAlDispSpec_holds`.
-/
import Kraken.Promising.SLR.EnvG.DispenserPureA64
import Kraken.Promising.SLR.EnvG.TicketAlSmoke
import Kraken.Promising.SLR.EnvG.TicketLockPure
import Kraken.Promising.SLR.DispenserRun
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.TicketLock

variable {A : Arch} {Q : Loc → Val → Prop} {x : Loc} {N : Nat}

/-! ## The worker -/

set_option mvcgen.warning false
set_option experimental.vcgen true

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]

local instance tkWorkerAl.envP : CodeEnv := ⟨layout tkWorkerAl⟩

/-- The phase table: the frame everywhere, before the hand-out at `worker`,
after it at `spin` and `done`. -/
abbrev tkPureTableAl (Q : Loc → Val → Prop) (N : Nat) (x o c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (dispPure Arch.armv8 Q ⟨x, 4⟩ (N + 1))).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
    Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
    ((lb = "worker" ∧ σ.1 = false) ∨ ((lb = "spin" ∨ lb = "done") ∧ σ.1 = true))

/-- **The ticket lock worker in `dispPure`** (counted, partial): the
`ldaddal` writes `old + 1` to `next`, pure there, and moves to the second
phase; the counter's increment is pure; the `stlr` is a release; nothing else
writes `next`. -/
theorem tkWorkerAl_dispPure (Q : Loc → Val → Prop) (N : Nat) (x o c : BitVec 64) (hN : N + 1 < 2 ^ 32)
    (hxo : x ≠ o) (hxc : x ≠ c) (hQx : ∀ v, Q ⟨x, 4⟩ v) (hQc : ∀ v, Q ⟨c, 4⟩ v) :
    PartialTripleEnv (SharedEnv.counted (dispPure Arch.armv8 Q ⟨x, 4⟩ (N + 1)))
      (fun s σ => s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
        Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none ∧
        σ.1 = false)
      tkWorkerAl (fun _ σ => σ.1 = true) (fun _ _ _ => False) := by
  have hox := Ne.symm hxo
  have hcx := Ne.symm hxc
  apply MachineWP.cfgEnv_partial (tkPureTableAl Q N x o c) (hP := by funext s g; simp [tkPureTableAl])
  tk_pure_vcgen [tkWorkerAl]

/-- **The worker's purity-and-phase specification**: the end of its text. -/
def tkAlDispSpec (Q : Loc → Val → Prop) (N : Nat) (x : BitVec 64) : DispSpec Arch.armv8 Q ⟨x, 4⟩ (N + 1) :=
  DispSpec.ofProgram tkWorkerAl fun _ b => ∃ _ : Nat, b = true

/-- **The specification holds at a start state, before the hand-out.** -/
theorem tkAlDispSpec_holds {Q : Loc → Val → Prop} {N : Nat} {x o c : BitVec 64} (hN : N + 1 < 2 ^ 32)
    (hxo : x ≠ o) (hxc : x ≠ c) (hQx : ∀ v, Q ⟨x, 4⟩ v) (hQc : ∀ v, Q ⟨c, 4⟩ v) {s : isa.State}
    (h : StartStateAl x o c s) : (tkAlDispSpec Q N x).Holds false s :=
  DispSpec.holds_of_partialTripleEnv (tkWorkerAl_dispPure Q N x o c hN hxo hxc hQx hQc).uncount rfl h.exe h.decls
    h.endPc h.pc ⟨0, h.x0, h.x1, h.x2, h.dx, h.dO, h.dc, rfl⟩

end Worker

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkAlDispSpec_holds
