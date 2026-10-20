/-
`LiftOb` (`SLR/X64SpinRule.lean`) for the x64 spinlock worker: a cell proof
from a state with no own pending promise (`EraseWPR` into `WpPostR Inv`)
lifts to the dead-branch form into `WpPostR InvX`, by the generic
`EvTree.EraseWPR.toD_run` (`SLR/ThreadRuleXLift.lean`): along the run the
memory grows and no promise is added, so after the instruction the pending
marks (`g'.pend ⊆ g.pend`) are messages (`PendIn`) and none is an own
promise (`OwnPend`, vacuously). The x64 twin of `SLR/SwpLift.lean`.

`InvX` is an `InvXOf` invariant (`SLR/RuleObligationsX.lean`), so the lift
is the generic `liftOb_invXOf` at the worker's `OwnPend` condition.
-/
import Kraken.Promising.SLR.X64SpinRule
import Kraken.Promising.SLR.ThreadRuleXLift

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

omit hv in
/-- **The lift** for the worker (`HardCellsX.lift`). -/
theorem x64_lift (P : Params) (A : Arch) (tid : Nat) : LiftOb P A tid :=
  liftOb_invXOf A tid (Inv P tid)
    (fun t c r g ts =>
      ((AtPos t.st 5 ∧ c.mem.get? ts = some ⟨P.Lk, BitVec.setWidth 128 (eaxOf t.st), tid⟩) ∨
        (AtPos t.st 10 ∧ c.mem.get? ts = some ⟨P.C, BitVec.setWidth 128 (ecxOf t.st), tid⟩) ∨
        (AtPos t.st 11 ∧ (r.wr P.C).q = 0 ∧ c.mem.get? ts = some ⟨P.Lk, 0, tid⟩)) ∧
      (∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts) ∧
      (∀ p ∈ t.prom, p ≠ ts → ∀ w w', c.mem.get? p = some w → c.mem.get? ts = some w' → w.loc = w'.loc → ts < p))

end Kraken.Promising.SLR.X64SpinInv
