/-
`LiftOb` (`SLR/SwpRuleX.lean`) for the SWP spinlock worker: a cell proof
from a state with no own pending promise (`EraseWPR` into `WpPostR Inv`)
lifts to the dead-branch form into `WpPostR InvX`, by the generic
`EvTree.EraseWPR.toD_run` (`SLR/ThreadRuleXLift.lean`): along the run the
memory grows and no promise is added, so after the instruction the pending
marks (`g'.pend ⊆ g.pend`) are messages (`PendIn`) and none is an own
promise (`OwnPend`, vacuously).

`InvX` is an `InvXOf` invariant (`SLR/RuleObligationsX.lean`), so the lift
is the generic `liftOb_invXOf` at the worker's `OwnPend` condition.
-/
import Kraken.Promising.SLR.SwpRuleX
import Kraken.Promising.SLR.ThreadRuleXLift

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

omit hv in
/-- **The lift** for the worker (`HardCellsX.lift`). -/
theorem swp_lift (P : Params) (A : Arch) (tid : Nat) : LiftOb P A tid :=
  liftOb_invXOf A tid (Inv P tid)
    (fun t _ r g ts => AtPos t.st 13 ∧ (r.wr P.C).q = 0 ∧ ∀ ts' ∈ t.prom, ts' ∈ g.pend → ts' = ts)

end Kraken.Promising.SLR.SwpInv
