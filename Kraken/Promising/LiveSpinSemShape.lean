/-
**Stage 3: writes and conditional RMWs with
outstanding promises** (ISA-neutral; defined in
`LiveSemShape.lean`, same full names; this module forwards them).

- `mem_writeSuccs_c`: `SemShape.mem_writeSuccs` plus the coherence view of
  the written location after the write (at least the written timestamp), and
  `vwOld` at least the fulfilled timestamp for a non-`nt` fulfilment.
- `spec_rmwo_p`: an RMW with an arbitrary operation `op : Val → Option Val`
  (a failing `CAS` writes nothing) by a thread with any promise set: the read,
  then no write, or an atomic append, or the fulfilment of an outstanding
  promise. `SpinStep.spec_rmwo` is the promise-free case,
  `SemShape.spec_rmw_p` the always-writing one.
- `replay_rmwo`: an outcome of such an RMW that does not append replays
  against a larger memory (`SemShape.replay_rmw` for an arbitrary `op`).
-/
import Kraken.Promising.LiveSemShape
import Kraken.Promising.LiveSpinSwpStep

namespace Kraken.Promising.Live.SpinSemShape

set_option linter.unusedSectionVars false

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape

variable {I : ISA}

/-! The declarations of this module (`mem_writeSuccs_c`,
`readNext_vwOld`, `run_rmwo_p`, `spec_rmwo_p`, `replay_rmwo`; same full
names) are in `LiveSemShape.lean`, where `SemShape.mem_writeSuccs`,
`spec_rmw_p` and `replay_rmw` are their instances. This module forwards them. -/

private theorem rmwPost_eq' (b : Bool) (c : Ctx) (l : Loc) :
    let c' := if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }
    c'.mem = c.mem ∧ c'.prom = c.prom ∧ c'.views.vwOld = c.views.vwOld ∧ c'.views.coh = c.views.coh := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩

end Kraken.Promising.Live.SpinSemShape
