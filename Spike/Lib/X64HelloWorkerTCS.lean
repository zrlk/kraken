/-
**hello.w on x86-64: `wc_worker`'s call node at depth** (the twin of
`Spike/Lib/A64HelloWorkerTCS.lean`): the node at `scc_rt_print`'s entry
after `wc_worker`'s `.entry` block (`Body.wkC`,
`Spike/Lib/X64HelloWorkerBody.lean`), the source at the call's control.

- `Body.wCall`: the call node, `%rsp` at `-96` (the pushed return
  address below the frame of 80 and the saved `%rbp`).

## Differences from the AArch64 version

- The call state is `wkC lab σ0 fl` for some multiply flags `fl` (`imulq`
  leaves the flags undefined), A64's `wkC lab σ0`.
- A64's `Wk.seg_wcWorkerS` (dead) is not twinned, so the module needs no
  `print` segment at depth.
-/
import Spike.Lib.X64HelloWorkerBody

namespace Spike.Lib.X64.Flow.Worker.Body

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64

/-- **The worker's call node**: at `scc_rt_print` with `%rsp` at `-96`,
after the `.entry` block from a state of `J` (any multiply flags), the
source at the call's control (`Kc`). -/
def wCall (lab : Label → Int64) (J Kc : AS → Ctl → Prop) : ND :=
  ⟨lab "scc_rt_print", ⟨-96, []⟩, fun σ c => (∃ σ0 c0 fl, J σ0 c0 ∧ σ = wkC lab σ0 fl) ∧ Kc σ c⟩

/-- The head's call node at `Kc` is `wCall` (`Pr` at 0 bytes). -/
theorem wN_call_eq (lab : Label → Int64) (J : AS → Ctl → Prop) (Pr : AS → Nat → Ctl → Prop) :
    wN lab J Pr .call = wCall lab J (fun σ c => Pr σ 0 c) := rfl

end Spike.Lib.X64.Flow.Worker.Body

/-- info: 'Spike.Lib.X64.Flow.Worker.Body.wN_call_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Body.wN_call_eq
