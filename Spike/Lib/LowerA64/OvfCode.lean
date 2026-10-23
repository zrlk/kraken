/-
**A lowered function's local overflow block from A9** (AArch64): the block
`fnCodeOk` checks at `cx.local "abort_overflow"` (`ovfBlk`,
`Spike/Lib/LowerA64/Checks.lean`) is the one the abort path's proofs run
(`Abort.Local.lb`, `Spike/Lib/A64AbortW.lean`), so its code at the block's
label (`hcodeA` of the abort path) follows from `PlaceOK`. Kept apart from
the checks so that `PlaceOK` does not import the abort path.

- `ovfBlk_eq_lb`: the checked block is `Local.lb`;
- `ovfCode_codeAt`: `CodeAt` of `Local.lb` at the block's label from the
  check (`fnCodeOk_func0`'s third conjunct or `ovfCode_of_placeOK`).
-/
import Spike.Lib.LowerA64.Checks
import Spike.Lib.A64AbortW
import Scc.Cert.Rt.A64Print

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)

/-- **The checked block is the abort path's** `movz x0, #1; bl scc_rt_abort`. -/
theorem ovfBlk_eq_lb : ovfBlk = Spike.Lib.A64.Abort.Local.lb := by decide

/-- **The local overflow block's code from the check**: with `ovfBlk` at
label `l` in a laid-out `prog`, every state of the executable has
`Local.lb` at `l`'s address. -/
theorem ovfCode_codeAt {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {endPc : Int64} (hend : endPc = endOf exe prog) {l : Label}
    (h : blockAt prog l 0 ovfBlk = true) :
    ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label l) Spike.Lib.A64.Abort.Local.lb :=
  ovfBlk_eq_lb ▸ Scc.Cert.Rt.A64.Print.code_field hp hend h (by simp)

end Spike.Lib.LowerA64
