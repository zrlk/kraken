/-
**A lowered function's local overflow block from A9** (x86-64): the block
`fnCodeOk` checks at `ovfL` (`ovfBlk`, `Spike/Lib/LowerX64/Checks.lean`)
is the one the abort path's proofs run (`Abort.Local.lb`,
`Spike/Lib/X64AbortW.lean`), so its code at the block's label (`hcodeA` of
the abort path) follows from `PlaceOK`. Kept apart from the checks so that
`PlaceOK` does not import the abort path. The twin of
`Spike/Lib/LowerA64/OvfCode.lean`.

- `ovfBlk_eq_lb`: the checked block (with its cell sizes) is `Local.lb`;
- `ovfCode_codeAt`: `CodeAt` of `Local.lb` at the block's label from the
  check (`fnCodeOk_func0`'s third conjunct or `ovfCode_of_placeOK`).
-/
import Spike.Lib.LowerX64.Checks
import Spike.Lib.X64AbortW

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB)

/-- **The checked block is the abort path's** `movl $1, %edi; call
scc_rt_abort`, at the same cell sizes. -/
theorem ovfBlk_eq_lb : ovfBlk = Spike.Lib.X64.Abort.Local.lb := by decide

/-- **The local overflow block's code from the check**: with `ovfBlk` at
label `l` in laid-out cells, every state of the executable has `Local.lb`
at `l`'s address. -/
theorem ovfCode_codeAt {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {endPc : Int64}
        (hend : endPc = endOf exe cells kp)
    {l : Label} (h : blockAtB cells l 0 ovfBlk = true) :
    ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label l) Spike.Lib.X64.Abort.Local.lb :=
  ovfBlk_eq_lb ▸ Scc.Cert.Rt.X64.code_field hp hend h (by simp)

end Spike.Lib.LowerX64
