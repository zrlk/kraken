import Spike.Lib.LowerA64.PhOfPlaceOK
import Spike.Lib.A64OwnLimRt
import Spike.Lib.A64Ret0I
import Spike.Test.LowerA64Ret0Oracle

/-!
# A9's phase part (`fnPhOk`) at `ret0.w` (AArch64)

`ret0.w`'s lowered `main` passes its phase facts (`fnPhAll`: the prologue's
`proPhOk`, the body's `bodyPhOk`, every label read resolving) at the hand
placement's tables (`Ret0.Inst.okPc`, `ph`, `labT`), the return address after
`scc_rt_main`'s `bl wc_main` (`.L1_scc_rt_main.0_entry` plus 4); it fails with
no pc allowed, with the phases moved, with a return into `scc_rt_stack_take`'s
phase, and with a label the check reads unresolved (the overflow branch, the
check label, `scc_rt_abort`); and with `scc_rt_abort` moved off the local
overflow block's phase. The certificates (`Spike/Test/Cert/A64*Cert.lean`)
decide `fnPhOk` itself inside A9 at A6's tables. (Twin of
`Spike/Test/LowerX64PhCheck.lean`.)
-/

namespace Spike.Test.LowerA64PhCheck

open Spike.Lib.LowerA64 Spike.Test.LowerInv
open Spike.Lib.A64.Flow.Ret0.Inst (okPc ph labT)

/-- The hand table's labels, with `scc_rt_abort` (the local overflow
block's call target, not in `labT`'s table) through `labIn`, so that the
kernel decides the check. -/
def labA (l : Label) : Int64 :=
  if l == "scc_rt_abort" then Spike.Lib.A64.OwnLimRt.labIn SccCode.ret0Λ.code.lo SccCode.ret0Prog l else labT l

/-- Every label resolves. -/
abbrev resT : String → Bool := fun _ => true

/-- The return address. -/
abbrev raT : Int64 := labT raL + 4

/- The labels the checks read: the prologue's growth branch, the body's
overflow branch. -/
#guard proLabs (Int64.ofInt 32) ".L18_wc_main.stack_grow" [] == [".L18_wc_main.stack_grow"]
#guard blkLabs ovfBlk == ["scc_rt_abort"]
#guard ((bodyBlks mainCtx 0 ret0Res.insts ret0Res.ret).flatMap (blkLabs ·.2)) == [".L18_wc_main.abort_overflow"]

/- The hand tables: `main` passes. -/
#guard fnPhAll okPc ph labT resT ret0IR raT

/- No pc allowed: fails. -/
#guard !fnPhAll (fun _ => false) ph labT resT ret0IR raT

/- The phases moved off `main`'s check label: fails. -/
#guard !fnPhAll okPc (fun pc => if pc == (labT ".L18_wc_main.stack_check").toBitVec.toNat then ph pc else ph pc + 1)
  labT resT ret0IR raT

/- A return into `scc_rt_stack_take` (phase 12): fails. -/
#guard ph 4195700 == 12
#guard !fnPhAll okPc ph labT resT ret0IR (Int64.ofNat 4195700)

/- The overflow label unresolved: fails. -/
#guard !fnPhAll okPc ph labT (· != ".L18_wc_main.abort_overflow") ret0IR raT

/- `main`'s check label unresolved: fails. -/
#guard !fnPhAll okPc ph labT (· != ".L18_wc_main.stack_check") ret0IR raT

/- `scc_rt_abort` moved to another phase than the local overflow block: fails. -/
#guard !fnPhAll okPc (fun pc => if pc == (labT "scc_rt_abort").toBitVec.toNat then ph pc + 1 else ph pc) labT resT
  ret0IR raT

/- The abort's label unresolved: fails. -/
#guard !fnPhAll okPc ph labT (· != "scc_rt_abort") ret0IR raT

/- `labA` is `labT` on `scc_rt_abort`. -/
#guard labA "scc_rt_abort" == labT "scc_rt_abort"

theorem ret0_fnPhAll : fnPhAll okPc ph labA resT ret0IR raT = true := by decide +kernel

end Spike.Test.LowerA64PhCheck
