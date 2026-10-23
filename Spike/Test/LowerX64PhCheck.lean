import Spike.Lib.LowerX64.PhOfPlaceOK
import Spike.Lib.X64OwnLimRt
import Spike.Lib.X64Ret0I
import Spike.Test.LowerInvX64

/-!
# A9's phase part (`fnPhOk`) at `ret0.w` (x86-64)

`ret0.w`'s lowered `main` passes its phase facts (`fnPhAll`: the prologue's
`proPhOk`, the body's `bodyPhOk`, every label read resolving) at the hand
placement's tables (`Ret0.Inst.okPc`, `ph`, `labT`), the return address
`.Lscc_rt_main.x2`; it fails with no pc allowed, with the phases moved, with a
return into `scc_rt_stack_take`'s phase, and with a label the check reads
unresolved (the overflow branch, the check label, `scc_rt_abort`); and with
`scc_rt_abort` moved off the local overflow block's phase. The certificates
(`Spike/Test/Cert/X64*Cert.lean`) decide `fnPhOk` itself inside A9 at A6's
tables.
-/

namespace Spike.Test.LowerX64PhCheck

open Spike.Lib.LowerX64 Spike.Test.LowerInvX64
open Spike.Lib.X64.Flow.Ret0.Inst (okPc ph labT)

/-- The hand table's labels, with `scc_rt_abort` (the local overflow
block's call target, not in `labT`'s table) through `labIn`, so that the
kernel decides the check. -/
def labA (l : Label) : Int64 :=
  if l == "scc_rt_abort" then Spike.Lib.X64.OwnLimRt.labIn SccCode.ret0Λ.code.lo SccCode.ret0Cells l else labT l

/-- Every label resolves. -/
abbrev resT : String → Bool := fun _ => true

/- The labels the checks read: the prologue's growth branch, the body's
overflow branch. -/
#guard proLabs (Int64.ofInt 16) ".Lwc_main.stk" 5 3 2 4 [] == [".Lwc_main.stk"]
#guard blkLabs ovfBlk == ["scc_rt_abort"]
#guard ((bodyBlks SccCode.ret0Cells (frOf ret0IR mainF) ".Lwc_main.entry" 0
  (match mainF.blocks with | [b] => b.insts | _ => []) [.reg "y%0"]).flatMap (blkLabs ·.2)) ==
  [".Lwc_main.ovf"]

/- The hand tables: `main` passes. -/
#guard fnPhAll okPc ph labT resT SccCode.ret0Cells ret0IR (labT raL)

/- No pc allowed: fails. -/
#guard !fnPhAll (fun _ => false) ph labT resT SccCode.ret0Cells ret0IR (labT raL)

/- The phases moved off `main`'s check label: fails. -/
#guard !fnPhAll okPc (fun pc => if pc == (labT ".Lwc_main.chk").toBitVec.toNat then ph pc else ph pc + 1) labT resT
  SccCode.ret0Cells ret0IR (labT raL)

/- A return into `scc_rt_stack_take` (phase 12): fails. -/
#guard ph 4195700 == 12
#guard !fnPhAll okPc ph labT resT SccCode.ret0Cells ret0IR (Int64.ofNat 4195700)

/- The overflow label unresolved: fails. -/
#guard !fnPhAll okPc ph labT (· != ".Lwc_main.ovf") SccCode.ret0Cells ret0IR (labT raL)

/- `main`'s check label unresolved: fails. -/
#guard !fnPhAll okPc ph labT (· != ".Lwc_main.chk") SccCode.ret0Cells ret0IR (labT raL)

/- `scc_rt_abort` moved to another phase than the local overflow block: fails. -/
#guard !fnPhAll okPc (fun pc => if pc == (labT "scc_rt_abort").toBitVec.toNat then ph pc + 1 else ph pc) labT resT
  SccCode.ret0Cells ret0IR (labT raL)

/- The abort's label unresolved: fails. -/
#guard !fnPhAll okPc ph labT (· != "scc_rt_abort") SccCode.ret0Cells ret0IR (labT raL)

/- `labA` is `labT` on `scc_rt_abort`. -/
#guard labA "scc_rt_abort" == labT "scc_rt_abort"

theorem ret0_fnPhAll : fnPhAll okPc ph labA resT SccCode.ret0Cells ret0IR (labT raL) = true := by decide +kernel

end Spike.Test.LowerX64PhCheck
