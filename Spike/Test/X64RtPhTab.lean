/-
**The runtime's phase facts at `ret0`** (x86-64; `Spike/Lib/Rt/X64RtPhTab.lean`,
`Scc/Cert/Rt/RtPhX64.lean`): `ret0`'s cells pass the table, with and
without `scc_rt_main`'s facts; a table with a wrong fact fails. The twin of
`Spike/Test/A64RtPhTab.lean`.
-/
import Spike.Lib.Rt.X64RtPhTab
import Spike.Lib.Rt.X64RtPhOfTab
import Spike.Lib.X64Ret0Code

namespace Spike.Lib.X64.Rt.PhTabTest

open Scc.Cert.Rt.X64 (PhFact rtPhOk)
open Spike.Lib.X64.Rt (rtPhTab bareMC)
open SccCode (ret0Λ ret0Cells)

/-- **`ret0` passes the runtime's phase facts**, `scc_rt_main`'s at
`bareMC`. -/
theorem ret0_rtPhOk : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ (rtPhTab (some bareMC)) = true := by
  decide +kernel

/-- Without `scc_rt_main`'s facts. -/
theorem ret0_rtPhOk_none : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ (rtPhTab none) = true := by
  decide +kernel

/-- A wrong phase index fails. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ (rtPhTab none ++ [.ph "scc_rt_thread_init" 0 13]) = false := by
  decide +kernel

/-- A wrong phase index before the take fails: `scc_rt_alloc_tcb`'s first
pc after the counter's `lock xadd` at `13`, `scc_rt_stack_take`'s pc holding
the lock at `12`, the take site at `0`. -/
example : (rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph Spike.Lib.X64.Rt.Code.Tcb.lenL 198 13],
    rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph Spike.Lib.X64.Rt.Code.Take.lockedL 4 12],
    rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph Spike.Lib.X64.Rt.Code.Take.siteL 0 0]) = (false, false, false) := by
  decide +kernel

/-- A block crossing a phase without its dead target fails: `.entry`'s
check of `scc_rt_alloc_tcb` without the abort branch dead. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ
    [.blk Spike.Lib.X64.Rt.Code.Tcb.entryL 0 Spike.Lib.X64.Rt.Code.Tcb.atChk none none] = false := by
  decide +kernel

/-- A `ret` without its return address fails. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ
    [.blk Spike.Lib.X64.Rt.Code.Tcb.okL 143 Spike.Lib.X64.Rt.Code.Tcb.atRet none none] = false := by
  decide +kernel

/-- A `ret` to the wrong return point fails: `scc_rt_stack_take`'s return
into `scc_rt_thread_init` named at `.entry` (the take's phase) instead of
`.entry` + 12. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ
    [.blk Spike.Lib.X64.Rt.Code.Take.siteL 1 Spike.Lib.X64.Rt.Code.Take.stRet
      (some (Spike.Lib.X64.Rt.Code.Ti.entryL, 0)) none] = false := by
  decide +kernel

/-- `_start`'s pcs are before the TCB's allocation (phase `13`): `12` there
fails. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph "_start" 0 12] = false := by
  decide +kernel

/-- A call into another phase fails: `.entry`'s block with the call of
`scc_rt_thread_init` (phase `12`) in place of `scc_rt_alloc_tcb`'s (`13`).
(The blocks' code is `rtCodeOk`'s check, not this one's.) -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ
    [.blk ".Lscc_rt_start.entry" 43 Spike.Lib.X64.Rt.Code.Start.startCall2 none none] = false := by
  decide +kernel

/-- A step across the TCB's allocation fails: `.x0` (phase `12`) named as
the next pc of `.entry` + 43 (`13`). -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.step ".Lscc_rt_start.entry" 43 23] = false := by
  decide +kernel

/-- A label that does not resolve fails. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ok "no_such_label" 0] = false := by
  decide +kernel

/-- A pc on a site fails: the take site. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ok "scc_rt_take_site" 0] = false := by
  decide +kernel

/-! The generic glue (`Spike/Lib/Rt/X64RtPhOfTab.lean`): a fact of the
checked table back in the hand proofs' form, at any label map agreeing with
the code labels. -/

section Glue

open Spike.Lib.X64.Rt.PhOfTab
open Scc.Cert.Rt.X64 (factOk_of_rtPhOk)

variable {lab : Label → Int64}
  (hlab : ∀ l a, Scc.Sem.X64.codeLabel ret0Λ.code.lo ret0Cells l = some a → lab l = Int64.ofNat a)

include hlab in
/-- `scc_rt_thread_init`'s prologue (`TiPh.e`). -/
example : Spike.Lib.X64Consumer.blkPh (Scc.Cert.Rt.X64.okPcOf ret0Λ.code.lo ret0Cells ret0Λ)
    (Scc.Cert.Rt.X64.phOf ret0Λ.code.lo ret0Cells) (fun _ => false) lab
    (lab Spike.Lib.X64.Rt.Code.Ti.fnL + Int64.ofNat 0) 0 Spike.Lib.X64.Rt.Code.Ti.tiPro = true :=
  blkPh_of_factOk hlab (ra := none) (dead := none) (fun _ _ h => nomatch h) (fun _ h => nomatch h)
    (factOk_of_rtPhOk ret0_rtPhOk_none (by simp [rtPhTab, Spike.Lib.X64.Rt.tiPhTab]))

include hlab in
/-- `scc_rt_thread_init`'s first pc in the take's phase (`.ph`). -/
example : Scc.Cert.Rt.X64.phOf ret0Λ.code.lo ret0Cells (lab Spike.Lib.X64.Rt.Code.Ti.fnL + Int64.ofNat 0).toBitVec.toNat
    = 12 :=
  ph_of_factOk hlab (factOk_of_rtPhOk ret0_rtPhOk_none (by simp [rtPhTab, Spike.Lib.X64.Rt.tiPhTab]))

end Glue

/-- The atomic accesses' phase indices fail closed: the counter's `lock xadd`
at `12`, the lock's `xchg` or `scc_rt_stack_next`'s store at `13`, the take
site's next pc at `8`. -/
example : (rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph Spike.Lib.X64.Rt.Code.Tcb.lenL 158 12],
    rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph Spike.Lib.X64.Rt.Code.Take.spinL 11 13],
    rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph Spike.Lib.X64.Rt.Code.Take.bumpL 56 13],
    rtPhOk ret0Λ.code.lo ret0Cells ret0Λ [.ph Spike.Lib.X64.Rt.Code.Take.siteL 1 8]) =
      (false, false, false, false) := by
  decide +kernel

end Spike.Lib.X64.Rt.PhTabTest
