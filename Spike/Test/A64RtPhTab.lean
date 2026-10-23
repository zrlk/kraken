/-
**The runtime's phase facts at `ret0`** (`Spike/Lib/Rt/A64RtPhTab.lean`,
`Scc/Cert/Rt/RtPhA64.lean`): `ret0`'s program passes the table, with and
without `scc_rt_main`'s facts; a table with a wrong fact fails; its facts
read through the consumer glue (`Spike/Lib/Rt/A64RtPhOfTab.lean`).
-/
import Spike.Lib.Rt.A64RtPhTab
import Spike.Lib.Rt.A64RtPhOfTab
import Spike.Lib.A64Ret0Code

namespace Spike.Lib.A64.Rt.PhTabTest

open Scc.Cert.Rt.A64 (PhFact rtPhOk)
open Spike.Lib.A64.Rt (rtPhTab bareMC)
open SccCode (ret0Λ ret0Prog)

/-- **`ret0` passes the runtime's phase facts**, `scc_rt_main`'s at
`bareMC`. -/
theorem ret0_rtPhOk : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ (rtPhTab (some bareMC)) = true := by
  decide +kernel

/-- Without `scc_rt_main`'s facts. -/
theorem ret0_rtPhOk_none : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ (rtPhTab none) = true := by
  decide +kernel

/-- A wrong phase index fails. -/
example : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ (rtPhTab none ++ [.ph "scc_rt_thread_init" 0 13]) = false := by
  decide +kernel

/-- A block crossing a phase without its dead target fails: `.0_entry`'s
check of `scc_rt_alloc_tcb` without the abort branch dead. -/
example : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ
    [.blk Spike.Lib.A64.Rt.Code.Tcb.entryL 0 Spike.Lib.A64.Rt.Code.Tcb.atChk none none] = false := by
  decide +kernel

/-- A `ret` without its return address fails. -/
example : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ
    [.blk Spike.Lib.A64.Rt.Code.Tcb.okL 30 Spike.Lib.A64.Rt.Code.Tcb.atRet none none] = false := by
  decide +kernel

/-- A label that does not resolve fails. -/
example : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ [.ok "no_such_label" 0] = false := by
  decide +kernel

/-- A pc on a site fails: the take site. -/
example : rtPhOk ret0Λ.code.lo ret0Prog ret0Λ [.ok "scc_rt_take_site" 0] = false := by
  decide +kernel

/-! The consumer glue (`Spike/Lib/Rt/A64RtPhOfTab.lean`): at any label map
agreeing with the loader's, `ret0`'s checked table gives the hand proofs'
forms. -/

section Glue

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (okPcOf phOf factOk_of_rtPhOk)
open Spike.Lib.A64.Rt.PhOfTab

variable {lab : Label → Int64}
  (hlab : ∀ l a, codeOf ret0Λ.code.lo ret0Prog l = some a → lab l = Int64.ofNat a)

include hlab in
/-- `scc_rt_thread_init`'s prologue passes `blkPh` (`TiPh.e`'s form). -/
example : Spike.Lib.A64Consumer.blkPh (okPcOf ret0Λ.code.lo ret0Prog ret0Λ) (phOf ret0Λ.code.lo ret0Prog)
    (fun _ => false) lab (lab Code.Ti.fnL + Int64.ofNat (4 * 0)) 0 Code.Ti.tiPro = true :=
  blkPh_of_factOk (ra := none) (dead := none) hlab (fun _ h => nomatch h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h)
    (factOk_of_rtPhOk ret0_rtPhOk_none (by simp [rtPhTab, Spike.Lib.A64.Rt.tiPhTab]))

include hlab in
/-- Its entry's phase index is `12`. -/
example : phOf ret0Λ.code.lo ret0Prog (lab Code.Ti.fnL + Int64.ofNat (4 * 0)).toBitVec.toNat = 12 :=
  ph_of_factOk hlab (factOk_of_rtPhOk (f := .ph Code.Ti.fnL 0 12) ret0_rtPhOk_none
    (by simp [rtPhTab, Spike.Lib.A64.Rt.tiPhTab]))

end Glue

end Spike.Lib.A64.Rt.PhTabTest
