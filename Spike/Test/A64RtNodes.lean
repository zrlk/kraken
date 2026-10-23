/-
**`RtNodesOk` on `ret0.w`** (`Spike/Lib/Rt/A64RtNodes.lean`): the rows of
`ret0.w`'s placement data under the runtime's code groups (`rtCodeTab`)
pass their phase checks at the hand labels (`labT`), phase index (`ph`) and
off-site pcs (`okPc`) of `Spike/Lib/A64Ret0I.lean`, each function returning
where the main path calls it from, a row's dead targets those off its entry's
phase.
-/
import Spike.Lib.Rt.A64RtNodes
import Spike.Lib.Rt.A64CodeIn
import Spike.Lib.A64Ret0I
import Spike.Test.A64Ret0PlaceOK

namespace Spike.Lib.A64.Rt.Test

open Spike.Lib.A64.Rt Spike.Lib.A64.Flow.Ret0.Inst

/-- The rows of `ret0.w`'s placement data under the runtime's code groups. -/
def ret0RtRows : List Scc.Cert.Rt.A64.OGrp :=
  Scc.Cert.PlaceOK.A64.Test.ret0Place.blocks.filter fun g => (rtCodeTab bareMC).any fun r => r.l == g.l

/-- Every runtime group of `rtCodeTab` has its rows but `scc_rt_main`'s
label, which falls through into its check without code of its own. -/
example : ((rtCodeTab bareMC).map (·.l)).filter (fun l => !(ret0RtRows.any (·.l == l))) = ["scc_rt_main"] := by
  decide +kernel

/-- The return points on the main path: `scc_rt_alloc_tcb` to `.sp2`,
`scc_rt_thread_init` to `.sp3`, `scc_rt_stack_take` to
`scc_rt_thread_init`'s `.sp0`; no `ret` elsewhere. -/
def ret0Ra : Label → Int64
  | ".L3_scc_rt_alloc_tcb.3_ok" => labT ".L0_scc_rt_start.sp2"
  | ".L5_scc_rt_thread_init.sp0" => labT ".L0_scc_rt_start.sp3"
  | "scc_rt_take_site" => labT ".L5_scc_rt_thread_init.sp0"
  | _ => 0

/-- A row's dead targets: those off its entry's phase. -/
def ret0Dead (l : Label) (k : Nat) (t : Nat) : Bool := ph t != ph (labT l + Int64.ofNat (4 * k)).toBitVec.toNat

/-- **`ret0.w`'s runtime rows pass their phase checks.** -/
theorem ret0_rtNodesOk : RtNodesOk okPc ph ret0Dead labT ret0Ra ret0RtRows :=
  rtNodesOk_sound (by decide +kernel)

/-- A row with a phase crossing: `scc_rt_alloc_tcb`'s check branches to the
abort, off its phase; with no dead target the check fails. -/
example : rtNodesOk okPc ph (fun _ _ _ => false) labT ret0Ra ret0RtRows = false := by decide +kernel

end Spike.Lib.A64.Rt.Test
