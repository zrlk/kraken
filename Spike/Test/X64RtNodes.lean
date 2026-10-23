/-
**`RtNodesOk` on `ret0.x`** (`Spike/Lib/Rt/X64RtNodes.lean`): the rows of
`ret0.x`'s placement data under the runtime's code groups (`rtCodeTab`)
pass their phase checks at the hand labels (`labT`), phase index (`ph`) and
off-site pcs (`okPc`) of `Spike/Lib/X64Ret0I.lean`, each function returning
where the main path calls it from, a row's dead targets those off its entry's
phase. The twin of `Spike/Test/A64RtNodes.lean`.
-/
import Spike.Lib.Rt.X64RtNodes
import Spike.Lib.Rt.X64CodeIn
import Spike.Lib.X64Ret0I
import Spike.Test.X64Ret0PlaceOK

namespace Spike.Lib.X64.Rt.Test

open Kraken
open Spike.Lib.X64.Rt Spike.Lib.X64.Flow.Ret0.Inst

/-- The rows of `ret0.x`'s placement data under the runtime's code groups. -/
def ret0RtRows : List Scc.Cert.Rt.X64.OGrp :=
  Scc.Cert.PlaceOK.X64.Test.ret0Place.blocks.filter fun g => (rtCodeTab bareMC).any fun r => r.l == g.l

/-- Every runtime group of `rtCodeTab` has its rows (x86-64's
`scc_rt_main` label carries code of its own, unlike AArch64's). -/
example : ((rtCodeTab bareMC).map (·.l)).filter (fun l => !(ret0RtRows.any (·.l == l))) = [] := by
  decide +kernel

/-- The return points on the main path: `scc_rt_alloc_tcb` to `.x0`,
`scc_rt_thread_init` to `.x1`, `scc_rt_stack_take` to `scc_rt_thread_init`'s
`.x7`; no `ret` elsewhere. -/
def ret0Ra : Label → Int64
  | ".Lscc_rt_alloc_tcb.ok" => labT ".Lscc_rt_start.x0"
  | ".Lscc_rt_thread_init.x7" => labT ".Lscc_rt_start.x1"
  | "scc_rt_take_site" => labT ".Lscc_rt_thread_init.x7"
  | _ => 0

/-- The take site's first row, its `nop` at offset 0 (unlike AArch64's
table, whose site group starts after it): skipped by `RtNodesOk`
(`siteBlk`), its pc a site (`okPc` false) whose obligation is `takeSiteW`'s;
its phase check alone fails. -/
example : ((ret0RtRows.find? (·.l == "scc_rt_take_site")).bind fun g => g.bs.head?.map fun b =>
    (b.off, decide (b.blk = siteBlk), rowPh okPc ph (fun _ _ _ => false) labT ret0Ra g b))
    = some (0, true, false) := by decide +kernel

/-- A row's dead targets: those off its entry's phase. -/
def ret0Dead (l : Label) (k : Nat) (t : Nat) : Bool :=
  ph t != ph (labT l + Int64.ofNat (((ret0RtRows.find? (·.l == l)).bind fun g =>
    (g.bs.find? (·.k == k)).map (·.off)).getD 0)).toBitVec.toNat

/-- **`ret0.x`'s runtime rows pass their phase checks.** -/
theorem ret0_rtNodesOk : RtNodesOk okPc ph ret0Dead labT ret0Ra ret0RtRows :=
  rtNodesOk_sound (by decide +kernel)

/-- A row with a phase crossing: `scc_rt_alloc_tcb`'s check branches to the
abort, off its phase; with no dead target the check fails. -/
example : rtNodesOk okPc ph (fun _ _ _ => false) labT ret0Ra ret0RtRows = false := by decide +kernel

end Spike.Lib.X64.Rt.Test
