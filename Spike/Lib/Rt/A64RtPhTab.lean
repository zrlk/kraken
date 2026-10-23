/-
**The runtime's phase facts, as a table** (`Scc/Cert/Rt/RtPhA64.lean`'s
`PhFact`): the facts of `Spike/Lib/Rt/A64RtTcb.lean`'s `TcbPh`,
`A64RtTake.lean`'s `TakePh`, `A64RtTi.lean`'s `TiPh` and
`A64RtMainU.lean`'s `MainPh` and `SwPh` that A6's pins (`phPins`), the
runtime's words' separation (A8) and the sites' distinctness do not give:

- every block's phase check (`PhFact.blk`) over the copies of the hand
  blocks (`Code.Tcb`, `Code.Take`, `Code.Ti`, `Code.Start`), each `ret`
  returning to its call's return point (`scc_rt_alloc_tcb` to
  `.L0_scc_rt_start.sp2`, `scc_rt_stack_take` to
  `.L5_scc_rt_thread_init.sp0`, `scc_rt_thread_init` to
  `.L0_scc_rt_start.sp3`), `.0_entry`'s check of `scc_rt_alloc_tcb` with
  its abort branch dead;
- the single instructions without an event and the stores
  (`PhFact.step`), the atomic accesses' pcs off the sites (`PhFact.ok`),
  the abort branch off the check's jump (`PhFact.ne`), and
  `scc_rt_thread_init`'s entries before the take (`PhFact.ph`, phase `12`);
- `_start`'s and `scc_rt_start`'s blocks and nodes up to the switch, with
  their pcs' phases (`13` before the TCB's allocation, `12` at `.sp2`);
- `scc_rt_main`'s facts at `mc`, none without one (a program whose
  `scc_rt_main` is not today's shape still passes the rest).

The labels are fixed (`Spike/Lib/Rt/A64CodeIn.lean`), so the table is the
same in every output but `scc_rt_main`'s.
-/
import Spike.Lib.Rt.A64CodeIn
import Scc.Cert.Rt.RtPhA64

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (PhFact)
open Code

/-- **`scc_rt_alloc_tcb`'s facts** (`TcbPh`). -/
def tcbPhTab : List PhFact :=
  [.blk Tcb.fnL 0 Tcb.atPro none none, .blk Tcb.entryL 0 Tcb.atChk none (some ".L3_scc_rt_alloc_tcb.2_full"),
    .blk Tcb.entryL 4 Tcb.atJ1 none none, .blk Tcb.lenL 0 Tcb.atLen none none,
    .blk Tcb.lenL 34 Tcb.atArg none none, .blk Tcb.lenL 38 Tcb.atBnd none none,
    .blk Tcb.lenL 47 Tcb.atJ2 none none, .blk Tcb.okL 2 Tcb.atOk none none,
    .blk Tcb.okL 30 Tcb.atRet (some Start.sp2L) none,
    .ne Tcb.entryL 4 ".L3_scc_rt_alloc_tcb.2_full" 0,
    .step Tcb.lenL 32, .step Tcb.lenL 33, .step Tcb.okL 0, .step Tcb.okL 1, .step Tcb.okL 29,
    .ok Tcb.lenL 37]

/-- **`scc_rt_stack_take`'s facts** (`TakePh`): the free count's load
(`.5_locked15` + 1) a single step. -/
def takePhTab : List PhFact :=
  [.blk Take.fnL 0 Take.stPro none none, .blk Take.entryL 0 Take.stInit none none,
    .blk Take.clsL 0 Take.stCls none none, .blk Take.clsL 4 Take.stJ1 none none,
    .blk Take.doneL 2 Take.stFreeN none none, .blk Take.doneL 9 Take.stFree none none,
    .blk Take.doneL 16 Take.stLock none none, .blk Take.spinL 0 Take.stSwp none none,
    .blk Take.spinL 3 Take.stSpin none none, .blk Take.lockedL 0 Take.stLdN none none,
    .blk Take.lockedL 2 Take.stEmpty none none, .blk Take.bumpL 2 Take.stUnl none none,
    .blk Take.bumpL 8 Take.stAdd none none, .blk Take.bumpL 12 Take.stBnd none none,
    .blk Take.bumpL 21 Take.stJ2 none none, .blk Take.okL 2 Take.stOk none none,
    .blk Take.takenL 0 Take.stSite none none, .blk Take.siteL 1 Take.stRet (some Ti.spL) none,
    .step Take.doneL 0, .step Take.doneL 1, .step Take.doneL 7, .step Take.doneL 8, .step Take.doneL 14,
    .step Take.doneL 15, .step Take.bumpL 0, .step Take.bumpL 1, .step Take.bumpL 6, .step Take.bumpL 7,
    .step Take.okL 0, .step Take.okL 1,
    .ok Take.spinL 2, .step Take.lockedL 1, .ok Take.bumpL 5, .ok Take.bumpL 11]

/-- **`scc_rt_thread_init`'s facts** (`TiPh`). -/
def tiPhTab : List PhFact :=
  [.blk Ti.fnL 0 Ti.tiPro none none, .blk Ti.entryL 0 Ti.tiCall none none, .blk Ti.spL 0 Ti.tiSp none none,
    .blk Ti.spL 12 Ti.tiF1 none none, .blk Ti.spL 15 Ti.tiF2 none none, .blk Ti.spL 18 Ti.tiF3 none none,
    .blk Ti.spL 21 Ti.tiF4 none none, .blk Ti.spL 24 Ti.tiF5 none none,
    .blk Ti.spL 27 Ti.tiRet (some Start.sp3L) none,
    .step Ti.spL 11, .step Ti.spL 14, .step Ti.spL 17, .step Ti.spL 20, .step Ti.spL 23, .step Ti.spL 26,
    .ph Ti.fnL 0 12, .ph Ti.entryL 0 12]

/-- **The switch's facts** (`SwPh`). -/
def swPhTab : List PhFact :=
  [.step Start.sp3L 5, .blk Start.sp3L 6 Start.startMain none none]

/-- **`_start`'s and `scc_rt_start`'s facts up to the switch** (the start's
blocks and nodes, `Spike/Lib/Rt/A64RtStartU.lean`): `_start`'s branch, the
frame's setup, the handler's address pair, the arguments and the system
call, the two calls' blocks (each `bl` to its callee's entry in the
caller's phase), `.sp3`'s loads and the thread pointer's `msr`; the pcs
before the take with their phase index (`13` up to the TCB's allocation,
`12` at `.sp2`). -/
def startPhTab : List PhFact :=
  [.blk "_start" 0 Start.entryB none none, .blk "scc_rt_start" 0 Abort.b0 none none,
    .step startE 0, .step startE 1, .blk startE 2 startArgs none none, .step startE 8,
    .blk startE 9 Start.startCall none none, .blk Start.sp2L 0 Start.startCall2 none none,
    .blk Start.sp3L 0 Start.startSw0 none none, .step Start.sp3L 4,
    .ph "_start" 0 13, .ph "scc_rt_start" 0 13, .ph startE 0 13, .ph startE 1 13, .ph startE 2 13,
    .ph startE 8 13, .ph startE 9 13, .ph Start.sp2L 0 12]

/-- **`scc_rt_main`'s facts at `mc`** (`MainPh`). -/
def mainPhTab (mc : MainCode) : List PhFact :=
  [.blk mc.sc 0 (chkHead mc.Z) none none, .step mc.sc 2, .blk mc.sc 3 (chkBr mc.grow) none none,
    .blk mc.sc 5 (frameSet mc.Z [(.X0, 0)]) none none, .blk mc.e0 0 [blD mc.fn] none none,
    .blk mc.sp0 0 (exitTail mc.k) none none, .step mc.sp0 3]

/-- **The runtime's phase facts**, `scc_rt_main`'s at `mc` if any. -/
def rtPhTab (mc : Option MainCode) : List PhFact :=
  tcbPhTab ++ takePhTab ++ tiPhTab ++ swPhTab ++ startPhTab ++ match mc with
    | some mc => mainPhTab mc
    | none => []

end Spike.Lib.A64.Rt
