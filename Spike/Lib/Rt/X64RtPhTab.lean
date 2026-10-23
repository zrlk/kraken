/-
**The runtime's phase facts, as a table** (x86-64; `Scc/Cert/Rt/RtPhX64.lean`'s
`PhFact`): the facts of `Spike/Lib/Rt/X64RtTcb.lean`'s `TcbPh`,
`X64RtTake.lean`'s `TakePh`, `X64RtTi.lean`'s `TiPh` and
`X64RtMainU.lean`'s `MainPh` and `SwPh` that A6's pins (`phPins`), the
runtime's words' separation (A8) and the sites' distinctness do not give.
The twin of `Spike/Lib/Rt/A64RtPhTab.lean`, at byte offsets:

- every block's phase check (`PhFact.blk`) over the copies of the hand
  blocks (`Code.Tcb`, `Code.Take`, `Code.Ti`, `Code.Start`), each `ret`
  returning to its call's return point (`scc_rt_alloc_tcb` to
  `.Lscc_rt_start.x0`, `scc_rt_stack_take` to `.Lscc_rt_thread_init.x7`,
  `scc_rt_thread_init` to `.Lscc_rt_start.x1`), `.entry`'s check of
  `scc_rt_alloc_tcb` with its abort branch (`.full`) dead;
- `scc_rt_thread_init`'s pcs after its call named from `.entry` (its
  return point `.entry` + 12 is a program-numbered label, `.x7` in
  `ret0`, as `Code.Ti.x7L` and `Spike/Lib/Rt/X64RtTi.lean` name it);
- the single instructions without an event and the stores, with their
  sizes (`PhFact.step`), the atomic accesses' pcs off the sites
  (`PhFact.ok`), the abort branch off the check's jump (`PhFact.ne`), and
  `scc_rt_thread_init`'s pcs before the take (`PhFact.ph`, phase `12`);
- `_start`'s and `scc_rt_start`'s blocks and nodes up to the switch, with
  their pcs' phases (`13` before the TCB's allocation, `12` at `.x0`);
- the phases of `scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s pcs before
  the take and of the atomic accesses' ends (`tkPhTab`);
- `scc_rt_main`'s facts at `mc`, none without one (a program whose
  `scc_rt_main` is not today's shape still passes the rest).

The labels are fixed (`Spike/Lib/Rt/X64CodeIn.lean`), so the table is the
same in every output but `scc_rt_main`'s.
-/
import Spike.Lib.Rt.X64CodeIn
import Scc.Cert.Rt.RtPhX64

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (PhFact)
open Code

/-- `scc_rt_alloc_tcb`'s abort label, the check's one dead target. -/
abbrev tcbFullL : String := ".Lscc_rt_alloc_tcb.full"

/-- **`scc_rt_alloc_tcb`'s facts** (`TcbPh`): the blocks, the counter's
`lock xadd` (`.len` + 158) off the sites, and the phase indices at both
of its ends: `13` at it, `12` after it (the counter owned there, `ownOf`). -/
def tcbPhTab : List PhFact :=
  [.blk Tcb.fnL 0 Tcb.atPro none none, .blk Tcb.entryL 0 Tcb.atChk none (some tcbFullL),
    .blk Tcb.entryL 20 Tcb.atJ1 none none, .blk Tcb.lenL 0 Tcb.atL0 none none,
    .blk Tcb.lenL 14 Tcb.atL1 none none, .blk Tcb.lenL 32 Tcb.atL2 none none,
    .blk Tcb.lenL 50 Tcb.atL3 none none, .blk Tcb.lenL 68 Tcb.atL4 none none,
    .blk Tcb.lenL 99 Tcb.atL5 none none, .blk Tcb.lenL 135 Tcb.atL6 none none,
    .blk Tcb.lenL 146 Tcb.atArg none none, .blk Tcb.lenL 163 Tcb.atBnd none none,
    .blk Tcb.lenL 198 Tcb.atJ2 none none, .blk Tcb.okL 7 Tcb.atO1 none none,
    .blk Tcb.okL 38 Tcb.atO2 none none, .blk Tcb.okL 56 Tcb.atO3 none none,
    .blk Tcb.okL 77 Tcb.atO4 none none, .blk Tcb.okL 98 Tcb.atO5 none none,
    .blk Tcb.okL 143 Tcb.atRet (some (Start.x0L, 0)) none,
    .ne Tcb.entryL 20 tcbFullL 0,
    .step Tcb.lenL 11 3, .step Tcb.lenL 29 3, .step Tcb.lenL 47 3, .step Tcb.lenL 65 3, .step Tcb.lenL 95 4,
    .step Tcb.lenL 132 3, .step Tcb.lenL 139 7, .step Tcb.okL 0 7, .step Tcb.okL 34 4, .step Tcb.okL 53 3,
    .step Tcb.okL 74 3, .step Tcb.okL 95 3, .step Tcb.okL 140 3,
    .ok Tcb.lenL 158, .ph Tcb.lenL 158 13, .ph Tcb.lenL 163 12]

/-- **`scc_rt_stack_take`'s facts** (`TakePh`): the free count's load
(`.locked15` + 4) a single step; the phase indices at both ends of the
owned accesses (`ownOf`): the lock's `xchg` (`.spin14` + 11, `12` then
`14`), its release (`.bump` + 28, `14` then `12`), `scc_rt_stack_next`'s
store (`.bump` + 56, `12` then `8`), and the take site (`8` then `0`). -/
def takePhTab : List PhFact :=
  [.blk Take.fnL 0 Take.stPro none none, .blk Take.entryL 0 Take.stInit none none,
    .blk Take.clsL 0 Take.stCls none none, .blk Take.clsL 13 Take.stJ1 none none,
    .blk Take.doneL 7 Take.stFreeN none none, .blk Take.doneL 33 Take.stFree none none,
    .blk Take.doneL 59 Take.stLock none none, .blk Take.spinL 0 Take.stSwp none none,
    .blk Take.spinL 14 Take.stSpin none none, .blk Take.lockedL 0 Take.stLdN none none,
    .blk Take.lockedL 7 Take.stEmpty none none, .blk Take.bumpL 7 Take.stUnl none none,
    .blk Take.bumpL 38 Take.stAdd none none, .blk Take.bumpL 61 Take.stBnd none none,
    .blk Take.bumpL 108 Take.stJ2 none none, .blk Take.okL 7 Take.stOk none none,
    .blk Take.takenL 0 Take.stSite none none, .blk Take.siteL 1 Take.stRet (some (Ti.entryL, 12)) none,
    .step Take.doneL 0 7, .step Take.doneL 26 7, .step Take.doneL 52 7, .step Take.bumpL 0 7,
    .step Take.bumpL 31 7, .step Take.okL 0 7,
    .ok Take.spinL 11, .step Take.lockedL 4 3, .ok Take.bumpL 28, .ok Take.bumpL 56,
    .ph Take.spinL 11 12, .ph Take.spinL 14 14, .ph Take.bumpL 28 14, .ph Take.bumpL 31 12,
    .ph Take.bumpL 56 12, .ph Take.bumpL 61 8, .ph Take.siteL 0 8, .ph Take.siteL 1 0]

/-- **`scc_rt_thread_init`'s facts** (`TiPh`). -/
def tiPhTab : List PhFact :=
  [.blk Ti.fnL 0 Ti.tiPro none none, .blk Ti.entryL 0 Ti.tiArg none none, .blk Ti.entryL 7 Ti.callBlk none none,
    .blk Ti.entryL (12 + 0) Ti.tiSp none none, .blk Ti.entryL (12 + 51) Ti.tiF1 none none,
    .blk Ti.entryL (12 + 63) Ti.tiZ none none, .blk Ti.entryL (12 + 78) Ti.tiZ none none,
    .blk Ti.entryL (12 + 93) Ti.tiF4 none none, .blk Ti.entryL (12 + 105) Ti.tiF5 none none,
    .blk Ti.entryL (12 + 117) Ti.tiRet (some (Start.x1L, 0)) none,
    .step Ti.entryL (12 + 48) 3, .step Ti.entryL (12 + 59) 4, .step Ti.entryL (12 + 74) 4,
    .step Ti.entryL (12 + 89) 4, .step Ti.entryL (12 + 101) 4, .step Ti.entryL (12 + 113) 4,
    .ph Ti.fnL 0 12, .ph Ti.entryL 0 12, .ph Ti.entryL 7 12]

/-- **The switch's facts** (`SwPh`). -/
def swPhTab : List PhFact :=
  [.step Start.x1L 28 3, .step Start.x1L 31 2, .blk Start.x1L 33 Start.startMain none none]

/-- **`_start`'s and `scc_rt_start`'s facts up to the switch** (the start's
blocks and nodes, `Spike/Lib/Rt/X64Entry.lean`, `X64Segs.lean`): `_start`'s
`xorl` and `andq` and its call, the frame's setup, the handler's `lea`, the
arguments, the system call, the two calls' blocks (each `call` to its
callee's entry in the caller's phase), `.x1`'s block, `arch_prctl`'s
`syscall` and the block before the switch; the pcs before the take with
their phase index (`13` up to the TCB's allocation, `12` at `.x0`). -/
def startPhTab : List PhFact :=
  [.step "_start" 0 2, .step "_start" 2 4, .blk "_start" 6 Start.entryCall none none,
    .blk "scc_rt_start" 0 xStart0 none none, .step startE 0 7, .blk startE 7 xStartArgs none none,
    .step startE 41 2, .blk startE 43 Start.startCall none none, .blk Start.x0L 0 Start.startCall2 none none,
    .blk Start.x1L 0 Start.startFs none none, .step Start.x1L 18 2, .blk Start.x1L 20 Start.startSw none none,
    .ph "_start" 0 13, .ph "_start" 2 13, .ph "_start" 6 13, .ph "scc_rt_start" 0 13, .ph startE 0 13,
    .ph startE 7 13, .ph startE 41 13, .ph startE 43 13, .ph Start.x0L 0 12]

/-- **`scc_rt_main`'s facts at `mc`** (`MainPh`). -/
def mainPhTab (mc : MainCode) : List PhFact :=
  [.blk "scc_rt_main" 0 xHead none none, .blk mc.sc 0 (xLea mc.Z mc.zl) none none, .step mc.sc mc.zl mc.zf,
    .blk mc.sc (mc.zl + mc.zf) (xCmp mc.grow mc.z1 mc.z2) none none,
    .blk mc.sc (mc.zl + mc.zf + mc.z1 + mc.z2) (xFr mc.Z mc.zs mc.ps) none none,
    .blk mc.e0 0 (callB mc.fn) none none, .blk mc.sp0 0 (xExit mc.k mc.ze0 mc.ze1 mc.ze2) none none,
    .step mc.sp0 (mc.ze0 + mc.ze1 + mc.ze2) 2]

/-- `scc_rt_alloc_tcb`'s pcs before the take with their phase index, in
`Tcb.tcbPcs`' order (`blkPcs`, `stepPcs`, the `lock xadd` and its next pc). -/
def tcbTkRows : List (String × Nat × Nat) :=
  [(Tcb.fnL, 0, 13), (Tcb.entryL, 0, 13), (Tcb.entryL, 20, 13), (Tcb.lenL, 0, 13), (Tcb.lenL, 14, 13),
    (Tcb.lenL, 32, 13), (Tcb.lenL, 50, 13), (Tcb.lenL, 68, 13), (Tcb.lenL, 99, 13), (Tcb.lenL, 135, 13),
    (Tcb.lenL, 146, 13), (Tcb.lenL, 163, 12), (Tcb.lenL, 198, 12), (Tcb.okL, 7, 12), (Tcb.okL, 38, 12),
    (Tcb.okL, 56, 12), (Tcb.okL, 77, 12), (Tcb.okL, 98, 12), (Tcb.okL, 143, 12),
    (Tcb.lenL, 11, 13), (Tcb.lenL, 29, 13), (Tcb.lenL, 47, 13), (Tcb.lenL, 65, 13), (Tcb.lenL, 95, 13),
    (Tcb.lenL, 132, 13), (Tcb.lenL, 139, 13), (Tcb.okL, 0, 12), (Tcb.okL, 34, 12), (Tcb.okL, 53, 12),
    (Tcb.okL, 74, 12), (Tcb.okL, 95, 12), (Tcb.okL, 140, 12),
    (Tcb.lenL, 158, 13), (Tcb.lenL, 163, 12)]

/-- `scc_rt_stack_take`'s pcs before the take with their phase index, in
`Take.takePcs`' order (the nodes' up to the site, after the swap, the
release and the add, then `siPcs`). -/
def takeTkRows : List (String × Nat × Nat) :=
  [(Take.fnL, 0, 12), (Take.entryL, 0, 12), (Take.clsL, 0, 12), (Take.clsL, 13, 12), (Take.doneL, 7, 12),
    (Take.doneL, 33, 12), (Take.doneL, 59, 12), (Take.spinL, 0, 12), (Take.spinL, 11, 12), (Take.spinL, 14, 14),
    (Take.spinL, 14, 14), (Take.lockedL, 0, 14), (Take.lockedL, 4, 14), (Take.lockedL, 7, 14),
    (Take.bumpL, 7, 14), (Take.bumpL, 28, 14), (Take.bumpL, 31, 12), (Take.bumpL, 38, 12),
    (Take.bumpL, 56, 12), (Take.bumpL, 61, 8), (Take.bumpL, 61, 8), (Take.bumpL, 108, 8), (Take.okL, 7, 8),
    (Take.takenL, 0, 8), (Take.siteL, 0, 8),
    (Take.doneL, 0, 12), (Take.doneL, 26, 12), (Take.doneL, 52, 12), (Take.bumpL, 0, 14), (Take.bumpL, 31, 12),
    (Take.okL, 0, 8)]

/-- **The phase indices of `scc_rt_alloc_tcb`'s and `scc_rt_stack_take`'s
pcs before the take** (`TcbPh.noTk`, `TakePh.noTk` over `tcbPcs` and
`takePcs`: each in a phase with bit 3 set), and the atomic accesses' both
ends (`rmwIn`/`rmwUpd`, `swpIn`/`swpUpd`, `unlIn`/`unlUpd`,
`nxtIn`/`nxtUpd`: the owned counters by `ownOf`), and the take site and
its next pc (`siteOwn`, `tk1`): `13` up to the counter's `lock xadd`
(`.len` + 158), `12` after it and in `scc_rt_stack_take` up to the lock's
`xchg` (`.spin14` + 11), `14` holding the lock up to its release
(`.bump` + 28), `12` to `scc_rt_stack_next`'s store (`.bump` + 56), `8`
to the take site, `0` after it. Each row is `(label, offset, phase)`. -/
def tkPhTab : List PhFact :=
  (tcbTkRows ++ takeTkRows ++ [(Take.siteL, 1, 0)]).map fun (r : String × Nat × Nat) => .ph r.1 r.2.1 r.2.2

/-- **The runtime's phase facts**, `scc_rt_main`'s at `mc` if any. -/
def rtPhTab (mc : Option MainCode) : List PhFact :=
  tcbPhTab ++ takePhTab ++ tiPhTab ++ swPhTab ++ startPhTab ++ tkPhTab ++ match mc with
    | some mc => mainPhTab mc
    | none => []

end Spike.Lib.X64.Rt
