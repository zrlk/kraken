/-
**The x86-64 runtime's code checks in one pass** (`rtCodeOk`): the code
premises of `startU_segW` (`Spike/Lib/Rt/X64Segs.lean`) and of `_start`'s
`entry_segW'` (`entryIn`, `Spike/Lib/Rt/X64Entry.lean`), namely
`scc_rt_start`'s pieces (`startIn`, `startCallIn`, `startCall2In`,
`startTailIn`), `scc_rt_main`'s (`mainUIn` at a `MainCode`),
`scc_rt_alloc_tcb`'s (`allocTcbIn`), `scc_rt_thread_init`'s
(`threadInitIn`) and `scc_rt_stack_take`'s (`stackTakeIn`), as groups of
fixed code (`RGrp`) in program order (`rtCodeTab`), checked by one pass
over the cells (`rtIn`, `Scc/Cert/Rt/RtPassX64.lean`) instead of a search
per label.

- The groups and `rtCodeOk` live in `Spike/Lib/Rt/X64CodeIn.lean` over
  copies of the hand blocks, light enough for A11
  (`Scc/Cert/PlaceOKX64.lean`, which also maps the placement data's tail to
  a `MainCode`, `mcOf`); here the groups over the hand blocks, and
  `rtCodeTab_eq` (`rfl`): the copies are the hand blocks.
- `rtCodeOk cells mc`: the one boolean; `rtCodeIn_of_ok` gives every check
  back (`RtCodeIn`), one lemma per group (`startIn_of` …).
- The pass is separate from A7's (`Scc/Cert/Rt/X64RtIn.lean`): `scc_rt_main`'s
  groups name its return point, which A7's tail group also names, and the
  pass checks each label once.
- **Oracle**: `ret0_rtCodeOk` decides it on `ret0Cells` at `ret0MC`; its
  checks are the hand ones (`Spike/Test/X64RtCode.lean`).
-/
import Spike.Lib.Rt.X64Main

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Kraken.X64.Parser
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (startCallIn startCall2In startTailIn startCall startCall2 startFs startSw startMain
  x0L x1L)
open Scc.Cert.Rt.X64 (RGrp rtIn rtIn_sound RtAll RtAll.append BsOk GapAt)

/-! ## The groups over the hand blocks

The groups of `rtCodeTab` with the hand files' blocks, which the hand
checks name; `rtCodeTab_eq` is `rfl`: the copies are the hand blocks. -/

/-- `_start`'s and `scc_rt_start`'s groups: `_start`'s three instructions;
`scc_rt_start`'s frame's setup and the fall-through into `.entry`; the
handler, the arguments, the system call and the call of `scc_rt_alloc_tcb`
at `.entry`, `.x0` after it; the call of `scc_rt_thread_init` at `.x0`,
`.x1` after it; the tail at `.x1`. -/
def startGrpsH : List RGrp := [
  ⟨"_start", [(0, [(FI.toDir (.xor_rr32_self .rbp), 2)]), (2, [(andRsp (-16), 4)]),
    (6, (parse("call scc_rt_start")).zip [5])], none⟩,
  ⟨"scc_rt_start", [(0, xStart0)], some (8, startE)⟩,
  ⟨startE, [(0, [(siSig.toDir, 7)]), (7, xStartArgs), (41, [(op64 .syscall, 2)]), (43, startCall)], some (66, x0L)⟩,
  ⟨x0L, [(0, startCall2)], some (13, x1L)⟩,
  ⟨x1L, [(0, startFs), (18, [(op64 .syscall, 2)]), (20, startSw), (28, [(swDir .rax, 3)]),
    (31, [(FI.toDir (.xor_rr32_self .rbp), 2)]), (33, startMain)], none⟩]

/-- `scc_rt_main`'s groups at `mc`: the prologue's head and its
fall-through into the check, the check, the frame and the parameters'
stores and the fall-through into the body, `call fn` and the return point
after it, the `exit_group` tail there. -/
def mainUGrpsH (mc : MainCode) : List RGrp := [
  ⟨"scc_rt_main", [(0, xHead)], some (4, mc.sc)⟩,
  ⟨mc.sc, [(0, xLea mc.Z mc.zl), (mc.zl, [(fsDir .r11 8, mc.zf)]), (mc.zl + mc.zf, xCmp mc.grow mc.z1 mc.z2),
    (mc.zl + mc.zf + mc.z1 + mc.z2, xFr mc.Z mc.zs mc.ps)],
    some (mc.zl + mc.zf + mc.z1 + mc.z2 + mc.zs + szSum mc.ps, mc.e0)⟩,
  ⟨mc.e0, [(0, callB mc.fn)], some (5, mc.sp0)⟩,
  ⟨mc.sp0, [(0, xExit mc.k mc.ze0 mc.ze1 mc.ze2), (mc.ze0 + mc.ze1 + mc.ze2, [(op64 .syscall, 2)])], none⟩]

section Tcb

open Spike.Lib.X64.Flow.Ret0.AllocTcb

/-- `scc_rt_alloc_tcb`'s groups (`allocTcbIn`). -/
def tcbGrpsH : List RGrp := [
  ⟨fnL, [(0, atPro)], some (19, entryL)⟩,
  ⟨entryL, [(0, atChk), (20, atJ1)], none⟩,
  ⟨lenL, [(0, atL0), (11, [((FI.shr_cl .rax).toDir, 3)]), (14, atL1), (29, [((FI.and_rr .rax .rcx).toDir, 3)]),
    (32, atL2), (47, [((FI.shr_cl .rax).toDir, 3)]), (50, atL3), (65, [((FI.and_rr .rax .rcx).toDir, 3)]),
    (68, atL4), (95, [((FI.imul_rr .rax .rcx).toDir, 4)]), (99, atL5), (132, [((FI.shl_cl .rax).toDir, 3)]),
    (135, atL6), (139, [((SI.leaRip .rax "scc_rt_pinned_next").toDir, 7)]), (146, atArg), (158, rmwBlk),
    (163, atBnd), (198, atJ2)], none⟩,
  ⟨okL, [(0, [((SI.leaRip .rax "scc_rt_pinned").toDir, 7)]), (7, atO1), (34, [((FI.imul_rr .rax .rcx).toDir, 4)]),
    (38, atO2), (53, [((FI.shl_cl .rax).toDir, 3)]), (56, atO3), (74, [((FI.shl_cl .rax).toDir, 3)]), (77, atO4),
    (95, [((FI.or_rr .rax .rcx).toDir, 3)]), (98, atO5), (140, hdrBlk), (143, atRet)], none⟩]

end Tcb

section Ti

open Spike.Lib.X64.Flow.Ret0.ThreadInit

/-- `scc_rt_thread_init`'s groups (`threadInitIn`). -/
def tiGrpsH : List RGrp := [
  ⟨fnL, [(0, tiPro)], some (12, entryL)⟩,
  ⟨entryL, [(0, tiArg), (7, callBlk)], some (12, x7L)⟩,
  ⟨x7L, [(0, tiSp), (51, tiF1), (63, tiZ), (78, tiZ), (93, tiF4), (105, tiF5), (117, tiRet)] ++
    storeOff.zip storeBlks, none⟩]

end Ti

section Take

open Spike.Lib.X64.Flow.Ret0.StackTake

/-- `scc_rt_stack_take`'s groups (`stackTakeIn`). -/
def takeGrpsH : List RGrp := [
  ⟨fnL, [(0, stPro)], some (15, entryL)⟩,
  ⟨entryL, [(0, stInit)], none⟩,
  ⟨clsL, [(0, stCls), (13, stJ1)], none⟩,
  ⟨doneL, [(0, [((SI.leaRip .rax "scc_rt_stack_free_n").toDir, 7)]), (7, stFreeN),
    (26, [((SI.leaRip .rax "scc_rt_stack_free").toDir, 7)]), (33, stFree),
    (52, [((SI.leaRip .rax "scc_rt_stack_lock").toDir, 7)]), (59, stLock)], none⟩,
  ⟨spinL, [(0, stSwp), (11, (parse("xchgq %rax, (%rcx)")).zip [3]), (14, stSpin)], none⟩,
  ⟨lockedL, [(0, stLdN), (4, (parse("movq (%rcx), %rax")).zip [3]), (7, stEmpty)], none⟩,
  ⟨bumpL, [(0, [((SI.leaRip .rax "scc_rt_stack_lock").toDir, 7)]), (7, stUnl),
    (28, (parse("movq %rax, (%rcx)")).zip [3]), (31, [((SI.leaRip .rax "scc_rt_stack_next").toDir, 7)]),
    (38, stAdd), (56, (parse("lock xaddq %rax, (%rcx)")).zip [5]), (61, stBnd), (108, stJ2)], none⟩,
  ⟨okL, [(0, [((SI.leaRip .rax "scc_rt_stacks").toDir, 7)]), (7, stOk)], none⟩,
  ⟨takenL, [(0, stSite)], some (11, siteL)⟩,
  ⟨siteL, [(0, (parse("nop")).zip [1]), (1, stRet)], none⟩]

end Take

/-- **The runtime's code at `mc`**, in program order: `_start`,
`scc_rt_start`, `scc_rt_main`, `scc_rt_alloc_tcb`, `scc_rt_thread_init`,
`scc_rt_stack_take`. -/
def rtCodeTabH (mc : MainCode) : List RGrp := startGrpsH ++ mainUGrpsH mc ++ tcbGrpsH ++ tiGrpsH ++ takeGrpsH

/-- **The copies are the hand blocks**: the light table is the one over the
hand files' blocks. -/
theorem rtCodeTab_eq (mc : MainCode) : rtCodeTab mc = rtCodeTabH mc := rfl

/-- **The runtime's code checks of `startU_segW` and `entry_segW'`**, one
field each. -/
structure RtCodeIn (cells : List (Directive × Nat)) (mc : MainCode) : Prop where
  start0 : Code.Start.entryIn cells = true
  start : startIn cells = true
  call : startCallIn cells = true
  call2 : startCall2In cells = true
  tail : startTailIn cells = true
  main : mainUIn cells mc = true
  tcb : Ret0.AllocTcb.allocTcbIn cells = true
  ti : Ret0.ThreadInit.threadInitIn cells = true
  take : Ret0.StackTake.stackTakeIn cells = true

/-- `bareMC`'s side conditions of `startU_segW` other than the depth's. -/
theorem bareMC_ok : 0 ≤ bareMC.Z.toInt ∧ bareMC.Z.toInt % 8 = 0 ∧
    (∀ q ∈ bareMC.ps, Spike.Lib.offOk (-8 - bareMC.Z.toInt) 0 (-8 + q.2.1.toInt) = true) ∧
    Spike.Lib.offOk (-8 - bareMC.Z.toInt) 0 (-8 + bareMC.k.toInt) = true := by
  decide

/-! ## The checks from the pass -/

section Of

variable {cells : List (Directive × Nat)} {mc : MainCode}

/-- `_start`'s and `scc_rt_start`'s checks from their groups. -/
theorem start_of (h : RtAll cells startGrpsH) :
    Code.Start.entryIn cells = true ∧ startIn cells = true ∧ startCallIn cells = true ∧
      startCall2In cells = true ∧ startTailIn cells = true := by
  simp only [startGrpsH, RtAll, BsOk, GapAt, and_true] at h
  simp only [Code.Start.entryIn, Code.Start.entryXor, Code.Start.entryAnd, Code.Start.entryCall, startIn,
    startCallIn, startCall2In, startTailIn, h, Bool.and_self, and_self]

/-- `scc_rt_main`'s check from its groups. -/
theorem mainUIn_of (h : RtAll cells (mainUGrpsH mc)) : mainUIn cells mc = true := by
  simp only [mainUGrpsH, RtAll, BsOk, GapAt, and_true] at h
  simp only [mainUIn, prologueIn, exitIn, h, Bool.and_self]

/-- `scc_rt_alloc_tcb`'s check from its groups. -/
theorem allocTcbIn_of (h : RtAll cells tcbGrpsH) : Ret0.AllocTcb.allocTcbIn cells = true := by
  simp only [tcbGrpsH, RtAll, BsOk, GapAt, and_true] at h
  simp only [Ret0.AllocTcb.allocTcbIn, Ret0.AllocTcb.fiAt, Ret0.AllocTcb.siAt, h, Bool.and_self]

/-- `scc_rt_thread_init`'s check from its groups. -/
theorem threadInitIn_of (h : RtAll cells tiGrpsH) : Ret0.ThreadInit.threadInitIn cells = true := by
  simp only [tiGrpsH, Ret0.ThreadInit.storeOff, Ret0.ThreadInit.storeBlks, List.zip_cons_cons, List.zip_nil_left,
    List.cons_append, List.nil_append, RtAll, BsOk, GapAt, and_true] at h
  simp only [Ret0.ThreadInit.threadInitIn, Ret0.ThreadInit.storeOff, Ret0.ThreadInit.storeBlks,
    List.zip_cons_cons, List.zip_nil_left, List.all_cons, List.all_nil, h, Bool.and_self]

/-- `scc_rt_stack_take`'s check from its groups. -/
theorem stackTakeIn_of (h : RtAll cells takeGrpsH) : Ret0.StackTake.stackTakeIn cells = true := by
  simp only [takeGrpsH, RtAll, BsOk, GapAt, and_true] at h
  simp only [Ret0.StackTake.stackTakeIn, Ret0.AllocTcb.siAt, h, Bool.and_self]

/-- **Every check from the pass.** -/
theorem rtCodeIn_of_ok (h : rtCodeOk cells mc = true) : RtCodeIn cells mc := by
  have h := rtIn_sound h
  rw [rtCodeTab_eq] at h
  unfold rtCodeTabH at h
  obtain ⟨h, hk⟩ := RtAll.append h
  obtain ⟨h, hi⟩ := RtAll.append h
  obtain ⟨h, ht⟩ := RtAll.append h
  obtain ⟨hs, hm⟩ := RtAll.append h
  obtain ⟨h0, h1, h2, h3, h4⟩ := start_of hs
  exact ⟨h0, h1, h2, h3, h4, mainUIn_of hm, allocTcbIn_of ht, threadInitIn_of hi, stackTakeIn_of hk⟩

end Of

end Spike.Lib.X64.Rt
