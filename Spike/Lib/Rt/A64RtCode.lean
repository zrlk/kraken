/-
**The AArch64 runtime's code checks in one pass** (`rtCodeOk`): the code
premises of `startU_segW` (`Spike/Lib/Rt/A64Segs.lean`), namely
`scc_rt_start`'s pieces (`startIn`, `startCallIn`, `startTailIn`),
`scc_rt_main`'s (`mainUIn` at a `MainCode`), `scc_rt_alloc_tcb`'s
(`allocTcbIn`), `scc_rt_thread_init`'s (`threadInitIn`, `tiSpIn`) and
`scc_rt_stack_take`'s (`stackTakeIn`), and `_start`'s branch (`entry_segW'`),
as groups of fixed code (`RGrp`) in program order (`rtCodeTab`), checked by
one pass over the program (`rtIn`, `Scc/Cert/Rt/RtPassA64.lean`) instead of a
search per label.

- The groups and `rtCodeOk` live in `Spike/Lib/Rt/A64CodeIn.lean` over
  copies of the hand blocks, light enough for A11
  (`Scc/Cert/PlaceOKA64.lean`, which also maps the placement data's tail to
  a `MainCode`, `mcOf`); here the groups over the hand blocks, and
  `rtCodeTab_eq` (`rfl`): the copies are the hand blocks.
- `rtCodeOk prog mc`: the one boolean; `rtCodeIn_of_ok` gives every check
  back (`RtCodeIn`), one lemma per group (`start_of` …).
- **Against the x86-64 twin**: `RtCodeIn` has `_start`'s branch (`entry`)
  and `scc_rt_thread_init`'s fall-through into `.sp0` (`tiSp`), which the
  AArch64 proofs take as separate premises, and no `call2`: the call of
  `scc_rt_thread_init` is part of `startTailIn`.
- The pass is separate from A7's (`Scc/Cert/Rt/A64RtIn.lean`): `scc_rt_main`'s
  groups name its return point, which A7's tail group also names, and the
  pass checks each label once.
- **Oracle**: `ret0_rtCodeOk` decides it on `ret0Prog` at `ret0MC`; its
  checks are the hand ones (`Spike/Test/A64RtCode.lean`).
-/
import Spike.Lib.Rt.A64Main

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64 Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (startCallIn startTailIn tiSpIn entryB startCall startCall2 startSw0 startMain sp2L
  sp3L)
open Scc.Cert.Rt.A64 (RGrp rtIn rtIn_sound RtAll RtAll.append BsOk GapAt blockAt)

/-! ## The groups over the hand blocks

The groups of `rtCodeTab` with the hand files' blocks, which the hand
checks name; `rtCodeTab_eq` is `rfl`: the copies are the hand blocks. -/

/-- `_start`'s and `scc_rt_start`'s groups: the branch at `_start`; the
frame's setup and the fall-through into `.0_entry`; the handler, the
arguments, the system call and the call of `scc_rt_alloc_tcb` at
`.0_entry`, `.sp2` after it; the call of `scc_rt_thread_init` at `.sp2`,
`.sp3` after it; the switch and the call of `scc_rt_main` at `.sp3`. -/
def startGrpsH : List RGrp := [
  ⟨"_start", [(0, entryB)], none⟩,
  ⟨"scc_rt_start", [(0, Abort.b0)], some (4, startE)⟩,
  ⟨startE, labPair 0 sigign ++ [(2, startArgs), (8, [svcDir]), (9, startCall)], some (13, sp2L)⟩,
  ⟨sp2L, [(0, startCall2)], some (3, sp3L)⟩,
  ⟨sp3L, [(0, startSw0), (4, [(SI.msr .X10).toDir]), (5, [swDir .X9]), (6, startMain)], none⟩]

/-- `scc_rt_main`'s groups at `mc`: the fall-through into the check, the
check and the frame's setup and the fall-through into the body, `bl fn` and
the return point after it, the `exit_group` tail there. -/
def mainUGrpsH (mc : MainCode) : List RGrp := [
  ⟨"scc_rt_main", [], some (0, mc.sc)⟩,
  ⟨mc.sc, [(0, chkHead mc.Z), (2, [ldrDir .X10 .X10 8]), (3, chkBr mc.grow), (5, frameSet mc.Z [(.X0, 0)])],
    some (10, mc.e0)⟩,
  ⟨mc.e0, [(0, [blD mc.fn])], some (1, mc.sp0)⟩,
  ⟨mc.sp0, [(0, exitTail mc.k), (3, [svcDir])], none⟩]

section Tcb

open Spike.Lib.A64.Flow.Ret0.AllocTcb

/-- `scc_rt_alloc_tcb`'s groups (`allocTcbIn`). -/
def tcbGrpsH : List RGrp := [
  ⟨fnL, [(0, atPro)], some (6, entryL)⟩,
  ⟨entryL, [(0, atChk), (4, atJ1)], none⟩,
  ⟨lenL, [(0, atLen)] ++ labPair 32 "scc_rt_pinned_next" ++
    [(34, atArg), (37, [rmwDir]), (38, atBnd), (47, atJ2)], none⟩,
  ⟨okL, labPair 0 "scc_rt_pinned" ++ [(2, atOk), (29, [hdrDir]), (30, atRet)], none⟩]

end Tcb

section Ti

open Spike.Lib.A64.Flow.Ret0.ThreadInit

/-- `scc_rt_thread_init`'s groups (`threadInitIn`, `tiSpIn`). -/
def tiGrpsH : List RGrp := [
  ⟨fnL, [(0, tiPro)], some (5, entryL)⟩,
  ⟨entryL, [(0, tiCall)], some (2, spL)⟩,
  ⟨spL, [(0, tiSp), (11, parseAArch64("str x9, [x10]")), (12, tiF1),
    (14, parseAArch64("str x9, [x10, #8]")), (15, tiF2), (17, parseAArch64("str x9, [x10, #16]")),
    (18, tiF3), (20, parseAArch64("str x9, [x10, #24]")), (21, tiF4),
    (23, parseAArch64("str x9, [x10, #32]")), (24, tiF5), (26, parseAArch64("str x9, [x10, #40]")),
    (27, tiRet)], none⟩]

end Ti

section Take

open Spike.Lib.A64.Flow.Ret0.StackTake

/-- `scc_rt_stack_take`'s groups (`stackTakeIn`). -/
def takeGrpsH : List RGrp := [
  ⟨fnL, [(0, stPro)], some (5, entryL)⟩,
  ⟨entryL, [(0, stInit)], none⟩,
  ⟨clsL, [(0, stCls), (4, stJ1)], none⟩,
  ⟨doneL, labPair 0 "scc_rt_stack_free_n" ++ [(2, stFreeN)] ++ labPair 7 "scc_rt_stack_free" ++
    [(9, stFree)] ++ labPair 14 "scc_rt_stack_lock" ++ [(16, stLock)], none⟩,
  ⟨spinL, [(0, stSwp), (2, parseAArch64("swpal x9, x11, [x10]")), (3, stSpin)], none⟩,
  ⟨lockedL, [(0, stLdN), (1, parseAArch64("ldr x9, [x10]")), (2, stEmpty)], none⟩,
  ⟨bumpL, labPair 0 "scc_rt_stack_lock" ++ [(2, stUnl), (5, parseAArch64("stlr x9, [x10]"))] ++
    labPair 6 "scc_rt_stack_next" ++
    [(8, stAdd), (11, parseAArch64("ldaddal x9, x11, [x10]")), (12, stBnd), (21, stJ2)], none⟩,
  ⟨okL, labPair 0 "scc_rt_stacks" ++ [(2, stOk)], none⟩,
  ⟨takenL, [(0, stSite)], some (2, siteL)⟩,
  ⟨siteL, [(0, parseAArch64("nop")), (1, stRet)], none⟩]

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
structure RtCodeIn (prog : List Directive) (mc : MainCode) : Prop where
  entry : blockAt prog "_start" 0 entryB = true
  start : startIn prog = true
  call : startCallIn prog = true
  tail : startTailIn prog = true
  main : mainUIn prog mc = true
  tcb : Ret0.AllocTcb.allocTcbIn prog = true
  ti : Ret0.ThreadInit.threadInitIn prog = true
  tiSp : tiSpIn prog = true
  take : Ret0.StackTake.stackTakeIn prog = true

/-! ## The checks from the pass -/

section Of

variable {prog : List Directive} {mc : MainCode}

/-- `_start`'s and `scc_rt_start`'s checks from their groups. -/
theorem start_of (h : RtAll prog startGrpsH) :
    blockAt prog "_start" 0 entryB = true ∧ startIn prog = true ∧ startCallIn prog = true ∧
      startTailIn prog = true := by
  simp only [startGrpsH, labPair, List.cons_append, List.nil_append, Nat.reduceAdd, RtAll, BsOk, GapAt, and_true] at h
  simp only [startIn, startCallIn, startTailIn, h, Bool.and_self, and_self]

/-- `scc_rt_main`'s check from its groups. -/
theorem mainUIn_of (h : RtAll prog (mainUGrpsH mc)) : mainUIn prog mc = true := by
  simp only [mainUGrpsH, RtAll, BsOk, GapAt, and_true] at h
  simp only [mainUIn, prologueIn, exitIn, List.length_cons, List.length_nil, h, Bool.and_self]

/-- `scc_rt_alloc_tcb`'s check from its groups. -/
theorem allocTcbIn_of (h : RtAll prog tcbGrpsH) : Ret0.AllocTcb.allocTcbIn prog = true := by
  simp only [tcbGrpsH, labPair, List.cons_append, List.nil_append, Nat.reduceAdd, RtAll, BsOk, GapAt, and_true] at h
  simp only [Ret0.AllocTcb.allocTcbIn, h, Bool.and_self]

/-- `scc_rt_thread_init`'s checks from its groups. -/
theorem threadInitIn_of (h : RtAll prog tiGrpsH) :
    Ret0.ThreadInit.threadInitIn prog = true ∧ tiSpIn prog = true := by
  simp only [tiGrpsH, RtAll, BsOk, GapAt, and_true] at h
  simp only [Ret0.ThreadInit.threadInitIn, tiSpIn, h, Bool.and_self, and_self]

/-- `scc_rt_stack_take`'s check from its groups. -/
theorem stackTakeIn_of (h : RtAll prog takeGrpsH) : Ret0.StackTake.stackTakeIn prog = true := by
  simp only [takeGrpsH, labPair, List.cons_append, List.nil_append, Nat.reduceAdd, RtAll, BsOk, GapAt,
    and_true] at h
  simp only [Ret0.StackTake.stackTakeIn, Ret0.StackTake.labIn, h, Bool.and_self]

/-- **Every check from the pass.** -/
theorem rtCodeIn_of_ok (h : rtCodeOk prog mc = true) : RtCodeIn prog mc := by
  have h := rtIn_sound h
  rw [rtCodeTab_eq] at h
  unfold rtCodeTabH at h
  obtain ⟨h, hk⟩ := RtAll.append h
  obtain ⟨h, hi⟩ := RtAll.append h
  obtain ⟨h, ht⟩ := RtAll.append h
  obtain ⟨hs, hm⟩ := RtAll.append h
  obtain ⟨h0, h1, h2, h3⟩ := start_of hs
  obtain ⟨h5, h6⟩ := threadInitIn_of hi
  exact ⟨h0, h1, h2, h3, mainUIn_of hm, allocTcbIn_of ht, h5, h6, stackTakeIn_of hk⟩

end Of

end Spike.Lib.A64.Rt
