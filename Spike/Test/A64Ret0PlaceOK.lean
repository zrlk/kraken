import Scc.Cert.PlaceOKA64
import Spike.Lib.A64Ret0Code
import Spike.Lib.A64Hello1Code
import Spike.Test.A64Ret0Offs
import Spike.Lib.A64Ret0
import Spike.Lib.A64Print
import Spike.Lib.A64Abort
import Scc.Lower.SpecA64
import Spike.Lib.Ret0Src
import Spike.Lib.Hello1Src

/-!
# `PlaceOK` against the hand checks of `ret0.w` and `hello1.w`

One kernel decision of `PlaceOK` (`Scc/Cert/PlaceOKA64.lean`) for
`ret0.w`, `ret0_placeOK` (one decision shares the reductions of the program
its parts would repeat; `placeOK_of` combines parts decided apart, for
larger programs), and each of the hand checks of
`Spike/Lib/A64Ret0Code.lean` re-derived from it by an extraction lemma, at
the hand statement: the components cover the hand facts, and the facts
follow without another decision.

`hello1.w` fails `PlaceOK` (`hello1_placeOK`): its `scc_rt_main` tail is
after a setup block, for which A11 has no `MainCode` yet. Its other
components are decided in one declaration (`hello1_parts`), and the hand
checks of `Spike/Lib/A64Hello1Code.lean` re-derived from them.

The block table of the placement data is the hand table `ret0T`
(`hello1T`) with the static offsets the analyser gives its blocks
(`ret0Offs`, `Spike/Test/A64Ret0Offs.lean`), zipped by `ofGrps`, and each
group's instructions in no block (`ret0Evs`, `withEvs`); the table is the
hand one again by `toGrps_withEvs` and `toGrps_ofGrps`.
-/

namespace Scc.Cert.PlaceOK.A64.Test

open Kraken Kraken.Promising.AArch64 Scc.Cert.Rt.A64 Scc.Cert.Link.A64 SccCode

/-! ## ret0 -/

/-- `ret0.w`'s placement data: its block table with its offsets, stack need and `scc_rt_main`'s tail. -/
def ret0Place : PlaceData :=
  { blocks := withEvs (ofGrps ret0T ret0Offs) ret0Evs, need := ret0Need, tail := .bare,
    ir := some (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Ret0Src.ret0Src).low.ir }

/-- **`ret0.w`'s `PlaceOK`**, one kernel decision. The output is written out, so that the extraction
lemmas' `o.prog` reduces to `ret0Prog` by projection. -/
theorem ret0_placeOK : placeOK Config.canonical ⟨ret0Prog, ret0Secs, [], ret0Place⟩ = true := by decide +kernel

example : ret0Λ.WF := (wf_link_of_placeOK ret0Imms ret0_placeOK :)
example : abortsIn ret0Prog ret0Λ = true := (abortsIn_link_of_placeOK ret0Imms ret0_placeOK :)
example : imageIn ret0Prog ret0Secs ret0Λ = true := (imageIn_link_of_placeOK ret0Imms ret0_placeOK :)
example : loadOk ret0Λ ret0Prog ret0Secs = true := (loadOk_link_of_placeOK ret0Imms ret0_placeOK :)
example : Scc.Sem.Entry.linux.clear ret0Λ = true := (clear_link_of_placeOK ret0Imms ret0_placeOK :)
example : Scc.Cert.WideA64.wideIn ret0Prog = true := (wideIn_of_placeOK ret0_placeOK :)
example : blocksIn ret0Prog ret0T := by
  have h := blocksIn_of_placeOK ret0_placeOK
  simp only [ret0Place, toGrps_withEvs, toGrps_ofGrps] at h
  exact h
example : coverOk ret0Prog ret0Place.blocks = true := by
  have h := cover_of_placeOK ret0_placeOK
  simp only at h
  exact h
example : Scc.Cert.Rt.A64.Abort.abortIn ret0Prog = true := (abortIn_of_placeOK ret0_placeOK :)
example : Scc.Cert.Rt.A64.Print.printIn ret0Prog = true := (printIn_of_placeOK ret0_placeOK :)
example : Scc.Cert.Rt.A64.Abort.mainIn0 ret0Prog = true := (mainIn0_of_placeOK ret0_placeOK rfl :)
example : Scc.Cert.NeedA64.needOk ret0Prog ret0Need 12288 ["scc_rt_main"] = true :=
  (needOk_of_placeOK ret0_placeOK :)

/-! ### ret0's `block_spec` coverage checks

Each hand `block_spec`'s `_ok` (`okBlk lo hi o blk`, by `decide`) whose
region and offsets are the row's, re-derived from `ret0_placeOK` (A5) by a
lookup of its row (`rowIn`), and `startMain_ok` in its wider hand region
(`okBlk_mono`). The other hand checks state weaker offsets than the rows
(the rows also know `x29`'s, after the frame record) or, in `scc_rt_main`
and `wc_main`, a smaller region; the rows' checks are at the rows'. -/

section Blocks

open Spike.Lib.A64.Flow Spike.Lib.A64

example : okBlk (-48) 0 Abort.oE Abort.b0 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Abort.oE, Abort.b0⟩)
    (l := "scc_rt_abort_threads") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Abort.oI Abort.b2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨8, (-48), 0, Abort.oI, Abort.b2⟩)
    (l := ".L17_scc_rt_abort_threads.0_entry") ret0_placeOK (by decide +kernel)
example : okBlk (-32) 0 Abort.oE Abort.Disp.d0 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-32), 0, Abort.oE, Abort.Disp.d0⟩)
    (l := "scc_rt_abort") ret0_placeOK (by decide +kernel)
example : okBlk (-192) 0 Ret0.AllocTcb.oI Ret0.AllocTcb.atBnd = true :=
  okBlk_of_rowIn_placeOK (b := ⟨38, (-192), 0, Ret0.AllocTcb.oI, Ret0.AllocTcb.atBnd⟩)
    (l := ".L3_scc_rt_alloc_tcb.1_len") ret0_placeOK (by decide +kernel)
example : okBlk (-192) 0 Ret0.AllocTcb.oI Ret0.AllocTcb.atJ2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨47, (-192), 0, Ret0.AllocTcb.oI, Ret0.AllocTcb.atJ2⟩)
    (l := ".L3_scc_rt_alloc_tcb.1_len") ret0_placeOK (by decide +kernel)
example : okBlk (-192) 0 Ret0.AllocTcb.oI Ret0.AllocTcb.atOk = true :=
  okBlk_of_rowIn_placeOK (b := ⟨2, (-192), 0, Ret0.AllocTcb.oI, Ret0.AllocTcb.atOk⟩)
    (l := ".L3_scc_rt_alloc_tcb.3_ok") ret0_placeOK (by decide +kernel)
example : okBlk (-192) 0 Ret0.AllocTcb.oE Ret0.AllocTcb.atPro = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-192), 0, Ret0.AllocTcb.oE, Ret0.AllocTcb.atPro⟩)
    (l := "scc_rt_alloc_tcb") ret0_placeOK (by decide +kernel)
example : okBlk (-192) 0 Ret0.AllocTcb.oI Ret0.AllocTcb.atRet = true :=
  okBlk_of_rowIn_placeOK (b := ⟨30, (-192), 0, Ret0.AllocTcb.oI, Ret0.AllocTcb.atRet⟩)
    (l := ".L3_scc_rt_alloc_tcb.3_ok") ret0_placeOK (by decide +kernel)
example : okBlk 0 0 Abort.oE Ret0.entryB = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, 0, Abort.oE, Ret0.entryB⟩) (l := "_start") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stAdd = true :=
  okBlk_of_rowIn_placeOK (b := ⟨8, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stAdd⟩)
    (l := ".L6_scc_rt_stack_take.7_bump") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stBnd = true :=
  okBlk_of_rowIn_placeOK (b := ⟨12, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stBnd⟩)
    (l := ".L6_scc_rt_stack_take.7_bump") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stEmpty = true :=
  okBlk_of_rowIn_placeOK (b := ⟨2, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stEmpty⟩)
    (l := ".L6_scc_rt_stack_take.5_locked15") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stJ2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨21, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stJ2⟩)
    (l := ".L6_scc_rt_stack_take.7_bump") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stLdN = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stLdN⟩)
    (l := ".L6_scc_rt_stack_take.5_locked15") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stOk = true :=
  okBlk_of_rowIn_placeOK (b := ⟨2, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stOk⟩)
    (l := ".L6_scc_rt_stack_take.9_ok") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oE Ret0.StackTake.stPro = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-208), 0, Ret0.StackTake.oE, Ret0.StackTake.stPro⟩)
    (l := "scc_rt_stack_take") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stRet = true :=
  okBlk_of_rowIn_placeOK (b := ⟨1, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stRet⟩)
    (l := "scc_rt_take_site") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stSite = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stSite⟩)
    (l := ".L6_scc_rt_stack_take.10_taken") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stSpin = true :=
  okBlk_of_rowIn_placeOK (b := ⟨3, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stSpin⟩)
    (l := ".L6_scc_rt_stack_take.4_spin14") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stSwp = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stSwp⟩)
    (l := ".L6_scc_rt_stack_take.4_spin14") ret0_placeOK (by decide +kernel)
example : okBlk (-208) 0 Ret0.StackTake.oI Ret0.StackTake.stUnl = true :=
  okBlk_of_rowIn_placeOK (b := ⟨2, (-208), 0, Ret0.StackTake.oI, Ret0.StackTake.stUnl⟩)
    (l := ".L6_scc_rt_stack_take.7_bump") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Abort.oI Ret0.startCall2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Abort.oI, Ret0.startCall2⟩)
    (l := ".L0_scc_rt_start.sp2") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Abort.oI Ret0.startCall = true :=
  okBlk_of_rowIn_placeOK (b := ⟨9, (-48), 0, Abort.oI, Ret0.startCall⟩)
    (l := ".L0_scc_rt_start.0_entry") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Abort.oI Ret0.startSw0 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Abort.oI, Ret0.startSw0⟩)
    (l := ".L0_scc_rt_start.sp3") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Ret0.ThreadInit.oE Ret0.ThreadInit.tiPro = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Ret0.ThreadInit.oE, Ret0.ThreadInit.tiPro⟩)
    (l := "scc_rt_unpark") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oE Print.b0 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Print.oE, Print.b0⟩) (l := "scc_rt_print") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b10 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨7, (-48), 0, Print.oI, Print.b10⟩)
    (l := ".L9_scc_rt_print.3_chk2") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b11 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Print.oI, Print.b11⟩)
    (l := ".L9_scc_rt_print.4_chk3") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b12 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, (-48), 0, Print.oI, Print.b12⟩)
    (l := ".L9_scc_rt_print.4_chk3") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b13 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Print.oI, Print.b13⟩)
    (l := ".L9_scc_rt_print.5_adv") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b14 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Print.oI, Print.b14⟩)
    (l := ".L9_scc_rt_print.6_fail") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b16 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Print.oI, Print.b16⟩)
    (l := ".L11_scc_rt_unpark.2_done") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Print.oI, Print.b2⟩)
    (l := ".L9_scc_rt_print.1_loop") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b3 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, (-48), 0, Print.oI, Print.b3⟩)
    (l := ".L9_scc_rt_print.1_loop") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b4 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, (-48), 0, Print.oI, Print.b4⟩)
    (l := ".L9_scc_rt_print.2_write") ret0_placeOK (by decide +kernel)
example : okBlk (-48) 0 Print.oI Print.b7 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨13, (-48), 0, Print.oI, Print.b7⟩)
    (l := ".L9_scc_rt_print.2_write") ret0_placeOK (by decide +kernel)
/-- `Ret0.startMain_ok`: the row's region `[0, 0)` is inside the hand one. -/
example : okBlk (-80) 0 SO.entry Ret0.startMain = true :=
  okBlk_mono (by decide) (by decide)
    (okBlk_of_rowIn_placeOK (b := ⟨6, 0, 0, SO.entry, Ret0.startMain⟩)
      (l := ".L0_scc_rt_start.sp3") ret0_placeOK (by decide +kernel))

end Blocks

/-! ## hello1 -/

/-- `hello1.w`'s placement data: its block table with its offsets, stack need and `scc_rt_main`'s tail. -/
def hello1Place : PlaceData :=
  { blocks := withEvs (ofGrps hello1T hello1Offs) hello1Evs, need := hello1Need, tail := .setup,
    ir := some (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Hello1Src.hello1Src).low.ir }

/-- `hello1.w`'s output. Written out, so that the components' `o.prog` reduces to `hello1Prog` by
projection. -/
abbrev hello1O : Out := ⟨hello1Prog, hello1Secs, [], hello1Place⟩

/-- **`hello1.w` fails `PlaceOK`**: `scc_rt_main`'s tail is after a setup block (`.setup`), for which A11
has no `MainCode` yet (`mcOf .setup = none`), so A11 is `false` by evaluation. -/
theorem hello1_placeOK : placeOK Config.canonical hello1O = false :=
  placeOK_eq_false_of_a11 rfl

/-- `hello1.w`'s components other than A11 (A9 is `true`), one kernel decision. -/
theorem hello1_parts : (a1 hello1O (tablesOf Config.canonical hello1O) &&
    a2 hello1O (tablesOf Config.canonical hello1O) &&
    a3 hello1O (tablesOf Config.canonical hello1O) && a4 Config.canonical hello1O (tablesOf Config.canonical hello1O) &&
    a5 hello1O (tablesOf Config.canonical hello1O) && a6 hello1O (tablesOf Config.canonical hello1O) &&
    a7 hello1O (tablesOf Config.canonical hello1O) && a8 hello1O (tablesOf Config.canonical hello1O)) = true := by
  decide +kernel

private theorem hello1_a1 : (PlaceOK.a1 (tablesOf Config.canonical hello1O) &&
    Scc.Cert.PlaceOK.layoutOk hello1O.secs (tablesOf Config.canonical hello1O).Λ) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (h.1.1.1.1.1.1.1 : (((PlaceOK.a1 _ && _) && _) && _) = true)).1).1
private theorem hello1_a2 : (loadOk (linkOf hello1Prog hello1Secs) hello1Prog hello1Secs &&
    abortsIn hello1Prog (linkOf hello1Prog hello1Secs) && imageIn hello1Prog hello1Secs (linkOf hello1Prog hello1Secs))
      = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.2
private theorem hello1_a3 :
    (decide (blocksIn hello1Prog (toGrps hello1Place.blocks)) && coverOk hello1Prog hello1Place.blocks) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.2
private theorem hello1_a4 : (Scc.Cert.WideA64.wideIn hello1Prog &&
    Scc.Cert.NeedA64.needOk hello1Prog hello1Need 12288 ["scc_rt_main"]) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.2
private theorem hello1_a7 : rtIn hello1Prog (RtIn.rtTab RtIn.mainGrps1) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h
  exact (Bool.and_eq_true_iff.mp (h.1.2 : (rtIn hello1Prog (RtIn.rtTab RtIn.mainGrps1) && _) = true)).1

example : hello1Λ.WF := by
  have h := hello1_a1; simp only [Bool.and_eq_true] at h; exact Scc.Cert.PlaceOK.wf_withImms (wf_of_a1 h.1) _
example : abortsIn hello1Prog hello1Λ = true := by
  have h := hello1_a2; simp only [Bool.and_eq_true] at h
  exact (abortsIn_withImms (linkOf hello1Prog hello1Secs) hello1Imms hello1Prog).trans h.1.2
example : imageIn hello1Prog hello1Secs hello1Λ = true := by
  have h := hello1_a2; simp only [Bool.and_eq_true] at h
  exact (imageIn_withImms (linkOf hello1Prog hello1Secs) hello1Imms hello1Prog hello1Secs).trans h.2
example : loadOk hello1Λ hello1Prog hello1Secs = true := by
  have h := hello1_a2; simp only [Bool.and_eq_true] at h
  exact (loadOk_withImms (linkOf hello1Prog hello1Secs) hello1Imms hello1Prog hello1Secs).trans h.1.1
example : Scc.Sem.Entry.linux.clear hello1Λ = true := by
  have h := hello1_a1; simp only [Bool.and_eq_true] at h
  exact (clear_withImms (linkOf hello1Prog hello1Secs) hello1Imms).trans
    (Scc.Cert.PlaceOK.clear_of_below32 (Scc.Cert.PlaceOK.below32_of_layoutOk h.2))
example : Scc.Cert.WideA64.wideIn hello1Prog = true := by
  have h := hello1_a4; simp only [Bool.and_eq_true] at h; exact h.1
example : blocksIn hello1Prog hello1T := by
  have h := hello1_a3
  simp only [Bool.and_eq_true, decide_eq_true_eq, hello1Place, toGrps_withEvs, toGrps_ofGrps] at h
  exact h.1
example : coverOk hello1Prog hello1Place.blocks = true := by
  have h := hello1_a3; simp only [Bool.and_eq_true] at h; exact h.2
example : Scc.Cert.Rt.A64.Abort.abortIn hello1Prog = true := RtIn.abortIn_of_rtIn hello1_a7
example : Scc.Cert.Rt.A64.Print.printIn hello1Prog = true := RtIn.printIn_of_rtIn hello1_a7
example : Scc.Cert.Rt.A64.Abort.mainIn hello1Prog = true := RtIn.mainIn_of_rtIn hello1_a7
example : Scc.Cert.NeedA64.needOk hello1Prog hello1Need 12288 ["scc_rt_main"] = true := by
  have h := hello1_a4; simp only [Bool.and_eq_true] at h; exact h.2

/-! ## A wrong table is rejected

Each part decides `false` on a wrong table, so `PlaceOK` does: its
conjunction is `false` (`placeOK_eq_false_of_a3`, `…_a5`, `…_a7`, `…_a8`,
`…_a11`). -/

/-- A block table with a block that is not in the program fails A3. -/
example : placeOK Config.canonical
    ⟨ret0Prog, ret0Secs, [], { ret0Place with blocks := [⟨"scc_rt_main", [⟨0, 0, 0, ⟨0, []⟩, [.label "x"]⟩], []⟩] }⟩
      = false :=
  placeOK_eq_false_of_a3 (by decide +kernel)

/-- An empty block table fails A3: the program's instructions are in no
row (`coverOk`). -/
example : placeOK Config.canonical ⟨ret0Prog, ret0Secs, [], { ret0Place with blocks := [] }⟩ = false :=
  placeOK_eq_false_of_a3 (by decide +kernel)

/-- The block table without its single instructions fails A3: the
instructions between blocks are in no row. -/
example : placeOK Config.canonical
    ⟨ret0Prog, ret0Secs, [], { ret0Place with blocks := ofGrps ret0T ret0Offs }⟩ = false :=
  placeOK_eq_false_of_a3 (by decide +kernel)

/-- Offsets under which a block is not covered fail A5: `ret0`'s table with
every row at `sp`'s entry offset and an empty region. -/
example : placeOK Config.canonical
    ⟨ret0Prog, ret0Secs, [], { ret0Place with blocks := ofGrps ret0T [] }⟩ = false :=
  placeOK_eq_false_of_a5 (by decide +kernel)

/-- An output without its IR fails A9. -/
example : placeOK Config.canonical ⟨ret0Prog, ret0Secs, [], { ret0Place with ir := none }⟩ = false :=
  placeOK_eq_false_of_a9 rfl

/-- `ret0.w`'s IR against `hello1.w`'s listing fails A9 (`main`'s code block is not there). -/
example : placeOK Config.canonical ⟨hello1Prog, hello1Secs, [], { hello1Place with ir := ret0Place.ir }⟩ = false :=
  placeOK_eq_false_of_a9 (by decide +kernel)

/-- The wrong tail shape fails A7. -/
example : placeOK Config.canonical ⟨ret0Prog, ret0Secs, [], { ret0Place with tail := .setup }⟩ = false :=
  placeOK_eq_false_of_a7 (by decide +kernel)

/-- A7's abort path phase check (`abortPhC`) holds on `ret0.w` at its link
and fails closed: with the heap abort's label at the overflow stub's first
instruction (a site there, so that pc is not off the sites), and with the
dispatcher's `.L12_scc_rt_abort.1_is0` renamed (a branch target that does not
resolve). -/
example :
    let Λ := linkOf ret0Prog ret0Secs
    let Λ' := { Λ with abortLbl := fun k => match k with
      | .heap => Spike.Lib.A64.Abort.overflow.entry
      | k => Λ.abortLbl k }
    let p := ret0Prog.map fun d => if d == .label ".L12_scc_rt_abort.1_is0" then .label ".Lx" else d
    (Spike.Lib.A64.StubW.abortPhC Λ.code.lo Λ ret0Prog, Spike.Lib.A64.StubW.abortPhC Λ.code.lo Λ' ret0Prog,
      Spike.Lib.A64.StubW.abortPhC Λ.code.lo Λ p) = (true, false, false) := by
  decide +kernel

/-- Without its `.bss` (the runtime's counters and the first TCB), the
runtime's data words are not data symbols: A8 fails. -/
example : placeOK Config.canonical ⟨ret0Prog, { ret0Secs with bss := [] }, [], ret0Place⟩ = false :=
  placeOK_eq_false_of_a8 (by decide +kernel)

/-- `ret0.w`'s layout at its canonical tables. -/
abbrev ret0LΛ : Scc.Sem.Layout := (tablesOf Config.canonical ⟨ret0Prog, ret0Secs, [], ret0Place⟩).Λ

/-- A8's `rtInitOk` holds on `ret0.w`, and the limit word (`scc_rt_pinned + 16`, the
`ret0_limInit` of `Spike/Lib/A64Ret0Correct.lean`) starts at `0` in the loaded memory
(`initVal_rt_of_rtInitOk`). -/
theorem ret0_limInitOk :
    rtA ret0LΛ ret0Prog ret0Secs "scc_rt_pinned" + 16#64
        = BitVec.ofNat 64 134217744 ∧
      ({ init := initOf ret0LΛ ret0Prog ret0Secs, msgs := #[] } :
        Kraken.Promising.Memory).initVal ⟨BitVec.ofNat 64 134217744, 8⟩ = 0 := by
  have hl : rtA ret0LΛ ret0Prog ret0Secs "scc_rt_pinned" + 16#64
      = BitVec.ofNat 64 134217744 := by decide +kernel
  have h := initVal_rt_of_rtInitOk (rtInit_of_placeOK ret0_placeOK)
    (m := { init := initOf ret0LΛ ret0Prog ret0Secs, msgs := #[] }) rfl
    (a := rtA ret0LΛ ret0Prog ret0Secs "scc_rt_pinned" + 16#64)
    (List.mem_append_right _ (List.mem_map.mpr ⟨1, List.mem_range.mpr (by decide), rfl⟩))
  exact ⟨hl, hl ▸ h⟩

/-- `rtInitOk` fails closed: with an image word at the limit word, or with
`.rodata` laid out over it, a runtime word has an initial word in the load. -/
example :
    let Λ := (tablesOf Config.canonical ⟨ret0Prog, ret0Secs, [], ret0Place⟩).Λ
    let Λi := { Λ with image := (134217744, 1) :: Λ.image }
    let Λr := { Λ with rodata := ⟨134217744, 8⟩ }
    (rtInitOk Λ ret0Prog ret0Secs, rtInitOk Λi ret0Prog ret0Secs,
      rtInitOk Λr ret0Prog { ret0Secs with rodata := [.quad 1] }) = (true, false, false) := by
  decide +kernel

/-- A1's `_start` check holds on `ret0.w`: `_start` is the first code label,
at the code base (`start_at_lo_of_placeOK`). -/
example : codeOf ret0LΛ.code.lo ret0Prog "_start" = some 4194304 ∧ ret0LΛ.code.lo = 4194304 :=
  ⟨start_at_lo_of_placeOK ret0_placeOK, rfl⟩

/-- A1's `_start` check fails closed: with an instruction before `_start`
(`_start` then 4 bytes past the code base) or with `_start` renamed, A1 fails. -/
example :
    let p := (ret0Prog.drop 1).take 1 ++ ret0Prog
    let q := ret0Prog.map fun d => if d == .label "_start" then .label "_strt" else d
    let lo := ret0LΛ.code.lo
    (codeOf lo p "_start", codeOf lo q "_start",
      a1 ⟨p, ret0Secs, [], ret0Place⟩ (tablesOf Config.canonical ⟨p, ret0Secs, [], ret0Place⟩),
      a1 ⟨q, ret0Secs, [], ret0Place⟩ (tablesOf Config.canonical ⟨q, ret0Secs, [], ret0Place⟩)) =
      (some (4194304 + 4), none, false, false) := by
  decide +kernel

example : placeOK Config.canonical ⟨(ret0Prog.drop 1).take 1 ++ ret0Prog, ret0Secs, [], ret0Place⟩ = false :=
  placeOK_eq_false_of_a1 (by decide +kernel)

/-- A8's `rtOffOk` holds on `ret0.w`: the limit word (`scc_rt_pinned + 16`) is in
the pinned region, clear of `.data` and the heap (`rtOff_of_placeOK`). -/
example : ret0LΛ.pinned.contains 134217744 = true ∧
    clearB ret0LΛ.data (BitVec.ofNat 64 134217744) = true ∧ clearB ret0LΛ.heap (BitVec.ofNat 64 134217744) = true := by
  have h := clear_of_rtOffOk (rtOff_of_placeOK ret0_placeOK) (j := 2) (by decide)
  have hl : rtA ret0LΛ ret0Prog ret0Secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * 2) = BitVec.ofNat 64 134217744 :=
    ret0_limInitOk.1
  rw [hl] at h
  exact ⟨by decide +kernel, h⟩

/-- `rtOffOk` fails closed: with `.data` or the heap laid out over the first TCB
(the limit word in it), a TCB word is not clear of it. -/
example :
    let Λ := ret0LΛ
    (rtOffOk Λ ret0Prog ret0Secs, rtOffOk { Λ with data := ⟨134217744, 8⟩ } ret0Prog ret0Secs,
      rtOffOk { Λ with heap := ⟨134217728, 4096⟩ } ret0Prog ret0Secs) = (true, false, false) := by
  decide +kernel

/-- `scc_rt_main` at a `MainCode` other than its own (another frame size) fails A11. -/
example : a11 ⟨ret0Prog, ret0Secs, [], ret0Place⟩ (tablesOf Config.canonical ⟨ret0Prog, ret0Secs, [], ret0Place⟩)
    = true ∧ Spike.Lib.A64.Rt.rtCodeOk ret0Prog { Spike.Lib.A64.Rt.bareMC with Z := 64 } = false :=
  ⟨a11_of_parts rfl (rtCodeOk_bare_of_placeOK ret0_placeOK) (mainPh_of_placeOK ret0_placeOK rfl), by decide +kernel⟩

/-- A6's runtime phase facts (`rtPhOk` at `rtPhTab none`) and A11's
`scc_rt_main` facts (`mainPhTab`) hold on `ret0.w`; a wrong `scc_rt_main`
phase fact fails. -/
example :
    let Λ := (tablesOf Config.canonical ⟨ret0Prog, ret0Secs, [], ret0Place⟩).Λ
    rtPhOk Λ.code.lo ret0Prog Λ (Spike.Lib.A64.Rt.rtPhTab none) = true ∧
      rtPhOk Λ.code.lo ret0Prog Λ (Spike.Lib.A64.Rt.mainPhTab Spike.Lib.A64.Rt.bareMC) = true ∧
      rtPhOk Λ.code.lo ret0Prog Λ [.ph Spike.Lib.A64.Rt.bareMC.sc 0 13] = false :=
  ⟨rtPh_of_placeOK ret0_placeOK, mainPh_of_placeOK ret0_placeOK rfl, by decide +kernel⟩

end Scc.Cert.PlaceOK.A64.Test
