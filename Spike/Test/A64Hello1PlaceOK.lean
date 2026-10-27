import Spike.Test.A64Ret0PlaceOK

/-!
# `PlaceOK` against the hand checks of `hello1.w`

`hello1.w`'s `scc_rt_main` tail is after a setup block; A11 checks it by
`setupOk` (`Spike/Lib/Rt/A64CodeInSetup.lean`, `hello1_a11`). Its components
but A9 and A11 are decided one declaration each (`hello1_part1` ...), and the hand
checks of `Spike/Lib/A64Hello1Code.lean` re-derived from them. The block
table of the placement data is the hand table `hello1T` with the static
offsets the analyser gives its blocks, as for `ret0.w`
(`Spike/Test/A64Ret0PlaceOK.lean`).
-/

namespace Scc.Cert.PlaceOK.A64.Test

open Kraken Kraken.Promising.AArch64 Scc.Cert.Rt.A64 Scc.Cert.Link.A64 SccCode

/-! ## hello1 -/

/-- `hello1.w`'s placement data: its block table with its offsets, stack need and `scc_rt_main`'s tail. -/
def hello1Place : PlaceData :=
  { blocks := withEvs (ofGrps hello1T hello1Offs) hello1Evs, need := hello1Need, tail := .setup,
    ir := some (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Hello1Src.hello1Src).low.ir }

/-- `hello1.w`'s output. Written out, so that the components' `o.prog` reduces to `hello1Prog` by
projection. -/
abbrev hello1O : Out := ⟨hello1Prog, hello1Secs, [], hello1Place⟩

/-! `hello1.w`'s components other than A9 and A11, one kernel decision each (together, one decision
peaks above 4 GB). -/

theorem hello1_part1 : a1 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel
theorem hello1_part2 : a2 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel
theorem hello1_part3 : a3 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel
theorem hello1_part4 : a4 Config.canonical hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel
theorem hello1_part5 : a5 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel
theorem hello1_part6 : a6 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel
theorem hello1_part7 : a7 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel
theorem hello1_part8 : a8 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel

/-- **`hello1.w`'s A11**: `scc_rt_main` after its setup block (`.setup`; `setupOk` at
`setupMC 4`), kernel-checked. -/
theorem hello1_a11 : a11 hello1O (tablesOf Config.canonical hello1O) = true := by decide +kernel

/-- `scc_rt_main` with three setup words, or a frame other than its own, fails A11's setup pass. -/
example : (Spike.Lib.A64.Rt.rtCodeOkS hello1Prog (Spike.Lib.A64.Rt.setupMC 3) ||
    Spike.Lib.A64.Rt.rtCodeOkS hello1Prog { Spike.Lib.A64.Rt.setupMC 4 with Z := 96 }) = false := by
  decide +kernel

private theorem hello1_a1 : (PlaceOK.a1 (tablesOf Config.canonical hello1O) &&
    Scc.Cert.PlaceOK.layoutOk hello1O.secs (tablesOf Config.canonical hello1O).Λ) = true := by
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (hello1_part1 : (((PlaceOK.a1 _ && _) && _) && _) = true)).1).1
private theorem hello1_a2 : (loadOk (linkOf hello1Prog hello1Secs) hello1Prog hello1Secs &&
    abortsIn hello1Prog (linkOf hello1Prog hello1Secs) && imageIn hello1Prog hello1Secs (linkOf hello1Prog hello1Secs))
      = true := by
  exact hello1_part2
private theorem hello1_a3 :
    (decide (blocksIn hello1Prog (toGrps hello1Place.blocks)) && coverOk hello1Prog hello1Place.blocks) = true := by
  exact hello1_part3
private theorem hello1_a4 : (Scc.Cert.WideA64.wideIn hello1Prog &&
    Scc.Cert.NeedA64.needOk hello1Prog hello1Need 12288 ["scc_rt_main"]) = true := by
  exact hello1_part4
private theorem hello1_a7 : rtIn hello1Prog (RtIn.rtTab RtIn.mainGrps1) = true := by
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (hello1_part7 : ((rtIn hello1Prog (RtIn.rtTab RtIn.mainGrps1) && _) && _) = true)).1).1

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

/-- `ret0.w`'s IR against `hello1.w`'s listing fails A9 (`main`'s code block is not there). -/
example : placeOK Config.canonical ⟨hello1Prog, hello1Secs, [], { hello1Place with ir := ret0Place.ir }⟩ = false :=
  placeOK_eq_false_of_a9 (by decide +kernel)

end Scc.Cert.PlaceOK.A64.Test
