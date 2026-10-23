import Scc.Cert.PlaceOKX64
import Spike.Lib.X64Hello1Code
import Spike.Test.X64Ret0Offs
import Spike.Lib.Hello1Src

/-!
# `PlaceOK` against the hand checks of `hello1.w` on x86-64

One kernel decision of the components of `PlaceOK`
(`Scc/Cert/PlaceOKX64.lean`) other than A6 and A11, `hello1_parts`, A6 in
`hello1_a6`, and each of the
hand checks of `Spike/Lib/X64Hello1Code.lean` re-derived from it, at the
hand statement. `ret0.w`'s twin is `Spike/Test/X64Ret0PlaceOK.lean`.

**A11 rejects `hello1.w`** (`a11`, the runtime's fixed code in one pass,
`Spike.Lib.X64.Rt.rtCodeOk`), for two reasons, each shown below:

1. its `scc_rt_main` has a setup block (`tail := .setup`), whose
   `MainCode` does not exist yet: `mcOf .setup = none`;
2. the emitter numbers the runtime's local return points per program
   (`Scc.Emit.X64.freshL`): `scc_rt_main`'s setup call takes one more, so
   `scc_rt_thread_init`'s return point is `.Lscc_rt_thread_init.x8` here
   and `.x7` in `ret0.w`, which the groups name (`tiGrps`); the other
   groups pass.

Every `Accepted0` program numbers them as `ret0.w` does (the runtime
functions come first, and only `scc_rt_main`'s setup call varies). `a11` is a slot of `checks`, so
`placeOK` on `hello1.w` is `false` (`hello1_placeOK`,
`placeOK_eq_false_of_a11`).
-/

namespace Scc.Cert.PlaceOK.X64.Test

open Kraken Kraken.Promising.X64 Scc.Cert.Rt.X64 Scc.Cert.Link.X64 SccCode

/-- `hello1.w`'s placement data: its block table with its offsets (`hello1Offs`), stack need and `scc_rt_main`'s tail (after a setup
block). The output is written out, as `ret0`'s (`Spike/Test/X64Ret0PlaceOK.lean`). -/
def hello1Place : PlaceData :=
  { blocks := withEvs (ofGrps hello1T hello1Offs) hello1Evs, need := hello1Need, tail := .setup,
    ir := some (Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Hello1Src.hello1Src).low.ir }

/-- `hello1.w`'s output. -/
abbrev hello1Out : Out := ⟨hello1Cells, hello1Secs, hello1Asm.labelOffs, hello1Place⟩

/-- `hello1.w`'s components other than A6 and A11 (A9 is `true`), one kernel decision. -/
theorem hello1_parts : (a1 hello1Out (tablesOf Config.canonical hello1Out) &&
    a2 hello1Out (tablesOf Config.canonical hello1Out) && a3 hello1Out (tablesOf Config.canonical hello1Out) &&
    a4 Config.canonical hello1Out (tablesOf Config.canonical hello1Out) &&
    a5 hello1Out (tablesOf Config.canonical hello1Out) && a7 hello1Out (tablesOf Config.canonical hello1Out) &&
    a8 hello1Out (tablesOf Config.canonical hello1Out)) = true := by
  decide +kernel

/-- A6 of `hello1.w`'s output: the block table in its phases. -/
theorem hello1_a6 : a6 hello1Out (tablesOf Config.canonical hello1Out) = true := by
  decide +kernel

private theorem hello1_a1 : (PlaceOK.a1 (tablesOf Config.canonical hello1Out) &&
    Scc.Cert.PlaceOK.layoutOk hello1Out.secs (tablesOf Config.canonical hello1Out).Λ) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (h.1.1.1.1.1.1 : (((PlaceOK.a1 _ && _) && _) && _) = true)).1).1
private theorem hello1_a2 : (loadOk (linkOf hello1Cells hello1Secs) hello1Cells hello1Secs hello1Asm.labelOffs &&
    abortsIn hello1Cells (linkOf hello1Cells hello1Secs) &&
    imageIn hello1Cells hello1Secs (linkOf hello1Cells hello1Secs)) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.2
private theorem hello1_a3 : a3 hello1Out (tablesOf Config.canonical hello1Out) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.2
private theorem hello1_a4 : (Scc.Cert.WideX64.wideIn (hello1Cells.map (·.1)) &&
    Scc.Cert.NeedX64.needOk hello1Cells hello1Need 12288 ["scc_rt_main"]) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h; exact h.1.1.1.2
private theorem hello1_a7 : rtIn hello1Cells (RtIn.rtTab RtIn.mainGrps1) = true := by
  have h := hello1_parts; simp only [Bool.and_eq_true] at h
  exact (Bool.and_eq_true_iff.mp (h.1.2 : (rtIn hello1Cells (RtIn.rtTab RtIn.mainGrps1) && _) = true)).1

/-- **`hello1.w` fails `PlaceOK`** (A11, below). -/
theorem hello1_placeOK : placeOK Config.canonical hello1Out = false :=
  placeOK_eq_false_of_a11 rfl

example : hello1Λ.WF := by
  have h := hello1_a1; simp only [Bool.and_eq_true] at h; exact Scc.Cert.PlaceOK.wf_withImms (wf_of_a1 h.1) _
example : abortsIn hello1Cells hello1Λ = true := by
  have h := hello1_a2; simp only [Bool.and_eq_true] at h
  exact (abortsIn_withImms (linkOf hello1Cells hello1Secs) hello1Imms hello1Cells).trans h.1.2
example : imageIn hello1Cells hello1Secs hello1Λ = true := by
  have h := hello1_a2; simp only [Bool.and_eq_true] at h
  exact (imageIn_withImms (linkOf hello1Cells hello1Secs) hello1Imms hello1Cells hello1Secs).trans h.2
example : loadOk hello1Λ hello1Cells hello1Secs hello1Asm.labelOffs = true := by
  have h := hello1_a2; simp only [Bool.and_eq_true] at h
  exact (loadOk_withImms (linkOf hello1Cells hello1Secs) hello1Imms hello1Cells hello1Secs
    hello1Asm.labelOffs).trans h.1.1
example : Scc.Cert.WideX64.wideIn (hello1Cells.map (·.1)) = true := by
  have h := hello1_a4; simp only [Bool.and_eq_true] at h; exact h.1
example : blocksIn hello1Cells hello1T := by
  have h := hello1_a3; simp only [a3, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hello1Place, toGrps_withEvs, toGrps_ofGrps] at h
  exact h.1
example : coverOk hello1Cells hello1Place.blocks = true := by
  have h := hello1_a3; simp only [a3, Bool.and_eq_true] at h; exact h.2
example : Scc.Cert.Rt.X64.Abort.abortIn hello1Cells = true := RtIn.abortIn_of_rtIn hello1_a7
example : Scc.Cert.Rt.X64.Print.printIn hello1Cells = true := RtIn.printIn_of_rtIn hello1_a7
example : Scc.Cert.Rt.X64.Abort.mainIn hello1Cells = true := RtIn.mainIn_of_rtIn hello1_a7
example : Scc.Cert.NeedX64.needOk hello1Cells hello1Need 12288 ["scc_rt_main"] = true := by
  have h := hello1_a4; simp only [Bool.and_eq_true] at h; exact h.2

/-! ### A11 on `hello1.w` -/

/-- **A11 fails on `hello1.w`.** -/
theorem hello1_a11 : a11 hello1Out (tablesOf Config.canonical hello1Out) = false := rfl

/-- Reason 1: no `MainCode` after a setup block. -/
example : mcOf hello1Place.tail = none := rfl

/-- Reason 2: at the bare `MainCode` too, the pass fails, at
`scc_rt_thread_init`'s groups only: its return point is `.x8`, not `.x7`. -/
example : Spike.Lib.X64.Rt.rtCodeOk hello1Cells Spike.Lib.X64.Rt.bareMC = false := by decide +kernel

#guard rtIn hello1Cells Spike.Lib.X64.Rt.startGrps
#guard rtIn hello1Cells Spike.Lib.X64.Rt.tcbGrps
#guard !rtIn hello1Cells Spike.Lib.X64.Rt.tiGrps
#guard rtIn hello1Cells Spike.Lib.X64.Rt.takeGrps
#guard hello1Cells.any (·.1 == .label ".Lscc_rt_thread_init.x8")
#guard !hello1Cells.any (·.1 == .label ".Lscc_rt_thread_init.x7")

end Scc.Cert.PlaceOK.X64.Test
