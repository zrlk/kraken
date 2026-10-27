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

**A11 on `hello1.w`** (`hello1_a11`): its `scc_rt_main` has a setup block
(`tail := .setup`, `mcOf .setup = none`), which A11 checks by
`Spike.Lib.X64.Rt.setupOk` (`Spike/Lib/Rt/X64CodeInSetup.lean`: two calls,
four setup words marshalled, `setupMC 4`). The emitter numbers the
runtime's local return points per program (`Scc.Emit.X64.freshL`):
`scc_rt_main`'s setup call takes one more, so `scc_rt_thread_init`'s return
point is `.Lscc_rt_thread_init.x8` here and `.x7` in `ret0.w`; the setup
pass names `.x8` (`tiGrpsAt`), the bare one `.x7` (`tiGrps`), shown below.

Every `Accepted0` program numbers them as `ret0.w` does (the runtime
functions come first, and only `scc_rt_main`'s setup call varies).
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
/-- The pass at `hello1.w`'s width (A7 at `.setup` takes any width below
six, `mainRtOk`, so the pass at four words is decided by itself). -/
private theorem hello1_a7 : rtIn hello1Cells (RtIn.rtTab RtIn.mainGrps1) = true := by
  decide +kernel


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
example : RtIn.mainInS hello1Cells 4 = true := RtIn.mainInS_of_rtIn (RtIn.mainGrps1_eq ▸ hello1_a7)
/-- A7 at `.setup` takes `hello1.w`'s tail (four setup words) and no other width below six. -/
example : ((List.range 6).filter fun sw => RtIn.mainInS hello1Cells sw) = [4] := by decide +kernel
example : Scc.Cert.NeedX64.needOk hello1Cells hello1Need 12288 ["scc_rt_main"] = true := by
  have h := hello1_a4; simp only [Bool.and_eq_true] at h; exact h.2

/-! ### A11 on `hello1.w` -/

/-- **`hello1.w`'s A11**: `scc_rt_main` after its setup block (`.setup`;
`setupOk` at `setupMC 4`), kernel-checked. -/
theorem hello1_a11 : a11 hello1Out (tablesOf Config.canonical hello1Out) = true := by
  decide +kernel

/-- No `MainCode` after a setup block: A11 takes the setup pass. -/
example : mcOf hello1Place.tail = none := rfl

/-- `scc_rt_main` with three setup words, or a frame other than its own, or
`scc_rt_thread_init`'s return point at `.x7`, fails A11's setup pass. -/
example : (Spike.Lib.X64.Rt.rtCodeOkS hello1Cells (Spike.Lib.X64.Rt.setupMC 3) ||
    Spike.Lib.X64.Rt.rtCodeOkS hello1Cells { Spike.Lib.X64.Rt.setupMC 4 with Z := 80 } ||
    Spike.Lib.X64.Rt.rtCodeOkS hello1Cells { Spike.Lib.X64.Rt.setupMC 4 with ti := Spike.Lib.X64.Rt.Code.Ti.x7L })
    = false := by
  decide +kernel

#guard rtIn hello1Cells (Spike.Lib.X64.Rt.mainSGrps (Spike.Lib.X64.Rt.setupMC 4))
#guard rtIn hello1Cells (Spike.Lib.X64.Rt.tiGrpsAt (Spike.Lib.X64.Rt.setupMC 4).ti)

/-- At the bare `MainCode` the pass fails, at `scc_rt_main`'s and at
`scc_rt_thread_init`'s groups: its return point is `.x8`, not `.x7`. -/
example : Spike.Lib.X64.Rt.rtCodeOk hello1Cells Spike.Lib.X64.Rt.bareMC = false := by decide +kernel

#guard rtIn hello1Cells Spike.Lib.X64.Rt.startGrps
#guard rtIn hello1Cells Spike.Lib.X64.Rt.tcbGrps
#guard !rtIn hello1Cells Spike.Lib.X64.Rt.tiGrps
#guard rtIn hello1Cells Spike.Lib.X64.Rt.takeGrps
#guard hello1Cells.any (·.1 == .label ".Lscc_rt_thread_init.x8")
#guard !hello1Cells.any (·.1 == .label ".Lscc_rt_thread_init.x7")

end Scc.Cert.PlaceOK.X64.Test
