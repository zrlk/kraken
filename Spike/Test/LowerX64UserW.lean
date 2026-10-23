import Spike.Lib.LowerX64.UserW
import Spike.Lib.LowerX64.UserCall
import Spike.Lib.X64Ret0I
import Spike.Test.LowerInvX64

/-!
# `ProPh` and `UPost` at `ret0.w`'s `main` (x86-64)

The twin of `Spike/Test/LowerA64UserW.lean`. The user `main`'s prologue
passes its phase facts at the hand placement's tables (`Ret0.Inst.okPc`,
`ph`, `labT`) and the listing's cell sizes; with no pc allowed, or with the
frame set-up's phase moved, it fails. `ret0`'s start satisfies the
return-value contract `UPost` at 42, and no other control than the start
does.
-/

namespace Spike.Test.LowerX64UserW

open Spike.Lib.LowerX64
open Spike.Test.LowerInvX64 (mainFr)
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.X64.Flow.Ret0.Inst (okPc ph labT)
open Spike.Lib.X64.Flow (xHead xLea xCmp xFr)
open Scc.Emit.X64 (labelOf)

/-- `main`'s check label, frame and growth label. -/
theorem fr_eq : labelOf mainFr.fn "chk" = ".Lwc_main.chk" ∧ mainFr.size = 16 ∧ proL mainFr = ".Lwc_main.stk" := by
  decide +kernel

/- The prologue's cell sizes, as the listing has them. -/
#guard sizesAt SccCode.ret0Cells ".Lwc_main.chk" 0 5 == [5, 9, 3, 2, 4]

/-- **The hand tables: the prologue passes `ProPh`.** -/
theorem ret0_proPh : ProPh okPc ph labT "wc_main" ".Lwc_main.chk" (Int64.ofInt 16) ".Lwc_main.stk" 5 9 3 2 4 [] :=
  ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel,
    by decide +kernel⟩

/-- At `main`'s frame. -/
example : ProPh okPc ph labT "wc_main" (labelOf mainFr.fn "chk") (Int64.ofInt mainFr.size) (proL mainFr) 5 9 3 2 4
    [] := by
  obtain ⟨h1, h2, h3⟩ := fr_eq
  rw [h1, h2, h3]; exact ret0_proPh

/-- No pc allowed: the head's check fails. -/
example : blkPh (fun _ => false) ph (fun _ => false) labT (labT "wc_main" + Int64.ofNat 0) 0 xHead = false := by
  decide +kernel

/-- A phase table moving the frame set-up's pc: its check fails. -/
example : blkPh okPc (fun pc => if pc == (labT ".Lwc_main.chk" + Int64.ofNat (5 + 9 + 3 + 2)).toBitVec.toNat
    then ph pc else ph pc + 1) (fun _ => false) labT (labT ".Lwc_main.chk" + Int64.ofNat (5 + 9 + 3 + 2)) 0
    (xFr (Int64.ofInt 16) 4 []) = false := by decide +kernel

/-- **`UPost` at `ret0`**: from the start a local run reaches `ret y` with
`y = 42`. -/
example {lbl : WeakMem.AllocLabel → Option Nat} :
    UPost Spike.Lib.Ret0Src.ret0Src lbl Spike.Lib.X64Consumer.c0 Spike.Lib.X64Consumer.c0 42#64 :=
  ⟨rfl, _, Spike.Lib.X64.Flow.Ret0.Inst.start_run rfl rfl, .var "y", _, _, rfl, rfl, rfl, ⟨42, rfl⟩, by
    show _ ∧ _; exact ⟨by decide, rfl⟩⟩

/-- `UPost` holds at the start only. -/
example {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c : Spike.Lib.Ctl} {v : BitVec 64}
    (h : c ≠ Spike.Lib.X64Consumer.c0) : ¬ UPost p lbl Spike.Lib.X64Consumer.c0 c v :=
  fun hp => h hp.1

end Spike.Test.LowerX64UserW
