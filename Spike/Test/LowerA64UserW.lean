import Spike.Lib.LowerA64.UserW
import Spike.Lib.LowerA64.UserCall
import Spike.Lib.A64Ret0I
import Spike.Test.LowerA64Ret0Oracle

/-!
# `ProPh` and `UPost` at `ret0.w`'s `main` (AArch64)

The user `main`'s prologue passes its phase facts at the hand placement's
tables (`Ret0.Inst.okPc`, `ph`, `labT`); with no pc allowed it fails.
`ret0`'s start satisfies the return-value contract `UPost` at 42, and no
other control than the start does.
-/

namespace Spike.Test.LowerA64UserW

open Spike.Lib.LowerA64
open Spike.Test.LowerInv (mainCtx)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.Flow.Ret0.Inst (okPc ph labT)
open Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow (chkHead chkBr frameSet)

/-- `main`'s check label, frame and growth label. -/
theorem ctx_eq : mainCtx.local "stack_check" = ".L18_wc_main.stack_check" ∧ mainCtx.frame = 32 ∧
    proL mainCtx = ".L18_wc_main.stack_grow" := by decide +kernel

/-- **The hand tables: the prologue passes `ProPh`.** -/
theorem ret0_proPh : ProPh okPc ph labT ".L18_wc_main.stack_check" (Int64.ofInt 32) ".L18_wc_main.stack_grow" [] :=
  ⟨by decide +kernel, ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- At `main`'s context. -/
example : ProPh okPc ph labT (mainCtx.local "stack_check") (Int64.ofInt mainCtx.frame) (proL mainCtx) [] := by
  obtain ⟨h1, h2, h3⟩ := ctx_eq
  rw [h1, h2, h3]; exact ret0_proPh

/-- No pc allowed: the head's check fails. -/
example : blkPh (fun _ => false) ph (fun _ => false) labT (labT ".L18_wc_main.stack_check" + Int64.ofNat (4 * 0)) 0
    (chkHead (Int64.ofInt 32)) = false := by decide +kernel

/-- A phase table moving the frame set-up's pcs: its check fails. -/
example : blkPh okPc (fun pc => if pc == (labT ".L18_wc_main.stack_check" + Int64.ofNat (4 * 5)).toBitVec.toNat
    then ph pc else ph pc + 1) (fun _ => false) labT (labT ".L18_wc_main.stack_check" + Int64.ofNat (4 * 5)) 0
    (frameSet (Int64.ofInt 32) []) = false := by decide +kernel

/-- **`UPost` at `ret0`**: from the start a local run reaches `ret y` with
`y = 42`. -/
example {lbl : WeakMem.AllocLabel → Option Nat} :
    UPost Spike.Lib.Ret0Src.ret0Src lbl Spike.Lib.A64Consumer.c0 Spike.Lib.A64Consumer.c0 42#64 :=
  ⟨rfl, _, Spike.Lib.A64.Flow.Ret0.Inst.start_run rfl rfl, .var "y", _, _, rfl, rfl, rfl, ⟨42, rfl⟩, by
    show _ ∧ _; exact ⟨by decide, rfl⟩⟩

/-- `UPost` holds at the start only. -/
example {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c : Spike.Lib.Ctl} {v : BitVec 64}
    (h : c ≠ Spike.Lib.A64Consumer.c0) : ¬ UPost p lbl Spike.Lib.A64Consumer.c0 c v :=
  fun hp => h hp.1

end Spike.Test.LowerA64UserW
