/-
**`SetupPostS` on `hello1.w`** (AArch64): the hand post of `wc_rodata`'s
setup block (`Hello1.rdPostS`) is the named post at `hello1Pl` (the slice's
locative in `x0`/`x1`, the offset word `0`; its length `2` in `x2`; the
count `13` in `x3`).
-/
import Spike.Lib.A64Hello1RodataSetup
import Spike.Lib.Rt.A64SetupRet

namespace Spike.Test.A64SetupRetHello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Spike.Lib.SetupRet
open Spike.Lib.A64.Rt (rdA64)

/-- **`rdPostS` is `SetupPostS` at `hello1Pl`.** -/
theorem rdPostS_setupPostS {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {c : Spike.Lib.Ctl} {r : Reg64s} (h : Spike.Lib.A64.Flow.Hello1.rdPostS lbl ms c r) :
    SetupPostS lbl rdA64 hello1Pl c r := by
  obtain ⟨l, ini, wo0, wo1, A, old, rfl, hl, hx0, -, -, hx1, hx2, hx3⟩ := h
  refine ⟨rfl, _, _, _, rfl, rfl, ?_, ?_, ?_, trivial⟩
  · show 0 = 0 ∧ lbl l = some (r.getXReg .X0).toBitVec.toNat ∧ (r.getXReg .X1).toBitVec.toNat = 8 * 0
    refine ⟨rfl, ?_, ?_⟩
    · rw [← hx0] at hl; exact hl
    · show r.X1.toBitVec.toNat = 0
      rw [hx1]; rfl
  · show 2 < 2 ^ 64 ∧ (r.getXReg .X2).toBitVec.toNat = 2
    exact ⟨by decide, by show r.X2.toBitVec.toNat = 2; rw [hx2]; rfl⟩
  · show 13 < 2 ^ 64 ∧ (r.getXReg .X3).toBitVec.toNat = 13
    exact ⟨by decide, by show r.X3.toBitVec.toNat = 13; rw [hx3]; rfl⟩

end Spike.Test.A64SetupRetHello1
