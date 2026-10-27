/-
**A buffer type's zero words represent 0** (`NodesA.zero`, an internal
premise of the allocation-capable consumers, from a check per type).

A buffer the allocator hands out is `.bss`, all zero; the source's buffer
starts at its type's zero words (`TermRun.zeroWords`). `NodesA.zero` asks
that each represents the target's 0 under every placement. That is not true
of every type (a sum's zero words may carry a nonzero tag), so it is checked
per type: `ZeroOkTy τ` holds when every zero word of `τ` is `num 0` or
`null` (`zero_of_zeroOkTy`). `zeroOkTy_lanes`: lanes of any width, as
`hello1.w`'s `newBuf m (lanes false w8)`.
-/
import WeakCore.TermRun
import Scc.Sem.Correct

namespace Spike.Lib

open CoreLang CoreTerm

/-- A word that represents 0 under every placement: `num 0` or `null`. -/
def zeroWordB : WeakMem.Val → Bool
  | .num 0 => true
  | .null => true
  | _ => false

/-- **The zero words of `τ` represent 0**, checked: each is `num 0` or
`null` (no zero words: nothing to check). -/
def ZeroOkTy (τ : Ty) : Bool :=
  match TermRun.zeroWords (TermRun.close [] τ) with
  | some vs => vs.all zeroWordB
  | none => true

theorem valRep_of_zeroWordB {v : WeakMem.Val} (h : zeroWordB v = true) (lbl : WeakMem.AllocLabel → Option Nat) :
    Scc.Sem.ValRep lbl v 0 := by
  match v, h with
  | .num 0, _ => exact ⟨by decide, rfl⟩
  | .null, _ => rfl

/-- **`NodesA.zero` at a type from the check.** -/
theorem zero_of_zeroOkTy {τ : Ty} (h : ZeroOkTy τ = true) :
    ∀ vs, TermRun.zeroWords (TermRun.close [] τ) = some vs → ∀ v ∈ vs,
      ∀ lbl : WeakMem.AllocLabel → Option Nat, Scc.Sem.ValRep lbl v 0 := by
  intro vs hz v hv lbl
  unfold ZeroOkTy at h
  rw [hz] at h
  exact valRep_of_zeroWordB (List.all_eq_true.mp h v hv) lbl

/-- Lanes pass the check (`hello1.w`'s buffer type `lanes false w8`). -/
theorem zeroOkTy_lanes (sg : Bool) (w : Wd) : ZeroOkTy (.lanes sg w) = true := by
  have hc : TermRun.close [] (.lanes sg w) = .lanes sg w := by simp [TermRun.close, substTs]
  simp only [ZeroOkTy, hc, TermRun.zeroWords]
  rfl

end Spike.Lib
