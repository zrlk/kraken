import WeakCore.TermOwnCOld
import WeakCore.TermOwnCLoad
import WeakCore.TermOverCrN
import WeakCore.TermMainDefs

/-! # TermOwnCH: zero items at demanded units under the window conditions (ownC (iii))

`zeroIt_unit`: at a demanded non-word unit of a copyable piece whose lowest own promise meets the
window conditions, a zero item exists.  The unit is a single word: an outstanding promise lies on
no word of a two-word unit (`PromNoTwoOK`, `SysInvN.promNoTwo`), so its access unit is the word
alone (`TermOverCrW.inAcc_single`); `freeQW_exists` pinned at the coherence message
(`TermOwnCPin.pin_of_winG`).  (This discharges the scratch binder `FreeQW2H`: the multi-word case is
vacuous,.)
-/

namespace TermOwnCH

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A laid-out cell type has the shape `inAcc_single` asks for. -/
theorem layT_shape {T : Ty} (h : LayT T) : (∃ L, accs T = some L) ∨ ∃ N e, T = .array (.lit N) e := by
  rcases h with h | ⟨n, e, rfl, -⟩
  · exact .inl (Option.ne_none_iff_exists'.1 h)
  · exact .inr ⟨n, e, rfl⟩

/-- **A zero item at a demanded unit of a copyable piece** under the window conditions. -/
theorem zeroIt_unit {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o q n : Nat} {U : Ty}
    {us : List Acc} {tw : Ts} {fr : Option Ts} {S : Ts → Prop} {vals : List Word} {v : Word}
    (hsto : E.sto l = some c) (hclo : tb 0 c.ty = true) (hlay : LayT c.ty)
    (hP : TermPiece.Piece c.ty q U) (hU : accs U = some us) (hq : q ≤ o) (ho : o < q + nWords us)
    (ha : Ty.affine U = false) (hnw : ¬ WordUnit E ⟨l, o⟩)
    (hno : ∀ q', TwoAtT c.ty q' → o ≠ q' ∧ o ≠ q' + 1)
    (hlo : TermPlant.LowOwn s ⟨l, o⟩ tw) (hW : TermOverCr.WinG E s l o tw) (hPA : PromAbove s)
    (hc : CellOK E n c.ty vals)
    (hi : ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → o < n * nWords us)
    (hv : vals[o]? = some v) (hL : LatestSF E c fr s.mem S s.vs.coh ⟨l, o⟩ v) :
    ∃ x, TermOwnCOld.ZeroIt E s l c tw x := by
  have eo : q + (o - q) = o := by omega
  have hs : ∀ i o2, InAcc us i (o - q) → InAcc us i o2 → o2 = o - q := fun i o2 hi h2 =>
    TermOverCrW.inAcc_single hP.1 hU hi (layT_shape hlay) (by rw [eo]; exact hno) o2 h2
  obtain ⟨w, hpin, hok⟩ := TermOwnCPin.pin_of_winG hlo hPA hW hc hi hv hL
  obtain ⟨x, hx⟩ := TermFreeQW.freeQW_exists hsto hlo hP hU hq ho hs
    (TermOwnCLoad.atOff_tb hP.1 hclo) ha hnw hpin hok
  exact ⟨x, TermOwnCOld.zeroIt_of_freeQW hx⟩

#print axioms zeroIt_unit

/-- `PromNoTwoOK` at the lowest own promise's message gives `hno`. -/
theorem hno_of_promNoTwo {Eg : GEnv} {cf : Cfg} {j : Nat} {th : TTh} {l : AllocLabel} {o : Nat} {c : Cell}
    {tw : Ts} (h : PromNoTwoOK Eg cf) (hth : cf.ths[j]? = some th)
    (hlo : TermPlant.LowOwn (stOf cf.mem cf.pairs th) ⟨l, o⟩ tw) (hsto : Eg.sto l = some c) :
    ∀ q', TwoAtT c.ty q' → o ≠ q' ∧ o ≠ q' + 1 := by
  obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hlo
  have h1 := h j th tw m c hth htw hm (by rw [hml]; exact hsto)
  rw [hml] at h1
  exact h1

#print axioms hno_of_promNoTwo

end TermOwnCH
