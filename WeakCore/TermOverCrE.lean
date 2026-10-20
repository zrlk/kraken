import WeakCore.TermOverCrZ
import WeakCore.TermForWU

/-!
# TermOverCrE: free items at foreign RMW atoms (G1 leaf)

The `TermForWU.RmwAtom` (an `Int` or a closed non-affine one-word leaf, or an epoch pair) at an
address whose lowest own promise has a `WordOK` predecessor gives a zero-resource credited item
(`crItemQ_free`); the epoch-pair case is returned as is (OPEN).  Guard-independent: `CrItemQ`
does not mention the window guard.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem solid_int : Solid Ty.int :=
  ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ h => by cases h)⟩

#print axioms solid_int

/-- **A free item at an RMW atom** (non-epair), or the atom is in an epoch pair (OPEN). -/
theorem crItemQ_rmw {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {a : Address}
    {tw : Ts} {w : Word}
    (hR : TermForWU.RmwAtom E a) (hl : a.label = l) (hsto : E.sto l = some c)
    (hlo : TermPlant.LowOwn s a tw) (hnw : ¬ WordUnit E a)
    (hpred : PredAt s.mem a tw w) (hok : WordOK E c.ty a.offset w) :
    (∃ U, accs U = some [Acc.one] ∧
      TermOverCr.CrItemQ E s cr l c (tw, a.offset, U, [w], .zero, fun _ => true)) ∨
    ∃ o n P, AtOff c.ty o (.epair (.lit n) P) ∧ o ≤ a.offset ∧ a.offset < o + 2 := by
  obtain ⟨c0, o, S, us, hs0, hat, hus, h1, h2, hk⟩ := hR
  rw [hl, hsto] at hs0
  cases hs0
  have ha : a = ⟨l, a.offset⟩ := by rw [← hl]
  have hlo' : TermPlant.LowOwn s ⟨l, a.offset⟩ tw := by rw [← ha]; exact hlo
  have hnw' : ¬ WordUnit E ⟨l, a.offset⟩ := by rw [← ha]; exact hnw
  have hpred' : PredAt s.mem ⟨l, a.offset⟩ tw w := by rw [← ha]; exact hpred
  rcases hk with rfl | ⟨hU, hsol, hcl, haf⟩ | ⟨n, P, rfl⟩
  · have e : us = [Acc.one] := by simp [accs] at hus; exact hus.symm
    subst e
    have ho : a.offset = o := by rw [TermForWU.nWords_one] at h2; exact Nat.le_antisymm (Nat.lt_succ_iff.mp h2) h1
    rw [← ho] at hat
    exact .inl ⟨.int, rfl, crItemQ_free hlo' hnw' hat solid_int rfl rfl rfl hpred' hok⟩
  · rw [hU] at hus
    cases hus
    have ho : a.offset = o := by rw [TermForWU.nWords_one] at h2; exact Nat.le_antisymm (Nat.lt_succ_iff.mp h2) h1
    rw [← ho] at hat
    exact .inl ⟨S, hU, crItemQ_free hlo' hnw' hat hsol hU hcl haf hpred' hok⟩
  · refine .inr ⟨o, n, P, hat, h1, ?_⟩
    have e : us = [Acc.two] := by simp [accs] at hus; exact hus.symm
    subst e
    rw [TermForWU.nWords_two] at h2
    exact h2

#print axioms crItemQ_rmw

end TermOverCrW
