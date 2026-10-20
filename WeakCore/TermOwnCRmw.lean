import WeakCore.TermOwnCH

/-! # TermOwnCRmw: `hFP` at a `fetch`/`cas` fulfilment (ownC R5, WPD route (A))

At a step fulfilling exactly one own promise `th0`, at a closed copyable one-word unit
(`RmwAtomC`), whose coherence rises to `th0`, `PromAbove` after the step discharges the unit's
lowest own promise: `hFP` of `TermOwnCOld.overCr_old` holds (the piece is the unit, `piece_one`).
-/

namespace TermOwnCRmw

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **`hFP` at an RMW one-unit fulfilment.** -/
theorem hFP_rmw {E : TEnv} {s s' : St} {l : AllocLabel} {c : Cell} {o : Nat} {th0 : Ts} {m0 : Msg}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hkeep : ∀ t, t ∈ s.promises → t ≠ th0 → t ∈ s'.promises)
    (hm0 : s.mem[th0]? = some m0) (hl0 : m0.loc = ⟨l, o⟩)
    (hR : TermOwnCR5.RmwAtomC E ⟨l, o⟩) (hsto : E.sto l = some c)
    (hcoh : th0 ≤ s'.vs.coh ⟨l, o⟩) (hPA : PromAbove s') :
    ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc.label = l →
      ¬ WordUnit E m.loc → ∀ q S usS, TermPiece.Piece c.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o' th1, q ≤ o' → o' < q + nWords usS →
          TermPlant.LowOwn s ⟨l, o'⟩ th1 → th1 ∉ s'.promises := by
  intro t m ht hn hm hl _ q S usS hP' hus b1 b2 o' th1 c1 c2 hlo
  have et : t = th0 := by
    by_cases e : t = th0
    · exact e
    · exact absurd (hkeep t ht e) hn
  subst et
  have em : m0 = m := Option.some.inj (hm0.symm.trans hm)
  subst em
  rw [hl0] at b1 b2
  simp only at b1 b2
  obtain ⟨c', S1, hsto', hat, hS1, hsol, -, -⟩ := hR
  simp only at hsto' hat
  rw [hsto] at hsto'
  cases hsto'
  obtain ⟨e1, e2⟩ := TermFulW.piece_one hP' hus b1 b2 hat hS1 TermForWU.nWords_one hsol
  have eo : o' = o := by omega
  subst eo
  intro h1s
  obtain ⟨m1, hm1, hl1⟩ := hlo.2.1
  have hm1' : s'.mem[th1]? = some m1 := by rw [hpre th1 (hP th1 hlo.1)]; exact hm1
  have hA := hPA th1 h1s m1 hm1'
  rw [hl1] at hA
  have hle : th1 ≤ t := hlo.2.2 t m0 ht hm hl0
  exact absurd (Nat.lt_of_le_of_lt hcoh hA) (Nat.not_lt.mpr hle)

#print axioms hFP_rmw

end TermOwnCRmw
