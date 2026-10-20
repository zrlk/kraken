import WeakCore.TermGbLp

/-!
# TermK5Lp: the planted count bound at a generic view bound (S1b, stage (iv))

`TermGbLp.iniLp_of` bounds the count of a planted own label along a certificate run before the root's
`publish` (`SoloNP`), using the G-0 window at the run's end. After the `publish`, the units added at
the label carry a witness index at most the `vWr` of the publishing thread (`PfrProvE`), which is
itself bounded by the window at the pre-publish configuration. `iniLp_ofV` takes that bound
generically: every added unit has a witness at an index `≤ vb < cP.mem.size`.
-/

namespace TermK5Lp

open CoreLang CoreTerm TermRun TermSound TermMem TermStep TermTyped TermOwnG0Defs TermOwnG0W TermGbLp
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (runAgree; shared) **The owner's buffer bound above the start count**: at an own start
buffer whose run count exceeds the start count, the run count is the cap (`IniHeld`'s `max` bound),
so `bufCap_of` bounds it by the slot count and, at zero width, gives the inhabitation. -/
theorem bufCap_gt {H : AllocLabel → Nat → Ts → Prop} {E0 E2 : TEnv} {v : Nat} {g : G} {s2 : St}
    (hrl : ∀ l, E0.rini l ≤ E0.ini l) (hIH : IniHeld H E0 E2 v) (hext : Ext E0 E2) (hmi : MemInv g E2 s2)
    {l : AllocLabel} {c : Cell} (hc : E0.sto l = some c) (ho : c.owner = some E0.tid)
    (hle : ¬ E2.ini l ≤ E0.ini l) {N : Nat} {e : Ty} (hT : c.ty = .array (.lit N) e) :
    ∃ us, accs e = some us ∧ E2.ini l ≤ N ∧ (nWords us = 0 → 0 < E2.ini l → InhZ E2.prog e) := by
  obtain ⟨hrl2, -, hmx, -⟩ := hIH hrl
  have hc2s : E2.sto l = some c := hext.2.2.2.2.1 l c hc
  have ho2 : c.owner = some E2.tid := by rw [hext.2.2.2.1]; exact ho
  obtain ⟨us, hus, hN, hZ⟩ := bufCap_of hmi.2.1 hc2s ho2 hT
  have hrc : E2.rc l = E2.ini l := by
    have h1 := hmx l c hc
    have h2 := hrl2 l
    unfold TEnv.rc
    rcases Nat.le_total (E0.ini l) (E2.rini l) with h | h
    · rw [Nat.max_eq_right h] at h1; exact Nat.min_eq_left h1
    · rw [Nat.max_eq_left h] at h1; exact absurd h1 hle
  rw [hrc] at hN hZ
  exact ⟨us, hus, hN, hZ⟩

/-- ** The planted count bound at a generic view bound.** -/
theorem iniLp_ofV {cP : Cfg} {thP : TTh} {E0 E2 : TEnv} {Lp : AllocLabel → Prop} {g : G} {s2 : St}
    {H : AllocLabel → Nat → Ts → Prop} {v vb : Ts} (hvb : vb < cP.mem.size) (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hIH : IniHeld H E0 E2 v) (hext : Ext E0 E2) (hmi : MemInv g E2 s2)
    {l : AllocLabel} {c : Cell} (hl : Lp l) (hc : E0.sto l = some c) (ho : c.owner = some E0.tid)
    (hcap : CapNAt E0 E2 l)
    (hu : ∀ N e us, c.ty = .array (.lit N) e → accs e = some us →
      ∀ o, o < E2.ini l * nWords us → ¬ o < E0.ini l * nWords us →
        ∃ τ, τ ≤ vb ∧ WitP cP.mem thP.promises l o τ) :
    E2.ini l ≤ (plantE E0 (stOf cP.mem cP.pairs thP) Lp).ini l := by
  rw [plantE_ini_in hl]
  by_cases hle : E2.ini l ≤ E0.ini l
  · exact Nat.le_trans hle (Nat.le_max_left _ _)
  obtain ⟨N, e, hT⟩ : ∃ N e, c.ty = .array (.lit N) e :=
    Classical.byContradiction fun hb => hle (hcap c hc hb)
  obtain ⟨us, hus, hN, hZ⟩ := bufCap_gt hrl hIH hext hmi hc ho hle hT
  have hNa : E2.ini l ≤ N := hN
  by_cases hE : EmptyZ E0 l
  · exfalso
    obtain ⟨c1, N1, e1, us1, hc1, hT1, hus1, h01, hinh⟩ := hE
    rw [hc] at hc1; cases hc1
    rw [hT] at hT1
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT1
    obtain ⟨rfl, rfl⟩ := hT1
    rw [hus] at hus1; cases hus1
    have := hZ h01 (Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_of_not_le hle))
    rw [hext.2.2.1] at this
    exact hinh this
  have hpre : PrefixHeld E0 (stOf cP.mem cP.pairs thP) l c (E2.ini l) := by
    intro N' e' us' hT' hus' o ho'
    rw [hT] at hT'
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
    obtain ⟨rfl, rfl⟩ := hT'
    rw [hus] at hus'
    cases hus'
    by_cases hlt : o < E0.ini l * nWords us
    · refine Or.inl fun N2 e2 us2 hT2 hus2 => ?_
      rw [hT] at hT2
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
      obtain ⟨rfl, rfl⟩ := hT2
      rw [hus] at hus2
      cases hus2
      exact hlt
    · obtain ⟨τ, hτ, hW⟩ := hu N e us hT hus o ho' hlt
      rcases hW with h | ⟨hτP, m, hm, hloc⟩
      · exact absurd (Nat.lt_of_le_of_lt hτ hvb) (Nat.not_lt.2 h)
      · exact Or.inr ⟨τ, hτP, m, hm, hloc⟩
  rw [NpZ_of_not hE]
  exact Nat.le_trans (le_Np hc hT hNa hpre) (Nat.le_max_right _ _)

end TermK5Lp

#print axioms TermK5Lp.bufCap_gt
#print axioms TermK5Lp.iniLp_ofV
