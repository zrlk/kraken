import WeakCore.TermCut

/-!
# TermZwIni: the zero-width count clause `ZwIniG`

At a shared buffer of zero-width elements whose element type is inhabited
(`InhZ`), the reader-visible count `ini` covers the whole buffer.  The plant
sets `ini := max ini (NpZ …)` and `NpZ = N` there (`NpZ_zw`); a publish sets it
by the `EFoot` new-frontier conjunct (`zwIni_post`'s `hnew`).

Consumer: `TermPlantWin.bh1_of` (the zero-width branch of BH1).
-/

namespace TermZwIni

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (ZwIni) **Zero-width buffers are fully counted**: at a frontier label not yet published
(`pubd`: a planted one) holding a buffer of inhabited zero-width elements, `ini` reaches the slot
count.  (Unguarded it is false: `publishBuf` of a partly initialised buffer keeps `ini`, P1 ZT3 z5/z7;
no own handle survives a publish, so `bufInit` never reads a published label, `ownPub`.) -/
def ZwIniG (Eg : GEnv) : Prop :=
  ∀ l c N e us, Eg.pfr l ≠ none → ¬ Eg.pubd l → Eg.sto l = some c → c.ty = .array (.lit N) e → accs e = some us →
    nWords us = 0 → InhZ Eg.prog e → N ≤ Eg.ini l

/-- (ZwIni, plant side) A plant `P` with counts `N` covers every planted buffer of inhabited
zero-width elements (`TermZwIniP.plantN_zw` for `TermPlantF.plantOf`/`plantN`). -/
def PlantZw (Eg : GEnv) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) : Prop :=
  ∀ l f c Nn e us, P l = some f → Eg.sto l = some c → c.ty = .array (.lit Nn) e →
    accs e = some us → nWords us = 0 → InhZ Eg.prog e → Nn ≤ N l

/-- The thread-env form (what `bh1_of` reads at `CE η`), guarded by a published-label set `Pd`. -/
def ZwIniE (E : TEnv) (Pd : AllocLabel → Prop) : Prop :=
  ∀ l c N e us, E.pfr l ≠ none → ¬ Pd l → E.sto l = some c → c.ty = .array (.lit N) e → accs e = some us →
    nWords us = 0 → InhZ E.prog e → N ≤ E.ini l

/-- `promIni` at an environment: every own outstanding promise at a frontier cell lies
at an initialised offset. -/
def PromIniE (E : TEnv) (s : St) : Prop :=
  ∀ t m, t ∈ s.promises → s.mem[t]? = some m → ∀ cl, E.sto m.loc.label = some cl →
    E.pfr m.loc.label ≠ none → InitR E cl m.loc.label m.loc.offset

/-- At a buffer of zero-width elements the maximal held prefix is the whole buffer. -/
theorem Np_zw {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hus : accs e = some us) (h0 : nWords us = 0) :
    Np E s l = N := by
  have hp : PrefixHeld E s l c N := fun N' e' us' hT' hus' o ho => by
    rw [hT] at hT'; cases hT'; rw [hus] at hus'; cases hus'; rw [h0, Nat.mul_zero] at ho
    exact absurd ho (Nat.not_lt_zero _)
  have h1 := le_Np hc hT (Nat.le_refl _) hp
  have h2 := Np_le (s := s) hc hT
  omega

/-- ... and so is `NpZ` at an inhabited element type. -/
theorem NpZ_zw {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc}
    (hc : E.sto l = some c) (hT : c.ty = .array (.lit N) e) (hus : accs e = some us) (h0 : nWords us = 0)
    (hinh : InhZ E.prog e) : NpZ E s l = N := by
  have hne : ¬ EmptyZ E l := by
    rintro ⟨c', N', e', us', hc', hT', hus', -, hni⟩
    rw [hc] at hc'; cases hc'; rw [hT] at hT'; cases hT'
    exact hni hinh
  rw [NpZ_of_not hne]
  exact Np_zw hc hT hus h0

/-- (init) With no frontier anywhere the clause is vacuous. -/
theorem zwIni_none {Eg : GEnv} (h : ∀ l, Eg.pfr l = none) : ZwIniG Eg :=
  fun l _ _ _ _ hp _ => absurd (h l) hp

/-- A cut reads the clause (its cells are cells of `E_g`; counts, frontiers, program shared). -/
theorem zwIniE_cut {Eg : GEnv} (hz : ZwIniG Eg) (i : Nat) (S : AllocLabel → Prop) :
    ZwIniE (Cut Eg i S) Eg.pubd :=
  fun l c N e us hp hd hs hT hus h0 hinh => hz l c N e us hp hd (cutSto_sub hs) hT hus h0 hinh

/-- (thread step) **`E_g` after a step keeps the clause**: old frontiers keep their (old) cells
and counts only grow; a new frontier the step marks seen is published (`pubd`), so exempt; an
unseen new frontier is counted by the footprint (`hnew`, the `EFoot` new-frontier conjunct); a
fresh label with a frontier has none before. -/
theorem zwIni_post {g : G} {Eg : GEnv} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St}
    (hz : ZwIniG Eg) (hf : EFoot g (Cut Eg g.i S) E' s s') (hfr : GFreshE g Eg s.nalloc s'.nalloc)
    (hnew : ∀ l, Eg.pfr l = none → E'.pfr l ≠ none → ¬ E'.seen l → ∀ cl N e us, E'.sto l = some cl →
      cl.ty = .array (.lit N) e → accs e = some us → nWords us = 0 → InhZ Eg.prog e → N ≤ E'.ini l) :
    ZwIniG (Eg.post g s.nalloc s'.nalloc E') := by
  intro l cl N e us hp hd hs hT hus h0 hinh
  obtain ⟨_, _, hsto, _, hini, hpfr, -⟩ := hf
  change E'.pfr l ≠ none at hp
  change ¬ (Eg.pubd l ∨ (Eg.pfr l = none ∧ E'.pfr l ≠ none ∧ E'.seen l)) at hd
  change InhZ Eg.prog e at hinh
  change N ≤ E'.ini l
  have hd0 : ¬ Eg.pubd l := fun h => hd (Or.inl h)
  have hns : Eg.pfr l = none → ¬ E'.seen l := fun h1 h2 => hd (Or.inr ⟨h1, hp, h2⟩)
  by_cases hF : FreshIn g s.nalloc s'.nalloc l
  · rw [post_sto_fresh hF] at hs
    have hn0 : Eg.pfr l = none := (hfr l hF).2.2
    exact hnew l hn0 hp (hns hn0) cl N e us hs hT hus h0 hinh
  · rw [post_sto_old hF] at hs
    rcases hpfr l with e1 | ⟨hn, F, -, -, -, ⟨c0, hc0, -⟩, -⟩ | ⟨hF2, -⟩
    · have hp0 : Eg.pfr l ≠ none := by rw [e1] at hp; exact hp
      exact Nat.le_trans (hz l cl N e us hp0 hd0 hs hT hus h0 hinh) (hini l).1
    · have h1 := cutSto_sub hc0
      rw [hs] at h1; cases h1
      have hs' : E'.sto l = some cl := by
        rcases hsto l with e2 | ⟨hF2, -⟩
        · rw [e2]; exact hc0
        · exact absurd hF2 hF
      exact hnew l hn hp (hns hn) cl N e us hs' hT hus h0 hinh
    · exact absurd hF2 hF

/-- (thread step, after the EFoot conjunct) **`hnew` from the footprint**: an unseen
new frontier of the step is the second `pfr` disjunct (the first keeps `none`; the third has no cell). -/
theorem hnew_of_efoot {g : G} {Eg : GEnv} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St}
    (hf : EFoot g (Cut Eg g.i S) E' s s') :
    ∀ l, Eg.pfr l = none → E'.pfr l ≠ none → ¬ E'.seen l → ∀ cl N e us, E'.sto l = some cl →
      cl.ty = .array (.lit N) e → accs e = some us → nWords us = 0 → InhZ Eg.prog e → N ≤ E'.ini l := by
  intro l hn hp hns cl N e us hs hT hus h0 hinh
  rcases hf.2.2.2.2.2.1 l with e1 | ⟨-, F, -, -, -, -, -, -, hz, -⟩ | ⟨-, -, hs0⟩
  · exact absurd (e1.trans hn) hp
  · exact hz hns cl N e us hs hT hus h0 hinh
  · rw [hs0] at hs; cases hs

#print axioms hnew_of_efoot

#print axioms Np_zw
#print axioms NpZ_zw
#print axioms zwIni_none
#print axioms zwIniE_cut
#print axioms zwIni_post

end TermZwIni
