import WeakCore.TermOverCrD

/-! # TermOverCrH: holders and targets of a foreign store's new items

`HolderLow` for the new items `dnOf` (each holder is a plant credit's promise, lowest among
own promises of its piece up to the window bound, and below the bound itself), and
injectivity of the target map (two entries targeting one promise name the same piece, so
the same drop key).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **A plant credit's promise is lowest in its piece**: below the window bound by the
credit's lowness, above it since the promise is at most the bound. -/
theorem plantCr_low {E : TEnv} {s : St} {m : Msg} {t : Ts} {R : Res} {c : Cell} {b : Nat} {S : Ty}
    {us : List Acc}
    (hP : PlantCr E s m t R) (hsto : E.sto m.loc.label = some c) (hpc : TermPiece.Piece c.ty b S)
    (hus : accs S = some us) (h1 : b ≤ m.loc.offset) (h2 : m.loc.offset < b + nWords us) :
    ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = m.loc.label →
      b ≤ m'.loc.offset → m'.loc.offset < b + nWords us → t ≤ t' := by
  obtain ⟨c', sb, S0, b0, S1, us1, wb, hsto', -, -, hseg, hat, hS, -, hus1, hn, hlo, hhi, htw, -, -,
    hlow, -⟩ := hP
  rw [hsto] at hsto'
  cases hsto'
  have hPc := TermPlant.plant_piece hseg hat hS (wc_of_accs hus1) hn
  obtain ⟨eb, eS⟩ := TermPlant.piece_match hPc hpc (wc_of_accs hus1) (wc_of_accs hus) hlo hhi h1 h2
  rw [eS, hus] at hus1
  cases hus1
  intro t' m' ht hm hl h1' h2'
  by_cases hle : t' ≤ wb
  · exact hlow t' m' ht hm hl (by rw [eb]; exact h1') (by rw [eb]; exact h2') hle
  · exact Nat.le_trans htw (Nat.le_of_lt (Nat.lt_of_not_le hle))

#print axioms plantCr_low

/-- **`HolderLow` for the new items**, from a plant credit at each target, in the
entry's piece. -/
theorem holderLow_dnOf {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {tg : TermPiece.GdE → Option Ts}
    {Kf : TermPiece.GdE → Nat → Bool} {Gd : List TermPiece.GdE}
    (hsto : E.sto l = some c)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m R us, s.mem[t]? = some m ∧ m.loc.label = l ∧
      PlantCr E s m t R ∧ TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us) :
    TermOverCr.HolderLow s l (dnOf l tg Kf Gd) := by
  intro y hy usS hus t' m' ht hm hl h1 h2
  obtain ⟨g, hg, hgl, t, htg, rfl⟩ := mem_dnOf.1 hy
  obtain ⟨m, R, us, hmt, hml, hP, hpc, hus', h1t, h2t⟩ := hT g hg hgl t htg
  have hus2 : accs g.S = some usS := hus
  rw [hus'] at hus2
  cases hus2
  have hsto' : E.sto m.loc.label = some c := by rw [hml]; exact hsto
  exact plantCr_low hP hsto' hpc hus' h1t h2t t' m' ht hm (by rw [hl, hml]) h1 h2

#print axioms holderLow_dnOf

/-- `HolderLow` back along a step keeping the promises and memory's prefix. -/
theorem holderLow_back {s s' : St} {l : AllocLabel} {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size) (h : TermOverCr.HolderLow s' l Gs) :
    TermOverCr.HolderLow s l Gs := by
  intro x hx usS hus t m ht hm hl h1 h2
  exact h x hx usS hus t m (by rw [hpr]; exact ht) (by rw [hpre t (hP t ht)]; exact hm) hl h1 h2

#print axioms holderLow_back

/-- **The target map is injective**: two drop entries targeting one promise name the
piece holding it, hence the same key. -/
theorem tg_inj {E : TEnv} {s : St} {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hT : ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ m us cg, s.mem[t]? = some m ∧ m.loc.label = g.l ∧
      E.sto g.l = some cg ∧ TermPiece.Piece cg.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup) :
    ∀ g ∈ Gd, ∀ g' ∈ Gd, ∀ t, tg g = some t → tg g' = some t → g' = g := by
  intro g hg g' hg' t ht ht'
  obtain ⟨m, us, cg, hm, hml, hs, hpc, hus, h1, h2⟩ := hT g hg t ht
  obtain ⟨m2, us2, cg2, hm2, hml2, hs2, hpc2, hus2, h1', h2'⟩ := hT g' hg' t ht'
  rw [hm] at hm2
  cases hm2
  have el : g'.l = g.l := hml2.symm.trans hml
  rw [el, hs] at hs2
  cases hs2
  obtain ⟨eb, eS⟩ := TermPlant.piece_match hpc hpc2 (wc_of_accs hus) (wc_of_accs hus2) h1 h2 h1' h2'
  have hk : g'.key = g.key := by simp only [TermPiece.GdE.key, el, eb, eS]
  exact eq_of_nodup_map TermPiece.GdE.key hnd hg' hg hk

#print axioms tg_inj

/-- A unit mask is on at a single-word access unit whose word meets `KOk`. -/
theorem kfOf_single {E : TEnv} {s : St} {l : AllocLabel} {g : TermPiece.GdE} {i o : Nat} {us : List Acc}
    (hus : accs g.S = some us) (hsing : ∀ o', InAcc us i o' → o' = o) (hk : KOk E s l g o) :
    kfOf E s l g i = true := by
  classical
  unfold kfOf
  exact decide_eq_true ⟨us, hus, fun o' h => by rw [hsing o' h]; exact hk⟩

#print axioms kfOf_single

/-- (hcovD core) **A newly overtaken unit is covered by a new item**: given, at such a unit, a
drop entry of its piece with a target, whose access unit there is a single word recorded
latest (`g.L`), the entry's item selects that unit. -/
theorem hcovD_core {E E' : TEnv} {s s' : St} {l : AllocLabel} {tg : TermPiece.GdE → Option Ts}
    {Gd : List TermPiece.GdE}
    (hWb : ∀ o tw, TermOverCr.WinG E' s' l o tw → TermOverCr.WinG E s l o tw)
    (hPA : ∀ o tw, ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      tw ∈ PromAt E s ⟨l, o⟩ ∨ (PredU E ⟨l, o⟩ ∧ FirstW s.mem ⟨l, o⟩ tw))
    (hent : ∀ o tw, ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) :
    ∀ o tw, ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw ∨
      ∃ y ∈ dnOf l tg (kfOf E s l) Gd, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧
        InAcc usS i (o - y.2.1) ∧ y.2.2.2.2.2 i = true := by
  classical
  intro o tw hv hl hw hov
  by_cases hold : TermPlant.OverT E s ⟨l, o⟩ tw
  · exact .inl hold
  · right
    obtain ⟨g, hg, hgl, ⟨t, ht⟩, us, i, hus, hb, hio, hsing, hL⟩ := hent o tw hv hl hw hov hold
    have heq : g.b + (o - g.b) = o := Nat.add_sub_cancel' hb
    have hk : KOk E s l g (o - g.b) := by
      unfold KOk
      rw [heq]
      refine ⟨⟨tw, hl⟩, fun tw' hl' => ?_⟩
      rw [TermPlant.LowOwn_uniq hl' hl]
      refine ⟨hL, hPA o tw hv hl, fun t1 m1 h1 h2 h3 => ?_, hWb o tw hw⟩
      exact (Classical.em _).elim id fun hn => False.elim <| by
        unfold TermPlant.OverT at hold
        exact hold ⟨t1, m1, h1, h2, h3, hn⟩
    exact ⟨(t, g.b, g.S, g.ws, g.R, kfOf E s l g), mem_dnOf.2 ⟨g, hg, hgl, t, ht, rfl⟩, us, i, hus, hb, hio,
      kfOf_single hus hsing hk⟩

#print axioms hcovD_core

/-- An own promise is skipped at a non-word unit (above the first write at a predicted one). -/
theorem mem_promAt_own {E : TEnv} {s : St} {a : Address} {tw : Ts} (hv : ¬ VisU E a)
    (hq : PredU E a → AboveFW s.mem a tw) (ht : tw ∈ s.promises) : tw ∈ PromAt E s a := by
  classical
  by_cases hp : PredU E a
  · unfold PromAt
    simp only [hv, hp, ↓reduceIte]
    exact List.mem_filter.2 ⟨List.mem_append_left _ ht, decide_eq_true (hq hp)⟩
  · rw [PromAt_nword hv hp]
    exact List.mem_append_left _ ht

#print axioms mem_promAt_own

end TermOverCrW
