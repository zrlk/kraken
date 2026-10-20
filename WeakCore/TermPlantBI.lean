import WeakCore.TermPlantWin
namespace TermPlant
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPiece
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! # (BI) `bufInit`-at-`rc` pool consumption: `tstepMCF_stepTKA_zfB` -/

/-- (BI) `KeepQRS` gives `KeepQRSB` when the `bufInit`-at-`rc` exclusion holds at every frontier
target. -/
theorem keepQRSB_of_exP {E E' : TEnv} {s s' : St} {th : TTh} {cr cr' plh : Ts → Res}
    (hex : ∀ lab, OpTgtP th lab → E.pfr lab ≠ none → ∀ x b i v e, th.term = .let_ x (.bufInit b i v) e →
      ∀ rti wi n, evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → n ≠ E.rc lab)
    (hK : KeepQRS E E' s s' th cr cr' plh) : KeepQRSB E E' s s' th cr cr' plh :=
  let ⟨cr0, RSc, RSh, h1, h2, h3, h4, h5, h6, h7, h8, h9, hV, h10, h11, h12⟩ := hK
  ⟨cr0, RSc, RSh, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun lab hot c o th0 tw hs hown hpf => hV lab (hex lab hot hpf) hot c o th0 tw hs hown hpf, h10, h11, h12⟩
#print axioms TermPlant.keepQRSB_of_exP

theorem rpSum_append (A B : List (AllocLabel × Cell × CrIt)) (t : Ts) :
    rpSum (A ++ B) t = rpSum A t + rpSum B t := by
  induction A with
  | nil => rw [List.nil_append, rpSum_nil, Res.zero_add]
  | cons y A ih =>
      rw [List.cons_append, rpSum_cons, rpSum_cons, ih]
      exact Res.ext fun k => by simp only [Res.add_apply]; omega
#print axioms TermPlant.rpSum_append

/-- (BI, adapted from `PromCrK_repinU`) Re-pin items raise a `PromCrK` credit to a `PlantCr` one at their
holders. -/
theorem promCrK_addRS {E' : TEnv} {s' : St} {cr db : Ts → Res} {RS : List (AllocLabel × Cell × CrIt)}
    (hC : PromCrK E' s' cr db) (hQ : RepinQU E' s' (rpSum RS) RS) (hP : RepinPl E' s' RS) :
    PromCrK E' s' (fun t => cr t + rpSum RS t) db := by
  intro tw htw
  obtain ⟨m, hm, hd, hc⟩ := hC tw htw
  refine ⟨m, hm, hd, ?_⟩
  by_cases hy : ∃ y ∈ RS, y.2.2.1 = tw
  · obtain ⟨y, hyR, rfl⟩ := hy
    obtain ⟨m1, hm1, hpl⟩ := hP y hyR
    obtain ⟨-, -, -, ⟨mh, -, hmh, -, -, hnw, -⟩, -⟩ := hQ y hyR
    rw [hm] at hm1; cases hm1
    rw [hm] at hmh; cases hmh
    have hK : CrKeys (rpSum RS y.2.2.1) := crKeys_rpSum _ (fun y' hy' => (hQ y' hy').2.2.2.2.1)
    have hge : y.2.2.2.2.2.2.1 ≤ cr y.2.2.1 + rpSum RS y.2.2.1 :=
      Res.le_trans (rpSum_ge hyR) (fun k => by simp only [Res.add_apply]; omega)
    refine .inr ⟨hpl _ hge, ?_⟩
    show CrKeys (cr y.2.2.1 + rpSum RS y.2.2.1)
    rcases hc with ho | ⟨-, hk⟩
    · rw [oldCr_nwordZ hnw ho, Res.zero_add]; exact hK
    · intro l; simp only [Res.add_apply, hk l, hK l]
  · have e : rpSum RS tw = .zero := rpSum_none fun y hy' e => hy ⟨y, hy', e⟩
    simp only [e, Res.add_zero]
    exact hc
#print axioms TermPlant.promCrK_addRS

/-- (BI) **Appending re-pin items to a `KeepQRS` output**: the credited ones raise `cr'`, the others
`plh`; the stepper's credit `cr` may exceed `cr₀` off the surviving promises. -/
theorem keepQRSB_addRS {E E' : TEnv} {s s' : St} {th : TTh} {cr cr₀ cr' plh : Ts → Res}
    {RS : List (AllocLabel × Cell × CrIt)}
    (hK : KeepQRS E E' s s' th cr₀ cr' plh)
    (hsur : ∀ t, t ∈ s'.promises → cr t = cr₀ t) (hle : ∀ t, cr₀ t ≤ cr t)
    (hRI : ∀ y ∈ RS, RepinItU E' s' y) (hcov : RepinCovSB E E' s s' th RS [])
    (hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e) (hnd : s'.promises.Nodup) :
    KeepQRSB E E' s s' th cr (fun t => cr' t + rpSum (rpC E' s' RS) t) (fun t => plh t + rpSum (rpH E' s' RS) t) ∧
    pSum s' (fun t => cr' t + rpSum (rpC E' s' RS) t) + pSum s' (fun t => plh t + rpSum (rpH E' s' RS) t) ≤
      pSum s' cr' + pSum s' plh + Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) := by
  obtain ⟨cr0, RSc, RSh, hKQ, hcr, hQ, hFc, hQh, hFh, hplh, hplhS, hplhK, -, hFul, hRK, -⟩ := hK
  obtain ⟨hQc2, -, hFc2, hQh2, hFh2, hmem2⟩ := repin_splitU hRI
  refine ⟨⟨cr0, RSc ++ rpC E' s' RS, RSh ++ rpH E' s' RS, fun h0 => ?_, fun t => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun t => ?_, fun t ht => ?_, fun t => ?_, ?_, hFul, hRK,
    pubKeep_np hnp⟩, ?_⟩
  · obtain ⟨hpl, hle0⟩ := hKQ h0
    exact ⟨fun t ht hc => by rw [hsur t ht] at hc ⊢; exact hpl t ht hc, fun t => Res.le_trans (hle0 t) (hle t)⟩
  · show cr' t + rpSum (rpC E' s' RS) t = cr0 t + rpSum (RSc ++ rpC E' s' RS) t
    rw [hcr t, rpSum_append]
    exact Res.ext fun k => by simp only [Res.add_apply]; omega
  · rcases List.mem_append.1 hy with h | h
    · exact RepinQU_mono (fun t => Res.le_add_right _ _) hQ y h
    · exact RepinQU_mono (fun t => Res.le_def.2 fun k => by simp only [Res.add_apply]; omega) hQc2 y h
  · rcases List.mem_append.1 hy with h | h
    · exact hFc y h
    · exact hFc2 y h
  · rcases List.mem_append.1 hy with h | h
    · exact hQh y h
    · exact hQh2 y h
  · rcases List.mem_append.1 hy with h | h
    · exact hFh y h
    · exact hFh2 y h
  · show plh t + rpSum (rpH E' s' RS) t = rpSum (RSh ++ rpH E' s' RS) t
    rw [hplh t, rpSum_append]
  · by_cases h1 : plh t = .zero
    · have ht' : rpSum (rpH E' s' RS) t ≠ .zero := by
        intro h2; apply ht; show plh t + rpSum (rpH E' s' RS) t = .zero; rw [h1, h2, Res.zero_add]
      refine Classical.byContradiction fun hn => ht' (rpSum_none fun y hy e => ?_)
      obtain ⟨-, -, -, ⟨mh, -, -, -, hlo, -⟩, -⟩ := hQh2 y hy
      exact hn (e ▸ hlo.1)
    · exact hplhS t h1
  · intro l
    show (plh t + rpSum (rpH E' s' RS) t) (.own l) = 0
    simp only [Res.add_apply, hplhK t l, crKeys_rpSum t (fun y hy => (hQh2 y hy).2.2.2.2.1) l]
  · intro lab hot c o th0 tw a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    obtain ⟨y, hy, hl, hc⟩ := hcov lab hot c o th0 tw a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    rw [List.append_nil] at hy
    refine ⟨y, ?_, hl, hc⟩
    rcases List.mem_append.1 (hmem2 y hy) with h | h
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr h)))
    · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr h)))
  · have e1 := sum_map_split (f := fun t => cr' t + rpSum (rpC E' s' RS) t) (fun t => rfl) s'.promises
    have e2 := sum_map_split (f := fun t => plh t + rpSum (rpH E' s' RS) t) (fun t => rfl) s'.promises
    have hrc := sum_rpSum_le (rpC E' s' RS) hnd
    have hrh := sum_rpSum_le (rpH E' s' RS) hnd
    have hsp := sum_rpC_rpH E' s' (fun y => y.2.2.2.2.2.2.1) RS
    intro k
    have a1 := congrArg (fun R : Res => R k) e1
    have a2 := congrArg (fun R : Res => R k) e2
    have a3 := congrArg (fun R : Res => R k) hsp
    have a4 := hrc k; have a5 := hrh k
    simp only [pSum, Res.add_apply] at a1 a2 a3 a4 a5 ⊢
    omega
#print axioms TermPlant.keepQRSB_addRS

theorem biSum_filter_le {α : Type} (R : α → Res) (p : α → Bool) :
    ∀ (L : List α), Res.sum ((L.filter p).map R) ≤ Res.sum (L.map R)
  | [] => fun k => Nat.le_refl _
  | x :: L => fun k => by
      have ih := biSum_filter_le R p L k
      by_cases h : p x = true
      · simp only [List.filter_cons, h, ite_true, List.map_cons, Res.sum_cons, Res.add_apply] at ih ⊢
        omega
      · simp only [List.filter_cons, h, List.map_cons, Res.sum_cons, Res.add_apply] at ih ⊢
        simp only [Bool.false_eq_true, ite_false]
        omega
#print axioms TermPlant.biSum_filter_le

theorem biSum_filter2_le {α : Type} (R : α → Res) (p q : α → Bool) :
    ∀ (L : List α), Res.sum (((L.filter p).filter q).map R) ≤ Res.sum ((L.filter q).map R)
  | [] => fun k => Nat.le_refl _
  | x :: L => fun k => by
      have ih := biSum_filter2_le R p q L k
      by_cases h : p x = true
      · by_cases h2 : q x = true
        · simp only [List.filter_cons, h, h2, ite_true, List.map_cons, Res.sum_cons, Res.add_apply] at ih ⊢
          omega
        · simp only [List.filter_cons, h, h2, ite_true, Bool.false_eq_true, ite_false] at ih ⊢
          exact ih
      · by_cases h2 : q x = true
        · simp only [List.filter_cons, h, h2, ite_true, Bool.false_eq_true, ite_false, List.map_cons,
            Res.sum_cons, Res.add_apply] at ih ⊢
          omega
        · simp only [List.filter_cons, h, h2, Bool.false_eq_true, ite_false] at ih ⊢
          exact ih
#print axioms TermPlant.biSum_filter2_le

theorem biSum_split {α : Type} (R : α → Res) (p : α → Bool) :
    ∀ (L : List α), Res.sum (L.map R) ≤
      Res.sum ((L.filter p).map R) + Res.sum ((L.filter fun x => !p x).map R)
  | [] => fun k => Nat.zero_le _
  | x :: L => fun k => by
      have ih := biSum_split R p L k
      simp only [Res.add_apply] at ih
      by_cases h : p x = true
      · simp only [List.filter_cons, h, ite_true, Bool.not_true, Bool.false_eq_true, ite_false, List.map_cons,
          Res.sum_cons, Res.add_apply] at ih ⊢
        omega
      · simp only [Bool.not_eq_true] at h
        simp only [List.filter_cons, h, Bool.not_false, ite_true, Bool.false_eq_true, ite_false, List.map_cons,
          Res.sum_cons, Res.add_apply] at ih ⊢
        omega
#print axioms TermPlant.biSum_split

/-- (BI, PoolCovUL v3) **Grouping by holder**: a list's sum is below the sum, over a key list `D`
covering every item's key, of any per-key bound `G t` on the items of key `t`. -/
theorem biSum_group {α : Type} (key : α → Ts) (R : α → Res) (G : Ts → Res) :
    ∀ (D : List Ts) (L : List α), (∀ x ∈ L, key x ∈ D) →
      (∀ t ∈ D, Res.sum ((L.filter fun x => decide (key x = t)).map R) ≤ G t) →
      Res.sum (L.map R) ≤ Res.sum (D.map G)
  | [], L, hk, _ => by
      cases L with
      | nil => exact fun k => Nat.le_refl _
      | cons x L => exact absurd (hk x List.mem_cons_self) List.not_mem_nil
  | d :: D, L, hk, hG => fun k => by
      have hs := biSum_split R (fun x => decide (key x = d)) L k
      have h1 := hG d List.mem_cons_self k
      have ih := biSum_group key R G D (L.filter fun x => !decide (key x = d)) (fun x hx => by
          obtain ⟨hx, hne⟩ := List.mem_filter.1 hx
          rcases List.mem_cons.1 (hk x hx) with e | e
          · simp only [e, decide_true, Bool.not_true, Bool.false_eq_true] at hne
          · exact e)
        (fun t ht => Res.le_trans (biSum_filter2_le R _ _ L) (hG t (List.mem_cons_of_mem _ ht))) k
      simp only [Res.add_apply, List.map_cons, Res.sum_cons] at hs h1 ih ⊢
      omega
#print axioms TermPlant.biSum_group

/-- (BI) **The pool items at a `bufInit` at its buffer's real count** (`hbiP`'s `Gs`, rebuilt in the
post-state): each item covering a discharged slot unit becomes a `RepinItU` item, its mask restricted
to the units with a post-state pin (`kPinU`); their sum is below the discharged promises' `plb` (grouped
by holder: per holder the items' sum is below `plf`, PoolCovUL v3). -/
theorem biPool {E E' : TEnv} {s s' : St} {lab : AllocLabel} {c : Cell} {N : Nat} {el : Ty}
    {us : List Acc} {plf plb : Ts → Res} {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hE' : E' = { E with rini := bumpIni E.rini lab (E.rc lab + 1) }) (hrcI : E.rc lab < E.ini lab)
    (hsto : E.sto lab = some c) (hown : c.owner = some E.tid) (hpf : E.pfr lab ≠ none)
    (hTc : c.ty = .array (.lit N) el) (hus : accs el = some us) (hnoT : Ty.noOwnIn [] c.ty = true)
    (hmem : s'.mem = s.mem) (hone : ∀ u, u ∈ us → u = .one) (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (hdis : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m →
      m.loc.label = lab ∧ E.rc lab * nWords us ≤ m.loc.offset ∧
      m.loc.offset < E.rc lab * nWords us + nWords us ∧ FirstW s.mem m.loc t ∧ s'.vs.coh m.loc = t)
    (hful : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → ¬ WordUnit E m.loc →
      ∀ q S usS, Piece c.ty q S → accs S = some usS → q ≤ m.loc.offset → m.loc.offset < q + nWords usS →
        ∀ o th0, q ≤ o → o < q + nWords usS → LowOwn s ⟨m.loc.label, o⟩ th0 → th0 ∉ s'.promises)
    (hnd : ∀ t, Res.sum ((Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) ≤ plf t) (hGit : ∀ x ∈ Gs, CrItemQP E s plf lab c x)
    (hGcov : ∀ o tw, PredU E ⟨lab, o⟩ → ¬ VisU E ⟨lab, o⟩ → LowOwn s ⟨lab, o⟩ tw → FirstW s.mem ⟨lab, o⟩ tw →
      OverT E s ⟨lab, o⟩ tw → ∃ x ∈ Gs, ∃ usS j, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS j (o - x.2.1) ∧ x.2.2.2.2.2 j = true)
    (hplf : ∀ t, t ∈ s.promises → t ∉ s'.promises → plf t ≤ plb t) :
    ∃ RS : List (AllocLabel × Cell × CrIt), (∀ y ∈ RS, RepinItU E' s' y ∧ y.1 = lab) ∧
      Res.sum (RS.map fun y => y.2.2.2.2.2.2.1) ≤ pSum s plb ∧
      ∀ o th0 tw, ¬ VisU E ⟨lab, o⟩ → LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises → LowOwn s' ⟨lab, o⟩ tw →
        OverT E' s' ⟨lab, o⟩ tw → WinGU E' s' lab o tw → ∃ y ∈ RS, y.1 = lab ∧ CrCov y.2.2 o := by
  classical
  -- the post-environment only bumps the real count
  have hsto' : E'.sto lab = some c := by subst hE'; exact hsto
  have hown' : c.owner = some E'.tid := by subst hE'; exact hown
  have hpf' : E'.pfr lab ≠ none := by subst hE'; exact hpf
  have hWU : ∀ a, WordUnit E' a ↔ WordUnit E a := fun a => by subst hE'; exact Iff.rfl
  have hVU : ∀ a, VisU E' a ↔ VisU E a := fun a => by subst hE'; exact Iff.rfl
  have hFp : ∀ a, FpAt E' a = FpAt E a := fun a => by subst hE'; rfl
  have hV : ∀ {S : Ty} {ws : List Word} {R0 : Res}, ValOfR E S ws R0 → ValOfR E' S ws R0 := fun h => by
    subst hE'
    exact ValOfR_mono (η₁ := E) (η₂ := { E with rini := bumpIni E.rini lab (E.rc lab + 1) }) rfl rfl (fun _ _ h => h) (fun _ => Nat.le_refl _) h (hri := fun l => bumpIni_le _ _ _ l)
  have hrc' : E.rc lab + 1 ≤ E'.rc lab := by
    subst hE'
    show E.rc lab + 1 ≤ min (E.ini lab) (bumpIni E.rini lab (E.rc lab + 1) lab)
    rw [bumpIni_self]; omega
  have hlay : LayT c.ty := Or.inr ⟨N, el, hTc, by rw [hus]; simp⟩
  -- a slot unit: predicted before, real after
  have hslot : ∀ o, E.rc lab * nWords us ≤ o → o < E.rc lab * nWords us + nWords us →
      PredU E ⟨lab, o⟩ ∧ ¬ PredU E' ⟨lab, o⟩ := by
    intro o h1 h2
    have esm : (E.rc lab + 1) * nWords us = E.rc lab * nWords us + nWords us := Nat.succ_mul _ _
    have hm1 : (E.rc lab + 1) * nWords us ≤ E.ini lab * nWords us := Nat.mul_le_mul_right _ hrcI
    have hm2 : (E.rc lab + 1) * nWords us ≤ E'.rc lab * nWords us := Nat.mul_le_mul_right _ hrc'
    rw [esm] at hm1 hm2
    refine ⟨⟨hpf, (IniW_cell hsto hTc hus).mpr (by omega), fun h => ?_⟩,
      fun h => h.2.2 ((IniWr_cell hsto' hTc hus).mpr (by omega))⟩
    have := (IniWr_cell hsto hTc hus).mp h
    omega
  -- a discharged unit: its old lowest promise is the first write, now coherence-latest, below the new one
  have hunit : ∀ o th0 tw, LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises → LowOwn s' ⟨lab, o⟩ tw →
      E.rc lab * nWords us ≤ o ∧ o < E.rc lab * nWords us + nWords us ∧ FirstW s.mem ⟨lab, o⟩ th0 ∧
        s'.vs.coh ⟨lab, o⟩ = th0 ∧ th0 < tw ∧ ∃ m0, s.mem[th0]? = some m0 ∧ m0.loc = ⟨lab, o⟩ := by
    intro o th0 tw hlo hth hlw
    obtain ⟨m0, hm0, hl0⟩ := hlo.2.1
    obtain ⟨-, h1, h2, h3, h4⟩ := hdis th0 m0 hlo.1 hth hm0
    rw [hl0] at h1 h2 h3 h4
    obtain ⟨mt, hmt, hlt⟩ := hlw.2.1
    have hle := hlo.2.2 tw mt (hsub tw hlw.1) (by rw [← hmem]; exact hmt) hlt
    have hne : th0 ≠ tw := fun e => hth (e ▸ hlw.1)
    exact ⟨h1, h2, h3, h4, Nat.lt_of_le_of_ne hle hne, m0, hm0, hl0⟩
  -- the items' accesses are single units (inside an element)
  have hone' : ∀ x ∈ Gs, ∀ usS, accs x.2.2.1 = some usS → ∀ u, u ∈ usS → u = .one := by
    intro x hx usS husS
    obtain ⟨-, -, -, -, -, -, hat, -⟩ := hGit x hx
    rcases AtOff_arr_elem hat hTc with h | ⟨us', j, o', hus', -, -, hat'⟩
    · rw [h, hTc] at husS; simp [accs] at husS
    · rw [hus] at hus'; cases hus'
      obtain ⟨pre, post, e, -⟩ := AtOff_embed hat' hus husS
      intro u hu; exact hone u (by rw [e]; simp [hu])
  -- the post-state pin at a covered discharged unit: the first write's word
  have hpin : ∀ x ∈ Gs, ∀ usS j o th0 tw, accs x.2.2.1 = some usS → x.2.1 ≤ o → InAcc usS j (o - x.2.1) →
      x.2.2.2.2.2 j = true → LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises → LowOwn s' ⟨lab, o⟩ tw →
      WinGU E' s' lab o tw → kPinU E' s' lab x.2.1 usS x.2.2.2.1 x.2.2.2.2.2 j = true := by
    intro x hx usS j o th0 tw husS hq hI hK hlo hth hlw hwn
    obtain ⟨mh, usS0, -, -, -, -, -, -, husS0, -, -, -, hv, -, hpn⟩ := hGit x hx
    rw [husS] at husS0; cases husS0
    have h1 := hone' x hx usS husS
    obtain ⟨-, -, hFW, hcoh, hlt, m0, hm0, hl0⟩ := hunit o th0 tw hlo hth hlw
    refine kPinU_iff.2 ⟨hK, fun o' hI' => ?_⟩
    have e1 := inAcc_ones_eq h1 hI'
    have e2 := inAcc_ones_eq h1 hI
    have e3 : x.2.1 + o' = o := by omega
    rw [e3]
    refine ⟨tw, hlw, hwn, fun w hw => ?_⟩
    have hlo' : LowOwn s ⟨lab, x.2.1 + o'⟩ th0 := by rw [e3]; exact hlo
    rcases hpn j o' w th0 hK hI' hw hlo' with hp | ⟨-, -, m, hm, hmw⟩
    · exfalso
      obtain ⟨t0, m, ht0, hm, hl, hmw, -⟩ := hp
      rw [e3] at hl
      have hu := hFW.2 t0 m ht0 hm hl
      have ho : o' < nWords usS := Nat.lt_of_lt_of_le hI'.2 (TermTear.nWords_take_le _ _)
      exact VR_ones_nundef _ (VRR_VR _ (RLink_of (Coh_CE _) (CohR_CE _)) hv.1) husS h1 o' w ho hw
        (by rw [← hmw]; exact hu)
    · rw [hm0] at hm; cases hm
      rw [← hmw]
      exact predAt_of_winGU hcoh hlt (by rw [hmem]; exact hm0) hl0 hlw hwn
  -- the good items: covering a discharged unit with a post-state pin
  let Good : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → Prop := fun x =>
    ∃ o th0 tw usS j, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS j (o - x.2.1) ∧ x.2.2.2.2.2 j = true ∧
      LowOwn s ⟨lab, o⟩ th0 ∧ th0 ∉ s'.promises ∧ LowOwn s' ⟨lab, o⟩ tw ∧ WinGU E' s' lab o tw
  let Q : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → AllocLabel × Cell × CrIt → Prop := fun x y =>
    y.1 = lab ∧ RepinItU E' s' y ∧ y.2.2.2.2.2.2.1 = x.2.2.2.2.1 ∧ (x.1 ∈ s.promises ∧ x.1 ∉ s'.promises) ∧
      ∀ o th0 tw usS j, accs x.2.2.1 = some usS → x.2.1 ≤ o → InAcc usS j (o - x.2.1) → x.2.2.2.2.2 j = true →
        LowOwn s ⟨lab, o⟩ th0 → th0 ∉ s'.promises → LowOwn s' ⟨lab, o⟩ tw → WinGU E' s' lab o tw →
        CrCov y.2.2 o
  have hmk : ∀ x ∈ Gs, Good x → ∃ y, Q x y := by
    rintro x hx ⟨o0, th0, tw0, usS, j0, husS, hq0, hI0, hK0, hlo0, hth0, hlw0, hwn0⟩
    obtain ⟨mh, usS1, hmh, hlab, hlo, hnw, hat, hsol, husS1, hq1, hq2, hwl, hv, -, -⟩ := hGit x hx
    rw [husS] at husS1; cases husS1
    have ho0 : o0 - x.2.1 < nWords usS := Nat.lt_of_lt_of_le hI0.2 (TermTear.nWords_take_le _ _)
    have hP : Piece c.ty x.2.1 x.2.2.1 :=
      ⟨hat, hsol, by rw [wc_of_accs husS]; intro h; injection h with h; omega⟩
    have hel : mh.loc = ⟨lab, mh.loc.offset⟩ := by rw [← hlab]
    have hnwE := nword_piece hsto hP husS hq1 hq2 (by rw [← hel]; exact hnw)
    have hnw' : ∀ o', x.2.1 ≤ o' → o' < x.2.1 + nWords usS → ¬ WordUnit E' ⟨lab, o'⟩ :=
      fun o' h1 h2 h => hnwE o' h1 h2 ((hWU _).1 h)
    have hk : CrKeysP x.2.2.2.2.1 := fun l => TermBlkZ.VRR_own_zero l x.2.2.1 [] (CE E.unsee) (fun _ => 0)
      (shp x.2.2.1) _ _ (noOwn_AtOff hat hnoT) (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h) hv.1
    obtain ⟨t, hRt⟩ := repin_itemU (K := x.2.2.2.2.2) hsto' hown' hpf' hlay hP husS hnw' hwl (hV hv) hk hI0
      (hpin x hx usS j0 o0 th0 tw0 husS hq0 hI0 hK0 hlo0 hth0 hlw0 hwn0)
    -- the holder is discharged: the step fulfils the whole piece
    obtain ⟨m0, hm0, hl0⟩ := hlo0.2.1
    have hnw0 : ¬ WordUnit E m0.loc := by rw [hl0]; exact hnwE o0 hq0 (by omega)
    have hl0' : m0.loc.label = lab := by rw [hl0]
    have hhd := hful th0 m0 hlo0.1 hth0 hm0 hnw0 x.2.1 x.2.2.1 usS hP husS (by rw [hl0]; exact hq0)
      (by rw [hl0]; show o0 < x.2.1 + nWords usS; omega) mh.loc.offset x.1 hq1 hq2
      (by rw [hl0']; rw [← hel]; exact hlo)
    refine ⟨(lab, c, (t, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, kPinU E' s' lab x.2.1 usS x.2.2.2.1 x.2.2.2.2.2)),
      rfl, hRt, rfl, ⟨hlo.1, hhd⟩, fun o th0' tw' usS' j husS' hq hI hK hlo' hth' hlw' hwn' => ?_⟩
    rw [husS] at husS'; cases husS'
    exact ⟨usS, j, husS, hq, hI, hpin x hx usS j o th0' tw' husS hq hI hK hlo' hth' hlw' hwn'⟩
  obtain ⟨RS, hRS1, hRS2, hRS3⟩ := pick_list Q (fun x => x.2.2.2.2.1) (fun y => y.2.2.2.2.2.2.1)
    (fun x y hq => by rw [hq.2.2.1]; exact Res.le_refl _) (Gs.filter fun x => decide (Good x))
  have hdis2 : ∀ x ∈ Gs.filter (fun x => decide (Good x)), x.1 ∈ s.promises ∧ x.1 ∉ s'.promises := by
    intro x hx
    obtain ⟨hx, hg⟩ := List.mem_filter.1 hx
    obtain ⟨y, hy⟩ := hmk x hx (of_decide_eq_true hg)
    exact hy.2.2.2.1
  refine ⟨RS, fun y hy => ?_, ?_, ?_⟩
  · obtain ⟨x, -, hq⟩ := hRS1 y hy
    exact ⟨hq.2.1, hq.1⟩
  · -- grouped by holder (PoolCovUL v3): per discharged holder the items' sum is below `plf ≤ plb`
    refine Res.le_trans hRS3 (Res.le_trans (biSum_group (fun x => x.1) (fun x => x.2.2.2.2.1) plb
      (nodupL ((Gs.filter fun x => decide (Good x)).map (·.1))) _
      (fun x hx => mem_nodupL.2 (List.mem_map.2 ⟨x, hx, rfl⟩)) (fun t ht => ?_)) ?_)
    · obtain ⟨x, hx, e⟩ := List.mem_map.1 (mem_nodupL.1 ht)
      obtain ⟨h1, h2⟩ := hdis2 x hx
      rw [← e]
      exact Res.le_trans (biSum_filter2_le _ _ _ Gs) (Res.le_trans (hnd x.1) (hplf x.1 h1 h2))
    · exact sum_sub_le (nodupL_nodup _) (fun t ht => by
        obtain ⟨x, hx, e⟩ := List.mem_map.1 (mem_nodupL.1 ht)
        rw [← e]
        exact (hdis2 x hx).1)
  · intro o th0 tw hnv hlo hth hlw hov hwn
    obtain ⟨h1, h2, hFW, hcoh, hlt, m0, hm0, hl0⟩ := hunit o th0 tw hlo hth hlw
    obtain ⟨hPU, hnP'⟩ := hslot o h1 h2
    -- the overtaking write was not an old promise there: the unit was overtaken before
    have hov0 : OverT E s ⟨lab, o⟩ th0 := by
      obtain ⟨t, m, htw, hm, hl, hnP⟩ := hov
      refine ⟨t, m, Nat.lt_trans hlt htw, by rw [← hmem]; exact hm, hl, fun hP => hnP ?_⟩
      have hnv' : ¬ VisU E' ⟨lab, o⟩ := fun h => hnv ((hVU _).1 h)
      have e1 : PromAt E' s' ⟨lab, o⟩ = s'.promises ++ FpAt E' ⟨lab, o⟩ := by
        simp only [PromAt, hnv', hnP', ↓reduceIte]
      have e0 : PromAt E s ⟨lab, o⟩ =
          (s.promises ++ FpAt E ⟨lab, o⟩).filter (fun t => decide (AboveFW s.mem ⟨lab, o⟩ t)) := by
        simp only [PromAt, hnv, hPU, ↓reduceIte]
      rw [e0] at hP
      rw [e1, hFp]
      rcases List.mem_append.1 (List.mem_filter.1 hP).1 with h | h
      · by_cases h' : t ∈ s'.promises
        · exact List.mem_append.2 (Or.inl h')
        · obtain ⟨-, -, -, -, hc⟩ := hdis t m h h' (by rw [← hmem]; exact hm)
          rw [hl, hcoh] at hc
          exact absurd hc (Nat.ne_of_lt (Nat.lt_trans hlt htw))
      · exact List.mem_append.2 (Or.inr h)
    obtain ⟨x, hx, usS, j, husS, hq, hI, hK⟩ := hGcov o th0 hPU hnv hlo hFW hov0
    have hg : Good x := ⟨o, th0, tw, usS, j, husS, hq, hI, hK, hlo, hth, hlw, hwn⟩
    obtain ⟨y, hy, hqy⟩ := hRS2 x (List.mem_filter.2 ⟨hx, decide_eq_true hg⟩) (hmk x hx hg)
    exact ⟨y, hy, hqy.1, hqy.2.2.2.2 o th0 tw usS j husS hq hI hK hlo hth hlw hwn⟩
#print axioms TermPlant.biPool

set_option maxHeartbeats 1600000 in
/-- (BI) **`tstepMCF_stepTKA_zfC` with the `bufInit`-at-`rc` pool consumed** (`hbiP`): at a frontier
`bufInit` at its buffer's real count the step runs at `cr₀` and `hbiP`'s pool items are rebuilt in the
post-state, so the cover needs no exclusion (`KeepQRSB`). -/
theorem tstepMCF_stepTKA_zfB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db cr₁ : Ts → Res}
    {cr₀ plb plf : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCrK (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    {Ok : Memory × List Ts × TTh → Prop}
    (hpo : OwnFrOp (CE η) cx th → ∀ lab c, (CE η).sto lab = some c → c.owner = some (CE η).tid →
      (CE η).pfr lab ≠ none → OpTgt th lab → PlantOp g mem pairs th (CE η) cr₁ Ok lab c)
    (hle : NotBiRc th (CE η) → ∀ r ∈ tstep g mem pairs th, Ok r → ∀ t m, t ∈ (stOf mem pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises →
      mem[t]? = some m → (∀ f mf, f ∈ FpAt (CE η) ⟨m.loc.label, 0⟩ → mem[f]? = some mf → mf.loc.label = m.loc.label → t < f) →
      cr₁ t ≤ cr t)
    (hni : OpNI cx th)
    (hclo : ∀ lab c, (CE η).sto lab = some c → Clo c.ty)
    (hbi : ∀ x b i v e, th.term = .let_ x (.bufInit b i v) e →
      (∀ rt w ad rti wi n, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
        evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → (CE η).pfr ad.label ≠ none →
        (CE η).rc ad.label ≤ n → n < (CE η).ini ad.label) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∀ o, PredU (CE η) ⟨ad.label, o⟩ → ∃ h, FirstW (stOf mem pairs th).mem ⟨ad.label, o⟩ h ∧
        h ∈ (stOf mem pairs th).promises ∧ ∀ t m, t ∈ (stOf mem pairs th).promises →
          (stOf mem pairs th).mem[t]? = some m → m.loc = ⟨ad.label, o⟩ →
          (stOf mem pairs th).vs.coh ⟨ad.label, o⟩ < t → h ≤ t) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∃ Sp, MemHeldL (CE η) (stOf mem pairs th) H Sp ∧ SlotPayS (CE η) (stOf mem pairs th) Sp cr db ad.label))
    (hbiP : HbiP g mem pairs th η H cr cr₀ plb plf db Ok)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hz0 : ∀ l, ¬ g.zf l := by exact fun _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
      ThInvMCFQK (fun E' => BiOut th E' ∧ KeepQRSB (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh ∧
          IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
        p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
          pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
        (¬ PubShape cx th → Gd = []) := by
  by_cases hBR : NotBiRc th (CE η)
  · -- off a frontier `bufInit` at its buffer's real count: the exclusion holds
    have h := tstepMCF_stepTKA_zfC (hz0 := hz0) (hPb := hPb) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw
      hwp hwin hfo hrmw hbf hpo hle hni hclo hbi hRP hPS hSub hSig hown1
    refine ⟨h.1, fun r hr hpa hok => ?_⟩
    obtain ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', hq, hrest⟩, h2⟩ := h.2 r hr hpa hok
    refine ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', ⟨hq.1, keepQRSB_of_exP
      (fun lab hot hpf x b i v e ht rti wi n hei hnm hnr => ?_) hq.2.1, hq.2.2.1⟩, hrest⟩, h2⟩
    obtain ⟨q, rt, w, ad, off, hq0, he, hw, rfl⟩ := hot
    rw [ht] at hq0
    simp only [opAtomP, Option.some.injEq] at hq0
    subst hq0
    have hz := bufInit_locZ hi.1.2.1 hT ht rt w ad off he hw
    subst hz
    exact hBR x b i v e rt w ad rti wi ht he hw hei (by rw [hnm, hnr]) hpf
  -- (H) a frontier `bufInit` at its buffer's real count: the step at `cr₀`, then the pool items
  obtain ⟨x, b, i, v, e, rt, w, ad, rti, wi, ht, he, hw, hei, hnm, hf⟩ : ∃ x b i v e rt w ad rti wi,
      th.term = .let_ x (.bufInit b i v) e ∧ evalAt th.env b = some (rt, [w]) ∧ w.val = .loc ad 0 ∧
      evalAt th.env i = some (rti, [wi]) ∧ numOf [wi] = some ((CE η).rc ad.label) ∧
      (CE η).pfr ad.label ≠ none :=
    Classical.byContradiction fun hc => hBR fun x b i v e rt w ad rti wi ht he hw hei hnm hf =>
      hc ⟨x, b, i, v, e, rt, w, ad, rti, wi, ht, he, hw, hei, hnm, hf⟩
  obtain ⟨Sp, Gs, hsplit, hCk0, hplb, hplf, hHL, hpay0, hndG, hcell⟩ :=
    hbiP x b i v e ht rt w ad rti wi he hw hei hnm hf
  have hO0 : OwnOpT cx th.term := Or.inl ⟨x, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, i, v, ht⟩))))⟩
  have htg : OpTgt th ad.label := ⟨b, rt, w, ad, 0, by rw [ht]; rfl, he, hw, rfl⟩
  have htgP : OpTgtP th ad.label := ⟨b, rt, w, ad, 0, by rw [ht]; rfl, he, hw, rfl⟩
  have hOF : OwnFrOp (CE η) cx th := ⟨hO0, ad.label, hf, htg⟩
  have hnp : ∀ x' a e', th.term ≠ .let_ x' (.publish a) e' := fun x' a e' h' => by rw [ht] at h'; cases h'
  have h := tstepMCF_stepTKA_zfC (cr := cr₀) (hz0 := hz0) (hPb := hPb) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx
    hCk0 hia hdw hwp hwin hfo hrmw hbf hpo (fun hnb => (hnb x b i v e rt w ad rti wi ht he hw hei hnm hf).elim)
    hni hclo (fun x' b' i' v' e' ht' => ⟨(hbi x' b' i' v' e' ht').1, (hbi x' b' i' v' e' ht').2.1,
      fun rt' w' ad' he' hw' _ => by
        rw [ht] at ht'; cases ht'
        cases some_det he he'
        rw [hw] at hw'; cases hw'
        exact ⟨Sp, hHL, hpay0⟩⟩) hRP hPS hSub hSig hown1
  refine ⟨h.1, fun r hr hpa hok => ?_⟩
  obtain ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', ⟨hq1, hq2, hq3, hq4⟩, hEF, hSO, hBV, hTI, hMI, hMH, hPC⟩,
    hMS, hCl, hDr, hbal, hG1, hG2⟩ := h.2 r hr hpa hok
  obtain ⟨hE', hrcI, c, N, el, us, hsto, hown, hTc, hus, hmem, hone, hsub, hdis⟩ :=
    hq4 x b i v e rt w ad rti wi ht he hw hei hnm hf
  have hmem0 : r.1 = mem := hok.1 hOF
  obtain ⟨wB, -, hW1, -, hW3, -⟩ := hpo hOF ad.label c hsto hown hf htg
  obtain ⟨hGit, hGcov⟩ := hcell c hsto
  obtain ⟨f, hff⟩ := Option.ne_none_iff_exists'.1 hf
  have hnoT := MemInv_noOwnT hm hsto hff
  -- the pool credit is below `plb` at the discharged promises (guarded by `PlantOp`)
  have hplf' : ∀ t, t ∈ (stOf mem pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises → plf t ≤ plb t := by
    intro t ht1 ht2
    obtain ⟨m, hm', -⟩ := hCk0 t ht1
    have hl := (hdis t m ht1 ht2 hm').1
    exact hplf r hr hok.2 t m ht1 ht2 hm' fun f' mf hf' hmf hl' => by
      rw [hl] at hf' hl'
      exact Nat.lt_of_le_of_lt (hW1 r hr hmem0 hok.2 t ht1 ht2) (hW3 f' mf hf' hmf hl')
  -- the step fulfils every piece it touches (`FulP`)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hFul, _, _⟩ := id hq2
  have hful : ∀ t m, t ∈ (stOf mem pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises →
      (stOf mem pairs th).mem[t]? = some m → ¬ WordUnit (CE η) m.loc →
      ∀ q S usS, Piece c.ty q S → accs S = some usS → q ≤ m.loc.offset → m.loc.offset < q + nWords usS →
        ∀ o th0, q ≤ o → o < q + nWords usS → LowOwn (stOf mem pairs th) ⟨m.loc.label, o⟩ th0 →
          th0 ∉ (stOf r.1 r.2.1 r.2.2).promises := by
    intro t m ht1 ht2 hm' hnw
    have hl := (hdis t m ht1 ht2 hm').1
    exact (hFul hmem (by rw [ht]; rfl) ⟨ad.label, htgP, hf⟩ t m c ht1 ht2 hm' (by rw [hl]; exact hsto) hown
      (by rw [hl]; exact hf) hnw).2
  obtain ⟨RS, hRS1, hRSs, hRSc⟩ := biPool (E := CE η) (E' := E') (s := stOf mem pairs th)
    (s' := stOf r.1 r.2.1 r.2.2) hE' hrcI hsto hown hf hTc hus hnoT hmem hone hsub hdis hful hndG hGit hGcov hplf'
  have hcov : RepinCovSB (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th RS [] := by
    intro lab hot c' o th0 tw _ _ _ hnv hlo hth hlw hov hwn _
    obtain rfl := opTgtP_of (q := b) (by rw [ht]; rfl) he hw lab hot
    obtain ⟨y, hy, hl, hc⟩ := hRSc o th0 tw hnv hlo hth hlw hov hwn
    exact ⟨y, by rw [List.append_nil]; exact hy, hl, hc⟩
  have hsur : ∀ t, t ∈ (stOf r.1 r.2.1 r.2.2).promises → cr t = cr₀ t := fun t ht' => by
    rw [hsplit t]
    by_cases h0 : plb t = .zero
    · rw [h0, Res.add_zero]
    · exact absurd ht' ((hplb t h0).2 r hr hok.2)
  obtain ⟨hKB, hbal2⟩ := keepQRSB_addRS hq2 hsur (fun t => by rw [hsplit t]; exact Res.le_add_right _ _)
    (fun y hy => (hRS1 y hy).1) hcov hnp (MemInv_nodup hMI)
  obtain ⟨hQc2, hPl2, -⟩ := repin_splitU (fun y hy => (hRS1 y hy).1)
  refine ⟨Tot, H', C, F, fun t => cr' t + rpSum (rpC E' (stOf r.1 r.2.1 r.2.2) RS) t, db', Gd,
    fun t => plh t + rpSum (rpH E' (stOf r.1 r.2.1 r.2.2) RS) t,
    ⟨E', ⟨hq1, hKB, hq3⟩, hEF, hSO, hBV, hTI, hMI, hMH, promCrK_addRS hPC hQc2 hPl2⟩, hMS, hCl, hDr, ?_, hG1, hG2⟩
  have e1 := sum_map_split (f := cr) (fun t => hsplit t) (stOf mem pairs th).promises
  intro k
  have a1 := hbal k; have a2 := hbal2 k; have a3 := hRSs k
  have a4 := congrArg (fun R : Res => R k) e1
  simp only [pSum, Res.add_apply] at a1 a2 a3 a4 ⊢
  omega
#print axioms TermPlant.tstepMCF_stepTKA_zfB

end TermPlant
