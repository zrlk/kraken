import WeakCore.TermOverCrX

/-!
# TermOverCrY: `hent_of`'s `hleft` at a foreign step

An old message leaving the owner's skip list `PromAt` at a non-visible unit was a foreign promise
(it left the owner's ghost footprint `E.fp`), and so was fulfilled by the stepper: it lies in the
store target (`TgtFoot`'s third clause, read through `PromsOK` before and after the step).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **(hleft) A message leaving the owner's skip list lies in the target**, given that the
footprint promises the owner loses lie in the target (`hfpT`). -/
theorem hleft_of {E E' : TEnv} {s s' : St} {l lt : AllocLabel} {ot n : Nat}
    (hpr : s'.promises = s.promises) (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPUb : ∀ o, PredU E' ⟨l, o⟩ → PredU E ⟨l, o⟩)
    (hVis : Vis E l → Vis E' l)
    (hfpT : ∀ t m, t ∈ E.fp → t ∉ E'.fp → t ∉ s.promises → s.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset) :
    ∀ o, ¬ VisU E' ⟨l, o⟩ → ∀ t m, t < s.mem.size → s.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      t ∈ PromAt E s ⟨l, o⟩ → t ∉ PromAt E' s' ⟨l, o⟩ → lt = l ∧ ot ≤ o ∧ ot + n > o := by
  intro o hv' t m _ hm hl hin hout
  have hv := hVU o hv'
  -- both memberships reduce to the unfiltered lists
  have hin0 : t ∈ s.promises ++ FpAt E ⟨l, o⟩ := by
    unfold PromAt at hin
    simp only [hv, ↓reduceIte] at hin
    by_cases hq : PredU E ⟨l, o⟩
    · simp only [hq, ↓reduceIte, List.mem_filter] at hin; exact hin.1
    · simp only [hq, ↓reduceIte] at hin; exact hin
  have hab : PredU E ⟨l, o⟩ → AboveFW s'.mem ⟨l, o⟩ t := by
    intro hq
    unfold PromAt at hin
    simp only [hv, hq, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hin
    obtain ⟨h0, hf, hlt⟩ := hin.2
    exact ⟨h0, FirstW_grow hpre hf, hlt⟩
  have hout0 : t ∉ s'.promises ++ FpAt E' ⟨l, o⟩ := by
    intro hx
    apply hout
    unfold PromAt
    simp only [hv', ↓reduceIte]
    by_cases hq' : PredU E' ⟨l, o⟩
    · simp only [hq', ↓reduceIte, List.mem_filter, decide_eq_true_eq]
      exact ⟨hx, hab (hPUb o hq')⟩
    · simp only [hq', ↓reduceIte]; exact hx
  rw [hpr] at hout0
  have hnp : t ∉ s.promises := fun h => hout0 (List.mem_append_left _ h)
  have hfp : t ∈ FpAt E ⟨l, o⟩ := by
    rcases List.mem_append.1 hin0 with h | h
    · exact absurd h hnp
    · exact h
  have hfp' : t ∉ FpAt E' ⟨l, o⟩ := fun h => hout0 (List.mem_append_right _ h)
  unfold FpAt at hfp hfp'
  by_cases hvl : Vis E l
  · have hvl' := hVis hvl
    simp only [hvl, hvl', ↓reduceIte] at hfp hfp'
    obtain ⟨a, b, c⟩ := hfpT t m hfp hfp' hnp hm
    rw [hl] at a b c
    exact ⟨a.symm, b, c⟩
  · simp only [hvl, ↓reduceIte] at hfp
    exact absurd hfp List.not_mem_nil

#print axioms hleft_of

/-- **(hfpT) A footprint promise the owner loses at a foreign step was the stepper's, and
fulfilled in the target**: by `PromsOK` before and after, and the target clause of `TgtFoot`. -/
theorem fpT_of {Eg Eg' : GEnv} {c c' : Cfg} {i k : Nat} {thi thk thk' : TTh} {lt : AllocLabel} {ot n : Nat}
    (hP : PromsOK Eg c) (hP' : PromsOK Eg' c')
    (hi : c.ths[i]? = some thi) (hik : i ≠ k) (hk' : c'.ths[k]? = some thk')
    (ho : ∀ j, j ≠ k → c'.ths[j]? = c.ths[j]?) (hk : c.ths[k]? = some thk)
    (htg : ∀ (t : Ts) (m : Msg), t ∈ thk.promises → c.mem[t]? = some m →
      ¬ (m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset) → t ∈ thk'.promises) :
    ∀ t m, t ∈ Eg.fpOf i → t ∉ Eg'.fpOf i → t ∉ thi.promises → c.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset := by
  intro t m hf hf' hnp hm
  have hi' : c'.ths[i]? = some thi := by rw [ho i hik]; exact hi
  have hall : t ∈ allProms c := (hP i thi hi t).1 (List.mem_append_right _ hf)
  have hnall : t ∉ allProms c' := fun h => by
    rcases List.mem_append.1 ((hP' i thi hi' t).2 h) with h1 | h1
    · exact hnp h1
    · exact hf' h1
  obtain ⟨j, thj, hj, htj⟩ := TermStepper.mem_allProms.1 hall
  by_cases hjk : j = k
  · subst hjk
    rw [hk] at hj
    cases hj
    exact (Classical.em _).elim id fun hn => False.elim <|
      hnall (TermStepper.mem_allProms.2 ⟨j, thk', hk', htg t m htj hm hn⟩)
  · exact absurd (TermStepper.mem_allProms.2 ⟨j, thj, by rw [ho j hjk]; exact hj, htj⟩) hnall

#print axioms fpT_of

/-- `overCr_foreignMO` with an explicit pre-cover list `Gs` whose `K` bits may cover (`hG`, `hcovD`). -/
theorem overCr_foreignMOG {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
    {Dn Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hI : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o) (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw ∨
      (∃ y ∈ Dn, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧ InAcc usS i (o - y.2.1) ∧
        y.2.2.2.2.2 i = true) ∨
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hL : TermOverCr.OverCrL E s cr l c (TermOverCr.WinG E s l) Gs) (hHL : TermOverCr.HolderLow s l Gs)
    (hD : ∀ y ∈ Dn, TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c y)
    (hsum : ∀ t, sumH Dn t ≤ δ t)
    (hwaD : ∀ y ∈ Dn, ∀ usS i o, accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, y.2.1 + o⟩ t0)
    (hHLD : TermOverCr.HolderLow s l Dn)
    (hcovD : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw ∨
      (∃ y ∈ Dn, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧ InAcc usS i (o - y.2.1) ∧
        y.2.2.2.2.2 i = true) ∨
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hδD : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → δ t ≠ .zero →
      t ∈ Dn.map (·.1)) :
    TermOverCr.OverCrE E' s' (fun t => cr t + δ t) l c := by
  have hsum' : ∀ t, sumH Dn t ≤ cr t + δ t := fun t => Res.le_trans (hsum t) (le_add_leftR _ _)
  obtain ⟨L', hnd, hit', hK', hsrc', htgt', hR'⟩ := crItems_dedup hcpl hni Dn hD hsum'
  have hmapL : ∀ o, (∃ x ∈ Dn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true) →
      ∃ y ∈ L', ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧ InAcc usS i (o - y.2.1) ∧
        y.2.2.2.2.2 i = true := by
    intro o ⟨x, hx, usS, i, h1, h2, h3, h4⟩
    obtain ⟨x', hx', -, f2, f3, f4⟩ := htgt' x hx
    exact ⟨x', hx', usS, i, by rw [f3]; exact h1, by rw [f2]; exact h2, by rw [f2]; exact h3, f4 i h4⟩
  refine overCr_foreignOG (Dn := L') hpre hpr hP hsto hV hI hVU hPU
    (fun o tw hi hv hl hg hov hold => (hG o tw hi hv hl hg hov hold).imp id (fun h2 => h2.imp (hmapL o) id)) hcpl hni hL hHL hit'
    (fun x' hx' => Res.le_trans (hR' x' hx') (hsum x'.1)) hnd
    (fun x' hx' usS i o h1 h2 h3 => ?_) (fun x' hx' usS hus t m ht hm hl h1 h2 => ?_)
    (fun o tw hI' hv hl hw hov => ?_) (fun t m ht hm hl hnz => ?_)
  · obtain ⟨x, hx, -, f2, f3, f4⟩ := hK' x' hx' i h2
    rw [← f3] at h1
    rw [← f2]
    exact hwaD x hx usS i o h1 f4 h3
  · obtain ⟨x, hx, f1, f2, f3⟩ := hsrc' x' hx'
    rw [← f1]
    rw [← f3] at hus
    rw [← f2] at h1 h2
    exact hHLD x hx usS hus t m ht hm hl h1 h2
  · rcases hcovD o tw hI' hv hl hw hov with ho | ⟨x, hx, usS, i, h1, h2, h3, h4⟩ | hgs
    · exact .inl ho
    · obtain ⟨x', hx', -, f2, f3, f4⟩ := htgt' x hx
      exact .inr (.inl ⟨x', hx', usS, i, by rw [f3]; exact h1, by rw [f2]; exact h2, by rw [f2]; exact h3, f4 i h4⟩)
    · exact .inr (.inr hgs)
  · obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hδD t m ht hm hl hnz)
    obtain ⟨x', hx', f1, -⟩ := htgt' x hx
    exact List.mem_map.2 ⟨x', hx', by rw [f1, hx1]⟩

#print axioms overCr_foreignMOG

/-- `hcovD_unit` with the window transport asked only where it is read (`hWbO`). -/
theorem hcovD_unitO {E E' : TEnv} {s : St} {l : AllocLabel} {tg : TermPiece.GdE → Option Ts}
    {Gd : List TermPiece.GdE} {o : Nat} {tw : Ts}
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hv : ¬ VisU E' ⟨l, o⟩) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) (hw0 : TermOverCr.WinG E s l o tw)
    (hold : ¬ TermPlant.OverT E s ⟨l, o⟩ tw)
    (hg : ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) :
    ∃ y ∈ dnOf l tg (kfOf E s l) Gd, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧
      InAcc usS i (o - y.2.1) ∧ y.2.2.2.2.2 i = true := by
  classical
  obtain ⟨g, hg, hgl, ⟨t, ht⟩, us, i, hus, hb, hio, hsing, hL⟩ := hg
  have heq : g.b + (o - g.b) = o := Nat.add_sub_cancel' hb
  have hk : KOk E s l g (o - g.b) := by
    unfold KOk
    rw [heq]
    refine ⟨⟨tw, hl⟩, fun tw' hl' => ?_⟩
    rw [TermPlant.LowOwn_uniq hl' hl]
    obtain ⟨h1, ⟨m, hm, hml⟩, -⟩ := id hl
    refine ⟨hL, TermPromAtFW.promAt_or_firstW h1 hm hml (hnu tw m h1 hm) (hVU o hv),
      fun t1 m1 h1 h2 h3 => ?_, hw0⟩
    exact (Classical.em _).elim id fun hn => False.elim <| by
      unfold TermPlant.OverT at hold
      exact hold ⟨t1, m1, h1, h2, h3, hn⟩
  exact ⟨(t, g.b, g.S, g.ws, g.R, kfOf E s l g), mem_dnOf.2 ⟨g, hg, hgl, t, ht, rfl⟩, us, i, hus, hb, hio,
    kfOf_single hus hsing hk⟩

#print axioms hcovD_unitO

theorem sumH_zero : ∀ {L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))},
    (∀ x ∈ L, x.2.2.2.2.1 = .zero) → ∀ t, sumH L t = .zero
  | [], _, _ => rfl
  | x :: L, h, t => by
      rw [sumH_cons, sumH_zero (fun y hy => h y (List.mem_cons_of_mem _ hy)) t, h x List.mem_cons_self]
      by_cases e : x.1 = t
      · simp [e]
      · simp [e]

/-- `foreign_overCrPZO` with an explicit pre-cover list `Gs` (`OverCrL` + `HolderLow`) whose `K` bits
may cover a unit (`hWbO`, `hent`). -/
theorem foreign_overCrPZOG {E E' : TEnv} {s s' : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    {Fz Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto0 : E.sto l = some c) (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hrc : E'.rc l ≤ E.rc l) (hini : E'.ini l ≤ E.ini l) (hpf : E.pfr l ≠ none)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hWbO : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw ∨
      (∃ x ∈ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hL : TermOverCr.OverCrL E s cr l c (TermOverCr.WinG E s l) Gs) (hHL : TermOverCr.HolderLow s l Gs)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    (hT : ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ m us, s'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ s'.promises → s'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, ∀ t, tg g = some t → t ∈ s.promises)
    (hTl : ∀ g ∈ Gd, ∀ t, tg g = some t → g.l = l)
    (hD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd,
      TermOverCr.CrItemQ E s (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd, ∀ usS i o, accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true →
      InAcc usS i o → ∃ t0, TermPlant.LowOwn s ⟨l, y.2.1 + o⟩ t0)
    (hFi : ∀ x ∈ Fz, TermOverCr.CrItemQ E s (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c x)
    (hFR : ∀ x ∈ Fz, x.2.2.2.2.1 = .zero)
    (hFwa : ∀ x ∈ Fz, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hFHL : TermOverCr.HolderLow s l Fz)
    (hent : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ((∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) ∧
        TermOverCr.WinG E s l o tw) ∨
      (∃ x ∈ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) :
    TermOverCr.OverCrE E' s' (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c := by
  have hpm : ∀ g ∈ Gd, ∀ t m, tg g = some t → s'.mem[t]? = some m → s.mem[t]? = some m := by
    intro g hg t m ht hm
    rw [← hpre t (hP t (hTp g hg t ht))]
    exact hm
  have hinj := tg_inj (E := E) (s := s) (tg := tg) (Gd := Gd) (fun g hg t ht => by
    obtain ⟨m, us, hm, hml, -, hpc, hus, h1, h2⟩ := hT g hg t ht
    exact ⟨m, us, c, hpm g hg t m ht hm, hml, by rw [hTl g hg t ht]; exact hsto0, hpc, hus, h1, h2⟩) hnd
  have hlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → s.mem[t]? = some m → m.loc.label = g.l := by
    intro g hg t m ht hm
    obtain ⟨m', us, hm', hml, -⟩ := hT g hg t ht
    rw [hpm g hg t m' ht hm'] at hm
    cases hm
    exact hml
  obtain ⟨hDR, hDnd, hδD⟩ := dnOf_facts (s := s) (l := l) (Kf := kfOf E s l) hinj hlab hnd
  have hHLD : TermOverCr.HolderLow s l (dnOf l tg (kfOf E s l) Gd) := by
    refine holderLow_dnOfL (fun g hg hgl t ht us hus => ?_)
    obtain ⟨m, us1, hm, hml, hpl, hpc, hus1, h1, h2⟩ := hT g hg t ht
    rw [hus] at hus1
    cases hus1
    intro t' m' ht' hm' hl' h1' h2'
    exact hpl t' m' (by rw [hpr]; exact ht') (by rw [hpre t' (hP t' ht')]; exact hm') (by rw [hl', hml, hgl])
      h1' h2'
  refine overCr_foreignMOG (Dn := dnOf l tg (kfOf E s l) Gd ++ Fz) hpre hpr hP hsto hV
    (covU_back hsto0 hsto hpf hini hrc) hVU hPU
    (fun o tw hi hv hl hg hov hold => (hWbO o tw hi hv hl hg hov hold).imp id
      (fun h2 => h2.imp (fun ⟨x, hx, hr⟩ => ⟨x, List.mem_append_right _ hx, hr⟩) id)) hcpl hni hL hHL
    (fun y hy => (List.mem_append.1 hy).elim (hD y) (hFi y)) (fun t => ?_)
    (fun y hy => (List.mem_append.1 hy).elim (hwaD y) (hFwa y))
    (fun y hy => (List.mem_append.1 hy).elim (fun h1 => hHLD y h1) (fun h1 => hFHL y h1))
    (fun o tw hI hv hl hw hov => ?_)
    (fun t m ht hm hl hnz => List.map_append ▸ List.mem_append_left _ (hδD t m hm hl hnz))
  · rw [sumH_append, sumH_zero hFR, Res.add_zero]
    exact sumH_le_of_nodup hDnd hDR t
  · by_cases hold : TermPlant.OverT E s ⟨l, o⟩ tw
    · exact .inl hold
    · right
      rcases hent o tw hI hv hl hw hov hold with ⟨hg, hw0⟩ | ⟨x, hx, hr⟩ | hgs
      · obtain ⟨y, hy, hr⟩ := hcovD_unitO hVU hnu hv hl hw0 hold hg
        exact .inl ⟨y, List.mem_append_left _ hy, hr⟩
      · exact .inl ⟨x, List.mem_append_right _ hx, hr⟩
      · exact .inr hgs

#print axioms foreign_overCrPZOG

/-- **(H7) The credited cover at a foreign store, post-step targets**: `foreign_overCr` with each
target's plant credit given after the step (`hT`), as TermMain's `Pδ` states it. -/
theorem foreign_overCrP {E E' : TEnv} {s s' : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto0 : E.sto l = some c) (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hrc : E'.rc l ≤ E.rc l) (hini : E'.ini l ≤ E.ini l) (hpf : E.pfr l ≠ none)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hWb : ∀ o tw, TermOverCr.WinG E' s' l o tw → TermOverCr.WinG E s l o tw)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (h : TermOverCr.OverCrE E s cr l c)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    (hT : ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ m R us, s'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      PlantCr E' s' m t R ∧ TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, ∀ t, tg g = some t → t ∈ s.promises)
    (hTl : ∀ g ∈ Gd, ∀ t, tg g = some t → g.l = l)
    (hD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd,
      TermOverCr.CrItemQ E s (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd, ∀ usS i o, accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true →
      InAcc usS i o → ∃ t0, TermPlant.LowOwn s ⟨l, y.2.1 + o⟩ t0)
    (hent : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) :
    TermOverCr.OverCrE E' s' (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c := by
  obtain ⟨Gs, hL, hHL⟩ := h
  exact foreign_overCrPZOG (Fz := []) hpre hpr hP hsto0 hsto hV hrc hini hpf hVU hPU hnu
    (fun o tw _ _ _ hw _ _ => .inl (hWb o tw hw)) hcpl hni hL hHL hnd
    (fun g hg t ht => by
      obtain ⟨m, R, us, hm, hml, hpl, hpc, hus, h1, h2⟩ := hT g hg t ht
      exact ⟨m, us, hm, hml, plantCr_low hpl (by rw [hml, hTl g hg t ht, hsto]; exact hsto0) hpc hus h1 h2,
        hpc, hus, h1, h2⟩)
    hTp hTl hD hwaD (fun x hx => by cases hx) (fun x hx => by cases hx) (fun x hx => by cases hx)
    (fun x hx => by cases hx) (fun o tw a0 a1 a2 hw a4 a5 => .inl ⟨hent o tw a0 a1 a2 hw a4 a5, hWb o tw hw⟩)

#print axioms foreign_overCrP

/-- **(H7) The credited cover at a foreign store, entries discharged**: `foreign_overCrP` with its
entry premise `hent` built by `hent_of` from the store's footprint (`hfoot`, `hpre`), the lost
footprint promises in the target (`hfpT`, for `hleft_of`), the drop list's coverage (`hcov`), the
mask export (`hLT`, for `hL_of`, read in the stepper's view `Ei`, `si` → `si'`) and the targets of
guarded entries (`htgW`, at the pre-state guard). -/
theorem foreign_overCrH {E E' Ek Ei : TEnv} {s s' sk si si' : St} {cr : Ts → Res} {l lt : AllocLabel}
    {c ck : Cell} {ot n : Nat} {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto0 : E.sto l = some c) (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hrc : E'.rc l ≤ E.rc l) (hini : E'.ini l ≤ E.ini l) (hpf : E.pfr l ≠ none)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩) (hPUb : ∀ o, PredU E' ⟨l, o⟩ → PredU E ⟨l, o⟩)
    (hVis : Vis E l → Vis E' l)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hWb : ∀ o tw, TermOverCr.WinG E' s' l o tw → TermOverCr.WinG E s l o tw)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (h : TermOverCr.OverCrE E s cr l c)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    (hT : ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ m R us, s'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      PlantCr E' s' m t R ∧ TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, ∀ t, tg g = some t → t ∈ s.promises)
    (hTl : ∀ g ∈ Gd, ∀ t, tg g = some t → g.l = l)
    (hD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd,
      TermOverCr.CrItemQ E s (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf E s l) Gd, ∀ usS i o, accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true →
      InAcc usS i o → ∃ t0, TermPlant.LowOwn s ⟨l, y.2.1 + o⟩ t0)
    -- the store's footprint
    (hfoot : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset)
    (hfpT : ∀ t m, t ∈ E.fp → t ∉ E'.fp → t ∉ s.promises → s.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset)
    -- the drop list's coverage, in the stepper's view
    (hmemk : sk.mem = s.mem)
    (hcov : ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), Ek.sto lt = some c →
      c.owner ≠ some Ek.tid → TermPiece.Piece c.ty b S → accs S = some vs → t ∈ Ek.fp → sk.mem[t]? = some m →
      m.loc.label = lt → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → ot ≤ m.loc.offset →
      ot + n > m.loc.offset → ∃ g ∈ Gd, g.l = lt ∧ g.b = b ∧ g.S = S)
    (hstok : Ek.sto l = some ck) (hty : ck.ty = c.ty) (hownk : ck.owner ≠ some Ek.tid)
    (hfp : ∀ t, t ∈ s.promises → t ∈ Ek.fp)
    (hpiece : ∀ o, TermOverCr.CovU E' c l o → ∃ b S us, TermPiece.Piece c.ty b S ∧ accs S = some us ∧ b ≤ o ∧
      o < b + nWords us)
    (hsing : ∀ o b S us i, TermPiece.Piece c.ty b S → accs S = some us → b ≤ o → InAcc us i (o - b) →
      ∀ o', InAcc us i o' → o' = o - b)
    -- the mask export
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = l → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis Ei si si' ⟨l, k⟩)
    (hm : si.mem = s.mem) (hm' : si'.mem = s'.mem)
    (hPi : ∀ k t, t ∈ PromAt Ei si ⟨l, k⟩ ↔ t ∈ PromAt E s ⟨l, k⟩)
    (hPi' : ∀ k t, t ∈ PromAt Ei si' ⟨l, k⟩ ↔ t ∈ PromAt E' s' ⟨l, k⟩)
    -- the targets of guarded entries
    (htgW : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E s l o tw →
      ∀ us, accs g.S = some us → g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t) :
    TermOverCr.OverCrE E' s' (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c :=
  foreign_overCrP hpre hpr hP hsto0 hsto hV hrc hini hpf hVU hPU hnu hWb hcpl hni h hnd hT hTp hTl hD hwaD
    (hent_of hmemk hfoot hpre (hleft_of hpr hpre hVU hPUb hVis hfpT) hcov hstok hty hownk hfp hpiece hsing
      (hL_of hLT hm hm' hPi hPi')
      (fun g hg hgl o tw hl hw us hus h1 h2 => htgW g hg hgl o tw hl (hWb o tw hw) us hus h1 h2))

#print axioms foreign_overCrH

/-- **(non-pub foreign step) No entry is needed** when the step's new messages at `l` and the
footprint promises the owner loses at `l` all sit at visible word units: no non-visible unit of
`l` is newly overtaken, so `foreign_overCrP`'s entry premise holds vacuously. -/
theorem hent_vac {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hpr : s'.promises = s.promises) (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPUb : ∀ o, PredU E' ⟨l, o⟩ → PredU E ⟨l, o⟩)
    (hVis : Vis E l → Vis E' l)
    (hnew : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → m.loc.label = l → VisU E' m.loc)
    (hlost : ∀ t m, t ∈ E.fp → t ∉ E'.fp → t ∉ s.promises → s.mem[t]? = some m → m.loc.label = l →
      VisU E' m.loc) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true := by
  intro o tw _ hv _ _ hov hno
  exfalso
  obtain ⟨t, m, hlt, hm, hl, hn⟩ := hov
  by_cases hsz : t < s.mem.size
  · have hm0 : s.mem[t]? = some m := by rw [← hpre t hsz]; exact hm
    have hin : t ∈ PromAt E s ⟨l, o⟩ := (Classical.em _).elim id fun h => False.elim <| hno ⟨t, m, hlt, hm0, hl, h⟩
    have hv0 := hVU o hv
    have hin0 : t ∈ s.promises ++ FpAt E ⟨l, o⟩ := by
      unfold PromAt at hin
      simp only [hv0, ↓reduceIte] at hin
      by_cases hq : PredU E ⟨l, o⟩
      · simp only [hq, ↓reduceIte, List.mem_filter] at hin; exact hin.1
      · simp only [hq, ↓reduceIte] at hin; exact hin
    have hout0 : t ∉ s'.promises ++ FpAt E' ⟨l, o⟩ := by
      intro hx
      apply hn
      unfold PromAt
      simp only [hv, ↓reduceIte]
      by_cases hq' : PredU E' ⟨l, o⟩
      · simp only [hq', ↓reduceIte, List.mem_filter, decide_eq_true_eq]
        refine ⟨hx, ?_⟩
        unfold PromAt at hin
        simp only [hv0, hPUb o hq', ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hin
        obtain ⟨h0, hf, hlt'⟩ := hin.2
        exact ⟨h0, FirstW_grow hpre hf, hlt'⟩
      · simp only [hq', ↓reduceIte]; exact hx
    rw [hpr] at hout0
    have hnp : t ∉ s.promises := fun h => hout0 (List.mem_append_left _ h)
    have hfp : t ∈ FpAt E ⟨l, o⟩ := by
      rcases List.mem_append.1 hin0 with h | h
      · exact absurd h hnp
      · exact h
    have hfp' : t ∉ FpAt E' ⟨l, o⟩ := fun h => hout0 (List.mem_append_right _ h)
    unfold FpAt at hfp hfp'
    by_cases hvl : Vis E l
    · have hvl' := hVis hvl
      simp only [hvl, hvl', ↓reduceIte] at hfp hfp'
      have := hlost t m hfp hfp' hnp hm0 (by rw [hl])
      rw [hl] at this
      exact hv this
    · simp only [hvl, ↓reduceIte] at hfp
      exact absurd hfp List.not_mem_nil
  · have := hnew t m (Nat.le_of_not_lt hsz) hm (by rw [hl])
    rw [hl] at this
    exact hv this

#print axioms hent_vac

end TermOverCrW
