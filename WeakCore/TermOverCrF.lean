import WeakCore.TermOverCrW

/-! # TermOverCrF: the credited cover at a foreign store (β′ composite)

A foreign store hands the owner a list `Dn` of new credited items (one per touched piece, at
the piece's lowest own promise, funded by the plant transfer `δ`).  An old item whose holder is
a new item's holder absorbs it (`crItem_merge`); the other new items are appended.  The
result is `OverCrE` after the step at credits `cr + δ`.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- Raising the credit at the holder keeps a credited item. -/
theorem crItem_mono {E : TEnv} {s : St} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hle : cr x.1 ≤ cr' x.1)
    (h : TermPlant.CrItem E s cr l c x) : TermPlant.CrItem E s cr' l c x := by
  obtain ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, hR, hpin⟩ := h
  exact ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, Res.le_trans hR hle, hpin⟩

/-- An item's resources are below its holder's credit. -/
theorem crItem_R {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (h : TermPlant.CrItem E s cr l c x) : x.2.2.2.2.1 ≤ cr x.1 := by
  obtain ⟨_mh, _usS, -, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := h
  exact hR

/-- Raising the credit at the holder keeps a pin-relaxed credited item. -/
theorem crItemQ_mono {E : TEnv} {s : St} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hle : cr x.1 ≤ cr' x.1)
    (h : TermOverCr.CrItemQ E s cr l c x) : TermOverCr.CrItemQ E s cr' l c x := by
  obtain ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, hR, hpin⟩ := h
  exact ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, Res.le_trans hR hle, hpin⟩

/-- A pin-relaxed item's resources are below its holder's credit. -/
theorem crItemQ_R {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (h : TermOverCr.CrItemQ E s cr l c x) : x.2.2.2.2.1 ≤ cr x.1 := by
  obtain ⟨_mh, _usS, -, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := h
  exact hR

/-- In a list with distinct keys, the key determines the element. -/
theorem eq_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {L : List α}, (L.map f).Nodup → ∀ {a b : α}, a ∈ L → b ∈ L → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: L, hnd, a, b, ha, hb, e => by
      rw [List.map_cons] at hnd
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
      rcases List.mem_cons.1 ha with rfl | ha'
      · rcases List.mem_cons.1 hb with rfl | hb'
        · rfl
        · exact absurd (by rw [e]; exact List.mem_map_of_mem hb') hx
      · rcases List.mem_cons.1 hb with rfl | hb'
        · exact absurd (by rw [← e]; exact List.mem_map_of_mem ha') hx
        · exact eq_of_nodup_map f hnd' ha' hb' e

/-- A key-preserving relation, total on a list, lifts to a list with the same keys. -/
theorem list_rel {α β : Type} (key : α → β) (R : α → α → Prop) (hk : ∀ x x', R x x' → key x' = key x) :
    ∀ (L : List α), (∀ x ∈ L, ∃ x', R x x') →
      ∃ L' : List α, L'.map key = L.map key ∧ (∀ x' ∈ L', ∃ x ∈ L, R x x') ∧ ∀ x ∈ L, ∃ x' ∈ L', R x x'
  | [], _ => ⟨[], rfl, fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (List.not_mem_nil)⟩
  | x :: L, h => by
      obtain ⟨x', hx'⟩ := h x (List.mem_cons_self)
      obtain ⟨L', e, h1, h2⟩ := list_rel key R hk L (fun y hy => h y (List.mem_cons_of_mem _ hy))
      refine ⟨x' :: L', by rw [List.map_cons, List.map_cons, e, hk x x' hx'], fun y hy => ?_, fun y hy => ?_⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, hx'⟩
        · obtain ⟨z, hz, hr⟩ := h1 y hy
          exact ⟨z, List.mem_cons_of_mem _ hz, hr⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨x', List.mem_cons_self, hx'⟩
        · obtain ⟨z, hz, hr⟩ := h2 y hy
          exact ⟨z, List.mem_cons_of_mem _ hz, hr⟩

/-- `hI` of `overCr_foreign` from the real count not rising at `l`. -/
theorem initRr_back {E E' : TEnv} {c : Cell} {l : AllocLabel} (hrc : E'.rc l ≤ E.rc l) :
    ∀ o, InitRr E' c l o → InitRr E c l o :=
  fun _ h N e us h1 h2 => Nat.lt_of_lt_of_le (h N e us h1 h2) (Nat.mul_le_mul_right _ hrc)

#print axioms initRr_back

/-- `overCr_interfM` with the window transport asked only where it is read (`hWbO`). -/
theorem overCr_interfMO {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
    {G G' : Nat → Ts → Prop}
    {Gs Gs' Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hI : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o) (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G' o tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw → G o tw ∨
      ∃ x ∈ Gs' ++ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (h : TermOverCr.OverCrL E s cr l c G Gs)
    (hmap : Gs'.map (·.1) = Gs.map (·.1))
    (hitU : ∀ x ∈ Gs', TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c x)
    (hwaU : ∀ x ∈ Gs', ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hup : ∀ o, (∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true) → ∃ x ∈ Gs', ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true)
    (hGn : ∀ x ∈ Gn, TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c x)
    (hnd : (Gn.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Gs', ∀ y ∈ Gn, x.1 ≠ y.1)
    (hwaN : ∀ x ∈ Gn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hcovN : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G' o tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw ∨
      ∃ x ∈ Gs' ++ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hδ : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → δ t ≠ .zero →
      t ∈ (Gs' ++ Gn).map (·.1)) :
    TermOverCr.OverCrL E' s' (fun t => cr t + δ t) l c G' (Gs' ++ Gn) := by
  have hpr1 : ∀ t, t ∈ s.promises → t ∈ s'.promises := fun t ht => by rw [hpr]; exact ht
  have hnew : ∀ t, t ∈ s'.promises → t ∉ s.promises → s.mem.size ≤ t := fun t ht hn => by
    rw [hpr] at ht; exact absurd ht hn
  have hcr2 : ∀ t, t ∈ s.promises → cr t + δ t ≤ cr t + δ t := fun t _ => Res.le_refl _
  obtain ⟨hnd0, -, hcov, -, hz⟩ := h
  have hlow' : ∀ a tw, TermPlant.LowOwn s' a tw → TermPlant.LowOwn s a tw := fun a tw hl =>
    TermOverCr.lowOwn_back hpre hpr1 hP hl (by rw [← hpr]; exact hl.1)
  refine ⟨?_, fun x hx => ?_, fun o tw hi hv hl hg hov => ?_, fun x hx usS i o h1 h2 h3 => ?_,
    fun t m ht hm hl hw hnz => ?_⟩
  · rw [List.map_append, hmap]
    refine List.nodup_append.2 ⟨hnd0, hnd, fun a ha b hb => ?_⟩
    rw [← hmap] at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact hdisj x hx y hy
  · rcases List.mem_append.1 hx with hx | hx
    · exact TermOverCr.crItem_frame hpre hpr1 hnew hP hsto hV hcr2 (hwaU x hx) hPU (hitU x hx)
    · exact TermOverCr.crItem_frame hpre hpr1 hnew hP hsto hV hcr2 (hwaN x hx) hPU (hGn x hx)
  · have hl0 := hlow' _ _ hl
    rcases hcovN o tw hi hv hl0 hg hov with hold | hr
    · rcases hG o tw hi hv hl0 hg hov hold with hg0 | hr
      · obtain ⟨x, hx, hr⟩ := hup o (hcov o tw (hI o hi) (hVU o hv) hl0 hg0 hold)
        exact ⟨x, List.mem_append_left _ hx, hr⟩
      · exact hr
    · exact hr
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨t0, h0⟩ := hwaU x hx usS i o h1 h2 h3
      exact ⟨t0, TermOverCr.lowOwn_fwd hpre hpr1 hnew hP h0⟩
    · obtain ⟨t0, h0⟩ := hwaN x hx usS i o h1 h2 h3
      exact ⟨t0, TermOverCr.lowOwn_fwd hpre hpr1 hnew hP h0⟩
  · have ht0 : t ∈ s.promises := by rw [← hpr]; exact ht
    have hm0 : s.mem[t]? = some m := by rw [← hpre t (hP t ht0)]; exact hm
    have hw0 : ¬ WordUnit E m.loc := fun hw0 => hw (by
      obtain ⟨c1, hc1, hor⟩ := hw0
      exact ⟨c1, by rw [hl, hsto, ← hl]; exact hc1, hor⟩)
    by_cases hd : δ t = .zero
    · have hnz0 : cr t ≠ .zero := fun h0 => hnz (by
        show cr t + δ t = .zero
        rw [h0, hd]; rfl)
      rw [List.map_append, hmap]
      exact List.mem_append_left _ (hz t m ht0 hm0 hl hw0 hnz0)
    · exact hδ t m ht0 hm0 hl hd

#print axioms overCr_interfMO

/-- `overCr_foreignO` with an explicit pre-cover list `Gs` whose `K` bits may cover (`hG`, `hcovD`). -/
theorem overCr_foreignOG {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
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
    (hDR : ∀ y ∈ Dn, y.2.2.2.2.1 ≤ δ y.1)
    (hDnd : (Dn.map (·.1)).Nodup)
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
  classical
  have hL0 := hL
  obtain ⟨hnd0, hit, -, hwa, -⟩ := hL0
  -- the in-place upgrade relation
  let R : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → Prop :=
    fun x x' => x'.1 = x.1 ∧ x'.2.1 = x.2.1 ∧ x'.2.2.1 = x.2.2.1 ∧
      TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c x' ∧
      (∀ i, x.2.2.2.2.2 i = true → x'.2.2.2.2.2 i = true) ∧
      (∀ i, x'.2.2.2.2.2 i = true → x.2.2.2.2.2 i = true ∨ ∃ y ∈ Dn, y.1 = x.1 ∧ y.2.2.2.2.2 i = true) ∧
      ∀ y ∈ Dn, y.1 = x.1 → y.2.1 = x.2.1 ∧ y.2.2.1 = x.2.2.1 ∧ ∀ i, y.2.2.2.2.2 i = true → x'.2.2.2.2.2 i = true
  have hlift : ∀ x ∈ Gs, TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c x := fun x hx =>
    crItemQ_mono (show cr x.1 ≤ cr x.1 + δ x.1 from Res.le_add_right _ _) (hit x hx)
  have htot : ∀ x ∈ Gs, ∃ x', R x x' := by
    intro x hx
    by_cases hy : ∃ y ∈ Dn, y.1 = x.1
    · obtain ⟨y, hyD, hyx⟩ := hy
      have hsum : x.2.2.2.2.1 + y.2.2.2.2.1 ≤ (fun t => cr t + δ t) x.1 := by
        show _ ≤ cr x.1 + δ x.1
        have h2 := hDR y hyD
        rw [hyx] at h2
        exact Res.add_le_add (crItemQ_R (hit x hx)) h2
      obtain ⟨eb, eS, x', e1, e2, e3, eK, hx'⟩ := crItem_merge hcpl hni (hlift x hx) (hD y hyD) hyx hsum
      refine ⟨x', e1, e2, e3, hx', fun i hi => by rw [eK]; simp [hi], fun i hi => ?_,
        fun y2 hy2 e => ?_⟩
      · rw [eK] at hi
        rcases Bool.or_eq_true_iff.1 hi with h1 | h1
        · exact .inl h1
        · exact .inr ⟨y, hyD, hyx, h1⟩
      · have e' : y2 = y := eq_of_nodup_map (·.1) hDnd hy2 hyD (by rw [e, hyx])
        subst e'
        exact ⟨eb, eS, fun i hi => by rw [eK]; simp [hi]⟩
    · refine ⟨x, rfl, rfl, rfl, hlift x hx, fun i hi => hi, fun i hi => .inl hi, fun y hyD e => ?_⟩
      exact absurd ⟨y, hyD, e⟩ hy
  obtain ⟨Gs', hmap, hback, hfwd⟩ := list_rel (·.1) R (fun x x' hr => hr.1) Gs htot
  let Gn := Dn.filter (fun y => decide (y.1 ∉ Gs.map (·.1)))
  have hGnD : ∀ y ∈ Gn, y ∈ Dn := fun y hy => (List.mem_filter.1 hy).1
  have hGnN : ∀ y ∈ Gn, y.1 ∉ Gs.map (·.1) := fun y hy => of_decide_eq_true (List.mem_filter.1 hy).2
  have hcovU : ∀ o, (∃ y ∈ Dn, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧ InAcc usS i (o - y.2.1) ∧
      y.2.2.2.2.2 i = true) → ∃ x ∈ Gs' ++ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true := by
    intro o ⟨y, hyD, usS, i, h1, h2, h3, h4⟩
    by_cases hin : y.1 ∈ Gs.map (·.1)
    · obtain ⟨x, hx, hxy⟩ := List.mem_map.1 hin
      obtain ⟨x', hx', e1, e2, e3, -, -, -, hY⟩ := hfwd x hx
      obtain ⟨eb, eS, hK⟩ := hY y hyD hxy.symm
      refine ⟨x', List.mem_append_left _ hx', usS, i, ?_, ?_, ?_, hK i h4⟩
      · rw [e3, ← eS]; exact h1
      · rw [e2, ← eb]; exact h2
      · rw [e2, ← eb]; exact h3
    · exact ⟨y, List.mem_append_right _ (List.mem_filter.2 ⟨hyD, decide_eq_true hin⟩), usS, i, h1, h2, h3, h4⟩
  have hupG : ∀ o, (∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true) → ∃ x ∈ Gs', ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true := fun o ⟨x, hx, usS, i, h1, h2, h3, h4⟩ => by
    obtain ⟨x', hx', e1, e2, e3, -, hK, -, -⟩ := hfwd x hx
    exact ⟨x', hx', usS, i, by rw [e3]; exact h1, by rw [e2]; exact h2, by rw [e2]; exact h3, hK i h4⟩
  have hupL : ∀ o, (∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true) → ∃ x ∈ Gs' ++ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
        InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true := fun o h => by
    obtain ⟨x', hx', hr⟩ := hupG o h
    exact ⟨x', List.mem_append_left _ hx', hr⟩
  have hL' := overCr_interfMO (Gs' := Gs') (Gn := Gn) (δ := δ) hpre hpr hP hsto hV hI hVU hPU
    (fun o tw hi hv hl hg hov hold => (hG o tw hi hv hl hg hov hold).imp id (fun h2 => h2.elim (hcovU o) (hupL o))) hL hmap
    (fun x' hx' => (let ⟨_x, _, hr⟩ := hback x' hx'; hr.2.2.2.1))
    (fun x' hx' usS i o h1 h2 h3 => by
      obtain ⟨x, hx, e1, e2, e3, -, -, hK, hY⟩ := hback x' hx'
      rw [e3] at h1
      rw [e2]
      rcases hK i h2 with hk | ⟨y, hyD, hyx, hk⟩
      · exact hwa x hx usS i o h1 hk h3
      · obtain ⟨eb, eS, -⟩ := hY y hyD hyx
        rw [← eb]
        exact hwaD y hyD usS i o (by rw [eS]; exact h1) hk h3)
    hupG
    (fun y hy => hD y (hGnD y hy))
    (List.Nodup.sublist (List.filter_sublist.map _) hDnd)
    (fun x' hx' y hy e => hGnN y hy (by rw [← e, ← hmap]; exact List.mem_map_of_mem hx'))
    (fun y hy => hwaD y (hGnD y hy))
    (fun o tw hi hv hl hg hov => by
      rcases hcovD o tw hi hv hl hg hov with hold | hnew | hgs
      · exact .inl hold
      · exact .inr (hcovU o hnew)
      · exact .inr (hupL o hgs))
    (fun t m ht hm hl hd => by
      obtain ⟨y, hyD, rfl⟩ := List.mem_map.1 (hδD t m ht hm hl hd)
      rw [List.map_append]
      by_cases hin : y.1 ∈ Gs.map (·.1)
      · rw [← hmap] at hin
        exact List.mem_append_left _ hin
      · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.2 ⟨hyD, decide_eq_true hin⟩)))
  refine ⟨Gs' ++ Gn, hL', ?_⟩
  have hHL0 : TermOverCr.HolderLow s l (Gs' ++ Gn) := by
    refine TermOverCr.holderLow_append (fun x' hx' usS hus t m ht hm hl h1 h2 => ?_)
      (fun y hy => hHLD y (hGnD y hy))
    obtain ⟨x, hx, e1, e2, e3, -⟩ := hback x' hx'
    rw [e3] at hus
    rw [e2] at h1 h2
    rw [e1]
    exact hHL x hx usS hus t m ht hm hl h1 h2
  exact TermOverCr.holderLow_tr (fun t m _ hin hm => by rw [← hpre t (hP t hin)]; exact hm)
    (fun t ht hin => absurd (by rw [← hpr]; exact ht) hin) hHL0

#print axioms overCr_foreignOG

/-- (β′) **The credited cover at a foreign store**.  The new items `Dn` (distinct holders,
credited from `δ` alone, units with lowest own promises, holder in `K`, holders lowest in
their pieces) cover every unit the step newly overtakes (`hcovD`), and carry every nonzero
`δ` at a promise at `l` (`hδD`).  Old items at a new item's holder absorb it; the rest are appended. -/
theorem overCr_foreign {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
    {Dn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hI : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o) (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, TermOverCr.WinG E' s' l o tw → TermOverCr.WinG E s l o tw)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (h : TermOverCr.OverCrE E s cr l c)
    (hD : ∀ y ∈ Dn, TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c y)
    (hDR : ∀ y ∈ Dn, y.2.2.2.2.1 ≤ δ y.1)
    (hDnd : (Dn.map (·.1)).Nodup)
    (hwaD : ∀ y ∈ Dn, ∀ usS i o, accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, y.2.1 + o⟩ t0)
    (hHLD : TermOverCr.HolderLow s l Dn)
    (hcovD : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw ∨
      ∃ y ∈ Dn, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧ InAcc usS i (o - y.2.1) ∧
        y.2.2.2.2.2 i = true)
    (hδD : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → δ t ≠ .zero →
      t ∈ Dn.map (·.1)) :
    TermOverCr.OverCrE E' s' (fun t => cr t + δ t) l c := by
  obtain ⟨Gs, hL, hHL⟩ := h
  exact overCr_foreignOG hpre hpr hP hsto hV hI hVU hPU (fun o tw _ _ _ hg _ _ => .inl (hG o tw hg)) hcpl hni
    hL hHL hD hDR hDnd hwaD hHLD (fun o tw a0 a1 a2 a3 a4 => (hcovD o tw a0 a1 a2 a3 a4).imp id .inl) hδD

#print axioms overCr_foreign

/-! ## The new items from a drop list -/

open Classical in
/-- The new items at `l` from a drop list `Gd` with plant targets `tg`: one per entry at `l`
with a target, held at the target, with access units `Kf g`. -/
noncomputable def dnOf (l : AllocLabel) (tg : TermPiece.GdE → Option Ts) (Kf : TermPiece.GdE → Nat → Bool)
    (Gd : List TermPiece.GdE) : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
  Gd.filterMap (fun g => if g.l = l then (tg g).map (fun t => (t, g.b, g.S, g.ws, g.R, Kf g)) else none)

theorem mem_dnOf {l : AllocLabel} {tg : TermPiece.GdE → Option Ts} {Kf : TermPiece.GdE → Nat → Bool}
    {Gd : List TermPiece.GdE} {y : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} :
    y ∈ dnOf l tg Kf Gd ↔ ∃ g ∈ Gd, g.l = l ∧ ∃ t, tg g = some t ∧ y = (t, g.b, g.S, g.ws, g.R, Kf g) := by
  classical
  unfold dnOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, h⟩
    by_cases hl : g.l = l
    · simp only [hl, ↓reduceIte] at h
      cases ht : tg g with
      | none => rw [ht] at h; exact absurd h (by simp)
      | some t =>
          rw [ht] at h
          exact ⟨g, hg, hl, t, ht, (Option.some.inj h).symm⟩
    · simp only [hl, ↓reduceIte] at h
      exact absurd h (by simp)
  · rintro ⟨g, hg, hl, t, ht, rfl⟩
    refine ⟨g, hg, ?_⟩
    simp only [hl, ↓reduceIte, ht, Option.map_some]

/-- A promise targeted by exactly one entry receives that entry's payload. -/
theorem plantD1_eq {α : Type} {Gd : List α} {R : α → Res} {tg : α → Option Ts} {g : α} {t : Ts}
    (hg : g ∈ Gd) (ht : tg g = some t) (hu : ∀ g' ∈ Gd, tg g' = some t → g' = g) :
    TermPlant.plantD1 Gd R tg t = R g := by
  rcases TermPlant.plantD1_cases Gd R tg t with h0 | ⟨g', hg', e, hr⟩
  · unfold TermPlant.plantD1 at h0
    cases hf : Gd.find? (fun g => decide (tg g = some t)) with
    | none =>
        have := List.find?_eq_none.1 hf g hg
        simp [ht] at this
    | some g' =>
        have h1 := List.mem_of_find?_eq_some hf
        have h2 : tg g' = some t := by simpa using List.find?_some hf
        unfold TermPlant.plantD1
        rw [hf]
        rw [hu g' h1 h2]
  · rw [hr, hu g' hg' e]

/-- (Dn bookkeeping) **The list facts of the new items**: with targets injective on the drop
list and lying at the entry's label, each new item's resources are its holder's `δ`, the holders
are distinct, and every nonzero `δ` at a promise at `l` is a holder. -/
theorem dnOf_facts {s : St} {l : AllocLabel} {tg : TermPiece.GdE → Option Ts}
    {Kf : TermPiece.GdE → Nat → Bool} {Gd : List TermPiece.GdE}
    (hinj : ∀ g ∈ Gd, ∀ g' ∈ Gd, ∀ t, tg g = some t → tg g' = some t → g' = g)
    (hlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → s.mem[t]? = some m → m.loc.label = g.l)
    (hnd : (Gd.map TermPiece.GdE.key).Nodup) :
    (∀ y ∈ dnOf l tg Kf Gd, y.2.2.2.2.1 ≤ TermPlant.plantD1 Gd TermPiece.GdE.R tg y.1) ∧
    ((dnOf l tg Kf Gd).map (·.1)).Nodup ∧
    (∀ t m, s.mem[t]? = some m → m.loc.label = l → TermPlant.plantD1 Gd TermPiece.GdE.R tg t ≠ .zero →
      t ∈ (dnOf l tg Kf Gd).map (·.1)) := by
  classical
  refine ⟨fun y hy => ?_, ?_, fun t m hm hl hd => ?_⟩
  · obtain ⟨g, hg, -, t, ht, rfl⟩ := mem_dnOf.1 hy
    rw [plantD1_eq hg ht (fun g' hg' e => hinj g hg g' hg' t ht e)]
    exact Res.le_refl _
  · unfold dnOf
    induction Gd with
    | nil => exact List.nodup_nil
    | cons g Gd ih =>
        rw [List.map_cons] at hnd
        have ih' := ih (fun a ha b hb t h1 h2 => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) t h1 h2)
          (fun a ha t m h1 h2 => hlab a (List.mem_cons_of_mem _ ha) t m h1 h2) (List.nodup_cons.1 hnd).2
        rw [List.filterMap_cons]
        by_cases hl : g.l = l
        · cases ht : tg g with
          | none => simp only [hl, ↓reduceIte, Option.map_none]; exact ih'
          | some t =>
              simp only [hl, ↓reduceIte, Option.map_some, List.map_cons]
              refine List.nodup_cons.2 ⟨fun hmem => ?_, ih'⟩
              obtain ⟨y, hy, e⟩ := List.mem_map.1 hmem
              have hy' : y ∈ dnOf l tg Kf Gd := hy
              obtain ⟨g', hg', -, t', ht', rfl⟩ := mem_dnOf.1 hy'
              have e' : t' = t := e
              subst e'
              have := hinj g List.mem_cons_self g' (List.mem_cons_of_mem _ hg') t' ht ht'
              subst this
              exact (List.nodup_cons.1 hnd).1 (List.mem_map_of_mem hg')
        · simp only [hl, ↓reduceIte]; exact ih'
  · rcases TermPlant.plantD1_cases Gd TermPiece.GdE.R tg t with h0 | ⟨g, hg, e, -⟩
    · exact absurd h0 hd
    · have hgl : g.l = l := by rw [← hlab g hg t m e hm]; exact hl
      exact List.mem_map.2 ⟨_, mem_dnOf.2 ⟨g, hg, hgl, t, e, rfl⟩, rfl⟩

#print axioms dnOf_facts

end TermOverCrW
