import WeakCore.TermOverCrNP

/-!
# TermOverCrWb: the window transport only where it is read (hWb → hWbO)

The window transport `hWb` (every post-step guarded unit was guarded before) is read only at units
that were already overtaken before the step (the old cover is reused, `overCr_interfM`), and, for
drop entries, at newly overtaken ones (`hcovD_unit`).  The `…O` copies below ask exactly that:
`hWbO` at old-overtaken units, and the pre-state guard bundled into the drop-entry disjunct of the
entry premise.  The free-item disjunct needs no guard, so the non-`PubShape` cover asks `hWbO` only.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `overCr_foreign` with the window transport asked only where it is read (`hWbO`). -/
theorem overCr_foreignO {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
    {Dn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hI : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o) (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw ∨
      ∃ y ∈ Dn, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧ InAcc usS i (o - y.2.1) ∧
        y.2.2.2.2.2 i = true)
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
  exact overCr_foreignOG hpre hpr hP hsto hV hI hVU hPU
    (fun o tw a0 a1 a2 a3 a4 a5 => (hG o tw a0 a1 a2 a3 a4 a5).imp id .inl) hcpl hni hL hHL hD hDR hDnd hwaD
    hHLD (fun o tw a0 a1 a2 a3 a4 => (hcovD o tw a0 a1 a2 a3 a4).imp id .inl) hδD

#print axioms overCr_foreignO

/-- `overCr_foreignM` with the window transport asked only where it is read (`hWbO`). -/
theorem overCr_foreignMO {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
    {Dn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hI : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o) (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E' ⟨l, o⟩)
    (hG : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw ∨
      ∃ y ∈ Dn, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧ InAcc usS i (o - y.2.1) ∧
        y.2.2.2.2.2 i = true)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (h : TermOverCr.OverCrE E s cr l c)
    (hD : ∀ y ∈ Dn, TermOverCr.CrItemQ E s (fun t => cr t + δ t) l c y)
    (hsum : ∀ t, sumH Dn t ≤ δ t)
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
  exact overCr_foreignMOG hpre hpr hP hsto hV hI hVU hPU
    (fun o tw a0 a1 a2 a3 a4 a5 => (hG o tw a0 a1 a2 a3 a4 a5).imp id .inl) hcpl hni hL hHL hD hsum hwaD hHLD
    (fun o tw a0 a1 a2 a3 a4 => (hcovD o tw a0 a1 a2 a3 a4).imp id .inl) hδD

#print axioms overCr_foreignMO

/-- `foreign_overCrPZ` with the window transport asked only where it is read (`hWbO`).  The targets
need only be piece-lowest own promises (`HolderLow`); no plant credit is read (`hT_low_of_plantCr`). -/
theorem foreign_overCrPZO {E E' : TEnv} {s s' : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    {Fz : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
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
      ∃ x ∈ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (h : TermOverCr.OverCrE E s cr l c)
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
      ∃ x ∈ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) :
    TermOverCr.OverCrE E' s' (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c := by
  obtain ⟨Gs, hL, hHL⟩ := h
  exact foreign_overCrPZOG hpre hpr hP hsto0 hsto hV hrc hini hpf hVU hPU hnu
    (fun o tw a0 a1 a2 a3 a4 a5 => (hWbO o tw a0 a1 a2 a3 a4 a5).imp id .inl) hcpl hni hL hHL hnd hT hTp hTl
    hD hwaD hFi hFR hFwa hFHL (fun o tw a0 a1 a2 a3 a4 a5 => (hent o tw a0 a1 a2 a3 a4 a5).imp id .inl)

#print axioms foreign_overCrPZO
#print axioms overCr_foreignMOG
#print axioms hcovD_unitO
#print axioms foreign_overCrPZOG

/-- The old target premise (a plant credit at each target) gives the piece-lowness one. -/
theorem hT_low_of_plantCr {E : TEnv} {s : St} {c : Cell} {l : AllocLabel}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} (hsto : E.sto l = some c)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m R us, s.mem[t]? = some m ∧ m.loc.label = g.l ∧
      PlantCr E s m t R ∧ TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us) :
    ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, s.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us := by
  intro g hg hgl t ht
  obtain ⟨m, R, us, hm, hml, hpl, hpc, hus, h1, h2⟩ := hT g hg hgl t ht
  exact ⟨m, us, hm, hml, plantCr_low hpl (by rw [hml, hgl]; exact hsto) hpc hus h1 h2, hpc, hus, h1, h2⟩

#print axioms hT_low_of_plantCr


/-- **Window transport back over an idle thread.**  The thread's promises and view are unchanged and
its memory prefix is kept, so part (A) transports; part (B) transports as long as each `fp` promise
`≤ tw` at the unit stays an `fp` promise (`hkeep`, false only at an FFUL step). -/
theorem winG_backK {E E' : TEnv} {s s' : St} {l : AllocLabel} {o : Nat} {tw : Ts}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hvs : s'.vs = s.vs)
    (hkeep : ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw →
      t ∈ FpAt E' ⟨l, 0⟩)
    (h : TermOverCr.WinG E' s' l o tw) : TermOverCr.WinG E s l o tw := by
  refine ⟨fun t m hm hl ht => ?_, fun t m ht hm hl => ?_⟩
  · have hlt : t < s.mem.size := (Array.getElem?_eq_some_iff.1 hm).1
    have hm' : s'.mem[t]? = some m := by rw [hpre t hlt]; exact hm
    rcases h.1 t m hm' hl ht with h1 | h1
    · exact .inl (hpr ▸ h1)
    · exact .inr (hvs ▸ h1)
  · exact (Classical.em _).elim id fun hn => False.elim <| by
      have hle : t ≤ tw := Nat.le_of_not_lt hn
      have hlt : t < s.mem.size := (Array.getElem?_eq_some_iff.1 hm).1
      have hm' : s'.mem[t]? = some m := by rw [hpre t hlt]; exact hm
      exact hn (h.2 t m (hkeep t m ht hm hl hle) hm' hl)

#print axioms winG_backK

/-- **Window transport back, or a lost footprint promise.**  Over an idle thread whose footprint
promises are not its own, either the window transports back, or some pre-step `fp` promise at the
unit left the footprint (the FFUL source of `hfree`). -/
theorem winG_or_lost {E E' : TEnv} {s s' : St} {l : AllocLabel} {o : Nat} {tw : Ts}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hvs : s'.vs = s.vs) (hfpf : ∀ t, t ∈ E.fp → t ∉ s.promises)
    (hV : Vis E l) (hV' : Vis E' l)
    (h : TermOverCr.WinG E' s' l o tw) :
    TermOverCr.WinG E s l o tw ∨ ∃ t m, s'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧
      (t ∈ E.fp ∧ t ∉ E'.fp ∧ t ∉ s.promises ∧ s.mem[t]? = some m) := by
  by_cases hk : ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw →
      t ∈ FpAt E' ⟨l, 0⟩
  · exact .inl (winG_backK hpre hpr hvs hk h)
  · refine .inr ((Classical.em _).elim id fun hn => False.elim <| hk fun t m ht hm hl _ => ?_)
    have e1 : FpAt E ⟨l, 0⟩ = E.fp := by unfold FpAt; simp only [hV, ↓reduceIte]
    have e2 : FpAt E' ⟨l, 0⟩ = E'.fp := by unfold FpAt; simp only [hV', ↓reduceIte]
    rw [e1] at ht
    rw [e2]
    have hlt : t < s.mem.size := (Array.getElem?_eq_some_iff.1 hm).1
    exact (Classical.em _).elim id fun ht' => False.elim <|
      hn ⟨t, m, by rw [hpre t hlt]; exact hm, hl, ht, ht', hfpf t ht, hm⟩

#print axioms winG_or_lost

/-- **`hWbO` from the FFUL residual.**  The only open part of the window transport is `hFFUL`: at a
newly read unit (post window and overtaking, pre overtaking) no `fp` promise `≤ tw` is lost. -/
theorem hWbO_of_keep {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hvs : s'.vs = s.vs)
    (hFFUL : ∀ (o : Nat) (tw : Ts), TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ →
      TermPiece.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw → TermPiece.OverT E' s' ⟨l, o⟩ tw →
      TermPiece.OverT E s ⟨l, o⟩ tw →
      ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw → t ∈ FpAt E' ⟨l, 0⟩) :
    ∀ (o : Nat) (tw : Ts), TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ →
      TermPiece.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw → TermPiece.OverT E' s' ⟨l, o⟩ tw →
      TermPiece.OverT E s ⟨l, o⟩ tw → TermOverCr.WinG E s l o tw :=
  fun o tw hI hv hl hw hov hold => winG_backK hpre hpr hvs (hFFUL o tw hI hv hl hw hov hold) hw

#print axioms hWbO_of_keep

/-- `hent_free` in the guard-bundled shape of `foreign_overCrPZO` (free items only). -/
theorem hent_freeO {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hpr : s'.promises = s.promises) (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPUb : ∀ o, PredU E' ⟨l, o⟩ → PredU E ⟨l, o⟩)
    (hVis : Vis E l → Vis E' l)
    (hfree : ∀ o, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → ∀ t m, s'.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      (s.mem.size ≤ t ∨ (t ∈ E.fp ∧ t ∉ E'.fp ∧ t ∉ s.promises ∧ s.mem[t]? = some m)) →
      FreeAt E s l c o) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ((∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) ∧
        TermOverCr.WinG E s l o tw) ∨
      ∃ x ∈ freeL E s l c, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true := by
  intro o tw hI hv hl _ hov hno
  obtain ⟨t, m, -, hm, hloc, hsrc⟩ := newOver_src hpr hpre hVU hPUb hVis hv hov hno
  exact .inr (freeL_cover (hfree o hI hv t m hm hloc hsrc) hl)

#print axioms hent_freeO

/-- (shared) **The `foreign_overCrNP*` family's cover** (non-`PubShape` step, through
`foreign_overCrPZO`), at any credit family `cv`, generalised over the `undef`-predecessor discharge
`hPN` (`np_hfree`).  `foreign_overCrNPO`/`NPOU`/`NPOUV` are its instances. -/
theorem foreign_overCrNPG {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Sp : TermRun.Cfg → TermRun.Cfg → Prop} {Init : TermSound.Res} {MintOK : TermSound.Res → Prop} {c0 : TermRun.Cfg} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hnps : ¬ TermPiece.PubShape cx th)
    {cv : Nat → Ts → Res} (hOC : TermOverCr.OverCrG Eg c cv)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- every thread's promises lie above its coherence (the `SysInvN` clause `PromAboveG`)
    (hPA : TermOverCr.PromAboveG c)
    -- the `undef`-predecessor discharge (the family parameter; see `np_hfree`)
    (hPN : ∀ o tw U, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermForWU.RmwAtom (Cut Eg j Sj) ⟨l, o⟩ → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      PredU (Cut Eg j Sj) ⟨l, o⟩ → Eg.pubd l → ¬ InitRr (Cut Eg j Sj) cl l o →
      AtOff cl.ty o U → Solid U → accs U = some [Acc.one] →
      (∃ t0 m0, t0 < tw ∧ c.mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val ≠ .undef) →
      ∃ w, PredAt c.mem ⟨l, o⟩ tw w ∧ w.val ≠ .undef) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cv j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, hini2, hrini2, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hpreM := tctx_pre X
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l =
      (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpfE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l =
      (Cut Eg j Sj).pfr l := hpfr2
  have hpf2' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f :=
    hpfr2.trans hf
  have hiniE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l =
      (Cut Eg j Sj).ini l := hini2
  have hrcE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc l =
      (Cut Eg j Sj).rc l := by
    show min ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l)
        ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').rini l) = min (Eg.ini l) (Eg.rini l)
    rw [hini2, hrini2]
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hcpl : Ty.coupledOKIn [] cl.ty = true := MemInv_cplT hmi hpre_c hf
  have hfree := np_hfree hsc X Y Z hm hnps hji hj hc2 hown hpf2 hPA hPN
  have hVU : ∀ o, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      ¬ VisU (Cut Eg j Sj) ⟨l, o⟩ :=
    fun o h hv => h ((VisU_congr (a := ⟨l, o⟩) hstoE rfl hpfE).2 hv)
  have hent := hent_freeO (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
    (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (s' := stOf c'.mem c'.pairs thj)
    (l := l) (c := cl) (tg := tgL l tg) (Gd := Gd) rfl hpreM hVU
    (fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).1 h)
    (fun _ => Vis_pfr hpf2') hfree
  -- the cover with the targets at `l`
  have hlabC : ∀ t m, c.mem[t]? = some m → m.loc.label = l →
      TermPlant.plantD1 Gd TermPiece.GdE.R (tgL l tg) t = TermPlant.plantD1 Gd TermPiece.GdE.R tg t :=
    fun t m hm1 hl => by
      have hlt : t < c.mem.size := by
        rcases Nat.lt_or_ge t c.mem.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none h1] at hm1; cases hm1
      exact plantD1_tgL hTlab (by rw [hpreM t hlt]; exact hm1) hl
  have hcovL := foreign_overCrPZO (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
    (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (s' := stOf c'.mem c'.pairs thj)
    (cr := cv j) (tg := tgL l tg) (Gd := Gd) (Fz := freeL (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl)
    hpreM rfl (fun t ht => X.inv.plt j thj t hj ht) hpre_c hstoE
    (fun S0 ws R0 hv => ValOfR_mono hI.prog rfl hI.sto hI.ini hv hI.pfr hI.box hI.rini)
    (Nat.le_of_eq hrcE) (Nat.le_of_eq hiniE) hpf hVU
    (fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).2 h)
    (fun t m ht hm1 => X.inv.promNU j thj t m hj ht hm1)
    (fun o tw hIc hv hl hw _ _ => by
      rcases winG_or_lost (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
          (s' := stOf c'.mem c'.pairs thj) hpreM rfl rfl
          (fun t ht => X.inv.fpfree j thj t hj ht) (Vis_pfr hf) (Vis_pfr hpf2') hw with
        hw0 | ⟨t, m, hm1, hloc, hsrc⟩
      · exact .inl hw0
      · exact .inr (freeL_cover (hfree o hIc hv t m hm1 hloc (.inr hsrc)) hl)) hcpl (X.inv.stoNI l cl hs)
    (hOC j thj Sj hj l cl hpre_c hown hpf) hnd
    (fun g hg t ht => by
      obtain ⟨hgl, ht'⟩ := tgL_some ht
      exact hT g hg hgl t ht')
    (fun g hg t ht => by
      obtain ⟨hgl, ht'⟩ := tgL_some ht
      exact hTp g hg hgl t ht')
    (fun g _ t ht => (tgL_some ht).1)
    (fun y hy => by
      rw [dnOf_tgL] at hy
      have hy' := hD y hy
      obtain ⟨mh, _, hmh, hlab, _⟩ := id hy'
      refine crItemQ_mono ?_ hy'
      show _ ≤ _
      rw [hlabC y.1 mh hmh hlab]
      exact Res.le_refl _)
    (fun y hy => by
      rw [dnOf_tgL] at hy
      exact hwaD y hy)
    freeL_item freeL_zero freeL_wa freeL_holder hent
  refine overCrE_congrL (fun t m hm1 hl => ?_) hcovL
  show cv j t + _ = cv j t + _
  rw [plantD1_tgL hTlab hm1 hl]

#print axioms foreign_overCrNPG

/-- **`foreign_overCrNP` without the window transport.**  Same proof through `foreign_overCrPZO`;
the free-item entries need no guard, and at units already overtaken before the step the window
either transports back or a footprint promise at the unit was lost (`winG_or_lost`), whose unit is
then covered by a free item (`hfree`, FFUL source).  OPEN item: `hpredNU`. -/
theorem foreign_overCrNPO {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Sp : TermRun.Cfg → TermRun.Cfg → Prop} {Init : TermSound.Res} {MintOK : TermSound.Res → Prop} {c0 : TermRun.Cfg} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hnps : ¬ TermPiece.PubShape cx th)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      (∀ t' m', t' ∈ thj.promises → c'.mem[t']? = some m' → m'.loc.label = m.loc.label →
        g.b ≤ m'.loc.offset → m'.loc.offset < g.b + nWords us → t ≤ t') ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- every thread's promises lie above its coherence (the `SysInvN` clause `PromAboveG`)
    (hPA : TermOverCr.PromAboveG c)
    -- OPEN (undef predecessor, narrowed): at a predicted, not initialised unit of a published cell
    -- with a defined message below the lowest own promise at a non-visible RMW atom, that promise has
    -- a defined predecessor
    (hpredNU : ∀ o tw, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermForWU.RmwAtom (Cut Eg j Sj) ⟨l, o⟩ → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      PredU (Cut Eg j Sj) ⟨l, o⟩ → Eg.pubd l → ¬ InitRr (Cut Eg j Sj) cl l o →
      (∃ t0 m0, t0 < tw ∧ c.mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val ≠ .undef) →
      ∃ w, PredAt c.mem ⟨l, o⟩ tw w ∧ w.val ≠ .undef) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl :=
  foreign_overCrNPG hsc X Y (Z.toC _ _ _ _ _) hm hnps hOC hji hj hc2 hown hpf2 hnd hTlab hT hTp hD hwaD hPA
    (fun o tw _ hv hR hlo hq hpb hIr _ _ _ hex => hpredNU o tw hv hR hlo hq hpb hIr hex)

#print axioms foreign_overCrNPO

/-- **`hWbT` from the FFUL residual** (as `hWbO_of_keep`, without the pre-step overtaking). -/
theorem hWbT_of_keep {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?) (hpr : s'.promises = s.promises)
    (hvs : s'.vs = s.vs)
    (hFFUL : ∀ (o : Nat) (tw : Ts), TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ →
      TermPiece.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw → TermPiece.OverT E' s' ⟨l, o⟩ tw →
      ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ≤ tw → t ∈ FpAt E' ⟨l, 0⟩) :
    ∀ (o : Nat) (tw : Ts), TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ →
      TermPiece.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw → TermPiece.OverT E' s' ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw :=
  fun o tw hI hv hl hw hov => winG_backK hpre hpr hvs (hFFUL o tw hI hv hl hw hov) hw

#print axioms hWbT_of_keep

/-- **`hent_ofC` with the pre-step guard**: the target premise `htg` is asked under the pre-step
window guard, which `hWbT` gives at every unit overtaken after the step; the guard is returned with
the entry (the drop-entry disjunct of `foreign_overCrPZO`'s `hent`). -/
theorem hent_ofCO {E E' Ek : TEnv} {s s' sk : St} {l : AllocLabel} {c ck : Cell} {lt ot n : Nat}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hmemk : sk.mem = s.mem)
    (hfoot : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset)
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hleft : ∀ o, ¬ VisU E' ⟨l, o⟩ → ∀ t m, t < s.mem.size → s.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      t ∈ PromAt E s ⟨l, o⟩ →
      t ∉ PromAt E' s' ⟨l, o⟩ → lt = l ∧ ot ≤ o ∧ ot + n > o)
    (hcov : ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), Ek.sto lt = some c →
      c.owner ≠ some Ek.tid → TermPiece.Piece c.ty b S → accs S = some vs → t ∈ Ek.fp → sk.mem[t]? = some m →
      m.loc.label = lt → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → ot ≤ m.loc.offset →
      ot + n > m.loc.offset → ∃ g ∈ Gd, g.l = lt ∧ g.b = b ∧ g.S = S)
    (hstok : Ek.sto l = some ck) (hty : ck.ty = c.ty) (hownk : ck.owner ≠ some Ek.tid)
    (hfp : ∀ t, t ∈ s.promises → t ∈ Ek.fp)
    (hpiece : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → ∃ b S us, TermPiece.Piece c.ty b S ∧ accs S = some us ∧
      b ≤ o ∧ o < b + nWords us)
    (hsing : ∀ o tw b S us i, TermPlant.LowOwn s ⟨l, o⟩ tw → TermPiece.Piece c.ty b S → accs S = some us →
      b ≤ o → InAcc us i (o - b) → ∀ o', InAcc us i o' → o' = o - b)
    (hL : lt = l → ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ¬ TermPlant.OverT E s ⟨l, o⟩ tw → ∀ g ∈ Gd, g.l = l → g.b ≤ o → g.L (o - g.b) = true)
    (hWbT : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermOverCr.WinG E s l o tw)
    (htg : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E s l o tw →
      ∀ us, accs g.S = some us →
      g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      (∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) ∧
        TermOverCr.WinG E s l o tw := by
  intro o tw hI hv' hl hw0 hov hno
  have hw := hWbT o tw hI hv' hl hw0 hov
  exact ⟨hent_ofG (L0 := fun _ => true) (Gw := TermOverCr.WinG E s l) hmemk hfoot hpre hleft (fun c b S vs t m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 _ => hcov c b S vs t m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
    hstok hty hownk hfp hpiece hsing hL (fun _ _ _ _ _ _ _ => rfl) (fun g hg hgl o tw hl hw _ => htg g hg hgl o tw hl hw) o tw hv' hl hov hno hw, hw⟩

#print axioms hent_ofCO

end TermOverCrW
