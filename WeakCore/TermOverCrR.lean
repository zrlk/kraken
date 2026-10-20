import WeakCore.TermOverCrQ

/-! # TermOverCrR: the credited cover at a foreign store, assembled

`foreign_overCr`: the owner's cover survives a foreign store, with the plant transfer
`δ = plantD1 Gd R tg` and the new items `dnOf l tg (kfOf E s l) Gd`.  The list facts come from
`dnOf_facts`, the holder clause from `holderLow_dnOf`, the new cover from `hcovD_coreQ`; the
remaining premises are the per-entry target facts (`hT`), the items' credit (`hD`, `hwaD`, from
`dn_items`) and the entry facts at a newly overtaken unit (`hent`).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `hPU` of `foreign_overCr` from `E_g` growing (`GFoot.le`): cuts read `ini`/`pfr` off `E_g`. -/
theorem predU_mono_cut {Eg Eg' : GEnv} {i i' : Nat} {S S' : AllocLabel → Prop} {l : AllocLabel}
    (hle : Eg.le Eg') (hsto : (Cut Eg' i' S').sto l = (Cut Eg i S).sto l)
    (hrc : (Cut Eg' i' S').rc l ≤ (Cut Eg i S).rc l) :
    ∀ o, PredU (Cut Eg i S) ⟨l, o⟩ → PredU (Cut Eg' i' S') ⟨l, o⟩ := by
  refine TermOverCr.predU_mono_of hsto (fun h => ?_) (hle.ini l) hrc
  rw [Cut_pfr] at h ⊢
  cases e : Eg.pfr l with
  | none => exact absurd e h
  | some f => rw [hle.pfr l f e]; exact fun h0 => by cases h0

#print axioms predU_mono_cut

/-- **The credited cover at a foreign store.** -/
theorem foreign_overCr {E E' : TEnv} {s s' : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
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
    (hT : ∀ g ∈ Gd, ∀ t, tg g = some t → ∃ m R us, s.mem[t]? = some m ∧ m.loc.label = g.l ∧
      PlantCr E s m t R ∧ TermPiece.Piece c.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧
      m.loc.offset < g.b + nWords us)
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
  have hinj := tg_inj (E := E) (s := s) (tg := tg) (Gd := Gd) (fun g hg t ht => by
    obtain ⟨m, R, us, hm, hml, -, hpc, hus, h1, h2⟩ := hT g hg t ht
    exact ⟨m, us, c, hm, hml, by rw [hTl g hg t ht]; exact hsto0, hpc, hus, h1, h2⟩) hnd
  have hlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → s.mem[t]? = some m → m.loc.label = g.l := by
    intro g hg t m ht hm
    obtain ⟨m', R, us, hm', hml, -⟩ := hT g hg t ht
    rw [hm] at hm'
    cases hm'
    exact hml
  obtain ⟨hDR, hDnd, hδD⟩ := dnOf_facts (s := s) (l := l) (Kf := kfOf E s l) hinj hlab hnd
  have hHLD : TermOverCr.HolderLow s l (dnOf l tg (kfOf E s l) Gd) :=
    holderLow_dnOf hsto0 (fun g hg hgl t ht => by
      obtain ⟨m, R, us, hm, hml, hpl, hpc, hus, h1, h2⟩ := hT g hg t ht
      exact ⟨m, R, us, hm, by rw [hml, hgl], hpl, hpc, hus, h1, h2⟩)
  exact overCr_foreign hpre hpr hP hsto hV (covU_back hsto0 hsto hpf hini hrc) hVU hPU hWb hcpl hni h hD hDR
    hDnd hwaD hHLD (hcovD_coreQ hVU hnu hWb hent) (fun t m _ hm hl hnz => hδD t m hm hl hnz)

#print axioms foreign_overCr

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **A newly overtaken unit lies in the store target**: the overtaking message is new (so in the
target by the footprint), or an old message that left `PromAt` (which `hleft` places in the
target: a fulfilled foreign promise). -/
theorem newOver_inTgt {E E' : TEnv} {s s' : St} {l : AllocLabel} {o tw : Ts} {lt ot n : Nat}
    (hfoot : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset)
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hleft : ∀ t m, t < s.mem.size → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ∈ PromAt E s ⟨l, o⟩ →
      t ∉ PromAt E' s' ⟨l, o⟩ → lt = l ∧ ot ≤ o ∧ ot + n > o)
    (hov : TermPlant.OverT E' s' ⟨l, o⟩ tw) (hno : ¬ TermPlant.OverT E s ⟨l, o⟩ tw) :
    lt = l ∧ ot ≤ o ∧ ot + n > o := by
  obtain ⟨t, m, hlt, hm, hl, hn⟩ := hov
  by_cases hsz : t < s.mem.size
  · have hm0 : s.mem[t]? = some m := by rw [← hpre t hsz]; exact hm
    have hin : t ∈ PromAt E s ⟨l, o⟩ := (Classical.em _).elim id fun h => False.elim <| hno ⟨t, m, hlt, hm0, hl, h⟩
    exact hleft t m hsz hm0 hl hin hn
  · obtain ⟨a, b, c⟩ := hfoot t m (Nat.le_of_not_lt hsz) hm
    rw [hl] at a b c
    exact ⟨a.symm, b, c⟩

#print axioms newOver_inTgt

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- Every word of a layout lies in some access unit. -/
theorem inAcc_ex : ∀ (us : List Acc) (o : Nat), o < nWords us → ∃ i, InAcc us i o
  | [], o, h => by simp [nWords] at h
  | u :: us, o, h => by
      have hu : nWords (u :: us) = u.size + nWords us := by simp [nWords]
      by_cases ho : o < u.size
      · exact ⟨0, by simp [nWords], by simp [nWords]; omega⟩
      · obtain ⟨i, h1, h2⟩ := inAcc_ex us (o - u.size) (by omega)
        refine ⟨i + 1, ?_, ?_⟩
        · have : nWords ((u :: us).take (i + 1)) = u.size + nWords (us.take i) := by simp [nWords]
          omega
        · have : nWords ((u :: us).take (i + 1 + 1)) = u.size + nWords (us.take (i + 1)) := by simp [nWords]
          omega

#print axioms inAcc_ex

/-- **(hent) A newly overtaken unit has a drop entry** with a target, at a single-word unit
whose latest-ness is recorded. -/
theorem hent_of {E E' Ek : TEnv} {s s' sk : St} {l : AllocLabel} {c ck : Cell} {lt ot n : Nat}
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
    (hpiece : ∀ o, TermOverCr.CovU E' c l o → ∃ b S us, TermPiece.Piece c.ty b S ∧ accs S = some us ∧ b ≤ o ∧
      o < b + nWords us)
    (hsing : ∀ o b S us i, TermPiece.Piece c.ty b S → accs S = some us → b ≤ o → InAcc us i (o - b) →
      ∀ o', InAcc us i o' → o' = o - b)
    (hL : ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∀ g ∈ Gd, g.l = l → g.b ≤ o → g.L (o - g.b) = true)
    (htg : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw →
      ∀ us, accs g.S = some us →
      g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true := by
  intro o tw hI hv' hl hw hov hno
  obtain ⟨hlt, ho1, ho2⟩ := newOver_inTgt hfoot hpre (hleft o hv') hov hno
  subst hlt
  obtain ⟨b, S, us, hP, hus, hb1, hb2⟩ := hpiece o hI
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := id hl
  have hmwk : sk.mem[tw]? = some mw := by rw [hmemk]; exact hmw
  obtain ⟨g, hg, hgl, hgb, hgS⟩ := hcov ck b S us tw mw hstok hownk (by rw [hty]; exact hP) hus (hfp tw htw)
    hmwk (by rw [hml]) (by rw [hml]; exact hb1) (by rw [hml]; exact hb2) (by rw [hml]; exact ho1)
    (by rw [hml]; exact ho2)
  subst hgb hgS
  obtain ⟨i, hi⟩ := inAcc_ex us (o - g.b) (by omega)
  exact ⟨g, hg, hgl, htg g hg hgl o tw hl hw us hus hb1 hb2,
    us, i, hus, hb1, hi, hsing o g.b g.S us i hP hus hb1 hi, hL o tw ho1 ho2 hov hno g hg hgl hb1⟩

#print axioms hent_of

end TermOverCrW
