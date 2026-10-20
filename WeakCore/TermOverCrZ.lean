import WeakCore.TermOverCrY

/-!
# TermOverCrZ: zero-credit items at RMW atoms (foreign RMW repair)

A foreign `fetch`/`cas` writes a one-word non-affine atom of the owner's cell.  Such an atom's
value carries no resource (`VR_VRR_copy_closed`), so a credited item for it costs nothing: its
pinned word only needs `WordOK` (`MemOKP`'s first clause), from which it is a value of the atom.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **A `WordOK` word at a closed non-affine one-word component is a resource-free value of it.** -/
theorem valOfR_zero_of_wordOK {E : TEnv} {T : Ty} {o : Nat} {w : Word} {U : Ty}
    (h : WordOK E T o w) (hP : AtOff T o U) (hU : accs U = some [Acc.one])
    (hcl : tb 0 U = true) (ha : Ty.affine U = false) : ValOfR E U [w] .zero := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, hvd⟩, hsh⟩, hw0, hle, hbo⟩ := h
  have hlt0 : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨hatS, usS, hS⟩ : AtOff S o' U ∧ ∃ us, accs S = some us := by
    rcases hseg with ⟨rfl, rfl, hT⟩ | ⟨N, us, j, rfl, hus, hj, rfl⟩
    · subst hbo
      exact ⟨by simpa using hP, Option.ne_none_iff_exists'.1 hT⟩
    · refine ⟨?_, us, hus⟩
      rcases AtOff_arr_elem hP rfl with h | ⟨us', j', o'', hus', hj', ho, hat⟩
      · rw [h] at hU; simp [accs] at hU
      · rw [hus] at hus'
        cases hus'
        have hlt1 : o' < nWords us := hsh us hus ▸ hlt0
        have hlt2 : o'' + nWords [Acc.one] ≤ nWords us := AtOff_bound hat hus hU
        have hlt2' : o'' < nWords us := by have h1 : nWords [Acc.one] = 1 := rfl; omega
        have e : o' + j * nWords us = o'' + j' * nWords us := by omega
        have e2 := congrArg (· % nWords us) e
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2'] at e2
        exact e2 ▸ hat
  obtain ⟨nn, hwcU, -, hvrU, hvdU⟩ :=
    VR_at E.unsee hatS hvr hvd (by simp [wc, hS, hsh usS hS])
  have hnn : nn = 1 := by simp [wc, hU, nWords, Acc.size] at hwcU; omega
  subst hnn
  rw [TermTyped.take_one_drop hw0] at hvrU hvdU
  exact ValOfR_up (show WLe [w0] [w] from ⟨hle, trivial⟩) ⟨VR_VRR_copy_closed hcl ha hvrU, hvdU⟩

#print axioms valOfR_zero_of_wordOK

/-- `InAcc` at a single one-word unit. -/
theorem inAcc_one {i o : Nat} (h : InAcc [Acc.one] i o) : o = 0 := by
  obtain ⟨h1, h2⟩ := h
  cases i with
  | zero => simp [nWords, Acc.size] at h2; omega
  | succ i => simp [nWords, Acc.size] at h1 h2; omega

/-- **The zero-credit item at a one-word atom**: at the atom `U` (word `b` of the owner's cell
`l`) whose lowest own promise is `tw`, the item `(tw, b, U, [w], 0, all)` with `w` the word just
below `tw` is credited, provided `w` is `WordOK` and the atom closed and non-affine. -/
theorem crItemQ_free {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {b : Nat} {U : Ty}
    {tw : Ts} {w : Word}
    (hlo : TermPlant.LowOwn s ⟨l, b⟩ tw) (hnw : ¬ WordUnit E ⟨l, b⟩)
    (hat : AtOff c.ty b U) (hsol : Solid U) (hU : accs U = some [Acc.one])
    (hcl : tb 0 U = true) (ha : Ty.affine U = false)
    (hpred : PredAt s.mem ⟨l, b⟩ tw w) (hok : WordOK E c.ty b w) :
    TermOverCr.CrItemQ E s cr l c (tw, b, U, [w], .zero, fun _ => true) := by
  obtain ⟨htw, ⟨mh, hmh, hml⟩, hlow⟩ := hlo
  refine ⟨mh, [Acc.one], hmh, by rw [hml], ?_, by rw [hml]; exact hnw, hat, hsol, hU,
    by rw [hml]; exact Nat.le_refl _, by rw [hml]; show b < b + 1; omega, rfl,
    valOfR_zero_of_wordOK hok hat hU hcl ha, Res.zero_le _, fun i o w' tw' _ hio hw hl => .inl ?_⟩
  · rw [hml]; exact ⟨htw, ⟨mh, hmh, hml⟩, hlow⟩
  · have ho := inAcc_one hio
    subst ho
    have hw' : w' = w := by simpa using hw.symm
    subst hw'
    have e : tw' = tw := TermPlant.LowOwn_uniq (by simpa using hl) ⟨htw, ⟨mh, hmh, hml⟩, hlow⟩
    subst e
    simpa using hpred

#print axioms crItemQ_free

/-- **`overCr_foreign` with repeated holders**: the new items are merged per holder
(`crItems_dedup`) when their per-holder resources fit `δ`. -/
theorem overCr_foreignM {E E' : TEnv} {s s' : St} {cr δ : Ts → Res} {l : AllocLabel} {c : Cell}
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
  exact overCr_foreignMOG hpre hpr hP hsto hV hI hVU hPU (fun o tw _ _ _ hw _ _ => .inl (hG o tw hw)) hcpl hni
    hL hHL hD hsum hwaD hHLD (fun o tw a0 a1 a2 a3 a4 => (hcovD o tw a0 a1 a2 a3 a4).imp id .inl) hδD

#print axioms overCr_foreignM

/-- `hcovD_coreQ` at one unit: a newly overtaken unit with a drop entry is covered by its item. -/
theorem hcovD_unit {E E' : TEnv} {s s' : St} {l : AllocLabel} {tg : TermPiece.GdE → Option Ts}
    {Gd : List TermPiece.GdE} {o : Nat} {tw : Ts}
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hWb : ∀ o tw, TermOverCr.WinG E' s' l o tw → TermOverCr.WinG E s l o tw)
    (hv : ¬ VisU E' ⟨l, o⟩) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) (hw : TermOverCr.WinG E' s' l o tw)
    (hold : ¬ TermPlant.OverT E s ⟨l, o⟩ tw)
    (hg : ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) :
    ∃ y ∈ dnOf l tg (kfOf E s l) Gd, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧
      InAcc usS i (o - y.2.1) ∧ y.2.2.2.2.2 i = true := by
  exact hcovD_unitO hVU hnu hv hl (hWb o tw hw) hold hg

#print axioms hcovD_unit

/-- **(H7 + RMW atoms) The credited cover at a foreign step, with free items**: `foreign_overCrP`
whose entry premise may instead give a zero-resource item of `Fz` (a foreign RMW atom). -/
theorem foreign_overCrPZ {E E' : TEnv} {s s' : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    {Fz : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
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
    (hFi : ∀ x ∈ Fz, TermOverCr.CrItemQ E s (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c x)
    (hFR : ∀ x ∈ Fz, x.2.2.2.2.1 = .zero)
    (hFwa : ∀ x ∈ Fz, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hFHL : TermOverCr.HolderLow s l Fz)
    (hent : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      (∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) ∨
      ∃ x ∈ Fz, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) :
    TermOverCr.OverCrE E' s' (fun t => cr t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l c := by
  obtain ⟨Gs, hL, hHL⟩ := h
  exact foreign_overCrPZOG hpre hpr hP hsto0 hsto hV hrc hini hpf hVU hPU hnu
    (fun o tw _ _ _ hw _ _ => .inl (hWb o tw hw)) hcpl hni hL hHL hnd
    (fun g hg t ht => by
      obtain ⟨m, R, us, hm, hml, hpl, hpc, hus, h1, h2⟩ := hT g hg t ht
      exact ⟨m, us, hm, hml, plantCr_low hpl (by rw [hml, hTl g hg t ht, hsto]; exact hsto0) hpc hus h1 h2,
        hpc, hus, h1, h2⟩)
    hTp hTl hD hwaD hFi hFR hFwa hFHL
    (fun o tw a0 a1 a2 hw a4 a5 => (hent o tw a0 a1 a2 hw a4 a5).imp (fun h => ⟨h, hWb o tw hw⟩) .inl)

#print axioms foreign_overCrPZ

end TermOverCrW
