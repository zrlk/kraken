import WeakCore.TermOverCrV

/-!
# TermOverCrX: the re-pin hand-off into the owner's cover (OvW3 R3 glue)

The `RepinQ` / `RepinCov` / `rpSum` (TermPiece, OvW3 R2) are restated here with their bodies
inlined (`RepinQI`, `CrCovI`, `rpSumI`), since this development sits on a different base.  From
`RepinQI E' s' cr' RS` with `cr' = cr0 + rpSumI RS`, the items of `RS` at the label give
`overCr_ownopD`'s re-pin items `rpL RS l` with all their side conditions (`overCr_ownopRS`).
-/

namespace TermOverCrX
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The `rpSum`, inlined: the re-pin credit at `t`. -/
noncomputable def rpSumI (RS : List (AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool))))
    (t : Ts) : Res :=
  Res.sum ((RS.filter fun y => decide (y.2.2.1 = t)).map fun y => y.2.2.2.2.2.2.1)

/-- The `CrCov`, inlined: item `x` covers word `o` of its cell. -/
def CrCovI (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) (o : Nat) : Prop :=
  ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true

/-- The `RepinQ`, inlined (`CrKeysP` and `WinGI` unfolded; `WinGI` is `TermOverCr.WinG`, at the unit under F3). -/
def RepinQI (E' : TEnv) (s' : St) (cr' : Ts → Res)
    (RS : List (AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))) : Prop :=
  ∀ y ∈ RS, E'.sto y.1 = some y.2.1 ∧ y.2.1.owner = some E'.tid ∧ E'.pfr y.1 ≠ none ∧
    TermPlant.CrItem E' s' cr' y.1 y.2.1 y.2.2 ∧ (∀ l, y.2.2.2.2.2.2.1 (.own l) = 0) ∧
    (∀ usS, accs y.2.2.2.2.1 = some usS → ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m →
      m.loc.label = y.1 → y.2.2.2.1 ≤ m.loc.offset → m.loc.offset < y.2.2.2.1 + nWords usS → y.2.2.1 ≤ t) ∧
    ∀ o, CrCovI y.2.2 o → ∃ tw, TermPlant.LowOwn s' ⟨y.1, o⟩ tw ∧ TermOverCr.WinG E' s' y.1 o tw

/-- The re-pin items at label `l`. -/
def rpL (RS : List (AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))) (l : AllocLabel) :
    List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
  (RS.filter fun y => decide (y.1 = l)).map (·.2.2)

theorem mem_rpL {RS : List (AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))}
    {l : AllocLabel} {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} :
    x ∈ rpL RS l ↔ ∃ y ∈ RS, y.1 = l ∧ y.2.2 = x := by
  unfold rpL
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, hl⟩, rfl⟩; exact ⟨y, hy, hl, rfl⟩
  · rintro ⟨y, hy, hl, rfl⟩; exact ⟨y, ⟨hy, hl⟩, rfl⟩

theorem rpSumI_cons (y : AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))
    (RS : List (AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))) (t : Ts) :
    rpSumI (y :: RS) t = (if y.2.2.1 = t then y.2.2.2.2.2.2.1 else .zero) + rpSumI RS t := by
  unfold rpSumI
  by_cases h : y.2.2.1 = t
  · simp [h]
  · simp [h]

/-- The holder sums of the re-pin items at `l` are within the re-pin credit. -/
theorem sumH_rpL_le (l : AllocLabel) (t : Ts) :
    ∀ RS : List (AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool))),
      TermOverCrW.sumH (rpL RS l) t ≤ rpSumI RS t
  | [] => Res.zero_le _
  | y :: RS => by
      have ih := sumH_rpL_le l t RS
      rw [rpSumI_cons]
      by_cases hl : y.1 = l
      · have e : rpL (y :: RS) l = y.2.2 :: rpL RS l := by
          unfold rpL; simp [hl]
        rw [e, TermOverCrW.sumH_cons]
        intro k
        have := ih k
        simp only [Res.add_apply]; omega
      · have e : rpL (y :: RS) l = rpL RS l := by
          unfold rpL; simp [hl]
        rw [e]
        exact Res.le_trans ih (TermOverCrW.le_add_leftR _ _)

#print axioms sumH_rpL_le

section ownRS
variable {s s' : St} (hmem : s'.mem = s.mem) (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
include hmem hsub

/-- **(OvW3 R3 glue) The owner's cover at its own op, from the re-pin hand-off.**
`overCr_ownopD` with re-pin items `rpL RS l`: `RepinQI` gives the items, their windows and
holder lowness; `cr' = cr0 + rpSumI RS` with the old and re-key items (distinct holders) within
`cr0` gives the per-holder fit; `RepinCov`'s conclusion is `hcovN0`'s re-pin case. -/
theorem overCr_ownopRS {E E' : TEnv} {cr cr0 cr' : Ts → Res} {l : AllocLabel} {c : Cell} {G G' : Nat → Ts → Prop}
    {Gs Gk Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    {RS : List (AllocLabel × Cell × (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hsto0 : E.sto l = some c) (hpf : E.pfr l ≠ none)
    (hpi : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → ∀ cl, E.sto m.loc.label = some cl →
      E.pfr m.loc.label ≠ none → InitR E cl m.loc.label m.loc.offset)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      PredU E ⟨l, x.2.1 + o⟩ → PredU E' ⟨l, x.2.1 + o⟩)
    (h : TermOverCr.OverCrL E s cr l c G Gs)
    (hGk : Gk.Sublist Gs)
    (hcrK : ∀ x ∈ Gk, cr x.1 ≤ cr' x.1)
    (hnfH : ∀ x ∈ Gk, ∀ mh, s.mem[x.1]? = some mh → ∀ t m, t ∈ s.promises → t ∉ s'.promises →
      s.mem[t]? = some m → m.loc ≠ mh.loc)
    (hnfK : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, x.2.1 + o⟩)
    (hGn : ∀ x ∈ Gn, TermOverCr.CrItemQ E' s' cr' l c x)
    (hwaN : ∀ x ∈ Gn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0)
    (hRS : RepinQI E' s' cr' RS)
    (hcr' : ∀ t, cr' t = cr0 t + rpSumI RS t)
    (hnd0 : ((Gk ++ Gn).map (·.1)).Nodup)
    (hR0 : ∀ x ∈ Gk ++ Gn, x.2.2.2.2.1 ≤ cr0 x.1)
    (hHL0 : TermOverCr.HolderLow s' l (Gk ++ Gn))
    (hcovN0 : ∀ o tw, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o → ¬ VisU E' ⟨l, o⟩ →
      TermPlant.LowOwn s' ⟨l, o⟩ tw → G' o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ((∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, o⟩) ∧
        ¬ VisU E ⟨l, o⟩ ∧ G o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw ∧
        ∀ x ∈ Gs, (∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
          x.2.2.2.2.2 i = true) → x ∈ Gk) ∨
      (∃ x ∈ Gn, CrCovI x o) ∨ ∃ y ∈ RS, y.1 = l ∧ CrCovI y.2.2 o)
    (hzN : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E' m.loc →
      cr' t ≠ .zero → (cr t ≠ .zero ∧ ∀ x ∈ Gs, x.1 = t → x ∈ Gk) ∨ t ∈ Gn.map (·.1) ∨
        ∃ y ∈ RS, y.1 = l ∧ y.2.2.1 = t) :
    ∃ Gs', TermOverCr.OverCrL E' s' cr' l c G' Gs' ∧ TermOverCr.HolderLow s' l Gs' := by
  have hcell : ∀ y ∈ RS, y.1 = l → y.2.1 = c := by
    intro y hy hl
    have h1 := (hRS y hy).1
    rw [hl, hsto, hsto0] at h1
    exact (Option.some.inj h1).symm
  have hDn : ∀ x ∈ rpL RS l, TermOverCr.CrItemQ E' s' cr' l c x := by
    intro x hx
    obtain ⟨y, hy, hl, rfl⟩ := mem_rpL.1 hx
    have hit := (hRS y hy).2.2.2.1
    rw [hl, hcell y hy hl] at hit
    exact TermOverCr.crItemQ_of hit
  have hwaD : ∀ x ∈ rpL RS l, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true →
      InAcc usS i o → ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0 := by
    intro x hx usS i o h1 h2 h3
    obtain ⟨y, hy, hl, rfl⟩ := mem_rpL.1 hx
    have hc : CrCovI y.2.2 (y.2.2.2.1 + o) :=
      ⟨usS, i, h1, Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact h3, h2⟩
    obtain ⟨tw, hlo, -⟩ := (hRS y hy).2.2.2.2.2.2 _ hc
    rw [hl] at hlo
    exact ⟨tw, hlo⟩
  have hsumL : ∀ t, TermOverCrW.sumH (Gk ++ Gn ++ rpL RS l) t ≤ cr' t := by
    intro t
    rw [TermOverCrW.sumH_append, hcr']
    have a := TermOverCrW.sumH_le_of_nodup hnd0 hR0 t
    have b := sumH_rpL_le l t RS
    intro k
    have a1 := a k; have b1 := b k
    simp only [Res.add_apply] at a1 b1 ⊢; omega
  have hHL : TermOverCr.HolderLow s' l (Gk ++ Gn ++ rpL RS l) := by
    intro x hx usS hus t m ht hm hl h1 h2
    rcases List.mem_append.1 hx with hx | hx
    · exact hHL0 x hx usS hus t m ht hm hl h1 h2
    · obtain ⟨y, hy, hyl, rfl⟩ := mem_rpL.1 hx
      exact (hRS y hy).2.2.2.2.2.1 usS hus t m ht hm (by rw [hyl]; exact hl) h1 h2
  refine TermOverCr5.overCr_ownopD hmem hsub (Dn := rpL RS l) hcpl hni hsto0 hpf hpi hsto hV hPU h
    hGk hcrK hnfH hnfK hGn hwaN hDn hwaD hsumL hHL (fun o tw hi hi0 hv hlo hg hov => ?_)
    (fun t m ht hm hl hw hnz => ?_)
  · rcases hcovN0 o tw hi hi0 hv hlo hg hov with hk | ⟨x, hx, hc⟩ | ⟨y, hy, hyl, hc⟩
    · exact .inl hk
    · exact .inr ⟨x, List.mem_append_left _ hx, hc⟩
    · exact .inr ⟨y.2.2, List.mem_append_right _ (mem_rpL.2 ⟨y, hy, hyl, rfl⟩), hc⟩
  · rcases hzN t m ht hm hl hw hnz with hk | hn | ⟨y, hy, hyl, hyt⟩
    · exact .inl hk
    · exact .inr (by rw [List.map_append]; exact List.mem_append_left _ hn)
    · exact .inr (by
        rw [List.map_append]
        exact List.mem_append_right _
          (List.mem_map.2 ⟨y.2.2, mem_rpL.2 ⟨y, hy, hyl, rfl⟩, hyt⟩))

#print axioms overCr_ownopRS

end ownRS

end TermOverCrX
