import WeakCore.TermOverCrE

/-!
# TermOverCrG: the free-item cover of newly overtaken units (F3 R=0 route)

At a foreign step, a unit of the owner's frontier cell newly overtaken under the (per-unit) guard
was written by the step: a new message there, or a footprint promise there that left the
footprint (`newOver_src`).  When every such unit is a free atom (`FreeAt`: a closed non-affine
one-word leaf pinned at a `WordOK` word: the predecessor of its lowest own promise, or that
promise's own word when it is the first write of a predicted unit), the list `freeL` of
zero-resource items covers it (`hent_free`), the second disjunct of `foreign_overCrPZ`'s `hent`.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The source of a newly overtaken unit**: a message above `tw` at the unit that memory's
reading newly does not skip is new, or a footprint promise that left the footprint. -/
theorem newOver_src {E E' : TEnv} {s s' : St} {l : AllocLabel} {o : Nat} {tw : Ts}
    (hpr : s'.promises = s.promises) (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hPUb : ∀ o, PredU E' ⟨l, o⟩ → PredU E ⟨l, o⟩)
    (hVis : Vis E l → Vis E' l)
    (hv : ¬ VisU E' ⟨l, o⟩) (hov : TermPlant.OverT E' s' ⟨l, o⟩ tw) (hno : ¬ TermPlant.OverT E s ⟨l, o⟩ tw) :
    ∃ t m, tw < t ∧ s'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧
      (s.mem.size ≤ t ∨ (t ∈ E.fp ∧ t ∉ E'.fp ∧ t ∉ s.promises ∧ s.mem[t]? = some m)) := by
  obtain ⟨t, m, hlt, hm, hl, hn⟩ := hov
  refine ⟨t, m, hlt, hm, hl, ?_⟩
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
      exact .inr ⟨hfp, hfp', hnp, hm0⟩
    · simp only [hvl, ↓reduceIte] at hfp
      exact absurd hfp List.not_mem_nil
  · exact .inl (Nat.le_of_not_lt hsz)

#print axioms newOver_src

/-- **`crItemQ_free` with the predicted-unit pin**: the pinned word is the predecessor of `tw`, or, at
a predicted unit whose first write is `tw`, `tw`'s own word (`CrItemQ`'s second disjunct). -/
theorem crItemQ_freeQ {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {b : Nat} {U : Ty}
    {tw : Ts} {w : Word}
    (hlo : TermPlant.LowOwn s ⟨l, b⟩ tw) (hnw : ¬ WordUnit E ⟨l, b⟩)
    (hat : AtOff c.ty b U) (hsol : Solid U) (hU : accs U = some [Acc.one])
    (hcl : tb 0 U = true) (ha : Ty.affine U = false)
    (hpred : PredAt s.mem ⟨l, b⟩ tw w ∨
      (PredU E ⟨l, b⟩ ∧ FirstW s.mem ⟨l, b⟩ tw ∧ ∃ m, s.mem[tw]? = some m ∧ mw m = w))
    (hok : WordOK E c.ty b w) :
    TermOverCr.CrItemQ E s cr l c (tw, b, U, [w], .zero, fun _ => true) := by
  obtain ⟨htw, ⟨mh, hmh, hml⟩, hlow⟩ := hlo
  refine ⟨mh, [Acc.one], hmh, by rw [hml], ?_, by rw [hml]; exact hnw, hat, hsol, hU,
    by rw [hml]; exact Nat.le_refl _, by rw [hml]; show b < b + 1; omega, rfl,
    valOfR_zero_of_wordOK hok hat hU hcl ha, Res.zero_le _, fun i o w' tw' _ hio hw hl => ?_⟩
  · rw [hml]; exact ⟨htw, ⟨mh, hmh, hml⟩, hlow⟩
  · have ho := inAcc_one hio
    subst ho
    have hw' : w' = w := by simpa using hw.symm
    subst hw'
    have e : tw' = tw := TermPlant.LowOwn_uniq (by simpa using hl) ⟨htw, ⟨mh, hmh, hml⟩, hlow⟩
    subst e
    simpa using hpred

#print axioms crItemQ_freeQ

/-- A free item for the lowest own promise `tw`: at a closed non-affine one-word leaf `U` at word
`o` of the cell, pinned at a `WordOK` word `w`: the predecessor of `tw`, or (at a predicted unit whose
first write is `tw`) `tw`'s own word. -/
def FreeQ (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts)
    (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ o U w, x = (tw, o, U, [w], .zero, fun _ => true) ∧ TermPlant.LowOwn s ⟨l, o⟩ tw ∧
    ¬ WordUnit E ⟨l, o⟩ ∧ AtOff c.ty o U ∧ Solid U ∧ accs U = some [Acc.one] ∧ tb 0 U = true ∧
    Ty.affine U = false ∧ (PredAt s.mem ⟨l, o⟩ tw w ∨
      (PredU E ⟨l, o⟩ ∧ FirstW s.mem ⟨l, o⟩ tw ∧ ∃ m, s.mem[tw]? = some m ∧ mw m = w)) ∧ WordOK E c.ty o w

open Classical in
/-- The chosen free item of `tw` (a dummy when there is none). -/
noncomputable def freeIt (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts) :
    Ts × Nat × Ty × List Word × Res × (Nat → Bool) :=
  if h : ∃ x, FreeQ E s l c tw x then Classical.choose h else (tw, 0, .unit, [], .zero, fun _ => true)

open Classical in
/-- **The free items**: one per own promise with a free item. -/
noncomputable def freeL (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) :
    List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
  (s.promises.filter (fun tw => decide (∃ x, FreeQ E s l c tw x))).map (freeIt E s l c)

theorem freeIt_spec {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {tw : Ts} (h : ∃ x, FreeQ E s l c tw x) :
    FreeQ E s l c tw (freeIt E s l c tw) := by
  classical
  unfold freeIt
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

#print axioms freeIt_spec

theorem mem_freeL {E : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hx : x ∈ freeL E s l c) :
    ∃ tw, FreeQ E s l c tw x := by
  classical
  unfold freeL at hx
  obtain ⟨tw, htw, rfl⟩ := List.mem_map.1 hx
  have h := of_decide_eq_true (List.mem_filter.1 htw).2
  exact ⟨tw, freeIt_spec h⟩

#print axioms mem_freeL

/-- Free items are credited (at zero). -/
theorem freeL_item {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ freeL E s l c, TermOverCr.CrItemQ E s cr l c x := by
  intro x hx
  obtain ⟨tw, o, U, w, rfl, hlo, hnw, hat, hsol, hU, hcl, ha, hpred, hok⟩ := mem_freeL hx
  exact crItemQ_freeQ hlo hnw hat hsol hU hcl ha hpred hok

#print axioms freeL_item

theorem freeL_zero {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ freeL E s l c, x.2.2.2.2.1 = .zero := by
  intro x hx
  obtain ⟨tw, o, U, w, rfl, -⟩ := mem_freeL hx
  rfl

#print axioms freeL_zero

theorem freeL_wa {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ freeL E s l c, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0 := by
  intro x hx usS i o' hus _ hio
  obtain ⟨tw, o, U, w, rfl, hlo, -, -, -, hU, -⟩ := mem_freeL hx
  have hu : usS = [Acc.one] := Option.some.inj (hus.symm.trans hU)
  subst hu
  have h0 := inAcc_one hio
  subst h0
  exact ⟨tw, hlo⟩

#print axioms freeL_wa

theorem freeL_holder {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} :
    TermOverCr.HolderLow s l (freeL E s l c) := by
  intro x hx usS hus t m ht hm hl h1 h2
  obtain ⟨tw, o, U, w, rfl, hlo, -, -, -, hU, -⟩ := mem_freeL hx
  have hu : usS = [Acc.one] := Option.some.inj (hus.symm.trans hU)
  subst hu
  have hn : nWords [Acc.one] = 1 := TermForWU.nWords_one
  rw [hn] at h2
  have ho : m.loc.offset = o := Nat.le_antisymm (Nat.lt_succ_iff.mp h2) h1
  exact hlo.2.2 t m ht hm (by rw [← hl, ← ho])

#print axioms freeL_holder

/-- A free atom at unit `o`: its lowest own promise has a free item. -/
def FreeAt (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (o : Nat) : Prop :=
  ∀ tw, TermPlant.LowOwn s ⟨l, o⟩ tw → ∃ U w, ¬ WordUnit E ⟨l, o⟩ ∧ AtOff c.ty o U ∧ Solid U ∧
    accs U = some [Acc.one] ∧ tb 0 U = true ∧ Ty.affine U = false ∧
    (PredAt s.mem ⟨l, o⟩ tw w ∨
      (PredU E ⟨l, o⟩ ∧ FirstW s.mem ⟨l, o⟩ tw ∧ ∃ m, s.mem[tw]? = some m ∧ mw m = w)) ∧ WordOK E c.ty o w

/-- **A free atom is covered by the free items.** -/
theorem freeL_cover {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o : Nat} {tw : Ts}
    (hf : FreeAt E s l c o) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) :
    ∃ x ∈ freeL E s l c, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true := by
  classical
  obtain ⟨U, w, hnw, hat, hsol, hU, hcl, ha, hpred, hok⟩ := hf tw hl
  have hQ : ∃ x, FreeQ E s l c tw x :=
    ⟨_, o, U, w, rfl, hl, hnw, hat, hsol, hU, hcl, ha, hpred, hok⟩
  have hmem : freeIt E s l c tw ∈ freeL E s l c := by
    unfold freeL
    exact List.mem_map.2 ⟨tw, List.mem_filter.2 ⟨hl.1, decide_eq_true hQ⟩, rfl⟩
  obtain ⟨o', U', w', hx, hl', -, -, -, hU', -⟩ := freeIt_spec hQ
  have e : o' = o := by
    obtain ⟨m1, hm1, hl1⟩ := hl.2.1
    obtain ⟨m2, hm2, hl2⟩ := hl'.2.1
    rw [hm1] at hm2
    cases hm2
    have := hl2.symm.trans hl1
    simp only [Address.mk.injEq] at this
    exact this.2
  subst e
  refine ⟨freeIt E s l c tw, hmem, [Acc.one], 0, by rw [hx]; exact hU', by rw [hx]; exact Nat.le_refl _,
    ?_, by rw [hx]⟩
  rw [hx]
  show InAcc [Acc.one] 0 (o' - o')
  rw [Nat.sub_self]
  exact ⟨Nat.le_refl _, by simp [nWords, Acc.size]⟩

#print axioms freeL_cover

/-- **(F3, R=0) The entry premise of `foreign_overCrPZ` from free atoms**: every unit written
by the step (a new message, or a footprint promise leaving the footprint, at the unit) that is
not a visible word unit is a free atom. -/
theorem hent_free {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell}
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
      (∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) ∨
      ∃ x ∈ freeL E s l c, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true := by
  intro o tw hI hv hl _ hov hno
  obtain ⟨t, m, -, hm, hloc, hsrc⟩ := newOver_src hpr hpre hVU hPUb hVis hv hov hno
  exact .inr (freeL_cover (hfree o hI hv t m hm hloc hsrc) hl)

#print axioms hent_free

end TermOverCrW
