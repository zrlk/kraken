import WeakCore.TermPoolStaging
import WeakCore.TermOverCrProm
import WeakCore.TermOwnCF

/-! # TermPoolTagW: transport lemmas for `poolTagP` across a promise step -/

namespace TermPoolTagW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermPoolStaging
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A frontier is kept by the plant (planted labels had none). -/
theorem egP_pfr {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (hspec : PlantSpec Eg P j n) {l : AllocLabel} {f : Ts} (hf : Eg.pfr l = some f) :
    (EgP Eg P N j n).pfr l = some f := by
  show (match P l with | some f => some f | none => Eg.pfr l) = some f
  cases e : P l with
  | none => exact hf
  | some f1 => rw [(hspec l f1 e).1] at hf; cases hf

/-- A cut cell is kept by the plant. -/
theorem cutSto_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (hspec : PlantSpec Eg P j n) {i : Nat} {l : AllocLabel} {cl : Cell} (h : cutSto Eg i l = some cl) :
    cutSto (EgP Eg P N j n) i l = some cl := by
  obtain ⟨h1, h2⟩ := cutSto_some.1 h
  exact cutSto_some.2 ⟨h1, h2.imp id fun ⟨f, hf⟩ => ⟨f, egP_pfr hspec hf⟩⟩

/-- Footprint messages are kept by a promise step (`fpProm` only appends; visibility only grows). -/
theorem fpAt_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (hspec : PlantSpec Eg P j n) {i : Nat} {S : AllocLabel → Prop} {a : Address} {t : Ts}
    (h : t ∈ FpAt (Cut Eg i S) a) : t ∈ FpAt (Cut (EgP Eg P N j n) i S) a := by
  unfold FpAt at h ⊢
  by_cases hv : Vis (Cut Eg i S) a.label
  · have hv2 : Vis (Cut (EgP Eg P N j n) i S) a.label := fun ⟨⟨c1, hc1, ho1⟩, hp1⟩ => by
      cases hpf : Eg.pfr a.label with
      | some f =>
        have h2 : (EgP Eg P N j n).pfr a.label = some f := egP_pfr hspec hpf
        rw [show (Cut (EgP Eg P N j n) i S).pfr a.label = (EgP Eg P N j n).pfr a.label from rfl, h2] at hp1
        cases hp1
      | none =>
        refine hv ⟨⟨c1, ?_, ho1⟩, hpf⟩
        exact cutSto_some.2 ⟨(cutSto_some.1 hc1).1, Or.inl ho1⟩
    simp only [hv, hv2, ↓reduceIte] at h ⊢
    show t ∈ fpProm Eg j n i
    unfold fpProm
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      rw [← hij]
      exact h
    · simp only [hij, ↓reduceIte]
      exact List.mem_append_left _ h
  · simp only [hv, ↓reduceIte] at h
    exact absurd h (List.not_mem_nil (a := t))

/-- Value resources are kept by the plant (copy of `TermOverCrProm.valOfR_EgP`). -/
theorem valOfR_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (hspec : PlantSpec Eg P j n) {i : Nat} {S : AllocLabel → Prop} {T : Ty} {ws : List Word}
    {R : Res} (h : ValOfR (Cut Eg i S) T ws R) : ValOfR (Cut (EgP Eg P N j n) i S) T ws R := by
  have hpf : ∀ l f, Eg.pfr l = some f → (EgP Eg P N j n).pfr l = some f := fun l f hf => egP_pfr hspec hf
  refine ValOfR_mono (η₁ := Cut Eg i S) (η₂ := Cut (EgP Eg P N j n) i S) rfl rfl (fun l c hc => ?_)
    (fun l => plantG_ini_le Eg P N l) h hpf (fun _ _ h => h) (fun _ => Nat.le_refl _)
  obtain ⟨h1, h2⟩ := cutSto_some.1 hc
  exact cutSto_some.2 ⟨h1, h2.imp id fun ⟨f, hf⟩ => ⟨f, hpf l f hf⟩⟩

/-- An old lowest own promise stays lowest (new promises lie above the old memory). -/
theorem lowOwn_fwd {s s2 : St} (hpre : ∀ t, t < s.mem.size → s2.mem[t]? = s.mem[t]?)
    (hpr : ∀ t, t ∈ s.promises → t ∈ s2.promises) (hnew : ∀ t, t ∈ s2.promises → t ∉ s.promises → s.mem.size ≤ t)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size) {a : Address} {tw : Ts} (h : TermPiece.LowOwn s a tw) :
    TermPiece.LowOwn s2 a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  refine ⟨hpr tw h1, ⟨m, by rw [hpre tw (hP tw h1)]; exact hm, hl⟩, fun t2 m2 ht2 hm2 hl2 => ?_⟩
  by_cases hin : t2 ∈ s.promises
  · exact h3 t2 m2 hin (by rw [← hpre t2 (hP t2 hin)]; exact hm2) hl2
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (hP tw h1) (hnew t2 ht2 hin))

/-- **A pool item survives a step keeping memory's prefix and only adding promises above it**,
with its mask restricted to the access groups whose units all had a lowest own promise before
(a unit that gains its first own promise drops out of the mask). -/
theorem crItem_tr {E E2 : TEnv} {s s2 : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hpre : ∀ t, t < s.mem.size → s2.mem[t]? = s.mem[t]?) (hpr : ∀ t, t ∈ s.promises → t ∈ s2.promises)
    (hnew : ∀ t, t ∈ s2.promises → t ∉ s.promises → s.mem.size ≤ t) (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsto : E2.sto l = E.sto l) (hV : ∀ U ws R, ValOfR E U ws R → ValOfR E2 U ws R)
    (h : TermPiece.CrItem E s cr l c x) :
    ∃ x2 : Ts × Nat × Ty × List Word × Res × (Nat → Bool), x2.1 = x.1 ∧ x2.2.1 = x.2.1 ∧ x2.2.2.1 = x.2.2.1 ∧
      TermPiece.CrItem E2 s2 cr l c x2 ∧ ∀ i, x.2.2.2.2.2 i = false → x2.2.2.2.2.2 i = false := by
  obtain ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, hR, hpin⟩ := h
  refine ⟨(x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, fun i => x.2.2.2.2.2 i &&
    @decide (∀ o, InAcc usS i o → ∃ t0, TermPiece.LowOwn s ⟨l, x.2.1 + o⟩ t0) (Classical.propDecidable _)), rfl, rfl, rfl,
    ⟨mh, usS, (hpre _ (hP _ hlo.1)).trans hmh, hlab, lowOwn_fwd hpre hpr hnew hP hlo,
    fun hw => hnw ?_, hat, hsol, husS, hq1, hq2, hwl, hV _ _ _ hvr, hR, fun i o w tw hk hi hw hl => ?_⟩,
    fun i hi => by simp only [hi, Bool.false_and]⟩
  · obtain ⟨c1, hc1, hor⟩ := hw
    exact ⟨c1, by rw [hlab, ← hsto, ← hlab]; exact hc1, hor⟩
  · obtain ⟨hk1, hk2⟩ := Eq.mp (Bool.and_eq_true _ _) hk
    obtain ⟨t0, h0⟩ := (@of_decide_eq_true _ (Classical.propDecidable _) hk2) o hi
    have e : tw = t0 := TermPiece.LowOwn_uniq hl (lowOwn_fwd hpre hpr hnew hP h0)
    subst e
    exact TermPlant.PredAt_mono (hP _ h0.1) hpre (hpin i o w tw hk1 hi hw h0)

/-- A promise step keeps frontiers (as `TermOwnPub.EgP_pfr`). -/
theorem egP_pfr_ne {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat} {l : AllocLabel}
    (h : Eg.pfr l ≠ none) : (EgP Eg P N j n).pfr l ≠ none := by
  show (match P l with | some f => some f | none => Eg.pfr l) ≠ none
  cases P l with
  | some f => exact fun h' => by cases h'
  | none => exact h

/-- A pool tag survives a promise step (memory pushed, promises only added above it). -/
theorem ptag_tr {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j : Nat} {c c2 : Cfg}
    (hspec : PlantSpec Eg P j c.mem.size) {mm : Msg} (hmem : c2.mem = c.mem.push mm)
    {jj : Nat} {thO thN : TTh} {f : Ts → Res} {t : Ts}
    (hpr : ∀ u, u ∈ thO.promises → u ∈ thN.promises) (hnew : ∀ u, u ∈ thN.promises → u ∉ thO.promises → c.mem.size ≤ u)
    (hP : ∀ u, u ∈ thO.promises → u < c.mem.size) (h : PTag Eg c jj thO f t) :
    PTag (EgP Eg P N j c.mem.size) c2 jj thN f t := by
  obtain ⟨ht, hk, m, hm, hfp, hit⟩ := h
  have hpre : ∀ u, u < c.mem.size → c2.mem[u]? = c.mem[u]? := fun u hu => by rw [hmem]; exact push_lt hu
  refine ⟨hpr t ht, hk, m, (hpre t (hP t ht)).trans hm, hfp.imp (fun hfp S => ?_) (fun hfp S => ?_), fun S => ?_⟩
  · obtain ⟨fq, mf, h1, h2, h3, h4⟩ := hfp S
    exact ⟨fq, mf, fpAt_egP hspec h1, (hpre fq (TermPiece.lt_size_of_some h2)).trans h2, h3, h4⟩
  · -- the K∅ branch: frontier kept (`EgP_pfr`), the empty-mask item transported
    obtain ⟨hpf, cl, x, hcl, hown, hx1, hK, hcr⟩ := hfp S
    have hcl2 : cutSto (EgP Eg P N j c.mem.size) jj m.loc.label = some cl := cutSto_egP hspec hcl
    obtain ⟨x2, hx2, -, -, hcr2, hK2⟩ := crItem_tr (s := stOf c.mem c.pairs thO) (s2 := stOf c2.mem c2.pairs thN)
      (E := Cut Eg jj S) (E2 := Cut (EgP Eg P N j c.mem.size) jj S) (l := m.loc.label) hpre hpr hnew hP
      (show cutSto (EgP Eg P N j c.mem.size) jj m.loc.label = cutSto Eg jj m.loc.label from hcl2.trans hcl.symm)
      (fun U ws R hv => valOfR_egP hspec hv) hcr
    exact ⟨egP_pfr_ne (N := N) (j := j) (n := c.mem.size) hpf, cl, x2, hcl2, hown, hx2.trans hx1, fun i => hK2 i (hK i), hcr2⟩
  · obtain ⟨cl, x, hcl, hown, hx1, hcr, hlow⟩ := hit S
    have hcl2 : cutSto (EgP Eg P N j c.mem.size) jj m.loc.label = some cl := cutSto_egP hspec hcl
    obtain ⟨x2, hx2, hb2, hS2, hcr2, -⟩ := crItem_tr (s := stOf c.mem c.pairs thO) (s2 := stOf c2.mem c2.pairs thN)
      (E := Cut Eg jj S) (E2 := Cut (EgP Eg P N j c.mem.size) jj S) (l := m.loc.label) hpre hpr hnew hP
      (show cutSto (EgP Eg P N j c.mem.size) jj m.loc.label = cutSto Eg jj m.loc.label from hcl2.trans hcl.symm)
      (fun U ws R hv => valOfR_egP hspec hv) hcr
    refine ⟨cl, x2, hcl2, hown, hx2.trans hx1, hcr2, ?_⟩
    rw [hb2, hS2]
    refine TermPool.pieceLow_frame hpre hP (fun u hu => ?_) (hP t ht) hlow
    by_cases hin : u ∈ thO.promises
    · exact Or.inl hin
    · exact Or.inr (hnew u hu hin)

/-! ## H v3: the own-cover list `PoolCovUL` across a promise step -/

/-- An item of the own cover. -/
abbrev ItemQ := Ts × Nat × Ty × List Word × Res × (Nat → Bool)

/-- The mask after a step: access `i` keeps its bit when every lowest own promise after the step on
its units is an old promise. -/
noncomputable def maskQ (s s2 : St) (l : AllocLabel) (x : ItemQ) : ItemQ :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, fun i => x.2.2.2.2.2 i &&
    @decide (∀ usS o tw', accs x.2.2.1 = some usS → InAcc usS i o →
      TermPlant.LowOwn s2 ⟨l, x.2.1 + o⟩ tw' → tw' ∈ s.promises) (Classical.propDecidable _))

/-- Masking keeps every holder's sum. -/
theorem sum_maskQ (s s2 : St) (l : AllocLabel) (t : Ts) (Gs : List ItemQ) :
    ((Gs.map (maskQ s s2 l)).filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1) =
      (Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1) := by
  induction Gs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    have e1 : (maskQ s s2 l x).1 = x.1 := rfl
    rw [e1]
    by_cases h : x.1 = t
    · simp only [h, decide_true, ↓reduceIte, List.map_cons, ih]
      rfl
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, ih]

section cov
variable {s s2 : St}
  (hpre : ∀ t, t < s.mem.size → s2.mem[t]? = s.mem[t]?)
  (hpr : ∀ t, t ∈ s.promises → t ∈ s2.promises)
  (hnew : ∀ t, t ∈ s2.promises → t ∉ s.promises → s.mem.size ≤ t)
  (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
include hpre hpr hnew hP

/-- **An own-cover item survives the step, masked.** -/
theorem crItemQ_mask {E E2 : TEnv} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {x : ItemQ}
    (hsto : E2.sto l = E.sto l) (hV : ∀ U ws R, ValOfR E U ws R → ValOfR E2 U ws R)
    (hPU : ∀ o, PredU E ⟨l, o⟩ → PredU E2 ⟨l, o⟩) (h : TermOverCr.CrItemQ E s cr l c x) :
    TermOverCr.CrItemQ E2 s2 cr l c (maskQ s s2 l x) := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  refine ⟨mh, usS, (hpre _ (hP _ a3.1)).trans a1, a2, TermOverCr.lowOwn_fwd hpre hpr hnew hP a3, ?_, a5, a6,
    a7, a8, a9, a10, hV _ _ _ a11, a12, ?_⟩
  · intro hw; apply a4
    exact (WordUnit_congr (show E2.sto mh.loc.label = E.sto mh.loc.label by rw [a2]; exact hsto)).1 hw
  · intro i o w tw' hK hIn hw hlo
    obtain ⟨hk1, hk2⟩ := Eq.mp (Bool.and_eq_true _ _) hK
    have hin := (@of_decide_eq_true _ (Classical.propDecidable _) hk2) usS o tw' a7 hIn hlo
    have hlo0 := TermOverCr.lowOwn_back hpre hpr hP hlo hin
    have htw : tw' < s.mem.size := hP _ hin
    rcases a13 i o w tw' hk1 hIn hw hlo0 with hp | ⟨hu, hf, m, hm, hmw⟩
    · exact .inl (TermPlant.PredAt_mono htw hpre hp)
    · exact .inr ⟨hPU _ hu, TermOwnCF.firstW_fwd hpre htw hf, m, by rw [hpre _ htw]; exact hm, hmw⟩

/-- **The own cover across the step** (old frontier cell): the masked list carries it, given that a
covering access keeps its old lowest promises (`hTwo`; automatic for a one-word access). -/
theorem covL_tr {E E2 : TEnv} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {Gs : List ItemQ}
    (hsz : s2.mem.size = s.mem.size + 1)
    (htop : ∀ o, s.mem.size ∈ s2.promises ++ FpAt E2 ⟨l, o⟩)
    (hsto : E2.sto l = E.sto l) (hV : ∀ U ws R, ValOfR E U ws R → ValOfR E2 U ws R)
    (hVU : ∀ o, VisU E2 ⟨l, o⟩ ↔ VisU E ⟨l, o⟩) (hPU : ∀ o, PredU E2 ⟨l, o⟩ ↔ PredU E ⟨l, o⟩)
    (hfp : ∀ a t, t ∈ FpAt E a → t ∈ FpAt E2 a)
    (hTwo : ∀ x ∈ Gs, ∀ usS i o o' tw tw', x.2.2.2.2.2 i = true → accs x.2.2.1 = some usS →
      InAcc usS i o → InAcc usS i o' → TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ tw →
      TermPlant.OverT E s ⟨l, x.2.1 + o⟩ tw → TermPlant.LowOwn s2 ⟨l, x.2.1 + o'⟩ tw' → tw' ∈ s.promises)
    (hGs : ∀ x ∈ Gs, TermOverCr.CrItemQ E s cr l c x)
    (hcov : ∀ o tw, PredU E ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩ →
      TermPlant.LowOwn s ⟨l, o⟩ tw → FirstW s.mem ⟨l, o⟩ tw →
      TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) :
    (∀ x ∈ Gs.map (maskQ s s2 l), TermOverCr.CrItemQ E2 s2 cr l c x) ∧
      ∀ o tw, PredU E2 ⟨l, o⟩ → ¬ VisU E2 ⟨l, o⟩ →
        TermPlant.LowOwn s2 ⟨l, o⟩ tw → FirstW s2.mem ⟨l, o⟩ tw →
        TermPlant.OverT E2 s2 ⟨l, o⟩ tw →
        ∃ x ∈ Gs.map (maskQ s s2 l), ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
          InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true := by
  refine ⟨fun x hx => ?_, fun o tw hu hv hl hf hov => ?_⟩
  · obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
    exact crItemQ_mask hpre hpr hnew hP hsto hV (fun o h => (hPU o).2 h) (hGs x0 hx0)
  obtain ⟨t, m, hlt, hm, hloc, hnp⟩ := hov
  obtain ⟨⟨m1, hm1, hl1, hv1⟩, hbelow⟩ := hf
  have hts : t < s.mem.size + 1 := hsz ▸ TermPiece.lt_size_of_some hm
  by_cases hin : tw ∈ s.promises
  · have hl0 := TermOverCr.lowOwn_back hpre hpr hP hl hin
    have htw := hP tw hin
    have hf0 : FirstW s.mem ⟨l, o⟩ tw :=
      ⟨⟨m1, by rw [← hpre tw htw]; exact hm1, hl1, hv1⟩, fun t' m' ht' hm' hl' =>
        hbelow t' m' ht' (by rw [hpre t' (Nat.lt_trans ht' htw)]; exact hm') hl'⟩
    have htn : t < s.mem.size := by
      refine Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hts) fun e => ?_
      subst e
      exact hnp (TermOverCrProm.mem_promAt_above hv (htop o) hlt hm1 hl1 hv1)
    have hm0 : s.mem[t]? = some m := by rw [← hpre t htn]; exact hm
    have hab : ∀ u, AboveFW s.mem ⟨l, o⟩ u → AboveFW s2.mem ⟨l, o⟩ u := fun u ⟨h0, hf1, hl2⟩ =>
      ⟨h0, TermOwnCF.firstW_fwd hpre (TermPiece.lt_size_of_some hf1.1.choose_spec.1) hf1, hl2⟩
    have hov0 : TermPlant.OverT E s ⟨l, o⟩ tw := ⟨t, m, hlt, hm0, hloc, fun h => hnp (TermOverCrProm.promAt_mono (hVU o) (hPU o) hpr (hfp _) hab h)⟩
    obtain ⟨x, hx, usS, i, h1, h2, h3, h4⟩ := hcov o tw ((hPU o).1 hu) (fun h => hv ((hVU o).2 h)) hl0 hf0 hov0
    refine ⟨maskQ s s2 l x, List.mem_map_of_mem hx, usS, i, h1, h2, h3, ?_⟩
    have e : x.2.1 + (o - x.2.1) = o := Nat.add_sub_cancel' h2
    show (x.2.2.2.2.2 i && _) = true
    rw [h4, Bool.true_and]
    refine @decide_eq_true _ (Classical.propDecidable _) fun usS' o' tw' hus hIn hlo' => ?_
    rw [h1] at hus
    cases hus
    exact hTwo x hx usS i (o - x.2.1) o' tw tw' h4 h1 h3 hIn (by rw [e]; exact hl0) (by rw [e]; exact hov0) hlo'
  · have h1 := hnew tw hl.1 hin
    exact absurd hts (Nat.not_lt.2 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt h1 hlt)))

end cov

/-- **The open TwoAt case** (open): a promise step does not give a fresh lowest
own promise to the other word of a covering access whose overtaken unit holds an old one. -/
def PromTwoNew (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PlantSpec Eg (plantOf c Eg j a v w) j c.mem.size → PoolTag Eg c pl →
    ∀ (S : AllocLabel → Prop) (l : AllocLabel) (cl : Cell) (x : ItemQ) (usS : List Acc) (i o o' : Nat) (tw tw' : Ts),
      (Cut Eg j S).sto l = some cl → cl.owner = some j → Eg.pfr l ≠ none → ¬ Eg.pubd l →
      TermOverCr.CrItemQ (Cut Eg j S) (stOf c.mem c.pairs th) (pl j) l cl x → x.2.2.2.2.2 i = true →
      accs x.2.2.1 = some usS → InAcc usS i o → InAcc usS i o' → o ≠ o' →
      TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, x.2.1 + o⟩ tw →
      TermPlant.OverT (Cut Eg j S) (stOf c.mem c.pairs th) ⟨l, x.2.1 + o⟩ tw →
      TermPlant.LowOwn (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) ⟨l, x.2.1 + o'⟩ tw' →
      tw' ∈ th.promises

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`PromTwoNew` holds**: an old own promise never lies on a two-word unit (`promNoTwo`), so a
covering access at a unit with an old lowest own promise is one-word (`inAcc_single`). -/
theorem promTwoNew_of {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts} :
    PromTwoNew p k arch Sp Init MintOK c0 plantOf := by
  intro c Eg Tot HP HS cr db pl j th a v w X _ _ S l cl x usS i o o' tw tw' hcl ho hpf _ hit _ hus hi hi' hne hl _ _
  exfalso
  apply hne
  obtain ⟨-, -, -, -, -, -, hat, -, -, -⟩ := hit
  obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hl
  have hsto0 : Eg.sto l = some cl := cutSto_sub (i := j) hcl
  have hno := X.inv.promNoTwo j th tw m cl X.hth htw hm (by rw [hml]; exact hsto0)
  rw [hml] at hno
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j th X.hth
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f (cutSto_own hsto0 ho) hf).1
  have hT0 : (∃ L, accs cl.ty = some L) ∨ ∃ N e, cl.ty = .array (.lit N) e := by
    rcases hlay with hA | ⟨N, e, he, -⟩
    · exact Or.inl (Option.ne_none_iff_exists'.1 hA)
    · exact Or.inr ⟨N, e, he⟩
  exact (TermOverCrW.inAcc_single hat hus hi hT0 hno o' hi').symm

end

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`poolTagP`**: the pool tags after a promise step (pool unchanged, planted environment), with
the own cover (`PoolCovUL`): at an old frontier cell the masked old list (`covL_tr`); at a newly
planted cell nothing is overtaken (`OwnOKSF` with no frontier and `PromAbove`). -/
theorem poolTagP_of {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
    {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat} :
    poolTagP p k arch Sp Init MintOK c0 plantOf plantN := by
  intro c Eg Tot HP HS cr db pl j th a v w X hspec htag
  obtain ⟨epc, hpj, -⟩ := promise_inv (a := a) (v := v) (w := w) X.hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [epc]
  have hpairs : (promise c j a v w).pairs = c.pairs := by rw [epc]
  have hpre : ∀ u, u < c.mem.size → (promise c j a v w).mem[u]? = c.mem[u]? := fun u hu => by
    rw [hmem]; exact push_lt hu
  have hsz : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hmem]; exact Array.size_push _
  refine And.intro ?_ ?_
  · intro jj thj t hthj hz
    by_cases hjj : jj = j
    · subst hjj
      rw [hpj] at hthj
      cases hthj
      refine ptag_tr hspec hmem (thO := th) (fun u hu => List.mem_append_left _ hu) (fun u hu hn => ?_)
        (fun u hu => X.inv.plt jj th u X.hth hu) (htag.1 jj th t X.hth hz)
      rcases List.mem_append.1 hu with h1 | h1
      · exact absurd h1 hn
      · rw [List.mem_singleton.1 h1]
        exact Nat.le_refl _
    · rw [promise_other X.hth hjj] at hthj
      exact ptag_tr hspec hmem (fun u hu => hu) (fun u hu hn => absurd hu hn)
        (fun u hu => X.inv.plt jj thj u hthj hu) (htag.1 jj thj t hthj hz)
  intro jj thj S hthj l cl hcl ho hpf hpb
  have hsto0 : Eg.sto l = some cl :=
    cutSto_sub (Eg := EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (i := jj) hcl
  have hV : ∀ U ws R, ValOfR (Cut Eg jj S) U ws R →
      ValOfR (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) jj S) U ws R :=
    fun U ws R h => valOfR_egP hspec h
  by_cases hpf0 : Eg.pfr l = none
  · -- a newly planted cell: nothing is overtaken
    obtain ⟨f, hf⟩ : ∃ f, plantOf c Eg j a v w l = some f := by
      cases e : plantOf c Eg j a v w l with
      | none => exact absurd ((TermOverCrProm.EgP_pfr_none (N := plantN c Eg j a v w) (j := j)
          (n := c.mem.size) e).trans hpf0) hpf
      | some f => exact ⟨f, rfl⟩
    obtain ⟨cl1, hcl1, hown1⟩ := (hspec l f hf).2.1
    rw [hsto0] at hcl1
    cases hcl1
    have hjj : jj = j := Option.some.inj (ho.symm.trans hown1)
    subst hjj
    rw [hpj] at hthj
    cases hthj
    refine ⟨[], fun t => Res.zero_le _, fun x hx => absurd hx (List.not_mem_nil (a := x)), ?_⟩
    intro o tw hu hv hl hfw hov
    exfalso
    obtain ⟨t, m, hlt, hm, hloc, hnp⟩ := hov
    obtain ⟨htw, ⟨mw, hmw, hlw⟩, -⟩ := hl
    obtain ⟨m1, hm1, hl1, hv1⟩ := hfw.1
    by_cases hin : t ∈ th.promises ++ [c.mem.size]
    · exact hnp (TermOverCrProm.mem_promAt_above hv (List.mem_append_left _ hin) hlt hm1 hl1 hv1)
    have htn : t < c.mem.size := by
      have h1 := TermPiece.lt_size_of_some hm
      change t < (promise c jj a v w).mem.size at h1
      rw [hsz] at h1
      refine Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h1) fun e => hin ?_
      rw [e]; exact List.mem_append_right _ (List.mem_singleton_self _)
    have hm0 : c.mem[t]? = some m := by rw [← hpre t htn]; exact hm
    have htp : t ∉ th.promises := fun h => hin (List.mem_append_left _ h)
    have htw0 : tw ∈ th.promises := by
      rcases List.mem_append.1 htw with h | h
      · exact h
      · rw [List.mem_singleton.1 h] at hlt
        exact absurd (Nat.lt_trans hlt htn) (Nat.lt_irrefl _)
    have hmw0 : c.mem[tw]? = some mw := by rw [← hpre tw (X.inv.plt jj th tw X.hth htw0)]; exact hmw
    obtain ⟨S0, -, -, hMI, -, -, -⟩ := X.inv.thr jj th X.hth
    have hle := TermOverCrProm.priv_le_coh (l := l) (cl := cl) hMI (cutSto_own hsto0 ho) ho hpf0
      (X.inv.msgWords t m cl hm0 (by rw [hloc]; exact hsto0)) htp hm0 (by rw [hloc])
    have hpa := X.inv.promAbove jj th X.hth tw htw0 mw hmw0
    rw [hlw, ← hloc] at hpa
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle (Nat.lt_trans hpa hlt))
  -- an old frontier cell: the masked old list
  have hPl : plantOf c Eg j a v w l = none := by
    cases e : plantOf c Eg j a v w l with
    | none => rfl
    | some f => exact absurd (hspec l f e).1 hpf0
  have hcl0 : (Cut Eg jj S).sto l = some cl := cutSto_own hsto0 ho
  have hsEq : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) jj S).sto l =
      (Cut Eg jj S).sto l := hcl.trans hcl0.symm
  have hU := fun o => TermOverCrProm.unit_congr (c := cl) (o := o) hsEq rfl
    (TermOverCrProm.EgP_pfr_none (N := plantN c Eg j a v w) (j := j) (n := c.mem.size) hPl)
    (TermOverCrProm.EgP_ini_none (N := plantN c Eg j a v w) (j := j) (n := c.mem.size) hPl) rfl
  have hfp : ∀ a0 t, t ∈ FpAt (Cut Eg jj S) a0 →
      t ∈ FpAt (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) jj S) a0 :=
    fun a0 t h => fpAt_egP hspec h
  by_cases hjj : jj = j
  · subst hjj
    rw [hpj] at hthj
    cases hthj
    obtain ⟨Gs, hsum, hit, hcov⟩ := htag.2 jj th S X.hth l cl hcl0 ho hpf0 hpb
    have hP : ∀ u, u ∈ th.promises → u < c.mem.size := fun u hu => X.inv.plt jj th u X.hth hu
    have hpr : ∀ u, u ∈ th.promises → u ∈ th.promises ++ [c.mem.size] := fun u hu => List.mem_append_left _ hu
    have hnew : ∀ u, u ∈ th.promises ++ [c.mem.size] → u ∉ th.promises → c.mem.size ≤ u := fun u hu hn => by
      rcases List.mem_append.1 hu with h1 | h1
      · exact absurd h1 hn
      · rw [List.mem_singleton.1 h1]
        exact Nat.le_refl _
    refine ⟨Gs.map (maskQ (stOf c.mem c.pairs th)
      (stOf (promise c jj a v w).mem (promise c jj a v w).pairs { th with promises := th.promises ++ [c.mem.size] }) l),
      fun t => by rw [sum_maskQ]; exact hsum t, ?_⟩
    refine covL_tr (s := stOf c.mem c.pairs th)
      (s2 := stOf (promise c jj a v w).mem (promise c jj a v w).pairs { th with promises := th.promises ++ [c.mem.size] }) hpre hpr hnew hP hsz
      (fun o => List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))) hsEq hV
      (fun o => (hU o).2.1) (fun o => (hU o).2.2) hfp ?_ hit hcov
    intro x hx usS i o o' tw tw' hb hus hi hi' hl hov hl'
    by_cases e : o = o'
    · subst e
      rw [← TermPlant.LowOwn_uniq (TermOverCr.lowOwn_fwd hpre hpr hnew hP hl) hl']
      exact hl.1
    · rw [hmem, hpairs] at hl'
      exact promTwoNew_of (plantOf := plantOf) X hspec htag S l cl x usS i o o' tw tw' hcl0 ho hpf0 hpb (hit x hx) hb hus hi hi' e hl hov hl'
  · rw [promise_other X.hth hjj] at hthj
    obtain ⟨Gs, hsum, hit, hcov⟩ := htag.2 jj thj S hthj l cl hcl0 ho hpf0 hpb
    have hP : ∀ u, u ∈ thj.promises → u < c.mem.size := fun u hu => X.inv.plt jj thj u hthj hu
    have hvis : Vis (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) jj S) l :=
      fun h => hpf h.2
    refine ⟨Gs.map (maskQ (stOf c.mem c.pairs thj) (stOf (promise c j a v w).mem (promise c j a v w).pairs thj) l),
      fun t => by rw [sum_maskQ]; exact hsum t, ?_⟩
    refine covL_tr (s := stOf c.mem c.pairs thj)
      (s2 := stOf (promise c j a v w).mem (promise c j a v w).pairs thj) hpre (fun u hu => hu) (fun u hu hn => absurd hu hn) hP hsz
      (fun o => List.mem_append_right _ ?_) hsEq hV (fun o => (hU o).2.1) (fun o => (hU o).2.2) hfp
      (fun x _ usS i o o' tw tw' _ _ _ _ _ _ hl' => hl'.1) hit hcov
    unfold FpAt
    simp only [hvis, ↓reduceIte]
    show c.mem.size ∈ fpProm Eg j c.mem.size jj
    unfold fpProm
    simp only [hjj, ↓reduceIte]
    exact List.mem_append_right _ (List.mem_singleton_self _)

end

end TermPoolTagW

#print axioms TermPoolTagW.cutSto_egP
#print axioms TermPoolTagW.fpAt_egP
#print axioms TermPoolTagW.crItem_tr
#print axioms TermPoolTagW.crItemQ_mask
#print axioms TermPoolTagW.covL_tr
#print axioms TermPoolTagW.promTwoNew_of
#print axioms TermPoolTagW.poolTagP_of
