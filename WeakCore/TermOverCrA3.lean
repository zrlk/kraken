import WeakCore.TermOverCrBII
import WeakCore.TermOverCrX
import WeakCore.TermOverCr5D
import WeakCore.TermOverCrOwnCommon
import WeakCore.TermPieceCov
import WeakCore.TermUnitKeepC

/-! # TermOverCrA3: the own cover at the own-path op kinds (M5)

`openOverCrOwnA_of : OpenOverCrOwnA …` (no premise).

* `overCr_ownopH` (closed): `overCr_ownopD` fed by pool-form re-pin items (`RepinQh`, no credit
  bound) whose credit is any `rpSum RS` inside the new credits: covers both of `KeepQRS`'s lists
  (`RSc` via `repinQh_of_U`, `RSh` directly) at the total credits `cr' + plStep`.
* `cover_core` (closed): the kept items are those away from the discharged promises; a unit in a
  piece holding a discharged promise is re-pinned (`FulP`, `RepinCovS`); every other unit keeps its
  old window and overtaking (`hUK`).
* `predU_iff` (closed): the prediction status across the footprint, given that the real count
  does not rise over the unit; the coherence half of `hUK` is `TermUnitKeepC` (closed).
* `repinCov_full` (closed): `KeepQRSB`'s `RepinCovSB` (no `bufInit`-at-`rc` exclusion) covers
  every unit; the former open `OpenBiRc` is gone.
* `OpenRcKeep` (discharged): the real count `rini` does not rise over an untouched predicted
  unit is `KeepQRS`'s last conjunct `TermPlant.RcKeepP`, produced at every step.
-/

namespace TermOverCrA3
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Re-pin item lists -/

theorem rpSum_eq (RS : List (AllocLabel × Cell × TermPiece.CrIt)) (t : Ts) :
    TermPiece.rpSum RS t = TermOverCrX.rpSumI RS t := rfl

/-- An item's resource is within its list's re-pin credit at its holder. -/
theorem le_rpSum : ∀ (RS : List (AllocLabel × Cell × TermPiece.CrIt)) (y : AllocLabel × Cell × TermPiece.CrIt),
    y ∈ RS → y.2.2.2.2.2.2.1 ≤ TermPiece.rpSum RS y.2.2.1
  | [], _, h => absurd h List.not_mem_nil
  | z :: RS, y, h => by
      rw [rpSum_eq, TermOverCrX.rpSumI_cons, ← rpSum_eq]
      rcases List.mem_cons.1 h with e | h
      · subst e
        simp only [ite_true]
        exact Res.le_add_right _ _
      · exact Res.le_trans (le_rpSum RS y h) (TermOverCrW.le_add_leftR _ _)
#print axioms TermOverCrA3.le_rpSum

theorem rpSum_append (L1 L2 : List (AllocLabel × Cell × TermPiece.CrIt)) (t : Ts) :
    TermPiece.rpSum (L1 ++ L2) t = TermPiece.rpSum L1 t + TermPiece.rpSum L2 t := by
  unfold TermPiece.rpSum
  rw [List.filter_append, List.map_append, Res.sum_append]
#print axioms TermOverCrA3.rpSum_append

/-- Credited re-pin items are pool-form ones. -/
theorem repinQh_of_U {E' : TEnv} {s' : St} {cr' : Ts → Res} {RS : List (AllocLabel × Cell × TermPiece.CrIt)}
    (h : TermPiece.RepinQU E' s' cr' RS) : TermPiece.RepinQh E' s' RS := by
  intro y hy
  obtain ⟨a1, a2, a3, ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -, bp⟩, a5, a6, a7⟩ := h y hy
  exact ⟨a1, a2, a3, ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, bp⟩, a5, a6, a7⟩
#print axioms TermOverCrA3.repinQh_of_U

theorem repinQh_append {E' : TEnv} {s' : St} {L1 L2 : List (AllocLabel × Cell × TermPiece.CrIt)}
    (h1 : TermPiece.RepinQh E' s' L1) (h2 : TermPiece.RepinQh E' s' L2) : TermPiece.RepinQh E' s' (L1 ++ L2) :=
  fun y hy => (List.mem_append.1 hy).elim (h1 y) (h2 y)
#print axioms TermOverCrA3.repinQh_append

/-! ## The glue: `overCr_ownopD` at pool-form re-pin items -/

section ownH
variable {s s' : St} (hmem : s'.mem = s.mem) (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
include hmem hsub

/-- **The owner's cover at its own op, pool-form re-pin items.**  As `TermOverCrX.overCr_ownopRS`,
with `RepinQh` (no credit bound) in place of `RepinQI` and the credit fit `cr0 + rpSum RS ≤ cr'`
in place of the equality: the item bound comes from `le_rpSum`. -/
theorem overCr_ownopH {E E' : TEnv} {cr cr0 cr' : Ts → Res} {l : AllocLabel} {c : Cell} {G G' : Nat → Ts → Prop}
    {Gs Gk Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    {RS : List (AllocLabel × Cell × TermPiece.CrIt)}
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
    (hRS : TermPiece.RepinQh E' s' RS)
    (hcrT : ∀ t, cr0 t + TermPiece.rpSum RS t ≤ cr' t)
    (hnd0 : ((Gk ++ Gn).map (·.1)).Nodup)
    (hR0 : ∀ x ∈ Gk ++ Gn, x.2.2.2.2.1 ≤ cr0 x.1)
    (hHL0 : TermOverCr.HolderLow s' l (Gk ++ Gn))
    (hcovN0 : ∀ o tw, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o → ¬ VisU E' ⟨l, o⟩ →
      TermPlant.LowOwn s' ⟨l, o⟩ tw → G' o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ((∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, o⟩) ∧
        ¬ VisU E ⟨l, o⟩ ∧ G o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw ∧
        ∀ x ∈ Gs, (∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
          x.2.2.2.2.2 i = true) → x ∈ Gk) ∨
      (∃ x ∈ Gn, TermOverCrX.CrCovI x o) ∨ ∃ y ∈ RS, y.1 = l ∧ TermPiece.CrCov y.2.2 o)
    (hzN : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E' m.loc →
      cr' t ≠ .zero → (cr t ≠ .zero ∧ ∀ x ∈ Gs, x.1 = t → x ∈ Gk) ∨ t ∈ Gn.map (·.1) ∨
        ∃ y ∈ RS, y.1 = l ∧ y.2.2.1 = t) :
    ∃ Gs', TermOverCr.OverCrL E' s' cr' l c G' Gs' ∧ TermOverCr.HolderLow s' l Gs' := by
  have hcell : ∀ y ∈ RS, y.1 = l → y.2.1 = c := by
    intro y hy hl
    have h1 := (hRS y hy).1
    rw [hl, hsto, hsto0] at h1
    exact (Option.some.inj h1).symm
  have hDn : ∀ x ∈ TermOverCrX.rpL RS l, TermOverCr.CrItemQ E' s' cr' l c x := by
    intro x hx
    obtain ⟨y, hy, hl, rfl⟩ := TermOverCrX.mem_rpL.1 hx
    have hit := (hRS y hy).2.2.2.1
    rw [hl, hcell y hy hl] at hit
    have hb : y.2.2.2.2.2.2.1 ≤ cr' y.2.2.1 :=
      Res.le_trans (le_rpSum RS y hy) (Res.le_trans (TermOverCrW.le_add_leftR _ _) (hcrT _))
    obtain ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, bp⟩ := hit
    exact ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, hb,
      fun i o w tw' hk hi hw hlo => .inl (bp i o w tw' hk hi hw hlo)⟩
  have hwaD : ∀ x ∈ TermOverCrX.rpL RS l, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true →
      InAcc usS i o → ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0 := by
    intro x hx usS i o h1 h2 h3
    obtain ⟨y, hy, hl, rfl⟩ := TermOverCrX.mem_rpL.1 hx
    have hc : TermPiece.CrCov y.2.2 (y.2.2.2.1 + o) :=
      ⟨usS, i, h1, Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact h3, h2⟩
    obtain ⟨tw, hlo, -⟩ := (hRS y hy).2.2.2.2.2.2 _ hc
    rw [hl] at hlo
    exact ⟨tw, hlo⟩
  have hsumL : ∀ t, TermOverCrW.sumH (Gk ++ Gn ++ TermOverCrX.rpL RS l) t ≤ cr' t := by
    intro t
    rw [TermOverCrW.sumH_append]
    have a := TermOverCrW.sumH_le_of_nodup hnd0 hR0 t
    have b := TermOverCrX.sumH_rpL_le l t RS
    have d := hcrT t
    intro k
    have a1 := a k; have b1 := b k; have d1 := d k
    rw [← rpSum_eq] at b1
    simp only [Res.add_apply] at a1 b1 d1 ⊢; omega
  have hHL : TermOverCr.HolderLow s' l (Gk ++ Gn ++ TermOverCrX.rpL RS l) := by
    intro x hx usS hus t m ht hm hl h1 h2
    rcases List.mem_append.1 hx with hx | hx
    · exact hHL0 x hx usS hus t m ht hm hl h1 h2
    · obtain ⟨y, hy, hyl, rfl⟩ := TermOverCrX.mem_rpL.1 hx
      exact (hRS y hy).2.2.2.2.2.1 usS hus t m ht hm (by rw [hyl]; exact hl) h1 h2
  refine TermOverCr5.overCr_ownopD hmem hsub (Dn := TermOverCrX.rpL RS l) hcpl hni hsto0 hpf hpi hsto hV hPU h
    hGk hcrK hnfH hnfK hGn hwaN hDn hwaD hsumL hHL (fun o tw hi hi0 hv hlo hg hov => ?_)
    (fun t m ht hm hl hw hnz => ?_)
  · rcases hcovN0 o tw hi hi0 hv hlo hg hov with hk | ⟨x, hx, hc⟩ | ⟨y, hy, hyl, hc⟩
    · exact .inl hk
    · exact .inr ⟨x, List.mem_append_left _ hx, hc⟩
    · exact .inr ⟨y.2.2, List.mem_append_right _ (TermOverCrX.mem_rpL.2 ⟨y, hy, hyl, rfl⟩), hc⟩
  · rcases hzN t m ht hm hl hw hnz with hk | hn | ⟨y, hy, hyl, hyt⟩
    · exact .inl hk
    · exact .inr (by rw [List.map_append]; exact List.mem_append_left _ hn)
    · exact .inr (by
        rw [List.map_append]
        exact List.mem_append_right _
          (List.mem_map.2 ⟨y.2.2, TermOverCrX.mem_rpL.2 ⟨y, hy, hyl, rfl⟩, hyt⟩))
#print axioms TermOverCrA3.overCr_ownopH

end ownH

/-! ## The open fact and the skeleton -/

/-- **The full re-pin cover**: `KeepQRSB`'s `RepinCovSB` has no `bufInit`-at-`rc`
exclusion, so it covers every unit directly. -/
theorem repinCov_full {E E' : TEnv} {s s' : St} {th : TTh} {RSc RSh : List (AllocLabel × Cell × TermPiece.CrIt)}
    (hcov : TermPiece.RepinCovSB E E' s s' th RSc RSh)
    (lab : AllocLabel) (htg : TermPiece.OpTgtP th lab) (c1 : Cell) (o : Nat) (th0 tw : Ts)
    (h1 : E.sto lab = some c1) (h2 : c1.owner = some E.tid) (h3 : E.pfr lab ≠ none)
    (h4 : ¬ VisU E ⟨lab, o⟩) (h5 : TermPlant.LowOwn s ⟨lab, o⟩ th0)
    (h6 : th0 ∉ s'.promises) (h7 : TermPlant.LowOwn s' ⟨lab, o⟩ tw)
    (h8 : TermPlant.OverT E' s' ⟨lab, o⟩ tw) (h9 : TermPiece.WinGU E' s' lab o tw)
    (h10 : ∃ q S usS, TermPiece.Piece c1.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) :
    ∃ y ∈ RSc ++ RSh, y.1 = lab ∧ TermPiece.CrCov y.2.2 o :=
  hcov lab htg c1 o th0 tw h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
#print axioms TermOverCrA3.repinCov_full

/-! ## Pieces of typed words -/

/-- A closed buffer type's element type is closed (copy of `TermOverCrW.Clo_arr`). -/
theorem clo_arrA {N : Idx} {e : Ty} (h : Clo (.array N e)) : Clo e := by
  have h1 := h.1
  simp only [tb] at h1
  refine ⟨h1, fun ρ W a b => ?_⟩
  have := h.2 ρ W a b
  simp only [cl, Ty.array.injEq] at this
  exact this.2

/-- **A typed word lies in a piece of its cell** (copy of `TermOverCrW.piece_of_wordOK`). -/
theorem piece_of_wordOKA {E : TEnv} {T : Ty} {o : Nat} {w : Word} (hc : Clo T) (hm : mg T = true)
    (hw : WordOK E T o w) :
    ∃ b S us, TermPiece.Piece T b S ∧ accs S = some us ∧ b ≤ o ∧ o < b + nWords us := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨-, hsh⟩, hw0, -, hbo⟩ := hw
  have ho' : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  rcases hseg with ⟨rfl, rfl, hA⟩ | ⟨N, us, jj, rfl, hus, hj, rfl⟩
  · obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.1 hA
    have hl := hsh L hL
    exact TermPieceCov.piece_cover hc hm hL (by omega)
  · have hl := hsh us hus
    have hm' : mg S = true := by simpa [mg] using hm
    have hle : (jj + 1) * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at hle
    exact TermPieceCov.piece_cover_arr (clo_arrA hc) hm' hus (by omega)
#print axioms TermOverCrA3.piece_of_wordOKA

/-! ## The step's unit facts -/

/-- **The prediction status across the footprint**: with no fresh frontier cell, the frontiers
kept (`PfrG` off the op's labels), the count `ini` fixed at a frontier cell with `ini ≤ rini`
(`IniFixZ`), and the real count not rising over the unit (`hR`), a unit is predicted before iff
after. -/
theorem predU_iff {g : G} {E E' : TEnv} {s s' : St} {a : Address} (hF : EFoot g E E' s s')
    (hfr : ∀ l, FreshIn g s.nalloc s'.nalloc l → E.sto l = none ∧ E.pfr l = none)
    (hpg : ∀ l, E.sto l ≠ none → E'.pfr l ≠ E.pfr l → False)
    (hIZ : ∀ l c f, E.pfr l ≠ none ∧ E.ini l ≤ E.rini l → ¬ FreshIn g s.nalloc s'.nalloc l →
      E.sto l = some c → E.pfr l = some f → E'.ini l = E.ini l)
    (hR : PredU E a → ∀ c N e us, E.sto a.label = some c → c.ty = .array (.lit N) e → accs e = some us →
      E'.rini a.label * nWords us ≤ a.offset) :
    PredU E a ↔ PredU E' a := by
  obtain ⟨-, -, hsto, -, hini, hpfr, -, -, -, hri, -⟩ := hF
  have hstoF : ∀ l c, E.sto l = some c → E'.sto l = some c := by
    intro l c hc
    rcases hsto l with e | ⟨hFr, -⟩
    · rw [e]; exact hc
    · rw [(hfr l hFr).1] at hc; cases hc
  have hstoB : ∀ l c, E'.sto l = some c → E'.pfr l ≠ none → E.sto l = some c := by
    intro l c hc hp
    rcases hsto l with e | ⟨hFr, -⟩
    · rw [← e]; exact hc
    · obtain ⟨h0, hp0⟩ := hfr l hFr
      rcases hpfr l with e2 | ⟨-, -, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, e2⟩
      · exact absurd (e2.trans hp0) hp
      · rw [h0] at hc1; cases hc1
      · rw [e2] at hc; cases hc
  have hstoB0 : ∀ l c, E'.sto l = some c → E.pfr l ≠ none → E.sto l = some c := by
    intro l c hc hp
    rcases hsto l with e | ⟨hFr, -⟩
    · rw [← e]; exact hc
    · exact absurd (hfr l hFr).2 hp
  have hpfrE : ∀ l, E.sto l ≠ none → E'.pfr l = E.pfr l := fun l hs =>
    (Classical.em _).elim id fun hne => False.elim (hpg l hs hne)
  have hiniE : ∀ l c, E.sto l = some c → E.pfr l ≠ none → E'.ini l = E.ini l := by
    intro l c hc hp
    rcases (hini l).2 with e | hFr | ⟨-, -, h3⟩
    · exact e
    · rw [(hfr l hFr).1] at hc; cases hc
    · rcases h3 hp with e | hle
      · exact e
      · obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hp
        exact hIZ l c f ⟨hp, hle⟩ (fun hFr => by rw [(hfr l hFr).1] at hc; cases hc) hc hf
  constructor
  · intro hP
    obtain ⟨hp, hw, hnr⟩ := id hP
    obtain ⟨c, hc⟩ : ∃ c, E.sto a.label = some c := by
      cases hcs : E.sto a.label with
      | none => exact absurd (show IniWr E a from fun c N e us h => by rw [hcs] at h; cases h) hnr
      | some c => exact ⟨c, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hpfrE a.label (by rw [hc]; exact Option.some_ne_none _)]; exact hp
    · intro c1 N e us hc1 hT hu
      exact Nat.lt_of_lt_of_le (hw c1 N e us (hstoB0 _ _ hc1 hp) hT hu)
        (Nat.mul_le_mul_right (nWords us) (hini a.label).1)
    · intro hw1
      apply hnr
      intro c1 N e us hc1 hT hu
      exfalso
      have h1 : a.offset < min (E'.ini a.label) (E'.rini a.label) * nWords us :=
        hw1 c1 N e us (hstoF _ _ hc1) hT hu
      have h2 := hR hP c1 N e us hc1 hT hu
      have h3 := Nat.mul_le_mul_right (nWords us) (Nat.min_le_right (E'.ini a.label) (E'.rini a.label))
      exact absurd (Nat.lt_of_lt_of_le h1 (Nat.le_trans h3 h2)) (Nat.lt_irrefl _)
  · intro hP
    obtain ⟨hp', hw', hnr'⟩ := hP
    obtain ⟨c, hc'⟩ : ∃ c, E'.sto a.label = some c := by
      cases hcs : E'.sto a.label with
      | none => exact absurd (show IniWr E' a from fun c N e us h => by rw [hcs] at h; cases h) hnr'
      | some c => exact ⟨c, rfl⟩
    have hc := hstoB _ _ hc' hp'
    have hpe := hpfrE a.label (by rw [hc]; exact Option.some_ne_none _)
    have hp : E.pfr a.label ≠ none := by rw [← hpe]; exact hp'
    have hie := hiniE _ _ hc hp
    refine ⟨hp, ?_, ?_⟩
    · intro c1 N e us hc1 hT hu
      have h1 := hw' c1 N e us (hstoF _ _ hc1) hT hu
      rw [hie] at h1
      exact h1
    · intro hw
      apply hnr'
      intro c1 N e us hc1 hT hu
      have h1 : a.offset < min (E.ini a.label) (E.rini a.label) * nWords us :=
        hw c1 N e us (hstoB _ _ hc1 hp') hT hu
      show a.offset < min (E'.ini a.label) (E'.rini a.label) * nWords us
      have h2 : min (E.ini a.label) (E.rini a.label) ≤ min (E'.ini a.label) (E'.rini a.label) :=
        Nat.le_min.2 ⟨Nat.le_trans (Nat.min_le_left _ _) (hini a.label).1,
          Nat.le_trans (Nat.min_le_right _ _) (hri a.label)⟩
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right (nWords us) h2)
#print axioms TermOverCrA3.predU_iff

/-! ## The cover core (abstract states) -/

theorem addr_eq {a : Address} {l : AllocLabel} {o : Nat} (h1 : a.label = l) (h2 : a.offset = o) :
    a = ⟨l, o⟩ := by
  subst h1
  subst h2
  rfl

/-- An item away from the step's discharged promises at `l`: none lies in its piece. -/
def NFi (s s' : St) (l : AllocLabel) (x : TermPiece.CrIt) : Prop :=
  ∀ usS, accs x.2.2.1 = some usS → ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m →
    m.loc.label = l → x.2.1 ≤ m.loc.offset → m.loc.offset < x.2.1 + nWords usS → False

/-- A credited item's piece: a piece of the cell, all of its units non-word, its holder the lowest
own promise at a unit of it. -/
theorem item_piece {E : TEnv} {s : St} {l : AllocLabel} {cl : Cell} {cr : Ts → Res} {x : TermPiece.CrIt}
    (hsto0 : E.sto l = some cl) (h : TermOverCr.CrItemQ E s cr l cl x) :
    ∃ mh usS, s.mem[x.1]? = some mh ∧ mh.loc = ⟨l, mh.loc.offset⟩ ∧
      TermPlant.LowOwn s ⟨l, mh.loc.offset⟩ x.1 ∧ accs x.2.2.1 = some usS ∧
      TermPiece.Piece cl.ty x.2.1 x.2.2.1 ∧ x.2.1 ≤ mh.loc.offset ∧ mh.loc.offset < x.2.1 + nWords usS ∧
      x.2.2.2.2.1 ≤ cr x.1 ∧ ∀ o', x.2.1 ≤ o' → o' < x.2.1 + nWords usS → ¬ WordUnit E ⟨l, o'⟩ := by
  obtain ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, hus, h1, h2, -, -, hR, -⟩ := h
  have hloc : mh.loc = ⟨l, mh.loc.offset⟩ := addr_eq hlab rfl
  have hP : TermPiece.Piece cl.ty x.2.1 x.2.2.1 := ⟨hat, hsol, by
    rw [wc_of_accs hus]
    intro e
    have := Option.some.inj e
    have h2n : x.2.1 + nWords usS > mh.loc.offset := h2
    omega⟩
  refine ⟨mh, usS, hmh, hloc, by rw [← hloc]; exact hlo, hus, hP, h1, h2, hR,
    TermPiece.nword_piece hsto0 hP hus h1 h2 (by rw [← hloc]; exact hnw)⟩
#print axioms TermOverCrA3.item_piece

/-- **The own cover at an own-path op, abstract form.**  The kept items are those away from the
discharged promises (`NFi`); a unit in a piece holding a discharged promise is re-pinned (`hRC`,
via `FulP`'s whole-piece discharge `hFP`); every other unit keeps its old window and overtaking
(`hUK`). -/
theorem cover_core {E E' : TEnv} {s s' : St} {l : AllocLabel} {cl : Cell} {crA cr0 crB : Ts → Res}
    {Gs : List TermPiece.CrIt} {RS : List (AllocLabel × Cell × TermPiece.CrIt)} {Tg : Prop}
    (hmem : s'.mem = s.mem) (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (hcpl : Ty.coupledOKIn [] cl.ty = true) (hni : noIallV cl.ty = true)
    (hsto0 : E.sto l = some cl) (hpf : E.pfr l ≠ none)
    (hpi : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → ∀ cl, E.sto m.loc.label = some cl →
      E.pfr m.loc.label ≠ none → InitR E cl m.loc.label m.loc.offset)
    (hsto : E'.sto l = E.sto l) (hpfe : E'.pfr l = E.pfr l) (htid : E'.tid = E.tid) (hfpe : E'.fp = E.fp)
    (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hL : TermOverCr.OverCrL E s crA l cl (TermOverCr.WinG E s l) Gs) (hHL : TermOverCr.HolderLow s l Gs)
    (hRS : TermPiece.RepinQh E' s' RS)
    (hcrE : ∀ t, crB t = cr0 t + TermPiece.rpSum RS t)
    (hle0 : ∀ t, cr0 t ≤ crA t)
    (hKeep : ∀ t m, t ∈ s'.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      crA t ≤ cr0 t)
    (hFP : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc.label = l →
      ¬ WordUnit E m.loc → Tg ∧ ∀ q S usS, TermPiece.Piece cl.ty q S → accs S = some usS →
        q ≤ m.loc.offset → m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn s ⟨l, o⟩ th0 → th0 ∉ s'.promises)
    (hRC : Tg → ∀ o th0 tw, ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ th0 → th0 ∉ s'.promises →
      TermPlant.LowOwn s' ⟨l, o⟩ tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw →
      (∃ q S usS, TermPiece.Piece cl.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
      ∃ y ∈ RS, y.1 = l ∧ TermPiece.CrCov y.2.2 o)
    (hPc : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l →
      ∃ q S usS, TermPiece.Piece cl.ty q S ∧ accs S = some usS ∧ q ≤ m.loc.offset ∧
        m.loc.offset < q + nWords usS)
    (hUK : ∀ a : Address, (∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ a) →
      s'.vs.coh a ≤ s.vs.coh a ∧ (PredU E a ↔ PredU E' a)) :
    ∃ Gs', TermOverCr.OverCrL E' s' crB l cl (TermOverCr.WinG E' s' l) Gs' ∧ TermOverCr.HolderLow s' l Gs' := by
  classical
  obtain ⟨hnd, hit, -⟩ := id hL
  -- an item whose holder survives is away from the discharged promises (`FulP`)
  have hnfS : ∀ x ∈ Gs, x.1 ∈ s'.promises → NFi s s' l x := by
    intro x hx hx1 usS hus t m ht hn hm hl h1 h2
    obtain ⟨mh, usS', hmh, hloc, hlo, hus', hP, g1, g2, -, hnw⟩ := item_piece hsto0 (hit x hx)
    obtain rfl := Option.some.inj (hus.symm.trans hus')
    have hwm : ¬ WordUnit E m.loc := by rw [addr_eq hl rfl]; exact hnw _ h1 h2
    exact (hFP t m ht hn hm hl hwm).2 _ _ _ hP hus h1 h2 _ _ g1 g2 hlo hx1
  -- and conversely
  have hnfH1 : ∀ x ∈ Gs, NFi s s' l x → x.1 ∈ s'.promises := by
    intro x hx hnf
    obtain ⟨mh, usS, hmh, hloc, hlo, hus, -, g1, g2, -, -⟩ := item_piece hsto0 (hit x hx)
    by_cases hn : x.1 ∈ s'.promises
    · exact hn
    · exact (hnf usS hus x.1 mh hlo.1 hn hmh (congrArg Address.label hloc) g1 g2).elim
  have hmemK : ∀ x, x ∈ Gs.filter (fun x => decide (NFi s s' l x)) ↔ x ∈ Gs ∧ NFi s s' l x :=
    fun x => by rw [List.mem_filter, decide_eq_true_iff]
  have hGk : (Gs.filter (fun x => decide (NFi s s' l x))).Sublist Gs := by apply List.filter_sublist
  refine overCr_ownopH hmem hsub (G' := TermOverCr.WinG E' s' l) (Gn := []) (RS := RS) (cr0 := cr0)
    hcpl hni hsto0 hpf hpi hsto hV ?_ hL hGk ?_ ?_ ?_
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil) hRS
    (fun t => by rw [hcrE t]; exact Res.le_refl _) ?_ ?_ ?_ ?_ ?_
  · -- hPU
    intro x hx usS i o hus _ hi hp
    obtain ⟨-, hnf⟩ := (hmemK x).1 hx
    have hio := hi.2
    have hle := TermOverCr.nWords_take_le usS (i + 1)
    refine (hUK ⟨l, x.2.1 + o⟩ (fun t m ht hn hm hml => ?_)).2.1 hp
    have el : m.loc.label = l := congrArg Address.label hml
    have eo : x.2.1 + o = m.loc.offset := (congrArg Address.offset hml).symm
    exact hnf usS hus t m ht hn hm el (by omega) (by show x.2.1 + nWords usS > m.loc.offset; omega)
  · -- hcrK
    intro x hx
    obtain ⟨hxG, hnf⟩ := (hmemK x).1 hx
    obtain ⟨mh, usS, hmh, hloc, -, -, -, g1, g2, -, hnw⟩ := item_piece hsto0 (hit x hxG)
    have hk := hKeep x.1 mh (hnfH1 x hxG hnf) hmh (congrArg Address.label hloc)
      (by rw [hloc]; exact hnw _ g1 g2)
    rw [hcrE]
    exact Res.le_trans hk (Res.le_add_right _ _)
  · -- hnfH
    intro x hx mh' hmh' t m ht hn hm heq
    obtain ⟨hxG, hnf⟩ := (hmemK x).1 hx
    obtain ⟨mh, usS, hmh, hloc, -, hus, -, g1, g2, -, -⟩ := item_piece hsto0 (hit x hxG)
    rw [hmh] at hmh'
    obtain rfl := Option.some.inj hmh'
    have el : m.loc.label = l := by rw [heq]; exact congrArg Address.label hloc
    exact hnf usS hus t m ht hn hm el (by rw [heq]; exact g1) (by rw [heq]; exact g2)
  · -- hnfK
    intro x hx usS i o hus _ hi t m ht hn hm hml
    obtain ⟨-, hnf⟩ := (hmemK x).1 hx
    have hio := hi.2
    have hle := TermOverCr.nWords_take_le usS (i + 1)
    have el : m.loc.label = l := congrArg Address.label hml
    have eo : x.2.1 + o = m.loc.offset := (congrArg Address.offset hml).symm
    exact hnf usS hus t m ht hn hm el (by omega) (by show x.2.1 + nWords usS > m.loc.offset; omega)
  · -- hnd0
    rw [List.append_nil]
    exact List.Nodup.sublist (hGk.map _) hnd
  · -- hR0
    intro x hx
    rw [List.append_nil] at hx
    obtain ⟨hxG, hnf⟩ := (hmemK x).1 hx
    obtain ⟨mh, usS, hmh, hloc, -, -, -, g1, g2, hR, hnw⟩ := item_piece hsto0 (hit x hxG)
    exact Res.le_trans hR (hKeep x.1 mh (hnfH1 x hxG hnf) hmh (congrArg Address.label hloc)
      (by rw [hloc]; exact hnw _ g1 g2))
  · -- hHL0
    rw [List.append_nil]
    exact TermOverCr.holderLow_sublist hGk (TermOverCr.holderLow_tr
      (fun t m _ _ hm => by rw [← hmem]; exact hm) (fun t ht hn => absurd (hsub t ht) hn) hHL)
  · -- hcovN0
    intro o tw _ _ hv hlo hg hov
    have hvE : ¬ VisU E ⟨l, o⟩ := fun h => hv ((VisU_congr (a := ⟨l, o⟩) hsto htid hpfe).2 h)
    have hwo : ¬ WordUnit E ⟨l, o⟩ := fun h => hvE ⟨h, fun hp => hpf hp.2⟩
    by_cases hY : ∃ t m, t ∈ s.promises ∧ t ∉ s'.promises ∧ s.mem[t]? = some m ∧ m.loc.label = l ∧
        ∃ q S usS, TermPiece.Piece cl.ty q S ∧ accs S = some usS ∧ q ≤ m.loc.offset ∧
          m.loc.offset < q + nWords usS ∧ q ≤ o ∧ o < q + nWords usS
    · -- a discharged promise in a piece holding `o`: re-pinned
      obtain ⟨t, m, ht, hn, hm, hl, q, S, usS, hP, hus, h1, h2, h3, h4⟩ := hY
      have hwm : ¬ WordUnit E m.loc := by
        rw [addr_eq hl rfl]
        exact TermPiece.nword_piece hsto0 hP hus h3 h4 hwo _ h1 h2
      obtain ⟨htg, hall⟩ := hFP t m ht hn hm hl hwm
      obtain ⟨htw, ⟨mw, hmw, hlw⟩, -⟩ := id hlo
      have el : mw.loc.label = l := congrArg Address.label hlw
      have eo : o = mw.loc.offset := (congrArg Address.offset hlw).symm
      obtain ⟨th0, m0, h0, hm0, hl0, g1, g2, -, hmin⟩ := TermOverCrW.lowest_in_piece (s := s) (lo := o)
        (hi := o + 1) (hsub tw htw) (by rw [← hmem]; exact hmw) el (by omega) (by show o + 1 > mw.loc.offset; omega)
      have hlo0 : TermPlant.LowOwn s ⟨l, o⟩ th0 := by
        refine ⟨h0, ⟨m0, hm0, addr_eq hl0 (show o = m0.loc.offset by
          have g2n : o + 1 > m0.loc.offset := g2
          omega).symm⟩, fun t' m' ht' hm' hl' => ?_⟩
        have el' : m'.loc.label = l := congrArg Address.label hl'
        have eo' : o = m'.loc.offset := (congrArg Address.offset hl').symm
        exact hmin t' m' ht' hm' el' (by omega) (by show o + 1 > m'.loc.offset; omega)
      exact .inr (.inr (hRC htg o th0 tw hvE hlo0 (hall q S usS hP hus h1 h2 o th0 h3 h4 hlo0) hlo hov hg
        ⟨q, S, usS, hP, hus, h3, h4⟩))
    · -- no discharged promise near `o`: the old cover's unit, kept
      have hnfo : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, o⟩ := by
        intro t m ht hn hm hml
        have el : m.loc.label = l := congrArg Address.label hml
        have eo : o = m.loc.offset := (congrArg Address.offset hml).symm
        obtain ⟨q, S, usS, hP, hus, h1, h2⟩ := hPc t m ht hm el
        have h2n : q + nWords usS > m.loc.offset := h2
        exact hY ⟨t, m, ht, hn, hm, el, q, S, usS, hP, hus, h1, h2, by omega, by omega⟩
      obtain ⟨hcoh, hpu⟩ := hUK ⟨l, o⟩ hnfo
      have hFa : ∀ o', FpAt E' ⟨l, o'⟩ = FpAt E ⟨l, o'⟩ := fun o' => FpAt_congr hsto htid hpfe hfpe
      refine .inl ⟨hnfo, hvE, ⟨fun t m hm hl ht => ?_, fun t m ht hm hl => ?_⟩, ?_, fun x hx hc => ?_⟩
      · rcases hg.1 t m (by rw [hmem]; exact hm) hl ht with h | h
        · exact .inl (hsub t h)
        · refine .inr ?_
          rw [hl] at h ⊢
          exact Nat.le_trans h hcoh
      · exact hg.2 t m (by rw [hFa]; exact ht) (by rw [hmem]; exact hm) hl
      · obtain ⟨t, m, hlt, hm, hl, hnot⟩ := hov
        refine ⟨t, m, hlt, by rw [← hmem]; exact hm, hl, fun hin => hnot ?_⟩
        have hm0 : s.mem[t]? = some m := by rw [← hmem]; exact hm
        have hkeep : t ∈ s.promises → t ∈ s'.promises := fun h1 => by
          by_cases h3 : t ∈ s'.promises
          · exact h3
          · exact absurd hl (hnfo t m h1 h3 hm0)
        have hv' : ¬ VisU E' ⟨l, o⟩ := hv
        unfold PromAt at hin ⊢
        by_cases hp : PredU E ⟨l, o⟩
        · have hp' : PredU E' ⟨l, o⟩ := hpu.1 hp
          simp only [hvE, hv', hp, hp', ite_false, ite_true, List.mem_filter, List.mem_append,
            decide_eq_true_eq, hmem, hFa] at hin ⊢
          obtain ⟨h1, h2⟩ := hin
          refine ⟨?_, h2⟩
          rcases h1 with h1 | h1
          · exact .inl (hkeep h1)
          · exact .inr h1
        · have hp' : ¬ PredU E' ⟨l, o⟩ := fun h => hp (hpu.2 h)
          simp only [hvE, hv', hp, hp', ite_false, List.mem_append, hFa] at hin ⊢
          rcases hin with h1 | h1
          · exact .inl (hkeep h1)
          · exact .inr h1
      · obtain ⟨usS, i, hus, h1, hi, -⟩ := hc
        refine (hmemK x).2 ⟨hx, fun usS' hus' t m ht hn hm hl g1 g2 => ?_⟩
        obtain rfl := Option.some.inj (hus.symm.trans hus')
        obtain ⟨-, -, -, -, -, -, hP, -, -, -, -⟩ := item_piece hsto0 (hit x hx)
        have hio := hi.2
        have hle := TermOverCr.nWords_take_le usS (i + 1)
        exact hY ⟨t, m, ht, hn, hm, hl, x.2.1, x.2.2.1, usS, hP, hus, g1, g2, h1, by omega⟩
  · -- hzN
    intro t m ht hm hl _ hnz
    by_cases hy : ∃ y ∈ RS, y.2.2.1 = t
    · obtain ⟨y, hy, hyt⟩ := hy
      obtain ⟨-, -, -, ⟨mh, -, hmh, hlab, -⟩, -⟩ := hRS y hy
      rw [hyt, hm] at hmh
      obtain rfl := Option.some.inj hmh
      exact .inr (.inr ⟨y, hy, hlab.symm.trans hl, hyt⟩)
    · have hy' : ∀ y ∈ RS, y.2.2.1 ≠ t := fun y h e => hy ⟨y, h, e⟩
      have hz : TermPiece.rpSum RS t = .zero := TermPiece.rpSum_none hy'
      refine .inl ⟨fun h0 => hnz ?_, fun x hx hxt => (hmemK x).2 ⟨hx, hnfS x hx (by rw [hxt]; exact ht)⟩⟩
      rw [hcrE t, hz, Res.add_zero]
      refine Res.ext fun k => ?_
      have h1 := Res.le_def.1 (hle0 t) k
      rw [h0, Res.zero_apply] at h1
      rw [Res.zero_apply]
      omega
#print axioms TermOverCrA3.cover_core

/-- **(M5) The own cover at the own-path op kinds**: the real count not rising over an untouched
predicted unit is `KeepQRSB`'s `RcKeepP` conjunct; the re-pin cover is its `RepinCovSB`
(no `bufInit`-at-`rc` exclusion). -/
theorem openOverCrOwnA_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} :
    OpenOverCrOwnA p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs pl X Y hK hPA hG hPT crS hQ Tot' H' C F cr' db' plh Gd E' hBi hKQ hIZ hOF
    hF hSO hRE hMI hMH hPC hMS hDr hineq hplp hplk hPfr Sj l cl hs ho hp
  -- the post-step cut is `E'` (Common leaf): move the goal there
  have hcut := TermOverCrOwnCommon.cutT_self X Y hF hRE
  rw [TermOverCrOwnCommon.cutT_sto hcut] at hs
  rw [TermOverCrOwnCommon.cutT_pfr hcut] at hp
  refine (TermOverCrOwnCommon.overCrE_cutT hcut Sj).2 ?_
  rw [X.e1, X.e2]
  -- the stepper's re-pin hand-off
  obtain ⟨cr0, RSc, RSh, hKq, hcr', hQU, -, hQh, -, hplh, -, -, hcovS, hFul, hRK, -⟩ := hKQ
  -- the old frontier at `l` is the new one: KindA terms are no `publish` (`PfrG` at `PubAt th`)
  have hold : (CE η).sto l = some cl ∧ (CE η).pfr l = E'.pfr l := by
    refine TermOverCrOwnCommon.old_of_newP X Y hF hPfr ?_ hs hp
    rintro ⟨y, a, e, rt, ws, ad, ht, -⟩
    have h1 := hK.1
    rw [ht] at h1
    simp [TermPiece.opAtomP] at h1
  have hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e := by
    intro x a e ht
    have h1 := hK.1
    rw [ht] at h1
    simp [TermPiece.opAtomP] at h1
  -- the pre-state's cover at `l`
  have hpre := TermOverCrOwnCommon.pre_overCrE (pl := pl) X Y hG hold.1 ho
    (by rw [hold.2]; exact hp)
  obtain ⟨S0, ρ0, η0, cx0, Rf0, Rs0, hCE0, -, -, -, -, -, -, -, hm0, -, hC0⟩ :=
    (X.inv.thr i th X.hth).env X.inv.clo
  have hsub : ∀ t, t ∈ (stOf r.1 r.2.1 r.2.2).promises → t ∈ (stOf c.mem c.pairs th).promises :=
    fun t ht => (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr).1.subset ht
  have hOw : TermPlant.OwnFrOp (CE η) cx th := hK.2
  -- the stepper's credits `crS`: `cr i` plus moved-back pool credits off the post promises
  obtain ⟨plq, hcS, hq01, hqP⟩ := hQ
  have hcSP : ∀ t, t ∈ (stOf r.1 r.2.1 r.2.2).promises → crS t = cr i t := by
    intro t ht
    rw [hcS t]
    rcases hq01 t with e | e
    · rw [e, Res.add_zero]
    · by_cases h0 : plq t = .zero
      · rw [h0, Res.add_zero]
      · exact absurd ht (hqP t h0)
  have hcSle : ∀ t, crS t ≤ cr i t + pl i t := by
    intro t
    rw [hcS t]
    rcases hq01 t with e | e
    · rw [e, Res.add_zero]; exact Res.le_add_right _ _
    · rw [e]; exact Res.le_refl _
  · -- own op on a frontier cell: memory unchanged
    have hmem : (stOf r.1 r.2.1 r.2.2).mem = (stOf c.mem c.pairs th).mem := hOF hOw
    obtain ⟨Gs, hL, hHL⟩ := hpre
    have hRS : TermPiece.RepinQh E' (stOf r.1 r.2.1 r.2.2) (RSc ++ RSh) :=
      repinQh_append (repinQh_of_U hQU) hQh
    have hcpl : Ty.coupledOKIn [] cl.ty = true := by
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hp
      exact MemInv_cplT hMI hs hf
    have hsG : Eg.sto l = some cl := by
      have h1 := hold.1
      rw [Y.1] at h1
      exact cutSto_sub h1
    have hni : noIallV cl.ty = true := X.inv.stoNI l cl hsG
    have hpi := TermOverCr5D.hpi_of_promIni (S := S) X.inv.promIni X.hth
    rw [← Y.1] at hpi
    have hV : ∀ S1 ws R0, ValOfR (CE η) S1 ws R0 → ValOfR E' S1 ws R0 :=
      fun _ _ _ h => TermOverCrOwnCommon.valOfR_step X Y hF h
    have hsto : E'.sto l = (CE η).sto l := hs.trans hold.1.symm
    have hown : cl.owner = some (CE η).tid := by rw [ho, Y.1]; rfl
    have hgd : ∃ lab, TermPiece.OpTgtP th lab ∧ (CE η).pfr lab ≠ none := by
      obtain ⟨lab, h1, h2⟩ := hOw.2
      exact ⟨lab, h2, h1⟩
    -- the total credits: `cr0 + kept pool` plus both re-pin lists
    have hcrE : ∀ t, cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t =
        (cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero)) +
          TermPiece.rpSum (RSc ++ RSh) t := by
      intro t
      rw [rpSum_append, hcr' t]
      unfold plStep
      rw [hplh t]
      by_cases ht : t ∈ (stOf r.1 r.2.1 r.2.2).promises
      · simp only [ht, ite_true]
        refine Res.ext fun key => ?_
        simp only [Res.add_apply]; omega
      · simp only [ht, ite_false]
        refine Res.ext fun key => ?_
        simp only [Res.add_apply]; omega
    -- the kept credits lie below the old ones
    have hle0 : ∀ t, cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero) ≤
        cr i t + pl i t := by
      intro t
      have h1 := (hKq hnp).2 t
      by_cases ht : t ∈ (stOf r.1 r.2.1 r.2.2).promises
      · simp only [ht, ite_true]
        rw [hcSP t ht] at h1
        exact Res.add_le_add h1 (Res.le_refl _)
      · simp only [ht, ite_false]
        rw [Res.add_zero]
        exact Res.le_trans h1 (hcSle t)
    -- a surviving promise at a non-word unit of `l` keeps its credit (`KeepPl`, `PromCrK`)
    have hKeep : ∀ t m, t ∈ (stOf r.1 r.2.1 r.2.2).promises → (stOf c.mem c.pairs th).mem[t]? = some m →
        m.loc.label = l → ¬ WordUnit (CE η) m.loc →
        cr i t + pl i t ≤ cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero) := by
      intro t m ht hm hl hw
      simp only [ht, ite_true]
      refine Res.add_le_add ?_ (Res.le_refl _)
      obtain ⟨m', hm', -, hc⟩ := hC0.1 t (hsub t ht)
      rw [hm] at hm'
      obtain rfl := Option.some.inj hm'
      have hw0 : ¬ WordUnit (CE η0) m.loc := by
        rw [hCE0]
        rw [Y.1] at hw
        exact hw
      rcases hc with hc | ⟨hc, hk⟩
      · rw [TermPlant.oldCr_nwordZ hw0 hc]
        exact Res.zero_le _
      · have hpc : PlantCr (CE η) (stOf c.mem c.pairs th) m t (cr i t) := by
          rw [Y.1]
          rw [hCE0] at hc
          exact hc
        have hl' : E'.sto m.loc.label = (CE η).sto m.loc.label := by rw [hl]; exact hsto
        have hpl' : E'.pfr m.loc.label = (CE η).pfr m.loc.label := by rw [hl]; exact hold.2.symm
        have hpc' : PlantCr E' (stOf r.1 r.2.1 r.2.2) m t (cr i t) :=
          TermPlant.PlantCr_frameK (fun t _ => by rw [hmem]) (by rw [hmem]; exact Nat.le_refl _) hsub
            (MemInv_promLt hm0) hl' hF.2.1 (fun h => by rw [hpl']; exact h)
            (fun h => (WordUnit_congr hl').1 h)
            (fun t _ h => by
              rw [FpAt_congr (a := ⟨m.loc.label, 0⟩) hl' hF.2.1 hpl' hF.2.2.2.2.2.2.2.2.1] at h
              exact h)
            hV hpc
        rw [← hcSP t ht] at hpc' hk
        have e := (hKq hnp).1 t ht (.inr ⟨m, by rw [hmem]; exact hm, hpc', hk⟩)
        rw [e, hcSP t ht]
        exact Res.le_refl _
    -- `FulP`: a discharged promise at `l` discharges its whole pieces
    have hFP : ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises →
        (stOf c.mem c.pairs th).mem[t]? = some m → m.loc.label = l → ¬ WordUnit (CE η) m.loc →
        TermPiece.OpTgtP th l ∧ ∀ q S usS, TermPiece.Piece cl.ty q S → accs S = some usS → q ≤ m.loc.offset →
          m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
            TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ th0 → th0 ∉ (stOf r.1 r.2.1 r.2.2).promises := by
      intro t m ht hn hm hl hw
      have h := hFul hmem hK.1 hgd t m cl ht hn hm (by rw [hl]; exact hold.1) hown
        (by rw [hl, hold.2]; exact hp) hw
      rw [hl] at h
      exact h
    -- the re-pin cover (`KeepQRSB`'s `RepinCovSB`)
    have hRC : TermPiece.OpTgtP th l → ∀ o th0 tw, ¬ VisU (CE η) ⟨l, o⟩ →
        TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ th0 → th0 ∉ (stOf r.1 r.2.1 r.2.2).promises →
        TermPlant.LowOwn (stOf r.1 r.2.1 r.2.2) ⟨l, o⟩ tw → TermPlant.OverT E' (stOf r.1 r.2.1 r.2.2) ⟨l, o⟩ tw →
        TermOverCr.WinG E' (stOf r.1 r.2.1 r.2.2) l o tw →
        (∃ q S usS, TermPiece.Piece cl.ty q S ∧ accs S = some usS ∧ q ≤ o ∧ o < q + nWords usS) →
        ∃ y ∈ RSc ++ RSh, y.1 = l ∧ TermPiece.CrCov y.2.2 o :=
      fun htg o th0 tw h4 h5 h6 h7 h8 h9 h10 =>
        repinCov_full hcovS l htg cl o th0 tw hold.1 hown
          (by rw [hold.2]; exact hp) h4 h5 h6 h7 h8 h9 h10
    -- every own promise at `l` lies in a piece (`PromTyAOK`)
    have hPc : ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → (stOf c.mem c.pairs th).mem[t]? = some m →
        m.loc.label = l → ∃ q S usS, TermPiece.Piece cl.ty q S ∧ accs S = some usS ∧ q ≤ m.loc.offset ∧
          m.loc.offset < q + nWords usS := by
      intro t m ht hm hl
      have hpg : Eg.pfr l ≠ none := by
        have h := hold.2
        rw [Y.1] at h
        rw [← h] at hp
        exact hp
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpg
      have hw := X.inv.promTy i th t m X.hth ht hm cl (by rw [hl]; exact hsG) (by rw [hl]; exact ⟨f, hf⟩)
      exact piece_of_wordOKA (X.inv.clo l cl hsG) (X.inv.cmg l cl hsG) hw
    -- the untouched units: coherence from the op's shape (`tstep_LS`), prediction from the
    -- footprint and `KeepQRS`'s `RcKeepP`
    have hRc := hRK hmem hK.1 hgd
    have hfrE : ∀ l, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l → (CE η).sto l = none ∧
        (CE η).pfr l = none := by
      intro l hFr
      have hg := X.inv.gfresh X.hth r.2.2.nalloc l hFr
      refine ⟨?_, by rw [Y.1]; exact hg.2.2⟩
      rw [Y.1]
      show cutSto Eg i l = none
      unfold cutSto
      split
      · exact hg.1
      · rfl
    have hnPub : ∀ l, ¬ TermOwnG0Defs.PubAt th l := by
      rintro l ⟨y, a, e, rt, ws, ad, ht, -⟩
      have h1 := hK.1
      rw [ht] at h1
      simp [TermPiece.opAtomP] at h1
    obtain ⟨s1, hLS, e1, e3, e4⟩ := TermUnitKeepC.tstep_LS hK.1 X.hr
    have hUK : ∀ a : Address, (∀ t m, t ∈ (stOf c.mem c.pairs th).promises →
        t ∉ (stOf r.1 r.2.1 r.2.2).promises → (stOf c.mem c.pairs th).mem[t]? = some m → m.loc ≠ a) →
        (stOf r.1 r.2.1 r.2.2).vs.coh a ≤ (stOf c.mem c.pairs th).vs.coh a ∧ (PredU (CE η) a ↔ PredU E' a) := by
      intro a ha
      refine ⟨?_, predU_iff hF hfrE (fun l hs hne => hnPub l (hPfr l hs hne))
        (fun l c f hz hnF hc hf => (hIZ l c f hz hnF hc hf).1) (hRc a ha)⟩
      have hm1 : s1.mem = (stOf c.mem c.pairs th).mem := by rw [← e1]; exact hmem
      have h := TermUnitKeepC.LS_cohKeep hLS (MemInv_nodup hm0) hm1 a (fun t m ht hn hm => by
        rw [← e4] at hn
        exact ha t m ht hn hm)
      show r.2.2.vs.coh a ≤ th.vs.coh a
      rw [e3]
      exact Nat.le_of_eq h
    exact cover_core (crA := fun t => cr i t + pl i t)
      (cr0 := fun t => cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero))
      (crB := fun t => cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t)
      hmem hsub hcpl hni hold.1 (by rw [hold.2]; exact hp) hpi hsto hold.2.symm hF.2.1 hF.2.2.2.2.2.2.2.2.1
      hV hL hHL hRS hcrE hle0 hKeep hFP hRC hPc hUK
#print axioms TermOverCrA3.openOverCrOwnA_of

end TermOverCrA3
