import WeakCore.TermPoolStaging
import WeakCore.TermOverCrOwnCommon
import WeakCore.TermOverCrX
import WeakCore.TermOwnCTop
import WeakCore.TermNewCoh
import WeakCore.TermTyped

/-! # TermPoolTagOwn: the stepper's own pool after its step is tagged

`poolTagOwnT_of : TermPoolStaging.poolTagOwnT …` (no premise; the member carries the whole-piece
discharge premise WPD of the amended staging).

* a new item (`plh t ≠ 0`): a `RepinQh` item of `KeepQRS`'s pool list `RSh` held by `t`, off the
  label's frontier messages (`¬ HolderFp`), lowest in its piece;
* a kept item (`plh t = 0`, `t` still outstanding): the pre-state's `PoolTag` item, moved along the
  step; its pins survive since the lowest own promise at a pinned unit is never discharged while
  its holder survives (WPD at the holder's unit).
* the own pool cover (`PoolCovUL` v3 at `i`): the pre-state's list filtered to surviving holders
  (`crItemQ_frameP`, `hPU_core`); a post demand is a pre demand (WPD; a new message is below `coh`,
  `tctx_newCoh`, `PromAbove`); a newly fronted cell demands nothing (premise `hNF`).
-/

namespace TermPoolTagOwn
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermPoolStaging
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem addr_eq {a : Address} {l : AllocLabel} {o : Nat} (h1 : a.label = l) (h2 : a.offset = o) :
    a = ⟨l, o⟩ := by
  subst h1
  subst h2
  rfl
#print axioms TermPoolTagOwn.addr_eq

theorem rpSum_eq (RS : List (AllocLabel × Cell × TermPiece.CrIt)) (t : Ts) :
    TermPiece.rpSum RS t = TermOverCrX.rpSumI RS t := rfl

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
#print axioms TermPoolTagOwn.le_rpSum

theorem crKeys_add {a b : Res} (ha : TermPlant.CrKeys a) (hb : TermPlant.CrKeys b) : TermPlant.CrKeys (a + b) :=
  fun l => by simp only [Res.add_apply, ha l, hb l]
#print axioms TermPoolTagOwn.crKeys_add

theorem nWords_take_le (us : List Acc) (n : Nat) : nWords (us.take n) ≤ nWords us := by
  have e := TermSound.nWords_append (us.take n) (us.drop n)
  rw [List.take_append_drop] at e
  omega
#print axioms TermPoolTagOwn.nWords_take_le

theorem inAcc_lt {us : List Acc} {i o : Nat} (h : InAcc us i o) : o < nWords us :=
  Nat.lt_of_lt_of_le h.2 (nWords_take_le us (i + 1))
#print axioms TermPoolTagOwn.inAcc_lt

/-- A nonzero pool credit at `t` has an item of the list held by `t`. -/
theorem rpSum_ne {RS : List (AllocLabel × Cell × TermPiece.CrIt)} {t : Ts} (h : TermPiece.rpSum RS t ≠ .zero) :
    ∃ y ∈ RS, y.2.2.1 = t := by
  refine Classical.byContradiction fun hno => h ?_
  unfold TermPiece.rpSum
  rw [List.filter_eq_nil_iff.2 (fun y hy => by
    simp only [decide_eq_true_eq]
    exact fun e => hno ⟨y, hy, e⟩)]
  rfl
#print axioms TermPoolTagOwn.rpSum_ne

/-- An item's segment meeting its holder's offset is a piece. -/
theorem piece_of_crIt {T S : Ty} {q off : Nat} {usS : List Acc} (a5 : AtOff T q S) (a6 : Solid S)
    (a7 : accs S = some usS) (a8 : q ≤ off) (a9 : off < q + nWords usS) : TermPiece.Piece T q S :=
  ⟨a5, a6, by
    rw [TermMem.wc_of_accs a7]
    intro e
    rw [Option.some.inj e, Nat.add_zero] at a9
    exact absurd a8 (Nat.not_le_of_lt a9)⟩
#print axioms TermPoolTagOwn.piece_of_crIt

theorem poolTagOwnT_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} : poolTagOwnT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F crS cr' db' δ plh X Y Z _hQ hG hPT hKQ hWP hNF
  obtain ⟨hF, hRE, hMI, -⟩ := Z
  have hcut := TermOverCrOwnCommon.cutT_self X Y hF hRE
  have htid : E'.tid = i := TermOverCrOwnCommon.cutT_tid hcut
  obtain ⟨cr0, RSc, RSh, -, -, -, -, hQh, hHh, hplh, hplm, hplk, -⟩ := hKQ
  obtain ⟨S0, ρ0, η0, cx0, Rf0, Rs0, hCE0, -, -, -, -, -, -, -, hm0, -, -⟩ :=
    (X.inv.thr i th X.hth).env X.inv.clo
  have hful := TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr
  have hsub : r.2.2.promises.Sublist th.promises := hful.1
  have hplt : ∀ t', t' ∈ th.promises → t' < c.mem.size := fun t' h => X.inv.plt i th t' X.hth h
  have hext := (TermLiveProps.tstep_ext _ _ _ _ r X.hr).mem
  have hpre : ∀ t', t' < c.mem.size → r.1[t']? = c.mem[t']? := hext.get
  have hext' : ∀ (t' : Ts) (m' : Msg), c.mem[t']? = some m' → r.1[t']? = some m' := fun t' m' h => by
    rw [hpre t' (TermMem.lt_of_get h)]; exact h
  -- the credit family and the post-step state
  have hplS : ∀ u, plStep pl i (stOf r.1 r.2.1 r.2.2) plh u =
      (if u ∈ r.2.2.promises then pl i u else .zero) + plh u := fun u => rfl
  refine ⟨fun t ht => ?_, ?_⟩
  · ---------------- the tags
    have hkeys : TermPlant.CrKeys (plStep pl i (stOf r.1 r.2.1 r.2.2) plh t) := by
      rw [hplS t]
      refine crKeys_add ?_ (hplk t)
      by_cases h1 : t ∈ r.2.2.promises
      · simp only [h1, ite_true]
        by_cases h2 : pl i t = .zero
        · rw [h2]; exact fun _ => rfl
        · exact (hPT.1 i th t X.hth h2).2.1
      · simp only [h1, ite_false]; exact fun _ => rfl
    unfold PTag
    rw [X.e1, X.e2]
    by_cases hN : plh t = .zero
    · ---------------- a kept item
      have h0 : (if t ∈ r.2.2.promises then pl i t else .zero) ≠ .zero := by
        intro e; apply ht; rw [hplS t, e, hN]; rfl
      have htP : t ∈ r.2.2.promises := by
        by_cases h1 : t ∈ r.2.2.promises
        · exact h1
        · simp only [h1, ite_false] at h0; exact absurd rfl h0
      have hpl0 : pl i t ≠ .zero := by simp only [htP, ite_true] at h0; exact h0
      have hle : pl i t ≤ plStep pl i (stOf r.1 r.2.1 r.2.2) plh t := by
        rw [hplS t]; simp only [htP, ite_true]; exact Res.le_add_right _ _
      obtain ⟨htth, -, m, hm, hFp, hIt⟩ := hPT.1 i th t X.hth hpl0
      obtain ⟨cl, x, hsto0, ho0, hx1, hIt0, hPL⟩ := hIt S
      rw [← Y.1] at hsto0 hIt0
      have hown : cl.owner = some (CE η).tid := by rw [ho0, Y.1]; rfl
      have hpf0 : (CE η).pfr m.loc.label ≠ none := by
        rcases hFp with hFp | hFp
        · obtain ⟨fq, mf, hfq, -, -, -⟩ := hFp S
          rw [← Y.1] at hfq
          have hvis : Vis (CE η) m.loc.label := by
            by_cases hv : Vis (CE η) m.loc.label
            · exact hv
            · simp [FpAt, hv] at hfq
          exact fun hn => hvis ⟨⟨cl, hsto0, hown⟩, hn⟩
        · have h1 := (hFp S).1
          rw [← Y.1] at h1
          exact h1
      obtain ⟨-, -, hstoF, -, -, hpfrF, -⟩ := id hF
      have hfr := X.inv.gfresh X.hth r.2.2.nalloc
      have hstoE : E'.sto m.loc.label = (CE η).sto m.loc.label := by
        rcases hstoF m.loc.label with e | ⟨hFr, -⟩
        · exact e
        · have hg := (hfr m.loc.label hFr).1
          have hc := hsto0
          rw [Y.1] at hc
          have := cutSto_sub hc
          rw [hg] at this; cases this
      have hpfE : E'.pfr m.loc.label = (CE η).pfr m.loc.label := by
        rcases hpfrF m.loc.label with e | ⟨e, -⟩ | ⟨-, e, -⟩
        · exact e
        · exact absurd e hpf0
        · exact absurd e hpf0
      -- an item of `pl i` at holder `t` on `cl` is one of `plStep` after the step
      have hTr : ∀ x : Ts × Nat × Ty × List Word × Res × (Nat → Bool), x.1 = t →
          TermPiece.CrItem (CE η) (stOf c.mem c.pairs th) (pl i) m.loc.label cl x →
          TermPiece.CrItem E' (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) m.loc.label cl x := by
        intro x hx1 hIt0
        obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hIt0
        have hmh : mh.loc = ⟨m.loc.label, mh.loc.offset⟩ := addr_eq a2 rfl
        have hP : TermPiece.Piece cl.ty x.2.1 x.2.2.1 := piece_of_crIt a5 a6 a7 a8 a9
        have hnwP := TermPiece.nword_piece hsto0 hP a7 a8 a9 (by rw [← hmh]; exact a4)
        have hxP : x.1 ∈ r.2.2.promises := by rw [hx1]; exact htP
        refine ⟨mh, usS, hext' _ _ a1, a2,
          ⟨hxP, ⟨mh, hext' _ _ a1, rfl⟩, fun t' m' h1 h2 h3 =>
            a3.2.2 t' m' (hsub.subset h1) ((hpre t' (hplt t' (hsub.subset h1))).symm.trans h2) h3⟩,
          fun h => a4 ((WordUnit_congr (by rw [a2]; exact hstoE)).1 h), a5, a6, a7, a8, a9, a10,
          TermOverCrOwnCommon.valOfR_step X Y hF a11, ?_, ?_⟩
        · rw [hx1] at a12 ⊢
          exact Res.le_trans a12 hle
        · intro j o w tw' hK hI hw hlo
          have hu : x.2.1 + o < x.2.1 + nWords usS := by
            have := inAcc_lt hI
            omega
          have htw : tw' ∈ th.promises := hsub.subset hlo.1
          have hlo0 : TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨m.loc.label, x.2.1 + o⟩ tw' := by
            obtain ⟨m1, hm1, hl1⟩ := hlo.2.1
            refine ⟨htw, ⟨m1, (hpre tw' (hplt tw' htw)).symm.trans hm1, hl1⟩, fun t0 m0 h0 hm0 hl0 => ?_⟩
            refine Nat.le_of_not_lt fun hlt => ?_
            by_cases h0' : t0 ∈ r.2.2.promises
            · exact absurd (hlo.2.2 t0 m0 h0' (hext' _ _ hm0) hl0) (Nat.not_le_of_lt hlt)
            · have hl0l : m0.loc.label = m.loc.label := by rw [hl0]
              have hl0o : m0.loc.offset = x.2.1 + o := by rw [hl0]
              have hw0 : ¬ WordUnit (CE η) m0.loc := by
                rw [hl0]
                exact hnwP _ (Nat.le_add_right _ _) hu
              have hgone := hWP t0 m0 cl h0 h0' hm0 (by rw [hl0l]; exact hsto0) ho0
                (by rw [hl0l]; exact hpf0) hw0 x.2.1 x.2.2.1 usS hP a7 (by rw [hl0o]; exact Nat.le_add_right _ _)
                (by rw [hl0o]; exact hu) mh.loc.offset x.1 a8 a9 (by rw [hl0l, ← hmh]; exact a3)
              exact hgone hxP
          exact (PredAt_prefix (n := c.mem.size) hpre (Nat.le_of_lt (hplt tw' htw))).1
            (a13 j o w tw' hK hI hw hlo0)
      refine ⟨htP, hkeys, m, hext' t m hm, ?_, fun S1 => ?_⟩
      · rcases hFp with hFp | hFp
        · refine Or.inl fun S1 => ?_
          obtain ⟨fq, mf, hfq, hmf, hlf, hft⟩ := hFp S
          rw [← Y.1] at hfq
          have hB : ∃ f mf, f ∈ FpAt E' ⟨m.loc.label, 0⟩ ∧ r.1[f]? = some mf ∧ mf.loc.label = m.loc.label ∧
              f ≤ t := by
            refine ⟨fq, mf, ?_, hext' fq mf hmf, hlf, hft⟩
            rw [FpAt_congr (a := ⟨m.loc.label, 0⟩) hstoE hF.2.1 hpfE hF.2.2.2.2.2.2.2.2.1]
            exact hfq
          have hB' : ∃ f mf, f ∈ FpAt (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen)
              ⟨m.loc.label, 0⟩ ∧ r.1[f]? = some mf ∧ mf.loc.label = m.loc.label ∧ f ≤ t := by
            rw [hcut]; exact hB
          exact hB'
        · refine Or.inr fun S1 => ?_
          obtain ⟨-, cl1, x1, hsto1, ho1, hxt, hK1, hIt1⟩ := hFp S
          rw [← Y.1] at hsto1 hIt1
          rw [hsto0] at hsto1
          cases hsto1
          have hB : E'.pfr m.loc.label ≠ none ∧ ∃ cl x, E'.sto m.loc.label = some cl ∧ cl.owner = some i ∧
              x.1 = t ∧ (∀ i, x.2.2.2.2.2 i = false) ∧
              TermPiece.CrItem E' (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) m.loc.label cl x :=
            ⟨by rw [hpfE]; exact hpf0, cl, x1, by rw [hstoE]; exact hsto0, ho0, hxt, hK1, hTr x1 hxt hIt1⟩
          have hB' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).pfr m.loc.label ≠ none ∧
              ∃ cl x, (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).sto m.loc.label =
                some cl ∧ cl.owner = some i ∧ x.1 = t ∧ (∀ i, x.2.2.2.2.2 i = false) ∧
              TermPiece.CrItem (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen)
                (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) m.loc.label cl x := by
            rw [hcut]; exact hB
          exact hB'
      · have hB : ∃ cl x, E'.sto m.loc.label = some cl ∧ cl.owner = some i ∧ x.1 = t ∧
            TermPiece.CrItem E' (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) m.loc.label cl x ∧
            PieceLow r.1 r.2.2.promises m.loc.label x.2.1 x.2.2.1 t :=
          ⟨cl, x, by rw [hstoE]; exact hsto0, ho0, hx1, hTr x hx1 hIt0,
            TermPool.pieceLow_own hpre hplt hsub (hplt t htth) hPL⟩
        have hB' : ∃ cl x, (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).sto m.loc.label =
              some cl ∧ cl.owner = some i ∧ x.1 = t ∧
            TermPiece.CrItem (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen)
              (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) m.loc.label cl x ∧
            PieceLow r.1 r.2.2.promises m.loc.label x.2.1 x.2.2.1 t := by
          rw [hcut]; exact hB
        exact hB'
    · ---------------- a new item
      have hplh0 : TermPiece.rpSum RSh t ≠ .zero := by rw [← hplh t]; exact hN
      obtain ⟨y, hy, hyt⟩ := rpSum_ne hplh0
      have htP : t ∈ r.2.2.promises := hplm t hN
      obtain ⟨hys, hyo, -, ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13⟩, -, hlow, -⟩ := hQh y hy
      have hle : y.2.2.2.2.2.2.1 ≤ plStep pl i (stOf r.1 r.2.1 r.2.2) plh t := by
        rw [hplS t, hplh t, ← hyt]
        exact Res.le_trans (le_rpSum RSh y hy) (TermOverCrW.le_add_leftR _ _)
      have hfp : ∃ fq mf, fq ∈ FpAt E' ⟨y.1, 0⟩ ∧ r.1[fq]? = some mf ∧ mf.loc.label = y.1 ∧ fq ≤ y.2.2.1 := by
        refine Classical.byContradiction fun hno => hHh y hy fun fq mf h1 h2 h3 => ?_
        exact Nat.lt_of_not_le fun h4 => hno ⟨fq, mf, h1, h2, h3, h4⟩
      subst hyt
      refine ⟨htP, hkeys, mh, a1, Or.inl fun S1 => ?_, fun S1 => ?_⟩
      · rw [a2]
        have hB' : ∃ f mf, f ∈ FpAt (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen)
            ⟨y.1, 0⟩ ∧ r.1[f]? = some mf ∧ mf.loc.label = y.1 ∧ f ≤ y.2.2.1 := by
          rw [hcut]; exact hfp
        exact hB'
      · rw [a2]
        have hB : ∃ cl x, E'.sto y.1 = some cl ∧ cl.owner = some i ∧ x.1 = y.2.2.1 ∧
            TermPiece.CrItem E' (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) y.1 cl x ∧
            PieceLow r.1 r.2.2.promises y.1 x.2.1 x.2.2.1 y.2.2.1 :=
          ⟨y.2.1, y.2.2, hys, by rw [hyo, htid], rfl,
            ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hle, a13⟩, hlow⟩
        have hB' : ∃ cl x, (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).sto y.1 =
              some cl ∧ cl.owner = some i ∧ x.1 = y.2.2.1 ∧
            TermPiece.CrItem (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen)
              (stOf r.1 r.2.1 r.2.2) (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) y.1 cl x ∧
            PieceLow r.1 r.2.2.promises y.1 x.2.1 x.2.2.1 y.2.2.1 := by
          rw [hcut]; exact hB
        exact hB'
  · ---------------- the own pool cover (PoolCovUL v3 at `i`)
    intro Sj l cl hs ho hp hnpub
    have hs1 : E'.sto l = some cl := by rw [← TermOverCrOwnCommon.cutT_sto hcut Sj]; exact hs
    have hp1 : E'.pfr l ≠ none := hp
    have hnpub0 : ¬ Eg.pubd l := fun h => hnpub (Or.inl h)
    obtain ⟨hold, hpo⟩ := TermOverCrOwnCommon.old_of_new X Y hF hs1 hp1
    by_cases hnone : (CE η).pfr l = none
    · -- a newly fronted cell: nothing is demanded
      refine ⟨[], fun _ => Res.zero_le _, fun _ hx => absurd hx List.not_mem_nil, ?_⟩
      intro o tw _ hnv hlo _ hov
      exact absurd hov (hNF Sj l o tw hnone hp1 (by rw [hs1]; exact Option.some_ne_none _) hnv hlo)
    have hpe : (CE η).pfr l = E'.pfr l := hpo.resolve_right hnone
    have hsG : Eg.sto l = some cl := by
      have h1 := hold
      rw [Y.1] at h1
      exact cutSto_sub h1
    have hpgE : Eg.pfr l ≠ none := by
      have h1 := hnone
      rw [Y.1] at h1
      exact h1
    obtain ⟨Gs0, hsum0, hit0, hcov0⟩ := hPT.2 i th S X.hth l cl (by rw [← Y.1]; exact hold) ho hpgE hnpub0
    rw [← Y.1] at hit0 hcov0
    have hCutE : Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj = { E' with seen := Sj } :=
      calc _ = { Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen with seen := Sj } := rfl
        _ = _ := by rw [hcut]
    rw [hCutE, X.e1, X.e2]
    -- the step's facts at `l`
    have hPA : PromAbove (stOf r.1 r.2.1 r.2.2) := by
      have h1 := TermTyped.certified_promAboveSt X.cert X.e3
      rw [X.e1, X.e2] at h1
      exact h1
    have hstoL : E'.sto l = (CE η).sto l := hs1.trans hold.symm
    have hV : ∀ S1 ws R0, ValOfR (CE η) S1 ws R0 → ValOfR E' S1 ws R0 :=
      fun _ _ _ h => TermOverCrOwnCommon.valOfR_step X Y hF h
    have hown' : cl.owner = some E'.tid := by rw [htid]; exact ho
    have hvis' : Vis E' l := fun h => hp1 h.2
    have hvis0 : Vis (CE η) l := fun h => hnone h.2
    have hPc : ∀ t m, t ∈ th.promises → c.mem[t]? = some m → m.loc.label = l →
        ∃ q S1 us, TermPiece.Piece cl.ty q S1 ∧ accs S1 = some us ∧ q ≤ m.loc.offset ∧
          m.loc.offset < q + nWords us := by
      intro t m ht hm hl
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpgE
      exact TermOwnCTop.piece_of_wordOKA (X.inv.clo l cl hsG) (X.inv.cmg l cl hsG)
        (X.inv.promTy i th t m X.hth ht hm cl (by rw [hl]; exact hsG) (by rw [hl]; exact ⟨f, hf⟩))
    have hPU := TermOwnCPU.hPU_core (E := CE η) hs1 hown' hMI.2.1 hstoL hpe.symm (hF.2.2.2.2.1 l).1 hPA
      (fun o tw' hlo => by
        obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hlo
        have htw0 := hsub.subset htw
        obtain ⟨q, S1, us, hP1, hus, h1, h2⟩ :=
          hPc tw' m htw0 ((hpre tw' (hplt tw' htw0)).symm.trans hm) (by rw [hml])
        rw [hml] at h1 h2
        exact ⟨q, S1, us, hP1.1, hus, h1, h2⟩)
      (fun o tw' hlo q' htwo => by
        obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hlo
        have htw0 := hsub.subset htw
        have h := X.inv.promNoTwo i th tw' m cl X.hth htw0 ((hpre tw' (hplt tw' htw0)).symm.trans hm)
          (by rw [hml]; exact hsG) q' htwo
        rw [hml] at h
        exact h)
    -- a fulfilled own promise of `l` discharges the lowest own promises of its pieces (WPD)
    have hgone : ∀ t m, t ∈ th.promises → t ∉ r.2.2.promises → c.mem[t]? = some m → m.loc.label = l →
        ¬ WordUnit (CE η) m.loc → ∀ q S1 usS, TermPiece.Piece cl.ty q S1 → accs S1 = some usS →
        q ≤ m.loc.offset → m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
        TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ th0 → th0 ∉ r.2.2.promises := by
      intro t m h1 h2 h3 h4 h5 q S1 usS hP hus b1 b2 o th0 b3 b4 hlo
      subst h4
      exact hWP t m cl h1 h2 h3 hold ho hnone h5 q S1 usS hP hus b1 b2 o th0 b3 b4 hlo
    -- a pool item of the pre list: its piece, and its holder's discharge
    have hitem : ∀ x ∈ Gs0, ∃ usS, accs x.2.2.1 = some usS ∧ TermPiece.Piece cl.ty x.2.1 x.2.2.1 ∧
        (x.1 ∉ r.2.2.promises → ∀ o th0, x.2.1 ≤ o → o < x.2.1 + nWords usS →
          TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ th0 → th0 ∉ r.2.2.promises) ∧
        (∀ t m, t ∈ th.promises → c.mem[t]? = some m → m.loc.label = l → x.2.1 ≤ m.loc.offset →
          m.loc.offset < x.2.1 + nWords usS → t ∉ r.2.2.promises → x.1 ∉ r.2.2.promises) := by
      intro x hx
      obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hit0 x hx
      have hP : TermPiece.Piece cl.ty x.2.1 x.2.2.1 := piece_of_crIt a5 a6 a7 a8 a9
      have hmh : mh.loc = ⟨l, mh.loc.offset⟩ := addr_eq a2 rfl
      refine ⟨usS, a7, hP, fun hn o th0 b1 b2 hlo => hgone x.1 mh a3.1 hn a1 a2 a4 x.2.1 x.2.2.1 usS hP a7
        a8 a9 o th0 b1 b2 hlo, fun t m ht hm hl b1 b2 hn => ?_⟩
      have hnw : ¬ WordUnit (CE η) m.loc := by
        rw [addr_eq hl rfl]
        exact TermPiece.nword_piece hold hP a7 a8 a9 (by rw [← hmh]; exact a4) _ b1 b2
      exact hgone t m ht hn hm hl hnw x.2.1 x.2.2.1 usS hP a7 b1 b2 mh.loc.offset x.1 a8 a9
        (by rw [← hmh]; exact a3)
    refine ⟨Gs0.filter (fun x => decide (x.1 ∈ r.2.2.promises)), fun t => ?_, fun x hx => ?_, ?_⟩
    · -- the per-holder sum bound
      by_cases htP : t ∈ r.2.2.promises
      · have e : (Gs0.filter (fun x => decide (x.1 ∈ r.2.2.promises))).filter (fun x => decide (x.1 = t)) =
            Gs0.filter (fun x => decide (x.1 = t)) := by
          rw [List.filter_filter]
          refine List.filter_congr fun x _ => ?_
          by_cases h : x.1 = t
          · simp [h, htP]
          · simp [h]
        rw [e]
        refine Res.le_trans (hsum0 t) ?_
        rw [hplS t]; simp only [htP, ite_true]; exact Res.le_add_right _ _
      · have e : (Gs0.filter (fun x => decide (x.1 ∈ r.2.2.promises))).filter (fun x => decide (x.1 = t)) = [] :=
          List.filter_eq_nil_iff.2 fun x hx => by
            simp only [decide_eq_true_eq]
            intro e
            simp only [List.mem_filter, decide_eq_true_eq] at hx
            exact htP (e ▸ hx.2)
        rw [e]
        exact Res.zero_le _
    · -- a kept item moves along the step
      simp only [List.mem_filter, decide_eq_true_eq] at hx
      obtain ⟨usS, hus, -, -, hkd⟩ := hitem x hx.1
      have hcr : pl i x.1 ≤ plStep pl i (stOf r.1 r.2.1 r.2.2) plh x.1 := by
        rw [hplS x.1]; simp only [hx.2, ite_true]; exact Res.le_add_right _ _
      refine TermOwnCR5.crItemQ_frameP (s := stOf c.mem c.pairs th) (s' := stOf r.1 r.2.1 r.2.2) hpre hplt
        (fun t h => hsub.subset h) (fun usS' hus' t m ht hm hl b1 b2 => ?_) hstoL hV hPU hcr (hit0 x hx.1)
      rw [hus] at hus'
      cases hus'
      exact Classical.byContradiction fun hn => hkd t m ht hm hl b1 b2 hn hx.2
    · -- the cover: a post demand is a pre demand, and its item's holder survives
      intro o tw hpu hnv hlo hfw hov
      have hpu' : PredU E' ⟨l, o⟩ := hpu
      have hnv' : ¬ VisU E' ⟨l, o⟩ := hnv
      have hov' : TermPlant.OverT E' (stOf r.1 r.2.1 r.2.2) ⟨l, o⟩ tw := hov
      obtain ⟨htwP, ⟨mw0, hmw0, hlw0⟩, hmin⟩ := hlo
      have htw0 : tw ∈ th.promises := hsub.subset htwP
      have htws : tw < c.mem.size := hplt tw htw0
      have hnw0 : ¬ WordUnit (CE η) ⟨l, o⟩ := fun h =>
        hnv' ⟨(WordUnit_congr (a := ⟨l, o⟩) hstoL).2 h, hvis'⟩
      have hnv0 : ¬ VisU (CE η) ⟨l, o⟩ := fun h => hnw0 h.1
      have hfw0 : FirstW c.mem ⟨l, o⟩ tw := by
        obtain ⟨⟨m1, hm1, hl1, hv1⟩, hb⟩ := hfw
        refine ⟨⟨m1, (hpre tw htws).symm.trans hm1, hl1, hv1⟩, fun t1 m2 hlt hm2 hl2 => ?_⟩
        exact hb t1 m2 hlt (hext' t1 m2 hm2) hl2
      have hlo0 : TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ tw := by
        refine ⟨htw0, ⟨mw0, (hpre tw htws).symm.trans hmw0, hlw0⟩, fun t1 m1 ht1 hm1 hl1 => ?_⟩
        by_cases ht1' : t1 ∈ r.2.2.promises
        · exact hmin t1 m1 ht1' (hext' t1 m1 hm1) hl1
        · refine Nat.le_of_not_lt fun hlt => ?_
          exact X.inv.promNU i th t1 m1 X.hth ht1 hm1 (hfw.2 t1 m1 hlt (hext' t1 m1 hm1) hl1)
      have hpu0 : PredU (CE η) ⟨l, o⟩ := by
        obtain ⟨-, hiw, hnr⟩ := hpu'
        obtain ⟨hini, hini2⟩ := hF.2.2.2.2.1 l
        have hri := hF.2.2.2.2.2.2.2.2.2.1 l
        refine ⟨hnone, fun c1 N e us h1 h2 h3 => ?_, fun hw => hnr fun c1 N e us h1 h2 h3 => ?_⟩
        · have h4 := hiw c1 N e us (by rw [hstoL]; exact h1) h2 h3
          rcases hini2 with e1 | hFr | ⟨-, hmax, -⟩
          · rw [e1] at h4; exact h4
          · have hg := (X.inv.gfresh X.hth r.2.2.nalloc l hFr).1
            rw [hg] at hsG; cases hsG
          · refine Classical.byContradiction fun hn => hnr fun c2 N2 e2 us2 g1 g2 g3 => ?_
            rw [hstoL, h1] at g1
            cases g1
            rw [h2] at g2
            cases g2
            rw [h3] at g3
            cases g3
            show o < min (E'.ini l) (E'.rini l) * nWords us
            have hle : E'.ini l ≤ E'.rini l := by
              rcases Nat.le_total ((CE η).ini l) (E'.rini l) with h5 | h5
              · rw [Nat.max_eq_right h5] at hmax; exact hmax
              · rw [Nat.max_eq_left h5] at hmax
                exact absurd (Nat.lt_of_lt_of_le h4 (Nat.mul_le_mul_right _ hmax)) hn
            rw [Nat.min_eq_left hle]
            exact h4
        · have h4 := hw c1 N e us (by rw [← hstoL]; exact h1) h2 h3
          exact Nat.lt_of_lt_of_le h4 (Nat.mul_le_mul_right _ (show (CE η).rc l ≤ E'.rc l from
            Nat.le_min.2 ⟨Nat.le_trans (Nat.min_le_left _ _) hini, Nat.le_trans (Nat.min_le_right _ _) hri⟩))
      have hov0 : TermPlant.OverT (CE η) (stOf c.mem c.pairs th) ⟨l, o⟩ tw := by
        obtain ⟨t, m, hlt, hm, hml, hnP⟩ := hov'
        by_cases hts : t < c.mem.size
        · refine ⟨t, m, hlt, (hpre t hts).symm.trans hm, hml, fun hin => hnP ?_⟩
          simp only [PromAt, hnv0, hpu0, ite_false, ite_true, List.mem_filter, decide_eq_true_eq,
            List.mem_append] at hin
          simp only [PromAt, hnv', hpu', ite_false, ite_true, List.mem_filter, decide_eq_true_eq,
            List.mem_append]
          obtain ⟨hin1, ⟨h0, hf0, hh0⟩⟩ := hin
          refine ⟨?_, ⟨h0, TermOwnCF.firstW_fwd (s := stOf c.mem c.pairs th) (s' := stOf r.1 r.2.1 r.2.2)
            hpre (Nat.lt_trans hh0 hts) hf0, hh0⟩⟩
          rcases hin1 with hin1 | hin1
          · by_cases ht' : t ∈ r.2.2.promises
            · exact Or.inl ht'
            · have hm0 : c.mem[t]? = some m := (hpre t hts).symm.trans hm
              have hml1 : m.loc.label = l := by rw [hml]
              obtain ⟨q, S1, us, hP1, hus, b1, b2⟩ := hPc t m hin1 hm0 hml1
              have hmo : m.loc.offset = o := by rw [hml]
              exact absurd htwP (hgone t m hin1 ht' hm0 hml1 (by rw [hml]; exact hnw0) q S1 us hP1 hus b1 b2 o tw
                (by rw [← hmo]; exact b1) (by rw [← hmo]; exact b2) hlo0)
          · right
            simp only [FpAt, hvis0, hvis', ite_true] at hin1 ⊢
            rw [hF.2.2.2.2.2.2.2.2.1]
            exact hin1
        · exact absurd (Nat.lt_of_le_of_lt (TermNewCoh.tctx_newCoh X Y t m cl (Nat.le_of_not_lt hts) hm
            (by rw [hml]; exact hold)) (by rw [hml, ← hlw0]; exact hPA tw htwP mw0 hmw0)) (Nat.not_lt_of_lt hlt)
      obtain ⟨x, hx, usS, ii, h1, h2, h3, h4⟩ := hcov0 o tw hpu0 hnv0 hlo0 hfw0 hov0
      obtain ⟨usS', hus', -, hxd, -⟩ := hitem x hx
      rw [hus'] at h1
      cases h1
      have hxP : x.1 ∈ r.2.2.promises := Classical.byContradiction fun hn =>
        hxd hn o tw h2 (by have := inAcc_lt h3; omega) hlo0 htwP
      refine ⟨x, ?_, usS, ii, hus', h2, h3, h4⟩
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hx, hxP⟩
#print axioms TermPoolTagOwn.poolTagOwnT_of

end TermPoolTagOwn
