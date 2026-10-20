import WeakCore.TermOwnCT
import WeakCore.TermOverCrProm
import WeakCore.TermOwnPub
import WeakCore.TermPoolDefs
import WeakCore.TermMsgWords

/-! # TermOwnCPub: the owner's cover at a newly published cell (ownC case (ii))

At a thread step of `i` whose witness gives a cell `l` of `i` a frontier it did not have
(`(CE η).pfr l = none`, `E'.pfr l ≠ none`), the step is a `publish` naming `l` (`PfrG`), which keeps
memory, promises and coherence.  Before the step `l` was private, so every own promise at `l`
lies in a coherence tail of own promises (`OwnOKPF`); hence nothing is overtaken
(`TermOwnCT.overCr_tail`) and the cover is one item per credited non-word promise: a plant credit
of `cr'` (`PromCrK`, empty mask), or a pool re-pin item of `KeepQRS` (`RepinQh`).  The old pool
credits at `l` are zero (`PoolTag` needs a frontier).
-/

namespace TermOwnCPub
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermPool TermOverCrBII
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A `publish` step keeps memory, promises, coherence and the allocation count. -/
theorem tstep_publish_keep {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {y : String} {a : At}
    {e : Expr} {r : Memory × List Ts × TTh} (hterm : th.term = .let_ y (.publish a) e)
    (hr : r ∈ tstep g mem pairs th) :
    r.2.2.promises = th.promises ∧ r.1 = mem ∧ r.2.2.vs.coh = th.vs.coh ∧ r.2.2.nalloc = th.nalloc := by
  simp only [tstep, hterm, evalOp, List.mem_map] at hr
  obtain ⟨⟨s', t', ws⟩, hs, rfl⟩ := hr
  cases hev : evalAt th.env a with
  | none => simp [hev, ol] at hs
  | some q =>
    obtain ⟨t0, ws0⟩ := q
    simp only [hev, ol, bind, Option.bind, pure] at hs
    split at hs
    all_goals first
      | (simp at hs; done)
      | (cases hs with
         | head => exact ⟨rfl, rfl, rfl, rfl⟩
         | tail _ h => cases h)

#print axioms tstep_publish_keep

/-- A nonzero sum has a nonzero summand. -/
theorem res_add_ne {a b : Res} (h : a + b ≠ .zero) : a ≠ .zero ∨ b ≠ .zero := by
  by_cases ha : a = .zero
  · exact .inr fun hb => h (by rw [ha, hb, Res.add_zero])
  · exact .inl ha

/-- A nonzero re-pin credit has an item held there. -/
theorem rpSum_ne {RS : List (AllocLabel × Cell × TermPiece.CrIt)} {t : Ts} (h : TermPiece.rpSum RS t ≠ .zero) :
    ∃ y ∈ RS, y.2.2.1 = t ∧ y.2.2.2.2.2.2.1 ≤ TermPiece.rpSum RS t := by
  classical
  by_cases hy : ∃ y ∈ RS, y.2.2.1 = t
  · obtain ⟨y, hyR, hyt⟩ := hy
    refine ⟨y, hyR, hyt, ?_⟩
    unfold TermPiece.rpSum
    have hmem : y ∈ RS.filter (fun y => decide (y.2.2.1 = t)) := List.mem_filter.2 ⟨hyR, decide_eq_true hyt⟩
    exact TermPiece.res_mem_le_sumR (f := fun y => y.2.2.2.2.2.2.1) hmem
  · apply absurd _ h
    unfold TermPiece.rpSum
    have : RS.filter (fun y => decide (y.2.2.1 = t)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hyR
      simp only [decide_eq_true_eq]
      exact fun e => hy ⟨y, hyR, e⟩
    rw [this]; rfl

#print axioms rpSum_ne

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The stepper's witness is its new cut (`TermInterf.tctx_cut` from `EFoot` and `ThInvRE`). -/
theorem cut_wit {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hEF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hTR : ThInvRE p E' r.2.2 Tot') :
    Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen = E' := by
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact hEF
  have hself := Cut_self (g := gOf p k arch c i) hF0 (X.inv.gfresh X.hth _)
  have hEE : CE E' = E' := by
    obtain ⟨_, η', _, _, _, hce', -⟩ := hTR
    rw [← hce']
    rfl
  have hfs : fpSync Eg c' i = Eg.fpOf i := fpSync_self X.inv.proms X.inv.fpfree X.hth X.ho
  exact (Cut_withFp (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') (fpSync Eg c') _ E'.seen hfs).trans
    (hself.symm.trans hEE)

#print axioms cut_wit

/-- **(ownC (ii)) The owner's cover at a cell the step publishes.** -/
theorem ownC_pub {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} (pl : Nat → Ts → Res)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hPA : PromAbove (stOf r.1 r.2.1 r.2.2)) (hPT : PoolTag Eg c pl)
    {Tot' : Res} {cr' db' plh : Ts → Res} {E' : TEnv}
    {crS : Ts → Res} (hKQ : TermPlant.KeepQRS (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) th crS cr' plh)
    (hEF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hTR : ThInvRE p E' r.2.2 Tot') (hCK : TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db')
    (hPG : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hsto : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj).sto l = some cl)
    (hown : cl.owner = some i)
    (hpf : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    (hnone : (CE η).pfr l = none) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj)
      (stOf c'.mem c'.pairs r.2.2) (fun t => cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t) l cl := by
  classical
  have hE' := cut_wit X Y hEF hTR
  -- the step is a `publish` naming `l`
  have hsto0 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl := cutSto_sub hsto
  have hown0 : OwnAt (CE η) l := by
    rcases hEF.2.2.2.2.2.1 l with h | ⟨-, F, -, -, -, hO, -⟩ | ⟨hfr, -, hs⟩
    · exact absurd (h.trans hnone) hpf
    · exact hO
    · have e := post_sto_fresh (Eg := Eg) (E' := E')
        (show FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l from hfr)
      have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto l = some cl := hsto0
      rw [e, hs] at h2
      cases h2
  have hpub : TermOwnG0Defs.PubAt th l := by
    obtain ⟨c1, hc1, -⟩ := hown0
    exact hPG l (by rw [hc1]; exact fun h => by cases h) (fun h => hpf (h.trans hnone))
  obtain ⟨yv, av, ev, -, -, -, hterm, -⟩ := hpub
  obtain ⟨hP, hM, hC, hN⟩ := tstep_publish_keep hterm X.hr
  -- the pre-step cell
  have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := by
    rintro ⟨j, h1, h2, -⟩; rw [hN] at h2; omega
  have hEg : Eg.sto l = some cl := by rw [← TermOwnPub.EgT_sto_old (c' := c') (E' := E') hnf]; exact hsto0
  have hpf0 : Eg.pfr l = none := by
    have := hnone; rw [Y.1] at this; exact this
  -- the post-state is the pre-state
  have hs' : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [X.e1, X.e2]
  rw [hs']
  have hmem : (stOf r.1 r.2.1 r.2.2).mem = c.mem := hM
  have hprom : (stOf r.1 r.2.1 r.2.2).promises = th.promises := hP
  have hcoh : (stOf r.1 r.2.1 r.2.2).vs.coh = th.vs.coh := hC
  -- coherence tails at `l`
  have hT : ∀ t m, t ∈ (stOf r.1 r.2.1 r.2.2).promises → (stOf r.1 r.2.1 r.2.2).mem[t]? = some m →
      m.loc.label = l → TailP (stOf r.1 r.2.1 r.2.2) m.loc := by
    intro t m ht hm hl
    rw [hmem] at hm
    obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
    have hc0 : (Cut Eg i S0).sto l = some cl := cutSto_own hEg hown
    obtain ⟨vals, hcok, h4⟩ := OwnOKPF_cellP hm0.2.1 hc0 hown hpf0
    have hw := X.inv.msgWords t m cl hm (by rw [hl]; exact hEg)
    have hlt : m.loc.offset < vals.length := by
      rcases hcok with ⟨hwc, -⟩ | ⟨N, e, us, hTy, hus, -, hlen, -⟩
      · obtain ⟨L, hL, hn⟩ := wc_some hwc
        have := hw.1 L hL
        first | exact Nat.lt_of_lt_of_eq this hn | exact Nat.lt_of_lt_of_eq this hn.symm
      · have := hw.2 N e us hTy hus
        first | exact Nat.lt_of_lt_of_eq this hlen.symm | exact Nat.lt_of_lt_of_eq this hlen
    have hL := h4 m.loc.offset (vals[m.loc.offset]'hlt) (List.getElem?_eq_getElem hlt)
    intro t' m' h1 h2 h3
    rw [hcoh] at h1
    rw [hmem] at h2
    rw [hprom]
    have e : m.loc = ⟨l, m.loc.offset⟩ := by rw [← hl]
    rw [e] at h1 h3
    exact hL.2.2 t' m' h1 h2 h3
  -- no `undef` promise
  have hnu : ∀ t m, t ∈ (stOf r.1 r.2.1 r.2.2).promises → (stOf r.1 r.2.1 r.2.2).mem[t]? = some m →
      m.val ≠ .undef := by
    intro t m ht hm
    rw [hprom] at ht; rw [hmem] at hm
    exact X.inv.promNU i th t m X.hth ht hm
  -- the witness's cells are the new cut's
  generalize hEgd : EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c' = Eg' at hE' hsto hpf ⊢
  have hstoE : E'.sto = cutSto Eg' i := by rw [← hE']; rfl
  have hWU : ∀ a, ¬ WordUnit (Cut Eg' i Sj) a → ¬ WordUnit E' a := by
    intro a h hw; apply h
    obtain ⟨c1, hc1, hor⟩ := hw
    exact ⟨c1, by rw [hstoE] at hc1; exact hc1, hor⟩
  refine TermOwnCT.overCr_tail hT hPA hnu fun t m ht hm hl hnw hnz => ?_
  -- the old pool credit at `l` is zero
  have hpl0 : (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero) = .zero := by
    by_cases hin : t ∈ (stOf r.1 r.2.1 r.2.2).promises
    · simp only [hin, ↓reduceIte]
      by_cases hz : pl i t = .zero
      · exact hz
      · obtain ⟨-, -, m1, hm1, hfp, -⟩ := hPT.1 i th t X.hth hz
        rw [hmem] at hm
        rw [hm] at hm1; cases hm1
        rcases hfp with hfp | hfp
        · obtain ⟨fq, mf, hfq, -⟩ := hfp S
          rw [FpAt_priv (fun hv => hv ⟨⟨cl, by rw [hl]; exact cutSto_own hEg hown, hown⟩, by rw [hl]; exact hpf0⟩)] at hfq
          cases hfq
        · -- the mask-free branch sits at a frontier label; `l` has none
          exact absurd (by rw [hl]; exact hpf0) (hfp S).1
    · simp only [hin, ↓reduceIte]
  have hsum : plStep pl i (stOf r.1 r.2.1 r.2.2) plh t = plh t := by
    unfold plStep; rw [hpl0, Res.zero_add]
  rw [hsum] at hnz
  by_cases hcz : cr' t = .zero
  · -- a pool re-pin item
    have hph : plh t ≠ .zero := by
      rcases res_add_ne hnz with h | h
      · exact absurd hcz h
      · exact h
    obtain ⟨cr0, RSc, RSh, -, -, -, -, hQh, -, hplh, -, -, -, -, -, -⟩ := hKQ
    rw [hplh] at hph
    obtain ⟨y, hyR, hyt, hyle⟩ := rpSum_ne hph
    obtain ⟨hys, -, -, ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩, -, hHL, hCov⟩ :=
      hQh y hyR
    rw [hyt] at a1
    rw [hm] at a1; cases a1
    have hy1 : y.1 = l := a2.symm.trans hl
    rw [hy1, hstoE] at hys
    have hy2 : y.2.1 = cl := Option.some.inj (hys.symm.trans hsto)
    refine ⟨y.2.2, hyt, ⟨m, usS, by rw [hyt]; exact hm, hl, a3, ?_, by rw [← hy2]; exact a5,
      a6, a7, a8, a9, a10, ?_, ?_, fun i' o w tw' hK hio hw hlo => .inl ?_⟩, ?_, ?_⟩
    · exact hnw
    · rw [← hE'] at a11; exact a11
    · refine Res.le_trans hyle ?_
      rw [← hplh t, hyt]
      show plh t ≤ cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t
      rw [hsum]
      exact fun kk => by simp only [Res.add_apply]; omega
    · rw [hy1] at a12; exact a12 i' o w tw' hK hio hw hlo
    · intro usS' i' o hus hK hio
      obtain ⟨tw, hlo, -⟩ := hCov (y.2.2.2.1 + o) ⟨usS', i', hus, Nat.le_add_right _ _,
        by rw [Nat.add_sub_cancel_left]; exact hio, hK⟩
      rw [hy1] at hlo
      exact ⟨tw, hlo⟩
    · intro x hx usS' hus t' m' ht' hm' hl' h1 h2
      rw [List.mem_singleton.1 hx] at hus h1 h2 ⊢
      exact hHL usS' hus t' m' ht' hm' (by rw [hy1]; exact hl') h1 h2
  · -- a plant credit of `cr'`
    obtain ⟨m1, hm1, -, hor⟩ := hCK t ht
    rw [hm] at hm1; cases hm1
    rcases hor with hold | ⟨hPc, -⟩
    · exact absurd (TermPlant.oldCr_nwordZ (hWU _ hnw) hold) hcz
    · have hPc' : PlantCr (Cut Eg' i E'.seen) (stOf r.1 r.2.1 r.2.2) m t (cr' t) := by rw [hE']; exact hPc
      obtain ⟨c1, sb, S0, b0, Sx, us, wb, hsto1, -, -, hseg, hat, hSol, hnw1, hus, hn0, h1, h2, htw, -, -,
        hlow, hK1⟩ := TermOverCrProm.plantCr_cutS (S2 := Sj) hPc'
      rw [hl, hsto] at hsto1
      obtain rfl : cl = c1 := Option.some.inj hsto1
      rcases hK1 with ⟨K, ws, R0, hlen, hv, hR0, -⟩ | hz
      · have hlowP : ∀ t' m', t' ∈ (stOf r.1 r.2.1 r.2.2).promises → (stOf r.1 r.2.1 r.2.2).mem[t']? = some m' →
            m'.loc.label = l → sb + b0 ≤ m'.loc.offset → m'.loc.offset < sb + b0 + nWords us → t ≤ t' := by
          intro t' m' ht' hm' hl' h1' h2'
          by_cases hle : t' ≤ wb
          · exact hlow t' m' ht' hm' (hl'.trans hl.symm) h1' h2' hle
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt htw (Nat.lt_of_not_le hle))
        have hLO : TermPlant.LowOwn (stOf r.1 r.2.1 r.2.2) m.loc t := ⟨ht, ⟨m, hm, rfl⟩, fun t' m' ht' hm' hloc =>
          hlowP t' m' ht' hm' (by rw [hloc]; exact hl) (by rw [hloc]; exact h1) (by rw [hloc]; exact h2)⟩
        have hI := TermOverCr.item_of_plantCr (c := cl) (K := fun _ => false) (wb := wb)
          (cr := fun t => cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t) hm hseg hat hSol hnw1 hus
          hn0 h1 h2 hlen hv hR0 (fun i o w t' hK => absurd hK (by simp)) hLO (Res.le_add_right _ _)
          (fun i o tw' hK => absurd hK (by simp))
        rw [hl] at hI
        refine ⟨(t, sb + b0, Sx, ws, R0, fun _ => false), rfl, TermOverCr.crItemQ_of hI, ?_, ?_⟩
        · intro usS i o _ hK
          simp at hK
        · intro x hx usS hus' t' m' ht' hm' hl' h1' h2'
          rw [List.mem_singleton.1 hx] at hus' h1' h2' ⊢
          rw [hus] at hus'
          obtain rfl : us = usS := Option.some.inj hus'
          exact hlowP t' m' ht' hm' hl' h1' h2'
      · exact absurd hz hcz

#print axioms ownC_pub

end

end TermOwnCPub
