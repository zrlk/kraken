import WeakCore.TermOwnCPU
import WeakCore.TermOwnCPub
import WeakCore.TermOwnCWpd
import WeakCore.TermOverCrOwnCommon
import WeakCore.TermOverCr5D
import WeakCore.TermPieceCov
import WeakCore.TermReadClsDefs

/-! # TermOwnCTop: the own cover at the remaining kinds (ownC member)

`openOverCrOwnC_of : OpenOverCrOwnC …` from
* `hsc : StepScopeF` (TermMain: `TermScope.scope_of O.progScope O.runDRF0`), for WPD (`hFP_of_wpd`);
* `hNC : NewCohF` (the interface, `TermReadClsDefs`);
* `hCaseB : CaseBCov`, `hCaseC : CaseCCov` (open: the fulfil and read covers; `CaseCCov` from
  `ReadClsF`);

A newly published cell is `TermOwnCPub.ownC_pub`.  At an old frontier cell, `TermOwnCOldR.overCr_oldR`
with the re-pin items `RSc ++ RSh` (off `publish`; `RSh` at `publish`): the kept credits from
`KeepQ`/`KeepQRS`'s `PubKeep` conjunct and the pre-step `PromCrK`; `hPU` from `TermOwnCPU.hPU_core` (no `RcKeepC`);
`hFP` from WPD; `hcovN` from `TermOwnCGlue.hcovN_of`.
-/

namespace TermOwnCTop
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Copies of the `TermOverCrA3` helpers (which sits on the ext base) -/

theorem rpSum_append (L1 L2 : List (AllocLabel × Cell × TermPiece.CrIt)) (t : Ts) :
    TermPiece.rpSum (L1 ++ L2) t = TermPiece.rpSum L1 t + TermPiece.rpSum L2 t := by
  unfold TermPiece.rpSum
  rw [List.filter_append, List.map_append, Res.sum_append]

theorem repinQh_of_U {E' : TEnv} {s' : St} {cr' : Ts → Res} {RS : List (AllocLabel × Cell × TermPiece.CrIt)}
    (h : TermPiece.RepinQU E' s' cr' RS) : TermPiece.RepinQh E' s' RS := by
  intro y hy
  obtain ⟨a1, a2, a3, ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -, bp⟩, a5, a6, a7⟩ := h y hy
  exact ⟨a1, a2, a3, ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, bp⟩, a5, a6, a7⟩

theorem repinQh_append {E' : TEnv} {s' : St} {L1 L2 : List (AllocLabel × Cell × TermPiece.CrIt)}
    (h1 : TermPiece.RepinQh E' s' L1) (h2 : TermPiece.RepinQh E' s' L2) : TermPiece.RepinQh E' s' (L1 ++ L2) :=
  fun y hy => (List.mem_append.1 hy).elim (h1 y) (h2 y)

theorem clo_arrA {N : Idx} {e : Ty} (h : Clo (.array N e)) : Clo e := by
  have h1 := h.1
  simp only [tb] at h1
  refine ⟨h1, fun ρ W a b => ?_⟩
  have := h.2 ρ W a b
  simp only [cl, Ty.array.injEq] at this
  exact this.2

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

/-! ## Named open hypotheses (cases B and C of the post-demand trichotomy) -/

/-- (open) **Case B, the fulfil cover**: off `publish`, at an old own frontier cell `l`, a demanded
unit whose coherence the step raises to a pre-step own promise is covered by a zero item or by a
re-pin item of `KeepQRS`'s lists (`RepinCovS`). -/
def CaseBCov (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    KindC (CE η) cx th → PromAbove (stOf r.1 r.2.1 r.2.2) → (∀ x a e, th.term ≠ .let_ x (.publish a) e) →
    ∀ (E' : TEnv) (RSc RSh : List (AllocLabel × Cell × TermPiece.CrIt)),
      EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) →
      MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2) →
      TermPiece.RepinCovS (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) th RSc RSh →
      ∀ (l : AllocLabel) (cl : Cell), (CE η).sto l = some cl → cl.owner = some i → (CE η).pfr l ≠ none →
        E'.sto l = some cl → E'.pfr l = (CE η).pfr l →
        ∀ o tw, TermOwnCGlue.PostD E' (stOf r.1 r.2.1 r.2.2) l cl o tw →
          th.vs.coh ⟨l, o⟩ < r.2.2.vs.coh ⟨l, o⟩ → r.2.2.vs.coh ⟨l, o⟩ ∈ th.promises →
          TermOwnCGlue.AltCov E' (stOf r.1 r.2.1 r.2.2) l cl (RSc ++ RSh) o tw

/-- (open) **Case C, the read cover**: at an old own frontier cell `l`, a demanded unit whose
coherence the step raises to an old message that is no own promise (a read) carries a zero item. -/
def CaseCCov (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    PromAbove (stOf r.1 r.2.1 r.2.2) →
    ∀ (E' : TEnv),
      EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) →
      MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2) →
      ∀ (l : AllocLabel) (cl : Cell), (CE η).sto l = some cl → cl.owner = some i → (CE η).pfr l ≠ none →
        E'.sto l = some cl → E'.pfr l = (CE η).pfr l →
        ∀ o tw, TermOwnCGlue.PostD E' (stOf r.1 r.2.1 r.2.2) l cl o tw →
          th.vs.coh ⟨l, o⟩ < r.2.2.vs.coh ⟨l, o⟩ → r.2.2.vs.coh ⟨l, o⟩ < c.mem.size →
          r.2.2.vs.coh ⟨l, o⟩ ∉ th.promises → ∃ x, TermOwnCOld.ZeroIt E' (stOf r.1 r.2.1 r.2.2) l cl tw x

/-! ## The member -/

theorem openOverCrOwnC_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0)
    (hNC : TermReadClsDefs.NewCohF p k arch Sp Init MintOK c0)
    (hCaseB : CaseBCov p k arch Sp Init MintOK c0) (hCaseC : CaseCCov p k arch Sp Init MintOK c0) :
    OpenOverCrOwnC p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs pl X Y hK hPA hG hPT crS hQ Tot' H' C F cr' db' plh Gd E' hBi hKQ
    hIZ hOF hF hSO hRE hMI hMH hPC hMS hDr hineq hplp hplk hPfr Sj l cl hs ho hp
  replace hKQ := TermPlant.keepQRS_of_B hKQ
  -- (a‴) the stepper's credits `crS`: `cr i` at the post promises, at most `cr i + pl i` everywhere
  obtain ⟨plq, hq1, hq2, hq3⟩ := hQ
  have hSe : ∀ t, t ∈ r.2.2.promises → crS t = cr i t := fun t ht => by
    by_cases hz : plq t = .zero
    · rw [hq1 t, hz, Res.add_zero]
    · exact absurd ht (hq3 t hz)
  have hSle : ∀ t, crS t ≤ cr i t + pl i t := fun t => by
    rw [hq1 t]
    rcases hq2 t with h | h
    · rw [h]; exact Res.add_le_add (Res.le_refl _) (Res.zero_le _)
    · rw [h]; exact Res.le_refl _
  have hcut := TermOverCrOwnCommon.cutT_self X Y hF hRE
  have hs1 : E'.sto l = some cl := by rw [← TermOverCrOwnCommon.cutT_sto hcut Sj]; exact hs
  have hp1 : E'.pfr l ≠ none := by rw [← TermOverCrOwnCommon.cutT_pfr hcut]; exact hp
  obtain ⟨hold, hpo⟩ := TermOverCrOwnCommon.old_of_new X Y hF hs1 hp1
  by_cases hnone : (CE η).pfr l = none
  · exact TermOwnCPub.ownC_pub pl X Y hPA hPT hKQ hF hRE hPC hPfr hs ho hp hnone
  have hpe : (CE η).pfr l = E'.pfr l := hpo.resolve_right hnone
  refine (TermOverCrOwnCommon.overCrE_cutT hcut Sj).2 ?_
  rw [X.e1, X.e2]
  obtain ⟨cr0, RSc, RSh, hKq, hcr', hQU, -, hQh, -, hplh, -, -, hcovS, -, -, hPKt⟩ := hKQ
  have hpf0 : (CE η).pfr l ≠ none := by rw [hpe]; exact hp1
  have hpre0 := TermOverCrOwnCommon.pre_overCrE (pl := pl) X Y hG hold ho hpf0
  obtain ⟨S0, ρ0, η0, cx0, Rf0, Rs0, hCE0, htid0, hE0, hT0, htv0, hFI0, hsum0, -, hm0, -, hC0⟩ :=
    (X.inv.thr i th X.hth).env X.inv.clo
  have Y0 : EnvAt p Eg i th (Tot i) S0 ρ0 η0 cx0 Rf0 Rs0 := ⟨hCE0, htid0, hE0, hT0, htv0, hFI0, hsum0⟩
  have hsto00 : ∀ l, (CE η0).sto l = (CE η).sto l := fun l => by rw [hCE0, Y.1]; rfl
  have hpfr00 : ∀ l, (CE η0).pfr l = (CE η).pfr l := fun l => by rw [hCE0, Y.1]; rfl
  -- the step's state facts
  have hP : ∀ t, t ∈ (stOf c.mem c.pairs th).promises → t < (stOf c.mem c.pairs th).mem.size :=
    fun t ht => X.inv.plt i th t X.hth ht
  have hsub : ∀ t, t ∈ (stOf r.1 r.2.1 r.2.2).promises → t ∈ (stOf c.mem c.pairs th).promises :=
    fun t ht => (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr).1.subset ht
  have hgrow := TermFul.tstep_grow X.hr
  have hpre : ∀ t, t < (stOf c.mem c.pairs th).mem.size →
      (stOf r.1 r.2.1 r.2.2).mem[t]? = (stOf c.mem c.pairs th).mem[t]? := by
    intro t ht
    have h : c.mem[t]? = some c.mem[t] := Array.getElem?_eq_getElem ht
    show r.1[t]? = c.mem[t]?
    rw [h]
    exact hgrow.1 t _ h
  have hsz : (stOf c.mem c.pairs th).mem.size ≤ (stOf r.1 r.2.1 r.2.2).mem.size := TermFul.memExt_size hgrow.1
  -- the cell
  have hsG : Eg.sto l = some cl := by
    have h1 := hold
    rw [Y.1] at h1
    exact cutSto_sub h1
  have hcpl : Ty.coupledOKIn [] cl.ty = true := by
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hp1
    exact MemInv_cplT hMI hs1 hf
  have hni : noIallV cl.ty = true := X.inv.stoNI l cl hsG
  have hV : ∀ S1 ws R0, ValOfR (CE η) S1 ws R0 → ValOfR E' S1 ws R0 :=
    fun _ _ _ h => TermOverCrOwnCommon.valOfR_step X Y hF h
  have hstoL : E'.sto l = (CE η).sto l := hs1.trans hold.symm
  have hown' : cl.owner = some E'.tid := by rw [TermOverCrOwnCommon.cutT_tid hcut]; exact ho
  have hpi := TermOverCr5D.hpi_of_promIni (S := S) X.inv.promIni X.hth
  rw [← Y.1] at hpi
  have hpgE : Eg.pfr l ≠ none := by
    have h := hpf0
    rw [Y.1] at h
    exact h
  -- every own promise at `l` lies in a piece (`PromTyAOK`)
  have hPc : ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → (stOf c.mem c.pairs th).mem[t]? = some m →
      m.loc.label = l → ∃ q S us, TermPiece.Piece cl.ty q S ∧ accs S = some us ∧ q ≤ m.loc.offset ∧
        m.loc.offset < q + nWords us := by
    intro t m ht hm hl
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpgE
    have hw := X.inv.promTy i th t m X.hth ht hm cl (by rw [hl]; exact hsG) (by rw [hl]; exact ⟨f, hf⟩)
    exact piece_of_wordOKA (X.inv.clo l cl hsG) (X.inv.cmg l cl hsG) hw
  -- `hPU` (no `RcKeepC`)
  have hPU := TermOwnCPU.hPU_core (E := CE η) hs1 hown' hMI.2.1 hstoL hpe.symm (hF.2.2.2.2.1 l).1 hPA
    (fun o tw' hlo => by
      obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hlo
      have htw0 := hsub tw' htw
      have hm0' : (stOf c.mem c.pairs th).mem[tw']? = some m := by rw [← hpre tw' (hP tw' htw0)]; exact hm
      obtain ⟨q, S1, us, hP1, hus, h1, h2⟩ := hPc tw' m htw0 hm0' (by rw [hml])
      rw [hml] at h1 h2
      exact ⟨q, S1, us, hP1.1, hus, h1, h2⟩)
    (fun o tw' hlo q' htwo => by
      obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hlo
      have htw0 := hsub tw' htw
      have hm0' : c.mem[tw']? = some m := by
        have h := hpre tw' (hP tw' htw0)
        rw [hm] at h
        exact h.symm
      have h := X.inv.promNoTwo i th tw' m cl X.hth htw0 hm0' (by rw [hml]; exact hsG) q' htwo
      rw [hml] at h
      exact h)
  -- `hFP` (WPD, at the invariant's own cut)
  have hFP0 := TermOwnCWpd.hFP_of_wpd hsc X Y0 hm0 hPA (l := l) (cl := cl) (by rw [hsto00]; exact hold) ho
    (by rw [hpfr00]; exact hpf0)
  have hFP : ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises →
      (stOf c.mem c.pairs th).mem[t]? = some m → m.loc.label = l → ¬ WordUnit (CE η) m.loc →
      ∀ q S usS, TermPiece.Piece cl.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ th0 → th0 ∉ (stOf r.1 r.2.1 r.2.2).promises :=
    fun t m ht hn hm hl hw => hFP0 t m ht hn hm hl (fun h => hw ((WordUnit_congr (hsto00 m.loc.label)).1 h))
  -- the pre-step credit forms at the cut
  have hCF : ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → (stOf c.mem c.pairs th).mem[t]? = some m →
      OldCr (CE η) (stOf c.mem c.pairs th) m t (cr i t) ∨
        (PlantCr (CE η) (stOf c.mem c.pairs th) m t (cr i t) ∧ TermPlant.CrKeys (cr i t)) := by
    intro t m ht hm
    obtain ⟨m', hm', -, hc⟩ := hC0.1 t ht
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    rw [hCE0] at hc
    rw [Y.1]
    exact hc
  -- the post-demand trichotomy, up to the fulfil and read covers
  have hSame : ∀ o tw, TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ tw →
      (stOf r.1 r.2.1 r.2.2).vs.coh ⟨l, o⟩ ≤ (stOf c.mem c.pairs th).vs.coh ⟨l, o⟩ →
      (PredU E' ⟨l, o⟩ → PredU (CE η) ⟨l, o⟩) ∧
        (TermOverCr.CovU E' cl l o → TermOverCr.CovU (CE η) cl l o) := by
    intro o tw hlo _
    obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hlo
    have hI := hpi tw m htw hm cl (by rw [hml]; exact hold) (by rw [hml]; exact hpf0)
    rw [hml] at hI
    have hIW : IniW (CE η) ⟨l, o⟩ := by
      intro c1 N e us h1 h2 h3
      have h1' : (CE η).sto l = some c1 := h1
      rw [hold] at h1'
      cases h1'
      exact hI N e us h2 h3
    have hrc : (CE η).rc l ≤ E'.rc l := by
      have h1 := (hF.2.2.2.2.1 l).1
      have h2 := hF.2.2.2.2.2.2.2.2.2.1 l
      unfold TEnv.rc
      omega
    refine ⟨fun h => ⟨hpf0, hIW, fun hw => h.2.2 fun c1 N e us h1 h2 h3 => ?_⟩, fun h => ?_⟩
    · have h1' : E'.sto l = some c1 := h1
      rw [hstoL] at h1'
      have h4 := hw c1 N e us h1' h2 h3
      exact Nat.lt_of_lt_of_le h4 (Nat.mul_le_mul_right _ hrc)
    · by_cases hIr : InitRr (CE η) cl l o
      · exact .inl hIr
      · exact .inr ⟨hpf0, hIW, fun hw => hIr fun N e us h1 h2 => hw cl N e us hold h1 h2⟩
  have hFC := TermTyped.tstep_fulC (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr
  have hNCl : ∀ t m, (stOf c.mem c.pairs th).mem.size ≤ t → (stOf r.1 r.2.1 r.2.2).mem[t]? = some m →
      m.loc.label = l → t ≤ (stOf r.1 r.2.1 r.2.2).vs.coh m.loc :=
    fun t m h1 h2 h3 => hNC X Y t m cl h1 h2 (by rw [h3]; exact hold)
  have hcovN := fun (RS : List (AllocLabel × Cell × TermPiece.CrIt)) hB hC =>
    TermOwnCGlue.hcovN_of (RS := RS) (c := cl) hpre hP hsub hFC (X.inv.promAbove i th X.hth) hPA hNCl hstoL hF.2.1
      hpe.symm hF.2.2.2.2.2.2.2.2.1 hSame hB hC
  -- total credits
  have hcrS : ∀ t, cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t =
      (cr' t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero)) + TermPiece.rpSum RSh t := by
    intro t
    unfold plStep
    rw [hplh t]
    refine Res.ext fun key => ?_
    simp only [Res.add_apply]
    omega
  by_cases hpub : ∃ x a e, th.term = .let_ x (.publish a) e
  · -- `publish`: memory, promises and coherence kept; the old credits kept (`PubKeep`)
    obtain ⟨yv, av, ev, hterm⟩ := hpub
    obtain ⟨hPr, -, hCo, -⟩ := TermOwnCPub.tstep_publish_keep hterm X.hr
    have hkeep : ∀ t m, t ∈ (stOf r.1 r.2.1 r.2.2).promises → (stOf c.mem c.pairs th).mem[t]? = some m →
        m.loc.label = l → cr' t = cr i t :=
      fun t m ht hm hl => (hPKt ⟨yv, av, ev, hterm⟩ t m ht hm (by rw [hl]; exact hpf0)
        (by rw [hSe t ht]; exact hCF t m (hsub t ht) hm)).trans (hSe t ht)
    have hcoh : (stOf r.1 r.2.1 r.2.2).vs.coh = (stOf c.mem c.pairs th).vs.coh := hCo
    refine TermOwnCOldR.overCr_oldR (RS := RSh) (cr := fun t => cr i t + pl i t) hpre hP hsub hold hcpl hni
      hstoL hV hPU hFP hQh ?_ ?_ ?_ ?_ hpre0
    · intro t m ht hm hl _
      show cr i t + pl i t + TermPiece.rpSum RSh t ≤ cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t
      rw [hcrS t, hkeep t m ht hm hl]
      simp only [ht, ↓reduceIte]
      exact Res.le_refl _
    · intro t
      show TermPiece.rpSum RSh t ≤ cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t
      rw [hcrS t]
      exact TermOverCrW.le_add_leftR _ _
    · intro t m ht hm hl _ hnz
      have hnz' : (cr' t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero)) +
          TermPiece.rpSum RSh t ≠ .zero := by rw [← hcrS t]; exact hnz
      rcases TermOwnCPub.res_add_ne hnz' with h1 | h1
      · left
        rw [hkeep t m ht hm hl] at h1
        simp only [ht, ↓reduceIte] at h1
        exact h1
      · right
        obtain ⟨y, hy, hyt, -⟩ := TermOwnCPub.rpSum_ne h1
        obtain ⟨-, -, -, ⟨mh, -, hmh, hlab, -⟩, -⟩ := hQh y hy
        rw [hyt] at hmh
        have hm' : (stOf r.1 r.2.1 r.2.2).mem[t]? = some m := by rw [hpre t (hP t (hsub t ht))]; exact hm
        rw [hm'] at hmh
        obtain rfl := Option.some.inj hmh
        exact ⟨y, hy, hlab.symm.trans hl, hyt⟩
    · refine hcovN RSh (fun o tw _ hgt _ => ?_) (fun o tw _ hgt _ _ => ?_)
      · rw [hcoh] at hgt; exact absurd hgt (Nat.lt_irrefl _)
      · rw [hcoh] at hgt; exact absurd hgt (Nat.lt_irrefl _)
  · -- off `publish`: `KeepQ`
    have hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e := fun x a e h => hpub ⟨x, a, e, h⟩
    have hRS : TermPiece.RepinQh E' (stOf r.1 r.2.1 r.2.2) (RSc ++ RSh) :=
      repinQh_append (repinQh_of_U hQU) hQh
    have hcrE : ∀ t, cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t =
        (cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero)) +
          TermPiece.rpSum (RSc ++ RSh) t := by
      intro t
      rw [rpSum_append, hcr' t]
      unfold plStep
      rw [hplh t]
      refine Res.ext fun key => ?_
      simp only [Res.add_apply]
      omega
    have hle0 : ∀ t, cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero) ≤
        cr i t + pl i t := by
      intro t
      have h1 := (hKq hnp).2 t
      by_cases ht : t ∈ (stOf r.1 r.2.1 r.2.2).promises
      · simp only [ht, ↓reduceIte]
        rw [hSe t ht] at h1
        exact Res.add_le_add h1 (Res.le_refl _)
      · simp only [ht, ↓reduceIte]
        refine Res.le_def.2 fun key => ?_
        have h2 := Res.le_def.1 (Res.le_trans h1 (hSle t)) key
        simp only [Res.add_apply, Res.zero_apply] at h2 ⊢; omega
    have hKeep : ∀ t m, t ∈ (stOf r.1 r.2.1 r.2.2).promises → (stOf c.mem c.pairs th).mem[t]? = some m →
        m.loc.label = l → ¬ WordUnit (CE η) m.loc →
        cr i t + pl i t ≤ cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero) := by
      intro t m ht hm hl hw
      simp only [ht, ↓reduceIte]
      refine Res.add_le_add ?_ (Res.le_refl _)
      rcases hCF t m (hsub t ht) hm with hc | ⟨hc, hk⟩
      · rw [TermPlant.oldCr_nwordZ hw hc]
        exact Res.zero_le _
      · have hl' : E'.sto m.loc.label = (CE η).sto m.loc.label := by rw [hl]; exact hstoL
        have hpl' : E'.pfr m.loc.label = (CE η).pfr m.loc.label := by rw [hl]; exact hpe.symm
        have hpc' : PlantCr E' (stOf r.1 r.2.1 r.2.2) m t (cr i t) :=
          TermPlant.PlantCr_frameK hpre hsz hsub hP hl' hF.2.1 (fun h => by rw [hpl']; exact h)
            (fun h => (WordUnit_congr hl').1 h)
            (fun t _ h => by
              rw [FpAt_congr (a := ⟨m.loc.label, 0⟩) hl' hF.2.1 hpl' hF.2.2.2.2.2.2.2.2.1] at h
              exact h)
            hV hc
        have hm' : (stOf r.1 r.2.1 r.2.2).mem[t]? = some m := by rw [hpre t (hP t (hsub t ht))]; exact hm
        have e := (hKq hnp).1 t ht (.inr ⟨m, hm', by rw [hSe t ht]; exact hpc', by rw [hSe t ht]; exact hk⟩)
        rw [e, hSe t ht]
        exact Res.le_refl _
    refine TermOwnCOldR.overCr_oldR (RS := RSc ++ RSh) (cr := fun t => cr i t + pl i t) hpre hP hsub hold hcpl
      hni hstoL hV hPU hFP hRS ?_ ?_ ?_ ?_ hpre0
    · intro t m ht hm hl hw
      show cr i t + pl i t + TermPiece.rpSum (RSc ++ RSh) t ≤ cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t
      rw [hcrE t]
      exact Res.add_le_add (hKeep t m ht hm hl hw) (Res.le_refl _)
    · intro t
      show TermPiece.rpSum (RSc ++ RSh) t ≤ cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t
      rw [hcrE t]
      exact TermOverCrW.le_add_leftR _ _
    · intro t m ht hm hl _ hnz
      have hnz' : (cr0 t + (if t ∈ (stOf r.1 r.2.1 r.2.2).promises then pl i t else .zero)) +
          TermPiece.rpSum (RSc ++ RSh) t ≠ .zero := by rw [← hcrE t]; exact hnz
      rcases TermOwnCPub.res_add_ne hnz' with h1 | h1
      · left
        intro h0
        apply h1
        refine Res.ext fun key => ?_
        have h2 := Res.le_def.1 (hle0 t) key
        have h3 : (cr i t + pl i t) key = 0 := by rw [h0]; rfl
        rw [h3] at h2
        rw [Res.zero_apply]
        omega
      · right
        obtain ⟨y, hy, hyt, -⟩ := TermOwnCPub.rpSum_ne h1
        obtain ⟨-, -, -, ⟨mh, -, hmh, hlab, -⟩, -⟩ := hRS y hy
        rw [hyt] at hmh
        have hm' : (stOf r.1 r.2.1 r.2.2).mem[t]? = some m := by rw [hpre t (hP t (hsub t ht))]; exact hm
        rw [hm'] at hmh
        obtain rfl := Option.some.inj hmh
        exact ⟨y, hy, hlab.symm.trans hl, hyt⟩
    · exact hcovN (RSc ++ RSh)
        (fun o tw hD hgt hK' => hCaseB X Y hK hPA hnp E' RSc RSh hF hMI hcovS l cl hold ho hpf0 hs1 hpe.symm o tw
          hD hgt hK')
        (fun o tw hD hgt hlt hK' => .inl (hCaseC X Y hPA E' hF hMI l cl hold ho hpf0 hs1 hpe.symm o tw hD hgt hlt hK'))

#print axioms openOverCrOwnC_of

end TermOwnCTop
