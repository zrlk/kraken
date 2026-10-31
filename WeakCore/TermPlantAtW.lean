import WeakCore.TermPlantAtN
import WeakCore.TermPtrRts
import WeakCore.TermWin
import WeakCore.TermCertScope
import WeakCore.TermNoFulRun

/-! # TermPlantAtW: `NoFulT` for `tm := TermPtrRts.tminG`

The two step facts of `TermPlantAtN` (`NoFulStepT`, `WinAfterT`) from the `TermPtrRts`:

* `NoFulStepT` from K-3 (`NoFulStep`) and the `SysInvN` clause `PtrRtsG` (here the named
  `PtrRtsAt`, to become `X.inv.ptrRts hk`), via `ptrRtsE_of_G` and `tminG_eq`;
* `WinAfterT` from the typed post-state (`postTyped`: `tstep_footprint` fed by `ThSys`, the
  run-DRF scope and the `CertWinC` window), K-2a (`PtrRtsThreadP`, named), K-4 (`NoFulPlRun`)
  re-rooted at `c'`, and K-5 (`winLe_gen`) along the certificate of `c'`.

`CertWinC` is consumed as a hypothesis only (nothing here proves `CertWinC`/`CertWinP`).
-/

namespace TermPlantAtW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (the `SysInvN` clause, named) `PtrRtsGL` (`PtrRtsG ∧ LblSto ∧ GateTmin`) at every `TCtx`
configuration. -/
def PtrRtsAt (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → k.storeDepRts = true →
    TermPtrRts.PtrRtsGL Eg Tot HP c

/-- `Eg` with the frontiers/boxes of `E'` joined in (old ones first), the `Eg'` of
`ptrRtsThreadGL_proj`. -/
def egJ (Eg : GEnv) (E' : TEnv) : GEnv :=
  { Eg with pfr := fun l => match Eg.pfr l with | some f => some f | none => E'.pfr l
            box := fun l => match Eg.box l with | some B => some B | none => E'.box l }

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

theorem gOf_thread {c c' : Cfg} {i : Nat} (hc' : c' ∈ threadSteps p k arch c i) (j : Nat) :
    gOf p k arch c' j = { gOf p k arch c j with tys := tysOf c' } := by
  unfold gOf
  rw [TermStep.threadSteps_n hc', (threadSteps_lbase hc').1, (threadSteps_lbase hc').2]

/-- The global store typing joined with the footprint's (old cells first). -/
def stoJ (sto : TermPtrRts.Sto) (E' : TEnv) : TermPtrRts.Sto := fun l =>
  match sto l with
  | some c => some c
  | none => E'.sto l

theorem stoJ_left {sto : TermPtrRts.Sto} {E' : TEnv} {l : AllocLabel} {c : Cell} (h : sto l = some c) :
    stoJ sto E' l = some c := by
  simp only [stoJ, h]

theorem stoJ_none {sto : TermPtrRts.Sto} {E' : TEnv} {l : AllocLabel} (h : sto l = none) :
    stoJ sto E' l = E'.sto l := by
  simp only [stoJ, h]

/-- **The typed post-state** of the taken step (the Q2 route). -/
theorem postTyped [ProgRetIall p] (hP : ProgT p) (hps : TermScope.ProgScopeOK p = true)
    (h0d : TermScope.RunScopeR p k arch Sp c0) (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ (S : AllocLabel → Prop) (E' : TEnv), ThInvE p (Cut Eg i S) th ∧
      MemInv (gOf p k arch c i) (Cut Eg i S) (stOf c.mem c.pairs th) ∧
      Foot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ∧
      ThInvE p E' r.2.2 ∧ MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2) ∧
      PromAbove (stOf r.1 r.2.1 r.2.2) ∧ (∀ l cl, E'.sto l = some cl → stoJ Eg.sto E' l = some cl) := by
  obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, htid, hE, hT, htv, hFI, hsum, -, hm, -, -, hrp, hDy⟩ := ThSysAt.env X.inv.clo hS
  have hCE' : CE η = Cut Eg i S := hCE
  have Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs := ⟨hCE, htid, hE, hT, htv, hFI, hsum⟩
  have hwin : PubWinT (CE η) (stOf c.mem c.pairs th) th :=
    TermWin.winM_of (TermCertScope.certRunC_of (TermCertScope.certScopeC_of hps h0d) hCW) X Y hS hm
  have hFi : FInv ρ η th.σs (Resume p th.stack) cx th.env :=
    FInvR_FInv htv.2.2.2.2.2.2.2
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hFI
  have hdrf := TermScope.run_drf hps h0d X.run i th X.hth
  have hsc : ScopeD th.σs cx th.term :=
    TermCertScope.scopeD_of hdrf.ok (TermScope.scope_termV hT.1 hFi.2.1 hdrf.ok hdrf.env (TermStep.not_spawnT_of_mem X.hr))
  have hn : 0 < (gOf p k arch c i).n := by
    show 0 < c.n
    exact TermLiveProps.lt_of_get X.hth |> fun h => Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n h)
  have hnd : isDone th = false := by
    have hr := X.hr
    cases hd : isDone th
    · rfl
    · rw [tstep_done hd] at hr; simp at hr
  have hpa : PromAbove (stOf r.1 r.2.1 r.2.2) := by
    have h1 := TermTyped.certified_promAboveSt X.cert X.e3
    rw [X.e1, X.e2] at h1
    exact h1
  have hpx := TermTyped.PAx_of_step X.hc' X.cert X.hth
  obtain ⟨-, hf⟩ := tstep_footprint (hDy := hDy) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP rfl hn hnd hsc hT.1 hFi hE htv hm X.inv.bf hpx hwin (hRP := hrp)
    (hTy := by rw [hCE']; exact (X.inv.tyRec X.hth S).1)
  obtain ⟨E', hF, -, hT', hm'⟩ := hf r X.hr hpa
  have hF2 : Foot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← hCE']; exact hF
  refine ⟨S, E', ⟨ρ, η, cx, hCE', hE, hT.1, htv, hFi, hrp, hDy⟩, ?_, hF2, hT', hm', hpa, ?_⟩
  · rw [← hCE']; exact hm
  · intro l cl hl
    rcases hF2.1.2.2.1 l with e | ⟨hfr, -⟩
    · rw [e] at hl
      exact stoJ_left (TermPlantAtT.sto_of_cut hl)
    · have hn := (X.inv.gfresh X.hth r.2.2.nalloc l hfr).1
      rw [stoJ_none hn]; exact hl

/-- `NoFulStepT` for `tminG` from K-3 and the `SysInvN` clause. -/
theorem noFulStepT_of (hNS : TermPtrRts.NoFulStep p) (hPR : PtrRtsAt p k arch Sp Init MintOK c0) :
    TermPlantAtN.NoFulStepT TermPtrRts.tminG p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r l cl t X hk hsto hown hpf hnp htm hpub
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpf
  obtain ⟨S, -, hT, hm, -⟩ := X.inv.thr i th X.hth
  have hR := TermPtrRts.ptrRtsE_of_G (hPR X hk).1 X.hth hsto hown hf hnp
  have ht : TermPtrRts.tminOf Eg.sto (stOf c.mem c.pairs th) l = some t := by
    rw [← TermPtrRts.tminG_eq X.hth]; exact htm
  exact hNS (Cut Eg i S) Eg.sto (gOf p k arch c i) c.mem c.pairs th l t r hk
    (fun _ _ h => TermPlantAtT.sto_of_cut h) hT hm hR ht X.hr hpub

/-- (shared start, the `noFul_pre` body) **`NFInv` at a reachable configuration** for an own cell
with a frontier under the key gate, every start fact from `SysInvN` and the run-DRF scope. -/
theorem nfInv_pre {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {l : AllocLabel} {cl : Cell} {f t : Ts}
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hrun : TermSpawnStep.StepsG p k arch Sp c0 c)
    (hth : c.ths[i]? = some th) {S : AllocLabel → Prop}
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hk : k.storeDepRts = true)
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some i) (hf : Eg.pfr l = some f)
    (hnp : TermPlantAtT.KeyG Tot HP i l) (htm : TermPtrRts.tminG Eg c i l = some t) :
    TermPtrKey.NFInv p k arch i l t (Cut Eg i S) (Cut Eg i S) c := by
  obtain ⟨-, hT, hm, -⟩ := id hS
  have hG := hinv.ptrGL hk
  have hR := TermPtrRts.ptrRtsE_of_G hG.1 hth hsto hown hf hnp
  have ht : TermPtrRts.tminOf Eg.sto (stOf c.mem c.pairs th) l = some t := by
    rw [← TermPtrRts.tminG_eq hth]; exact htm
  have hGW : TermPtrRts.GranuleW Eg.sto c.mem c.pairs := by
    rcases hinv.granW hk with h | h
    · have := (Array.getElem?_eq_some_iff.1 hth).1
      omega
    · exact h
  have hba : Eg.box l = none := by
    cases e : Eg.box l with
    | none => rfl
    | some B => rw [hinv.boxSto l B e] at hsto; cases hsto
  refine ⟨th, Cut Eg i S, Eg.sto, hth, hT, hm, fun _ _ h => TermPlantAtT.sto_of_cut h, hR, ht, hinv.bf,
    TermPtrKey.fresh_sto_none hinv hth, TermPtrKey.thLbl_cut hG.2.1 hth, StoClo_Cut hinv.clo i S,
    TermScope.run_drf hps h0d hrun i th hth,
    fun t' h => hG.2.2.2 i th l cl f hth hsto hown hf hnp t' (by rw [TermPtrRts.tminG_eq hth]; exact h),
    TermGranW.granuleWP_of _ hGW, hinv.stoLay hk, ⟨cl, cutSto_own hsto hown⟩,
    by rw [Cut_pfr, hf]; exact Option.some_ne_none f, by rw [Cut_box]; exact hba, ?_, TermTyped.anchR_start hm (hinv.riniCoh i th S hth)
      (fun l cl f hs hp => hinv.frlt l cl f (cutSto_sub hs) hp),
    by obtain ⟨_, η, _, hCE, -⟩ := id hT; have e : CE η = Cut Eg i S := hCE; rw [← e]; exact Ext_refl (Coh_CE η) (CohR_CE η),
    TermMain.tidAt_cut hinv i S, fun th2 hth2 hl2 => by
      rw [hth] at hth2; cases hth2
      have hb := (hinv.tidBox i th hth l hl2).1
      rw [hsto] at hb; cases hb; simp at hown, (hinv.tyRec hth S).1, (hinv.tyRec hth S).2⟩
  intro t' ht' lb B hB o w hw hN f' hf'
  rw [Cut_box] at hB
  rw [Cut_pfr] at hf'
  exact hinv.boxPlantSep hk lb B hB o w hw i th l cl f' t' hth hsto hown hf' hnp
    (by rw [TermPtrRts.tminG_eq hth]; exact ht') hN

/-- **`NoFulPlRunGL` from an `NFInv` start**: the plant edge stays outstanding along the owner's
solo runs not publishing `l`. -/
theorem noFul_ofNF {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {l : AllocLabel} {t : Ts} {Eu Ea : TEnv} {c1 : Cfg}
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hps : TermScope.ProgScopeOK p = true) (hk : k.storeDepRts = true)
    (hJ : TermPtrKey.NFInv p k arch i l t Eu Ea c1)
    (hsc : ∀ c2, Solo p k arch i c1 c2 → Certified p k arch c2 i → TermTyped.ScopeAt p i c2) (hvI : TermViewInv.ViewInv c1)
    (hwin : ∀ c2, Solo p k arch i c1 c2 → Certified p k arch c2 i → TermTyped.NoHoldPubA p k arch Eu Ea i c2) :
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch i l c1 c2 → Certified p k arch c2 i → c2.ths[i]? = some th2 →
      t ∈ th2.promises := by
  obtain ⟨th, E, S, hth, hE, hm, hES, hR, ht, hbf, hfr, hL, hSC, hD, hC, hG, hLay, hsa, hpa, hba, hBS, hA, hXa, hTA, hNa, hTyJ, hRcJ⟩ := hJ
  exact hNP i l c1 th E S t hk hES hsc hvI Eu Ea hwin hA hXa hTA hNa hth hE hm hTyJ hRcJ hR ht hbf hfr hL hSC hps hD hC hG hLay hsa hpa hba hBS

/-- (D-B) **The start of the owner's solo run at the pre-state**: `NoFulPlRunGL` (the run, v3d) at
`(c, Cut Eg i S, Eg.sto)`, every start fact from `SysInvN` (`ptrGL`, `granW`, `stoLay`, `fresh`, `clo`,
`boxSto`, `boxPlantSep`) and the run-DRF scope / `CertWinC` window. -/
theorem noFul_pre (hV0 : TermViewInv.ViewInvR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0) (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {l : AllocLabel} {cl : Cell} {f t : Ts}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (hk : k.storeDepRts = true)
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some i) (hf : Eg.pfr l = some f)
    (hnp : TermPlantAtT.KeyG Tot HP i l) (htm : TermPtrRts.tminG Eg c i l = some t) :
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch i l c c2 → Certified p k arch c2 i → c2.ths[i]? = some th2 →
      t ∈ th2.promises := by
  obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
  exact noFul_ofNF hNP hps hk (nfInv_pre hps h0d X.inv X.run X.hth hS hk hsto hown hf hnp htm)
    (fun c2 hs hc => TermCertScope.certScopeC_of hps h0d X c2 hs hc) (TermViewInv.viewInv_run hV0 X.run)
    (fun c2 hs hc => hCW X S hS c2 hs hc)

/-- `WinAfterT` for `tminG` from K-4 (`NoFulPlRunGL`, started at the pre-state) and K-5. -/
theorem winAfterT_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0) (hNP : TermPtrKey.NoFulPlRunGL p k arch) :
    TermPlantAtN.WinAfterT TermPtrRts.tminG p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r l cl t mP X hk hsto hown hpf hnp htm hmP hpub h1
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hpf
  have hNo0 := noFul_pre (hV0 := hV0) hps h0d hCW hNP X hk hsto hown hf hnp htm
  have hNo : ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch i l c' c2 → Certified p k arch c2 i → c2.ths[i]? = some th2 →
      t ∈ th2.promises := fun c2 th2 hs hc h2 =>
    hNo0 c2 th2 (.thread X.hc' (fun th0 h0 => by rw [X.hth] at h0; cases h0; exact hpub) hs) hc h2
  obtain ⟨cs, hs, hn⟩ := X.cert
  exact TermPtrRts.winLe_gen (j := i) (a := l) (c1 := c') hNo (TermPlantAtN.mem_along X.hr X.e1 hmP) hs hn
    (.refl c') r.2.2 X.e3 h1

/-- **`NoFulT`** for `tminG`. -/
theorem noFulT_tminG (hV0 : TermViewInv.ViewInvR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0)
    (hNS : TermPtrRts.NoFulStep p) (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    (hPR : PtrRtsAt p k arch Sp Init MintOK c0) :
    TermPlantAtT.NoFulT TermPtrRts.tminG p k arch Sp Init MintOK c0 :=
  TermPlantAtN.noFulT_of (noFulStepT_of hNS hPR) (winAfterT_of (hV0 := hV0) hps h0d hCW hNP)

end

end TermPlantAtW

#print axioms TermPlantAtW.postTyped
#print axioms TermPlantAtW.noFulStepT_of
#print axioms TermPlantAtW.nfInv_pre
#print axioms TermPlantAtW.noFul_ofNF
#print axioms TermPlantAtW.noFul_pre
#print axioms TermPlantAtW.winAfterT_of
#print axioms TermPlantAtW.noFulT_tminG
