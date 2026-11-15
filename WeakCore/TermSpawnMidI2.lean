import WeakCore.TermSpawnMidAsm
import WeakCore.TermSpawnMidBridge
import WeakCore.TermSpawnTy
import WeakCore.TermBoxG
import WeakCore.TermBoxO
import WeakCore.TermInit
import WeakCore.TermScopeW
import WeakCore.TermBlkZ
import WeakCore.TermSpawnMidI
/-! # TermSpawnMidI2 — `SysInvN` across a `spawnI` (mid-run), internal frame transfer.

The kid's frame total is a part `R` of the parent's (`R ≤ Tot i`, own-key free); the parent keeps
`Tot i - R` (`totI`).  Per-key thread sums are unchanged; own keys are unchanged. -/
namespace TermSpawnI
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn TermSpawnGlobM TermSpawnMid
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The `spawnI` kid's shape: `tail nm is (var a) ts` at the env type `K`. -/
structure KidShapeI (par kid : TTh) (nm : String) (is : List String) (ts : List Ty) (K : Ty) (ws : List Word) :
    Prop where
  term : kid.term = .tail nm is (.var "a") ts
  env : kid.env = [("a", K, ws.map (TermSpawn.bumpW par.vs.vRelSt))]
  σs : kid.σs = []
  stack : kid.stack = []
  vs : kid.vs = { par.vs with mine := [] }
  promises : kid.promises = []
  nalloc : kid.nalloc = 0
  undefs : kid.undefs = 0
  tys : kid.tys = []

theorem spawnKidI_shape (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr) (d : Decl) (ts : List Ty)
    (ws : List Word) :
    KidShapeI (TermSpawnStep.spawnPar c i th x e) (TermSpawnStep.spawnKidI c i th d ts ws) d.name d.idx ts
      (TermRun.close (ts.map (TermRun.close [])).reverse d.argTy) ws :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The post-spawn frame totals: the kid holds `R`, the parent `Tot i - R`. -/
def totI (Tot : Nat → Res) (i n : Nat) (R : Res) : Nat → Res :=
  fun j => if j = n then R else if j = i then (fun key => Tot i key - R key) else Tot j

theorem totI_lt {Tot : Nat → Res} {i n j : Nat} {R : Res} (hj : j < n) (hji : j ≠ i) : totI Tot i n R j = Tot j := by
  simp [totI, Nat.ne_of_lt hj, hji]

/-! ## Sums and own keys under the split totals -/

theorem sum_totI_core {Tot : Nat → Res} {i n : Nat} {R : Res} (hi : i < n) (key : Key) (hR : R key ≤ Tot i key)
    (G : Nat → Nat) :
    ((List.range (n + 1)).map (fun j => totI Tot i n R j key + G j)).sum =
      ((List.range (n + 1)).map (fun j => extZ Tot n j key + G j)).sum := by
  rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have e1 : ((List.range n).map (fun j => totI Tot i n R j key + G j)).sum =
      ((List.range n).map (fun j => (if j = i then Tot i key - R key else Tot j key) + G j)).sum :=
    TermBal.sum_range_congr (fun j hj => by
      simp only [totI, Nat.ne_of_lt hj, ↓reduceIte]
      by_cases h : j = i
      · subst h; simp
      · simp [h])
  have e2 : ((List.range n).map (fun j => extZ Tot n j key + G j)).sum =
      ((List.range n).map (fun j => Tot j key + G j)).sum :=
    TermBal.sum_range_congr (fun j hj => by simp only [extZ, Nat.ne_of_lt hj, ↓reduceIte])
  have e3 := TermBal.sum_range_upd hi (f := fun j => (if j = i then Tot i key - R key else Tot j key) + G j)
    (g := fun j => Tot j key + G j) (fun j hj => by simp only [hj, ↓reduceIte])
  simp only [↓reduceIte] at e3
  rw [e1, e2]
  have e4 : totI Tot i n R n key = R key := by simp [totI]
  have e5 : extZ Tot n n key = 0 := by simp [extZ]
  rw [e4, e5]
  omega

theorem keySum_totI {Tot : Nat → Res} {i n : Nat} {R : Res} (hi : i < n) (hR : ∀ key, R key ≤ Tot i key)
    (P Q : Nat → Res) (key : Key) :
    ((List.range (n + 1)).map (fun j => (totI Tot i n R j + P j + Q j) key)).sum =
      ((List.range (n + 1)).map (fun j => (extZ Tot n j + P j + Q j) key)).sum := by
  have a1 : ((List.range (n + 1)).map (fun j => (totI Tot i n R j + P j + Q j) key)).sum =
      ((List.range (n + 1)).map (fun j => totI Tot i n R j key + (P j key + Q j key))).sum :=
    TermBal.sum_range_congr (fun j _ => by simp only [Res.add_apply, Nat.add_assoc])
  have a2 : ((List.range (n + 1)).map (fun j => (extZ Tot n j + P j + Q j) key)).sum =
      ((List.range (n + 1)).map (fun j => extZ Tot n j key + (P j key + Q j key))).sum :=
    TermBal.sum_range_congr (fun j _ => by simp only [Res.add_apply, Nat.add_assoc])
  rw [a1, a2]
  exact sum_totI_core hi key (hR key) _

theorem thSum_totI {Tot : Nat → Res} {i n : Nat} {R : Res} (hi : i < n) (hR : ∀ key, R key ≤ Tot i key)
    (P Q : Nat → Res) :
    thSum (n + 1) (fun j => totI Tot i n R j + P j + Q j) = thSum (n + 1) (fun j => extZ Tot n j + P j + Q j) :=
  Res.ext fun key => by
    rw [TermBal.thSum_apply, TermBal.thSum_apply]
    exact keySum_totI hi hR P Q key

theorem totI_own {Tot : Nat → Res} {i n : Nat} {R : Res} (hRown : ∀ l, R (.own l) = 0) (j : Nat)
    (l : AllocLabel) : totI Tot i n R j (.own l) = extZ Tot n j (.own l) := by
  unfold totI extZ
  by_cases hn : j = n
  · simp [hn, hRown]
  · by_cases h : j = i
    · subst h; simp [hn, hRown]
    · simp [hn, h]

section
variable {c : Cfg} {i : Nat} {th par kid : TTh} {Eg : GEnv}

theorem vwr_spawnTI {nm : String} {is : List String} {ts : List Ty} {K : Ty} {ws : List Word}
    (hth : c.ths[i]? = some th)
    (hv : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs) (hK : KidShapeI par kid nm is ts K ws) {N : Nat}
    (h : ∀ (j : Nat) (tj : TTh), c.ths[j]? = some tj → tj.vs.vWr ≤ N) :
    ∀ (j : Nat) (tj : TTh), (spawnT c i par kid).ths[j]? = some tj → tj.vs.vWr ≤ N :=
  spawnT_thAll hth (P := fun _ (tj : TTh) => tj.vs.vWr ≤ N) (fun j tj hj _ => h j tj hj)
    (by rw [vWr_par hv]; exact h i th hth) (by rw [hK.vs]; show par.vs.vWr ≤ N; rw [vWr_par hv]; exact h i th hth)

theorem cfgCoh_spawnTI {nm : String} {is : List String} {ts : List Ty} {K : Ty} {ws : List Word}
    (hth : c.ths[i]? = some th)
    (hv : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs) (hK : KidShapeI par kid nm is ts K ws)
    (h : TermLiveProps.CfgCoh c) : TermLiveProps.CfgCoh (spawnT c i par kid) := by
  have hp : TermLiveProps.CohAt c.mem par.vs := by
    rw [hv]; exact h i th hth
  exact spawnT_thAll hth (P := fun _ (tj : TTh) => TermLiveProps.CohAt c.mem tj.vs) (fun j tj hj _ => h j tj hj) hp
    (by rw [hK.vs]; exact hp)
end

/-- **`SysInvN` across a mid-run `spawnI`** (twin of `sysInvN_spawnMid`): the parent's and the kid's
`ThSys` at the split totals are inputs (`spawnI_sites`). -/
theorem sysInvN_spawnMidI {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th par kid : TTh} {nm : String} {is : List String} {ts : List Ty} {K : Ty} {ws : List Word} {R : Res}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hth : c.ths[i]? = some th) (hnp : th.promises = [])
    (hpar : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs) (hpty : par.tys = th.tys)
    (hPenv : ∃ (x : String) (w0 : Word), par.env = (x, .tid, [w0]) :: th.env ∧ par.stack = th.stack ∧
      ∀ w ∈ TermPtrRts.pubWords .tid [w0], ∀ l, TermPtrRts.Names l w → Eg.pfr l ≠ none ∨ Eg.box l ≠ none)
    (hTBp : TidBox Eg par) (hTBk : TidBox Eg kid)
    (hK : KidShapeI par kid nm is ts K ws)
    (hRle : ∀ key, R key ≤ Tot i key) (hRown : ∀ l, R (.own l) = 0)
    (hParSys : ThSys p (gOf p k arch (spawnT c i par kid) i) (spawnT c i par kid).mem (spawnT c i par kid).pairs par
      (EgK Eg c) (fun key => Tot i key - R key) (HP i) HS (cr i) (db i))
    (hKidSys : ThSys p (gOf p k arch (spawnT c i par kid) c.ths.size) (spawnT c i par kid).mem
      (spawnT c i par kid).pairs kid (EgK Eg c) R .zero HS (fun _ => .zero) (fun _ => .zero))
    (hLblK : k.storeDepRts = true → TermPtrRts.ThLbl (EgK Eg c) kid)
    (hThrS : ∀ j tj, c.ths[j]? = some tj →
      ThSys p (gOf p k arch (spawnT c i par kid) j) c.mem c.pairs tj Eg (Tot j) (HP j) HS (cr j) (db j))
    (hFrS : ∀ j tj, c.ths[j]? = some tj → ∀ q, tj.nalloc ≤ q →
      GFreshL Eg c tj (freshLabel c.lbase (spawnT c i par kid).n j q))
    (hU : ∀ q, Eg.sto (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.box (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.ini (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = 0 ∧
      Eg.pfr (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      ∀ (t : Nat) (m : Msg), c.mem[t]? = some m →
        m.loc.label ≠ freshLabel c.lbase (spawnT c i par kid).n c.ths.size q)
    (hOwnFS : ∀ (q : Nat) (thq : TTh) (j : Nat), c.ths[q]? = some thq → thq.nalloc ≤ j →
      (∀ n, n < c.ths.size → (Tot n + HP n + pSumAt c n (cr n))
          (.own (freshLabel c.lbase (spawnT c i par kid).n q j)) = 0) ∧
        HS (.own (freshLabel c.lbase (spawnT c i par kid).n q j)) = 0)
    (hOwnU : ∀ j, (∀ n, n < c.ths.size → (Tot n + HP n + pSumAt c n (cr n))
          (.own (freshLabel c.lbase (spawnT c i par kid).n c.ths.size j)) = 0) ∧
        HS (.own (freshLabel c.lbase (spawnT c i par kid).n c.ths.size j)) = 0)
    (hT : ∀ j l, TgtOK Eg c j l → TgtOK (EgK Eg c) (spawnT c i par kid) j l)
    (hFU : FreshU (spawnT c i par kid).n Eg c Tot HP HS cr) :
    SysInvN p k arch Init MintOK (spawnT c i par kid) (EgK Eg c) (totI Tot i c.ths.size R) (extZ HP c.ths.size) HS
        (extZT cr c.ths.size) (extZT db c.ths.size) ∧
      OwnLive (EgK Eg c) (spawnT c i par kid) ∧ ObsAll (EgK Eg c) (spawnT c i par kid) := by
  obtain ⟨hv, hpp, hna, hun⟩ := hpar
  have hkp : kid.promises = [] := hK.promises
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  have hpp1 : par.promises = th.promises := by rw [hpp, hnp]
  have hsz : (spawnT c i par kid).ths.size = c.ths.size + 1 := spawnT_size
  have E := easy_spawnT (par := par) (kid := kid) (i := i) hN
  obtain ⟨eClo, eCmg, eShty, eRle, eZw, eBn, eBpv, eBfl, eBft, ePay, eBst, eNI, eUa, eUl, eMw, eSl, eSw⟩ := E
  have hLbl : k.storeDepRts = true →
      TermPtrRts.ThLbl (EgK Eg c) par ∧ TermPtrRts.ThLbl (EgK Eg c) kid := by
    intro hk
    obtain ⟨x, w0, he, hs, hw0⟩ := hPenv
    exact ⟨thLbl_par (hN.ptrGL hk).2.1 hth he hs hw0, hLblK hk⟩
  have hOwnF : OwnFreshZ (spawnT c i par kid) (totI Tot i c.ths.size R) (extZ HP c.ths.size) HS
      (extZT cr c.ths.size) := by
    intro q thq j hq hj
    have key : (∀ n, n < c.ths.size → (Tot n + HP n + pSumAt c n (cr n))
          (.own (freshLabel c.lbase (spawnT c i par kid).n q j)) = 0) ∧
        HS (.own (freshLabel c.lbase (spawnT c i par kid).n q j)) = 0 := by
      rcases spawnT_get_cases hi hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hq1⟩
      · exact hOwnFS q th j hth (by rw [← hna]; exact hj)
      · exact hOwnU j
      · exact hOwnFS q thq j hq1 hj
    refine ⟨fun m hm => ?_, key.2⟩
    have h1 := ownZ_spawnT (par := par) (kid := kid) (i := i) hth hpp1 hkp key.1 m hm
    simp only [Res.add_apply] at h1 ⊢
    rw [totI_own hRown]; exact h1
  have hthr : ∀ j tj, (spawnT c i par kid).ths[j]? = some tj →
      ThSys p (gOf p k arch (spawnT c i par kid) j) (spawnT c i par kid).mem (spawnT c i par kid).pairs tj
        (EgK Eg c) (totI Tot i c.ths.size R j) (extZ HP c.ths.size j) HS (extZT cr c.ths.size j)
        (extZT db c.ths.size j) := by
    intro j tj hj
    rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hji, hjn, hj1⟩
    · simp only [totI, extZ, extZT, Nat.ne_of_lt hi, ↓reduceIte]
      exact hParSys
    · simp only [totI, extZ, extZT, ↓reduceIte]
      exact hKidSys
    · simp only [totI, extZ, extZT, hjn, hji, ↓reduceIte]
      exact thSys_otherM (hThrS j tj hj1) hjn
  have hbal := bal_spawnT (par := par) (kid := kid) hth hpp1 hkp hN.bal
  have hpool := pool_spawnT (par := par) (kid := kid) hOL hth hnp hpp hkp hN.pool
  refine ⟨{
    thr := hthr
    held := memHeldG_spawnT hth hnp hpp hkp hN.held
    clo := eClo
    cmg := eCmg
    shty := eShty
    proms := proms_spawnT hth hnp hpp hkp hN.proms
    fpok := fpok_spawnT hth hpp hkp hOL hN.plt hN.fpok
    fresh := fresh_spawnT hth hnp hpp hkp hna hFrS hU
    bal := by
      obtain ⟨M, hM, hle⟩ := hbal
      refine ⟨M, hM, ?_⟩
      rw [hsz] at hle ⊢
      rw [thSum_totI hi hRle]
      exact hle
    knet := fun key hk => by
      have h := keyNet_spawnT (par := par) (kid := kid) (i := i) hth hpp1 hkp (hN.knet key hk)
      unfold KeyNet at h ⊢
      rw [hsz] at h ⊢
      rw [keySum_totI hi hRle]
      exact h
    bf := bf_spawnT hN.bf
    boxtop := boxTop_spawnT hOL hth hnp hpp hkp hN.boxtop
    disj := disj_spawnT hth hpp hkp hN.disj
    fpfree := fpfree_spawnT hth hpp hkp hN.fpfree
    plt := plt_spawnT hth hpp hkp hN.plt
    vwr := vwr_spawnTI hth hv hK hN.vwr
    frle := frle_spawnT hN.frle
    rle := eRle
    zwIni := eZw
    predHold := predHold_spawnT hOL hth hnp hpp hkp hN.predHold
    bnamed := eBn
    rid := by
      obtain ⟨rc, h⟩ := hN.rid
      refine ⟨rc, ?_⟩
      have h2 := ridOK_spawnT (par := par) (kid := kid) (i := i) hth hpp1 hkp h
      intro n hn key hkey
      have h3 := h2 n hn key hkey
      rw [hsz] at h3 ⊢
      rw [keySum_totI hi hRle]
      exact h3
    promIni := promIni_spawnT hth hpp hkp hN.promIni
    promTy := promTy_spawnT hth hpp hkp hN.promTy
    promNU := promNU_spawnT hth hpp hkp hN.promNU
    ownF := hOwnF
    promNoTwo := promNoTwo_spawnT hth hpp hkp hN.promNoTwo
    undefAt := eUa
    ownKeyOwn := by
      have h := ownKeyOwn_spawnT (par := par) (kid := kid) hN hth
      intro j tj l hj hne
      rw [totI_own hRown] at hne
      exact h j tj l hj hne
    ownPub := by
      have h := ownPub_spawnT (par := par) (kid := kid) hN hth
      intro l hl
      obtain ⟨h1, h2⟩ := h l hl
      refine ⟨h1, fun hs => ?_⟩
      obtain ⟨h3, h4⟩ := h2 hs
      refine ⟨fun j tj hj => ?_, h4⟩
      have h5 := h3 j tj hj
      simp only [Res.add_apply] at h5 ⊢
      rw [totI_own hRown]; exact h5
    boxPV := eBpv
    boxFrOwn := boxFrOwn_spawnT hN hOL hth (Nat.le_of_eq (vWr_par hv).symm)
    boxFrLe := eBfl
    vwrLt := vwr_spawnTI hth hv hK hN.vwrLt
    boxFrLt := eBft
    frlt := frlt_spawnT hN.frlt
    payOwn := ePay
    boxSto := eBst
    ownCoh := ownCoh_spawnT hth hv hOL hN.ownCoh
    riniCoh := riniCoh_spawnT hth hnp hpp hOL hN.riniCoh
    promInCut := promInCut_spawnT hth hpp hkp hN.promInCut
    promClos := promClos_spawnT hth hpp hkp hN.promClos
    stoNI := eNI
    undefLow := eUl
    promAbove := promAbove_spawnT hth hpp hkp hN.promAbove
    msgWords := eMw
    fgnClos := fgnClos_spawnT hth hpp hkp hN.fgnClos hT
    cellOwn := cellOwn_spawnT hN
    ptrGL := fun hk => by
      have h := ptrGL_spawnT hOL hth hnp hpp hkp (hN.ptrGL hk) (hLbl hk).1 (hLbl hk).2
      unfold TermPtrRts.PtrRtsGL TermPtrRts.PtrRtsG TermPtrRts.GateTmin TermPtrRts.MemRtsCG at h ⊢
      simp only [Res.add_apply, totI_own hRown] at h ⊢
      exact h
    granW := granW_spawnT hN hth
    stoLay := eSl
    boxPlantSep := fun hk => by
      have h := boxPlantSep_spawnT (par := par) (kid := kid) hOL hth hnp hpp hkp (hN.boxPlantSep hk)
      unfold TermPtrRts.BoxPlantSep at h ⊢
      simp only [Res.add_apply, totI_own hRown] at h ⊢
      exact h
    fgnCnt := fun hk => fgnCnt_spawnT hth hpp hkp (hN.fgnCnt hk) hT
    pool := by
      obtain ⟨pl, h1, h2, ⟨M, hM, hle⟩, h4, ⟨rc, h5⟩⟩ := hpool
      refine ⟨pl, h1, h2, ⟨M, hM, ?_⟩, fun key hk => ?_, ⟨rc, ?_⟩⟩
      · rw [hsz] at hle ⊢
        rw [thSum_totI hi hRle]
        exact hle
      · have h := h4 key hk
        unfold KeyNet at h ⊢
        rw [hsz] at h ⊢
        rw [keySum_totI hi hRle]
        exact h
      · intro n hn key hkey
        have h3 := h5 n hn key hkey
        rw [hsz] at h3 ⊢
        rw [keySum_totI hi hRle]
        exact h3
    plantIdx := fun hk => by
      have h := plantIdx_spawnT (par := par) (kid := kid) hOL hth hnp hpp hkp (hN.plantIdx hk)
      unfold TermPlantAtT.PlantIdxG TermPlantAtT.KeyG at h ⊢
      simp only [Res.add_apply, totI_own hRown] at h ⊢
      exact h
    cfgCoh := cfgCoh_spawnTI hth hv hK hN.cfgCoh
    stoW := eSw
    freshU := by
      have h := TermFreshU.freshU_spawnT hth hpp1 hkp hFU
      intro q j h1 h2
      obtain ⟨h3, ⟨h4, h5⟩⟩ := h q j h1 h2
      refine ⟨h3, fun m hm => ?_, h5⟩
      have h6 := h4 m hm
      simp only [Res.add_apply] at h6 ⊢
      rw [totI_own hRown]; exact h6
    scalIni := hN.scalIni
    tysOK := by
      have e : tysOf (spawnT c i par kid) = tysOf c := by
        funext l
        have h1 := congrFun (tysOf_set (d := { c with ths := c.ths.set! i par }) hth rfl hpty) l
        simp only [tysOf] at h1 ⊢
        rw [← h1]
        simp [spawnT, Array.toList_push, List.findSome?_append, hK.tys]
      rw [e]
      exact hN.tysOK
    tidBox := by
      intro j tj hj
      rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hj1⟩
      · exact hTBp
      · exact hTBk
      · exact hN.tidBox j tj hj1 }, TermSpawnRunX.ownLive_spawnT hOL, TermSpawnRunX.obsAll_spawnT hObs⟩

/-! ## Helpers: the kid's frame -/

/-- `dyFr_tail` at any index arguments. -/
theorem dyFr_tailI (ann : Op → Option Ty) (tg : List Ty) (p : CoreTerm.Prog) (η : TEnv) (f : String)
    (is : List String) (a : At) (ts : List Ty) : DyFr p ann tg η [] (.tail f is a ts) := by
  refine ⟨[], [], ?_, ⟨rfl, ?_⟩, ?_, ?_⟩
  · intro g b h; simp at h
  · intro c hc hne
    simp only [scan, List.mem_singleton] at hc
    subst hc; exact absurd (taintOf_nil ts) hne
  · intro σ h; simp at h
  · intro j σ h; simp at h

/-- A closed type's values at a thread-wide view do not depend on the index valuation. -/
theorem VRR_rho_closed (η : TEnv) {σ : Ty} (hσ : σ.wf 0 0 = true) (ρ ρ2 : Nat → Nat) (S : Shp)
    (ws : List Word) (X : Res) : VRR ρ (CE η) σ S ws X ↔ VRR ρ2 (CE η) σ S ws X := by
  have a := VRR_close (Coh_CE η) (CohR_CE η) ρ σ [] 0 ρ ρ2 S ws X (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have b := VRR_close (Coh_CE η) (CohR_CE η) ρ2 σ [] 0 ρ2 ρ2 S ws X (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  simp only [List.length_nil, TEnv.pre] at a b
  rw [@cl_wf _ ρ2 _ (CE η).wit σ 0 0 hσ] at a
  exact a.trans b.symm

/-- `subE` at closed type arguments does not depend on the outer index valuation. -/
theorem VRR_subE_rho (η : TEnv) {σs : List Ty} (hσ : ∀ σ ∈ σs, σ.wf 0 0 = true) {A : Ty}
    (hA : TermClose.tb σs.length A = true) (ρ ρ2 ρ1 : Nat → Nat) (S : Shp) (ws : List Word) (X : Res)
    (h : VRR ρ1 (subE ρ (CE η) σs) A S ws X) : VRR ρ1 (subE ρ2 (CE η) σs) A S ws X := by
  refine TermTear.VRR_congr A ρ1 ρ1 (subE ρ (CE η) σs) (subE ρ2 (CE η) σs) S ws X (fun _ _ => rfl) ?_ rfl h
  intro j hj
  have hlt : j < σs.length := by
    cases Nat.lt_or_ge j σs.length with
    | inl h => exact h
    | inr h => rw [tyMentions_tb A σs.length j hA h] at hj; cases hj
  obtain ⟨σ, hk⟩ : ∃ σ, σs[j]? = some σ := ⟨σs[j], List.getElem?_eq_getElem hlt⟩
  have hw := hσ σ (List.mem_of_getElem? hk)
  refine ⟨?_, ?_, ?_⟩
  · simp only [subE, hk]; exact cl_wf σ hw
  · simp only [subE, hk]
    funext rt ws0 X0
    exact propext (VRR_rho_closed η hw ρ ρ2 rt ws0 X0)
  · simp only [subE, hk]
    funext rt ws0 X0
    exact propext (VRR_rho_closed η.unsee hw ρ ρ2 rt ws0 X0)

/-- `arg_move` with resources, at any index valuation. -/
theorem VRR_arg_move {Eg Eg2 : GEnv} {S S2 : AllocLabel → Prop} {i j : Nat} {V : Ts} {R0 : Ty} {sh : Shp}
    {res : List Word} {ρ : Nat → Nat} {X : Res}
    (hI : InclS (Cut Eg i (fun _ => False)) (Cut Eg2 j S2)) (hS : SeenLE (Cut Eg i S) V)
    (hn : noOR R0 = true) (hv : VRR ρ (Cut Eg i S) R0 sh res X) :
    VRR ρ (Cut Eg2 j S2) R0 sh (res.map (TermSpawn.bumpW V)) X := by
  have h1 := VRR_up _ _ _ _ _ (WLe_bumpS V res) hv
  have h2 : VRR ρ (Cut Eg i (fun _ => False)) R0 sh (res.map (TermSpawn.bumpW V)) X :=
    VRR_unsee V R0 (Cut Eg i S) (Cut Eg i (fun _ => False)) _ _ _ _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      rfl rfl rfl (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl))
      (fun _ _ h => h) (LocAbove_bumpS V res) h1 (fun _ => Nat.le_refl _)
  exact VRR_transferS R0 (Cut Eg i (fun _ => False)) (Cut Eg2 j S2) _ _ _ _ hn (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) rfl hI.prog hI.sto hI.ini hI.rini hI.pfr (fun _ h => (h : False).elim) hI.box h2

/-- A closed type's values do not see the frame part of the view. -/
theorem VRR_closed_CE (E : TEnv) {σ : Ty} (hσ : σ.wf 0 0 = true) (ρ : Nat → Nat) (S : Shp) (ws : List Word)
    (X : Res) : VRR ρ E σ S ws X ↔ VRR ρ (CE E) σ S ws X := by
  have htb : TermClose.tb 0 σ = true := tb_of_wf_le hσ (Nat.le_refl 0)
  have hm : ∀ j, σ.tyMentions j = false := fun j => tyMentions_tb σ 0 j htb (Nat.zero_le j)
  exact ⟨TermTear.VRR_congr σ ρ ρ E (CE E) S ws X (fun _ _ => rfl) (fun j hj => by rw [hm j] at hj; cases hj) rfl,
    TermTear.VRR_congr σ ρ ρ (CE E) E S ws X (fun _ _ => rfl) (fun j hj => by rw [hm j] at hj; cases hj) rfl⟩

/-- **The argument transfer** of a `spawnI`: a value at the instantiated signature type, in the caller's
frame view, is a value of the kid's (closed-argument) static type at the thread-wide view, under the
callee's index valuation. -/
theorem VRR_spawnI_arg {η : TEnv} {ρ : Nat → Nat} {ts : List Ty} {us : List Idx} {u : Ty}
    (hts : ∀ σ ∈ ts, σ.wf 0 0 = true) (hu : TermClose.tb ts.length u = true) {S : Shp} {ws : List Word}
    {X : Res} (h : VRR ρ η (substTs ts.reverse 0 0 (instT us 0 u)) S ws X) :
    VRR (vinsL 0 (us.map (ev ρ)) ρ) (CE η) (substTs ts.reverse 0 0 u) S ws X := by
  have h1 := (VRR_call ts us η ρ u S ws X).1 h
  have h2 : VRR (vinsL 0 (us.map (ev ρ)) ρ) (subE (vinsL 0 (us.map (ev ρ)) ρ) (CE η) ts.reverse) u S ws X := by
    refine TermTear.VRR_congr u _ _ (subE ρ η ts.reverse) _ S ws X (fun _ _ => rfl) ?_ rfl h1
    intro j hj
    have hlt : j < ts.reverse.length := by
      cases Nat.lt_or_ge j ts.reverse.length with
      | inl h => exact h
      | inr h => rw [tyMentions_tb u ts.reverse.length j (by rw [List.length_reverse]; exact hu) h] at hj; cases hj
    obtain ⟨σ, hk⟩ : ∃ σ, ts.reverse[j]? = some σ := ⟨ts.reverse[j], List.getElem?_eq_getElem hlt⟩
    have hw := hts σ (List.mem_reverse.1 (List.mem_of_getElem? hk))
    refine ⟨?_, ?_, ?_⟩
    · simp only [subE, hk]; exact cl_wf σ hw
    · simp only [subE, hk]
      funext rt ws0 X0
      exact propext ((VRR_closed_CE η hw ρ rt ws0 X0).trans (VRR_rho_closed η hw ρ _ rt ws0 X0))
    · simp only [subE, hk]
      funext rt ws0 X0
      exact propext ((VRR_closed_CE η.unsee hw ρ rt ws0 X0).trans (VRR_rho_closed η.unsee hw ρ _ rt ws0 X0))
  exact (VRR_substTs ts.reverse (CE η) (vinsL 0 (us.map (ev ρ)) ρ) u [] 0 _ S ws X (fun _ => rfl)).2 h2

/-- `finv_entryR` at any index valuation and index names, static = runtime type. -/
theorem finv_entryRI {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {th : TTh} {t r : Ty} {ws : List Word}
    {ρ : Nat → Nat} {X : Res} {ins : List String}
    {K : TEnv → List Word → Prop} (hK : ∀ E ws, K E ws)
    (henv : th.env = [("a", t, ws)]) (hσ : th.σs = [])
    (hv : VRR ρ (Cut Eg i S) t (shp t) ws X) (hlay : Lay [] t t ws) :
    FInv ρ (Cut Eg i S) th.σs K { inames := ins, vars := [("a", t, true)], ret := r } th.env := by
  have hRL : RLink (Cut Eg i S) := RLink_of (Coh_CE (Cut Eg i S)) (CohR_CE (Cut Eg i S))
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k t1 h; simp at h
  · intro x e hx
    obtain ⟨rfl, rfl⟩ := hfind x e hx
    refine ⟨t, ws, by rw [henv]; simp [lookupE], VRR_VR t hRL hv, by rw [hσ]; exact hlay⟩
  · intro _ _ _ _ _; exact hK _ _
  · refine ⟨fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _), fun k σ h => by rw [hσ] at h; simp at h,
      fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _)⟩
  · simp
  · refine ⟨fun k h => by simp [KEnv.ask] at h, fun k h => by simp [KEnv.ask] at h, fun σ h => by rw [hσ] at h; simp at h⟩
  · intro k; exact ⟨rfl, rfl, rfl⟩
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h

/-- `entryR_ofR` at any index valuation, index names/arguments and frame total. -/
theorem entryR_ofRI {p : Prog} {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {th : TTh} {f : String}
    {is ins : List String} {ts : List Ty} {t r : Ty} {ws : List Word} {ρ : Nat → Nat} (Tot : Res)
    (hp : Eg.prog = p)
    (hterm : th.term = .tail f is (.var "a") ts) (henv : th.env = [("a", t, ws)]) (hσ : th.σs = [])
    (hstk : th.stack = [])
    (hchk : check p { inames := ins, vars := [("a", t, true)], ret := r } (.tail f is (.var "a") ts) = .ok ())
    (htv : TvOK { inames := ins, vars := [("a", t, true)], ret := r })
    (hv : VRR ρ (Cut Eg i S) t (shp t) ws Tot) (hlay : Lay [] t t ws)
    (hts : ts.all TermScope.argOK = true) (hwt : TermScope.wrapOK t = true) :
    ThInvRE p (Cut Eg i S) th Tot ∧ ThInvE p (Cut Eg i S) th := by
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  have hE : EnvOK p (Cut Eg i S) := ⟨hp, Coh_CE (Cut Eg i S), CohR_CE (Cut Eg i S)⟩
  have hT : TypedK p (Cut Eg i S) { inames := ins, vars := [("a", t, true)], ret := r } th.term := by
    rw [hterm]
    exact ⟨check_sound p _ _ hchk, TermInit.checkW_tail_of hchk hts,
      fun v hm => by simp only [List.mem_singleton] at hm; subst hm; exact hwt,
      fun k hk _ => absurd hk (Nat.not_lt_zero _)⟩
  refine ⟨⟨ρ, Cut Eg i S, { inames := ins, vars := [("a", t, true)], ret := r }, Tot, .zero, rfl, hE, hT, htv,
    ⟨finv_entryRI (fun _ _ => trivial) henv hσ hv hlay, ?_, ?_⟩, Res.add_zero _,
    (fun f rest h => by rw [hstk] at h; cases h), by rw [hterm, hσ]; exact dyFr_tailI annNew (progTgts p) p _ f is _ ts⟩,
    ⟨ρ, Cut Eg i S, { inames := ins, vars := [("a", t, true)], ret := r }, rfl, hE, hT, htv, ?_⟩⟩
  · rw [hstk]; intro _ _ _ _ _ _; rfl
  · refine ⟨by simp, by simp, fun y h => by simp at h, fun _ => Tot, fun x e hx _ => ?_, ?_⟩
    · obtain ⟨rfl, rfl⟩ := hfind x e hx
      exact ⟨t, ws, by rw [henv]; simp [lookupE], hv⟩
    · simp only [TermSound.Holds, List.filter, Bool.true_or, List.map, Res.sum_cons, Res.sum_nil, Res.add_zero]
      exact Res.le_refl _
  · rw [hstk]; exact ⟨finv_entryRI (fun _ _ => trivial) henv hσ hv hlay, (fun _ _ h => by cases h),
    by rw [hterm, hσ]; exact dyFr_tailI annNew (progTgts p) p _ f is _ ts⟩

/-- `thSys_kidM` at a frame total `R`. -/
theorem thSys_kidMR {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {g : G}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th par kid : TTh}
    {R : Res}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hgi : g.i = c.ths.size)
    (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hpp : par.promises = []) (hkp : kid.promises = [])
    (hty : ThInvRE p (Cut (EgK Eg c) c.ths.size (fun _ => False)) kid R ∧
      ThInvE p (Cut (EgK Eg c) c.ths.size (fun _ => False)) kid)
    (hM : MemInv g (Cut (EgK Eg c) c.ths.size (fun _ => False)) (stOf c.mem c.pairs kid)) :
    ThSys p g (spawnT c i par kid).mem (spawnT c i par kid).pairs kid
      (EgK Eg c) R .zero HS (fun _ => .zero) (fun _ => .zero) := by
  unfold ThSys; rw [hgi]
  refine ⟨fun _ => False, hty.1, hty.2, hM, ?_, ?_, ?_⟩
  · refine ⟨[], fun _ => .zero, List.nodup_nil, ?_, ?_, rfl, ?_⟩
    · intro l cl hq _
      obtain ⟨⟨c1, hc1, ho⟩, -⟩ := hq
      exact absurd ho (TermSpawnKidMem.cutSto_kid_own hOL hc1)
    · intro l h; cases h
    · intro l h; cases h
  · exact MemHeldS_of_G (c := spawnT c i par kid) rfl hN.shty (promsOK_kid hth hnp hpp hkp)
      (memHeldG_spawnT hth hnp hpp hkp hN.held)
  · intro tw htw
    simp [stOf, hkp] at htw

/-- **The two sites of a `spawnI`** (twin of `arg_of_site`/`par_of_site`/`thSys_kidFull`): from the site
thread's invariant, a part `R` of its frame total goes with the (handed-off) argument to the kid. -/
theorem spawnI_sites {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th par kid : TTh} {x f : String} {is : List String} {a : At} {T : Ty} {ts : List Ty} {e : Expr} {d : Decl}
    {rt : Ty} {ws : List Word} {L : AllocLabel}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hth : c.ths[i]? = some th) (hnp : th.promises = [])
    (hterm : th.term = .let_ x (.spawnI f is a T ts) e) (hfind : p.find? (·.name == f) = some d)
    (hev : evalAt th.env a = some (rt, ws))
    (hp : TermScope.ProgScopeOKW p = true) (hPT : CoreTyping.ProgT p)
    (hpar : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs)
    (hpt : par.term = e) (hpe : par.env = (x, .tid, [cst (.loc ⟨L, 0⟩ 0)]) :: th.env) (hps : par.σs = th.σs)
    (hpk : par.stack = th.stack)
    (hbx : ∀ S, (Cut Eg i S).sto L = some ⟨.unit, none⟩ ∧ (Cut Eg i S).pfr L = some 0)
    (hK : KidShapeI par kid d.name d.idx ts (TermRun.close (ts.map (TermRun.close [])).reverse d.argTy) ws)
    (hU : ∀ q, Eg.sto (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.box (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.ini (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = 0 ∧
      Eg.pfr (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      ∀ (t : Nat) (m : Msg), c.mem[t]? = some m →
        m.loc.label ≠ freshLabel c.lbase (spawnT c i par kid).n c.ths.size q)
    (hts : ts.all TermC1.drf1 = true) :
    ∃ R : Res, (∀ key, R key ≤ Tot i key) ∧ (∀ l, R (.own l) = 0) ∧
      ThSys p (gOf p k arch c i) (spawnT c i par kid).mem (spawnT c i par kid).pairs par (EgK Eg c)
        (fun key => Tot i key - R key) (HP i) HS (cr i) (db i) ∧
      ThSys p (gOf p k arch (spawnT c i par kid) c.ths.size) (spawnT c i par kid).mem (spawnT c i par kid).pairs kid
        (EgK Eg c) R .zero HS (fun _ => .zero) (fun _ => .zero) ∧
      (k.storeDepRts = true → TermPtrRts.ThLbl (EgK Eg c) kid) := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  obtain ⟨S, hRE, hE, hM, hP, hS, hC⟩ := hN.thr i th hth
  have hd : d ∈ p := List.mem_of_find?_eq_some hfind
  have hname : d.name = f := by simpa using List.find?_some hfind
  obtain ⟨hwa, -, -, -, -⟩ := hPT d hd
  have hpo : TermScope.ProgScopeOK p = true ∧ TermScope.ProgWrapOK p = true := by
    simpa [TermScope.ProgScopeOKW] using hp
  have hdrfA := (TermScope.ProgScopeOK.decl hpo.1 hd).1
  have hwA : TermScope.wrapOK d.argTy = true := by
    have h := List.all_eq_true.1 hpo.2 d hd
    simp only [TermScope.declWrapOK, Bool.and_eq_true] at h
    exact h.1.1
  have hmap : ts.map (TermRun.close []) = ts := by
    conv => rhs; rw [← List.map_id ts]
    exact List.map_congr_left (fun t _ => substTs_nil t 0 0)
  have hKe : TermRun.close (ts.map (TermRun.close [])).reverse d.argTy = substTs ts.reverse 0 0 d.argTy := by
    rw [hmap]; rfl
  rw [hKe, hname] at hK
  have hSL : SeenLE (Cut Eg i S) par.vs.vRelSt := by
    rw [hpar.1]; exact (MemInv_fenceG .sy hM).2.2.2.2.1
  have hpE : Eg.prog = p := by
    obtain ⟨ρ, η, cx, Rf, Rs, hce, hEO, -⟩ := hRE
    have : (CE η).prog = (Cut Eg i S).prog := by rw [hce]; rfl
    exact this.symm.trans hEO.1
  have hl0 : Lay th.σs .tid .tid [cst (.loc ⟨L, 0⟩ 0)] :=
    ⟨fun us h => by simp [accs] at h; subst h; rfl, by first | rfl | simp [etok, close, substTs, skel],
      by simp [wc, accs], trivial, by first | rfl | simp [etok, close, substTs, lyt]⟩
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hEO, hT, htv, hi0, hsum, hpw, hDy⟩ := hRE
  have hT2 := hT.2
  rw [hterm] at hT2
  obtain ⟨c1, -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
  have htv1 := OpT_TvOK hPT hop htv
  cases hop with
  | spawnI hfd hinst hu hs1 hs2 hno hwf htb hwr harg htc hrt hb =>
    have hdd := find_ok hfd
    rw [hfind] at hdd
    cases hdd
    obtain ⟨us, hlen, hat, -⟩ := instantiate_ok hinst
    subst hat
    obtain ⟨rt0, ws0, R, Rr, hea, -, hl, hvr, hi1, hle⟩ := useR hu hi0 hEO.2.2
    rw [hev] at hea
    simp only [Option.some.injEq, Prod.mk.injEq] at hea
    obtain ⟨rfl, rfl⟩ := hea
    have hσts : ∀ σ ∈ ts, σ.wf 0 0 = true := fun σ hσ =>
      wf_tb_lower σ 0 _ 0 (List.all_eq_true.1 htb σ hσ) (List.all_eq_true.1 hwf σ hσ)
    have htbA : TermClose.tb ts.length d.argTy = true := by rw [hlen]; exact tb_of_wf _ hwa
    have hvT := VRR_sub hi1.1.1 hs1 _ _ _ hvr
    have hvA := VRR_sub hi1.1.1 hs2 _ _ _ hvT
    have hvK := VRR_spawnI_arg hσts htbA hvA
    rw [hCE] at hvK
    obtain ⟨hs1b, hl1⟩ := Lay_canon hs1 hl
    obtain ⟨hs2b, hl2⟩ := Lay_canon hs2 hl1
    have htsc : ts.map (TermRun.close th.σs) = ts := by
      conv => rhs; rw [← List.map_id ts]
      exact List.map_congr_left (fun t ht => TermSpawnStep.close_tb0 th.σs (List.all_eq_true.1 htb t ht))
    have Ea : skel (TermRun.close th.σs (substTs ts.reverse 0 0 (instT us 0 d.argTy))) =
        skel (substTs ts.reverse 0 0 d.argTy) := by
      rw [skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa), htsc]; try rfl
    have e0 : TermRun.close [] (substTs ts.reverse 0 0 d.argTy) = substTs ts.reverse 0 0 d.argTy :=
      substTs_nil _ 0 0
    have hLay : Lay [] (substTs ts.reverse 0 0 d.argTy) (substTs ts.reverse 0 0 d.argTy) ws := by
      have h := Lay_move hl2 (Ea.trans (congrArg skel e0.symm))
      rw [e0] at h; exact h
    have hshp : shp rt = shp (substTs ts.reverse 0 0 d.argTy) := hs1b.trans (hs2b.trans (shp_of_skel Ea))
    rw [hshp] at hvK
    have hnK : noOR (substTs ts.reverse 0 0 d.argTy) = true := by
      have h := noOR_kidI hno hs2 rfl hdrfA hts
      rw [hKe] at h; exact h
    have hvKb := VRR_arg_move (InclS_cut_EgK Eg c i c.ths.size (fun _ => False) (fun _ => False)) hSL hnK hvK
    have hLayB := Lay_bumpS par.vs.vRelSt hLay
    -- the kid
    simp only [Bool.and_eq_true] at hrt
    have hmgts : ∀ σ ∈ ts.reverse, TermTv.mg σ = true := fun σ h =>
      mg_of_wf σ (List.all_eq_true.1 hwf σ (List.mem_reverse.1 h))
    have htv0 : TvOK { inames := d.idx.reverse, vars := [("a", substTs ts.reverse 0 0 d.argTy, true)], ret := substTs ts.reverse 0 0 d.retTy } := by
      refine ⟨fun e he => ?_, fun tn htn => (by simp at htn), hrt.1.1, fun e he => ?_, fun e he => ?_,
        fun tn htn => (by simp at htn), hrt.1.2, hrt.2⟩
      · simp only [List.mem_singleton] at he; subst he
        exact tb_substTs (fun σ h => List.all_eq_true.1 htb σ (List.mem_reverse.1 h)) d.argTy 0 0
          (by simpa using htbA)
      · simp [Cx.opaqueOK]
      · simp only [List.mem_singleton] at he; subst he
        exact mg_substTs hmgts d.argTy 0 0 (mg_of_wf _ hwa)
    have hchk : check p { inames := d.idx.reverse, vars := [("a", substTs ts.reverse 0 0 d.argTy, true)], ret := substTs ts.reverse 0 0 d.retTy } (.tail f d.idx (.var "a") ts) = .ok () := by
      rw [check_tail]; exact htc
    have hwK : TermScope.wrapOK (substTs ts.reverse 0 0 d.argTy) = true :=
      wrapOK_substTs (by simpa using htb) (by simpa using harg) hwA
    have hkty := entryR_ofRI (p := p) (Eg := EgK Eg c) R hpE hK.term hK.env hK.σs hK.stack hchk htv0 hvKb hLayB harg hwK
    have hMk : MemInv (gOf p k arch (spawnT c i par kid) c.ths.size) (Cut (EgK Eg c) c.ths.size (fun _ => False))
        (stOf c.mem c.pairs kid) :=
      TermSpawnKidMem.memInv_kidM _ hM hnp hOL hN.shty hN.boxSto hN.boxtop hObs hN.rle hU hK.promises hK.nalloc
    have hKid := thSys_kidMR (g := gOf p k arch (spawnT c i par kid) c.ths.size) hN hOL rfl hth hnp hpar.2.1
      hK.promises hkty hMk
    have hLbl : TermPtrRts.ThLbl (EgK Eg c) kid := by
      have hwc : wc (substTs ts.reverse 0 0 d.argTy) = some (ws.map (TermSpawn.bumpW par.vs.vRelSt)).length := by
        have h1 := hLayB.2.2.1
        cases hac : accs (substTs ts.reverse 0 0 d.argTy) with
        | none => simp [wc, hac] at h1
        | some us2 => simp only [wc, hac, Option.map_some]; rw [hLayB.1 us2 hac]
      have hl := TermPtrRts.labsIn_pubVR (G := fun l => (EgK Eg c).pfr l ≠ none ∨ (EgK Eg c).box l ≠ none)
        (substTs ts.reverse 0 0 d.argTy) (vinsL 0 (us.map (ev ρ)) ρ) (Cut (EgK Eg c) c.ths.size (fun _ => False))
        (substTs ts.reverse 0 0 d.argTy) (ws.map (TermSpawn.bumpW par.vs.vRelSt)) (fun _ _ _ h => h)
        (fun l f h => Or.inl (by intro h2; change Eg.pfr l = some f at h; change Eg.pfr l = none at h2; rw [h] at h2; cases h2))
        (fun l B h => Or.inr (by intro h2; change Eg.box l = some B at h; change Eg.box l = none at h2; rw [h] at h2; cases h2))
        rfl hwc hLayB.2.2.2.1 (VRR_VR (substTs ts.reverse 0 0 d.argTy) (RLink_of (Coh_CE (Cut (EgK Eg c) c.ths.size (fun _ => False))) (CohR_CE (Cut (EgK Eg c) c.ths.size (fun _ => False)))) hvKb)
      refine ⟨?_, fun fr hfr => by rw [hK.stack] at hfr; cases hfr⟩
      intro x0 rt1 ws1 hm w hw l hnm
      rw [hK.env] at hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨-, rfl, rfl⟩ := hm
      obtain ⟨a0, g, hva, rfl⟩ := hnm
      exact hl w hw a0 g hva
    -- the split
    have hRle : ∀ key, R key ≤ Tot i key := fun key => by
      have h1 := hle key
      have h2 := congrFun hsum key
      simp only [Res.add_apply] at h1 h2; omega
    have hno1 := noOwnIn_subS hs2 _ hno
    rw [noOwnIn_substTs_instT] at hno1
    have hRown : ∀ l, R (.own l) = 0 := fun l =>
      TermBlkZ.VRR_own_zero l _ _ _ _ _ _ R hno1 (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h) hvK
    -- the parent
    have hcxr : c1.ret = cx.ret := by rw [bind_ret hb, handOffR_ret, use_ret hu]
    have hs1L : η.sto L = some ⟨.unit, none⟩ := by rw [← CE_sto, hCE]; exact (hbx S).1
    have hp1L : η.pfr L = some 0 := by rw [← CE_pfr, hCE]; exact (hbx S).2
    have hvr0 : VRR ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] .zero :=
      ⟨⟨L, ⟨.unit, none⟩, rfl, hs1L, rfl, 0, hp1L, .inr fun _ _ => Nat.zero_le _⟩, rfl⟩
    have hRr : Rr ≤ (fun key => Rf key - R key) := fun key => by
      have h1 : R key + Rr key ≤ Rf key := hle key
      show Rr key ≤ Rf key - R key
      omega
    have hi2 := handOff_FInvR true T (FInvR_mono hi1 hRr)
    rw [if_pos rfl] at hi2
    have hf := bindRZ hb hi2 (RLink_of hEO.2.1 hEO.2.2) hvr0 hl0
    have hParRE : ThInvRE p (Cut Eg i S) par (fun key => Tot i key - R key) := by
      refine ⟨ρ, η, c1, fun key => Rf key - R key, Rs, hCE, hEO, ⟨by rw [hpt]; exact he, by rw [hpt]; exact hck⟩,
        htv1, by rw [hps, hpk, hpe]; exact hf, ?_, ?_, by rw [hpt, hps]; exact hDy.letW hterm rfl⟩
      · funext key
        have h1 : R key + Rr key ≤ Rf key := hle key
        have h2 : Rf key + Rs key = Tot i key := congrFun hsum key
        show Rf key - R key + Rs key = Tot i key - R key
        omega
      · intro fr rest hst ws2
        rw [hpk] at hst
        rw [hcxr, hps]; exact hpw fr rest hst ws2
    have hParE : ThInvE p (Cut Eg i S) par := by
      obtain ⟨ρ2, η2, cx2, hCE2, hE2, hT2b, htv2, hi2b, hpw2, hDy2⟩ := hE
      have hT3 := hT2b.2
      rw [hterm] at hT3
      obtain ⟨c2, -, hop2, he2, hck2, -⟩ := TermA4.CkW_let hT3
      have htv3 := OpT_TvOK hPT hop2 htv2
      cases hop2 with
      | spawnI _ _ hu2 _ _ _ _ _ _ _ _ _ hb2 =>
        have hs1b : η2.sto L = some ⟨.unit, none⟩ := by rw [← CE_sto, hCE2]; exact (hbx S).1
        have hp1b : η2.pfr L = some 0 := by rw [← CE_pfr, hCE2]; exact (hbx S).2
        have hvrb : VR ρ2 η2 .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] :=
          ⟨L, ⟨.unit, none⟩, rfl, hs1b, rfl, 0, hp1b, .inr fun _ _ => Nat.zero_le _⟩
        have hF := handOff_FInv true T (use_FInv hu2 hi2b).1
        rw [if_pos rfl] at hF
        refine ⟨ρ2, η2, c2, hCE2, hE2, ⟨by rw [hpt]; exact he2, by rw [hpt]; exact hck2⟩, htv3,
          by rw [hps, hpe, hpk]; exact bind_FInv hb2 hF hvrb hl0, ?_, by rw [hpt, hps]; exact hDy2.letW hterm rfl⟩
        show RetPw par.σs par.stack c2.ret
        rw [bind_ret hb2, handOffR_ret, use_ret hu2, hps, hpk]; exact hpw2
    have hPar : ThSys p (gOf p k arch c i) (spawnT c i par kid).mem (spawnT c i par kid).pairs par (EgK Eg c)
        (fun key => Tot i key - R key) (HP i) HS (cr i) (db i) := by
      refine (thSys_EgK (g := gOf p k arch c i) (c := c) (show i ≠ c.ths.size from Nat.ne_of_lt hi)).2 ?_
      have hs := stOf_par (mem := c.mem) (pairs := c.pairs) hnp hpar
      refine ⟨S, hParRE, hParE, ?_, ?_, ?_, ?_⟩
      · show MemInv _ _ (stOf c.mem c.pairs par)
        rw [hs]; exact MemInv_fenceG _ hM
      · show MemHeldP _ (stOf c.mem c.pairs par) (HP i)
        rw [hs]; exact hP
      · show MemHeldS _ (stOf c.mem c.pairs par) HS
        rw [hs]; exact hS
      · intro tw htw
        simp [stOf, hpar.2.1] at htw
    exact ⟨R, hRle, hRown, hPar, hKid, fun _ => hLbl⟩

end TermSpawnI

#print axioms TermSpawnI.spawnI_sites
#print axioms TermSpawnI.sysInvN_spawnMidI
#print axioms TermSpawnI.entryR_ofRI
#print axioms TermSpawnI.thSys_kidMR
