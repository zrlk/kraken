import WeakCore.TermSpawnMidKid
import WeakCore.TermSpawnMidGlob
import WeakCore.TermSpawnGlobM
import WeakCore.TermSpawnRunX
import WeakCore.TermFreshUSpawn
/-!
# TermSpawnMidAsm — `sysInvN_spawnMid`: `SysInvN` across a mid-run spawn

Sorry-free assembly of the clause lemmas of `TermSpawnMid*` and of `TermSpawnKidMem`, `TermSpawnGlobM`,
`TermSpawnRunX`.  On the pre-M0 base the stripe width `gOf`/`freshLabel` read is `c.ths.size`, which
the spawn changes; every stride-dependent fact therefore enters as a hypothesis **at the post-spawn
stride** `(spawnT c i par kid).ths.size` (tagged [M0]).  None is contradictory on the pre-M0 base (each is a
statement about the old configuration at a different width).  On the M0 base (`gOf`/`freshLabel` read
`c.n`, `(spawnT …).n = c.n`) each [M0] hypothesis is the corresponding `SysInvN`/freshU/OpT fact of
the pre-state, by `rw [spawnT_n]`:
* `hThrS` ← `hN.thr`;  `hParTy` ← the OpT.spawn continuation typing (at `gOf c i`);
* `hFrS` ← `hN.fresh`; `hOwnFS` ← `hN.ownF`; `hT` ← identity (`TgtOK` reads only `c.lbase`/`c.n`);
* `hU`/`hOwnU` ← freshU at the unborn stripe `c.ths.size < c.n`.
Non-[M0] hypotheses are the step's shape (`hpar`/`hPenv`/`hK`, by rfl from `spawnCfg`, see
`TermSpawnMidBridge`) and the typing rule's content (`hKE`, `hArg`; the type transport at `T`).
-/
namespace TermSpawnMid
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn TermSpawnGlobM
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem sysInvN_spawnMid {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th par kid : TTh} {f : String} {ts : List Ty} {t : Ty} {ws : List Word}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hth : c.ths[i]? = some th) (hnp : th.promises = [])
    -- the step's shape (the `spawnPar`/`spawnKid`, `TermSpawnMidBridge`)
    (hpar : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs)
    (hPenv : ∃ (x : String) (w0 : Word), par.env = (x, .tid, [w0]) :: th.env ∧ par.stack = th.stack ∧
      ∀ w ∈ TermPtrRts.pubWords .tid [w0], ∀ l, TermPtrRts.Names l w → Eg.pfr l ≠ none ∨ Eg.box l ≠ none)
    -- (E2) the parent keeps its box, the kid's is published (`TermBox`)
    (hTBp : TidBox Eg par) (hTBk : TidBox Eg kid)
    (hK : KidShape par kid f ts t ws)
    -- the typing rule's content (OpT.spawn; the argument at the bound type `t := T`)
    (hKE : KidEntryOK p t f ts)
    (hArg : ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      VR (fun _ => 0) (Cut Eg i S) t (shp t) ws ∧ Lay [] t t ws)
    -- [M0] stride facts at the post-spawn width
    (hThrS : ∀ j tj, c.ths[j]? = some tj →
      ThSys p (gOf p k arch (spawnT c i par kid) j) c.mem c.pairs tj Eg (Tot j) (HP j) HS (cr j) (db j))
    (hParTy : ∀ S, ThSysAt p (gOf p k arch (spawnT c i par kid) i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      ThInvRE p (Cut Eg i S) par (Tot i) ∧ ThInvE p (Cut Eg i S) par)
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
    SysInvN p k arch Init MintOK (spawnT c i par kid) (EgK Eg c) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS
        (extZT cr c.ths.size) (extZT db c.ths.size) ∧
      OwnLive (EgK Eg c) (spawnT c i par kid) ∧ ObsAll (EgK Eg c) (spawnT c i par kid) := by
  obtain ⟨hv, hpp, hna, hun⟩ := hpar
  have hkp : kid.promises = [] := hK.promises
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  have hpp' : par.promises = th.promises := by rw [hpp, hnp]
  obtain ⟨r, hchk, htv⟩ := hKE.chk
  have E := easy_spawnT (par := par) (kid := kid) (i := i) hN
  obtain ⟨eClo, eCmg, eShty, eRle, eZw, eBn, eBpv, eBfl, eBft, ePay, eBst, eNI, eUa, eUl, eMw, eSl, eSw⟩ := E
  -- the parent's and the kid's labels (for `ptrGL`)
  have hLbl : k.storeDepRts = true →
      TermPtrRts.ThLbl (EgK Eg c) par ∧ TermPtrRts.ThLbl (EgK Eg c) kid := by
    intro hk
    obtain ⟨x, w0, he, hs, hw0⟩ := hPenv
    refine ⟨thLbl_par (hN.ptrGL hk).2.1 hth he hs hw0, ?_⟩
    obtain ⟨S, hRE, hE, hM, hP, hS, hC⟩ := hN.thr i th hth
    obtain ⟨hvr, hlay⟩ := hArg S ⟨hRE, hE, hM, hP, hS, hC⟩
    have hSL : SeenLE (Cut Eg i S) par.vs.vRelSt := by
      rw [hv]; exact (MemInv_fenceG .sy hM).2.2.2.2.1
    exact thLbl_kid (p := p) hK hKE.aff hKE.drf hvr hlay hSL
  have hOwnF : OwnFreshZ (spawnT c i par kid) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS (extZT cr c.ths.size) := by
    intro q thq j hq hj
    have key : (∀ n, n < c.ths.size → (Tot n + HP n + pSumAt c n (cr n))
          (.own (freshLabel c.lbase (spawnT c i par kid).n q j)) = 0) ∧
        HS (.own (freshLabel c.lbase (spawnT c i par kid).n q j)) = 0 := by
      rcases spawnT_get_cases hi hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hq'⟩
      · exact hOwnFS q th j hth (by rw [← hna]; exact hj)
      · exact hOwnU j
      · exact hOwnFS q thq j hq' hj
    exact ⟨ownZ_spawnT hth hpp' hkp key.1, key.2⟩
  refine ⟨{
    thr := thr_spawnT (rt := t) hN hOL hObs hth hnp ⟨hv, hpp, hna, hun⟩ hK hKE.aff hKE.tb hKE.drf hKE.tsArg
      hKE.wrap hchk htv hArg hU hThrS hParTy
    held := memHeldG_spawnT hth hnp hpp hkp hN.held
    clo := eClo
    cmg := eCmg
    shty := eShty
    proms := proms_spawnT hth hnp hpp hkp hN.proms
    fpok := fpok_spawnT hth hpp hkp hOL hN.plt hN.fpok
    fresh := fresh_spawnT hth hnp hpp hkp hna hFrS hU
    bal := bal_spawnT hth hpp' hkp hN.bal
    knet := fun key hk => keyNet_spawnT hth hpp' hkp (hN.knet key hk)
    bf := bf_spawnT hN.bf
    boxtop := boxTop_spawnT hOL hth hnp hpp hkp hN.boxtop
    disj := disj_spawnT hth hpp hkp hN.disj
    fpfree := fpfree_spawnT hth hpp hkp hN.fpfree
    plt := plt_spawnT hth hpp hkp hN.plt
    vwr := vwr_spawnT hth hv hK hN.vwr
    frle := frle_spawnT hN.frle
    rle := eRle
    zwIni := eZw
    predHold := predHold_spawnT hOL hth hnp hpp hkp hN.predHold
    bnamed := eBn
    rid := by obtain ⟨rc, h⟩ := hN.rid; exact ⟨rc, ridOK_spawnT hth hpp' hkp h⟩
    promIni := promIni_spawnT hth hpp hkp hN.promIni
    promTy := promTy_spawnT hth hpp hkp hN.promTy
    promNU := promNU_spawnT hth hpp hkp hN.promNU
    ownF := hOwnF
    promNoTwo := promNoTwo_spawnT hth hpp hkp hN.promNoTwo
    undefAt := eUa
    ownKeyOwn := ownKeyOwn_spawnT hN hth
    ownPub := ownPub_spawnT hN hth
    boxPV := eBpv
    boxFrOwn := boxFrOwn_spawnT hN hOL hth (Nat.le_of_eq (vWr_par hv).symm)
    boxFrLe := eBfl
    vwrLt := vwr_spawnT hth hv hK hN.vwrLt
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
    ptrGL := fun hk => ptrGL_spawnT hOL hth hnp hpp hkp (hN.ptrGL hk) (hLbl hk).1 (hLbl hk).2
    granW := granW_spawnT hN hth
    stoLay := eSl
    boxPlantSep := fun hk => boxPlantSep_spawnT hOL hth hnp hpp hkp (hN.boxPlantSep hk)
    fgnCnt := fun hk => fgnCnt_spawnT hth hpp hkp (hN.fgnCnt hk) hT
    pool := pool_spawnT hOL hth hnp hpp hkp hN.pool
    plantIdx := fun hk => plantIdx_spawnT hOL hth hnp hpp hkp (hN.plantIdx hk)
    cfgCoh := cfgCoh_spawnT hth hv hK hN.cfgCoh
    stoW := eSw
    freshU := TermFreshU.freshU_spawnT hth hpp' hkp hFU
    tidBox := by
      intro j tj hj
      rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hj'⟩
      · exact hTBp
      · exact hTBk
      · exact hN.tidBox j tj hj' }, TermSpawnRunX.ownLive_spawnT hOL, TermSpawnRunX.obsAll_spawnT hObs⟩

end TermSpawnMid

#print axioms TermSpawnMid.sysInvN_spawnMid
