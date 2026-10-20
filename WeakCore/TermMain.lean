import WeakCore.TermFgnClos
import WeakCore.TermRiniCohW
import WeakCore.TermOwnCMain
import WeakCore.TermCellOwn
import WeakCore.TermPubCons
import WeakCore.TermPredHoldP
import WeakCore.TermPredStoreFree
import WeakCore.TermPredHoldW
import WeakCore.TermPlantWin
import WeakCore.TermZwIniP
import WeakCore.TermInterf
import WeakCore.TermPlantFrz
import WeakCore.TermBal
import WeakCore.TermInit
import WeakCore.TermFreshU
import WeakCore.TermDwf
import WeakCore.TermWdCover
import WeakCore.TermIall
import WeakCore.TermK5Z
import WeakCore.TermBufPubT
import WeakCore.TermRunLocK
import WeakCore.TermBiiF
import WeakCore.TermNoHold
import WeakCore.TermPlantF
import WeakCore.TermPlantS
import WeakCore.TermPlantP
import WeakCore.TermStoreNI
import WeakCore.TermPromNU
import WeakCore.TermSeenHid
import WeakCore.TermShty
import WeakCore.TermOwnFresh
import WeakCore.TermOwnNet
import WeakCore.TermCohLe
import WeakCore.TermCertScope
import WeakCore.TermRmw
import WeakCore.TermPinBIOf
import WeakCore.TermWin
import WeakCore.TermB5
import WeakCore.TermPromPred
import WeakCore.TermStepPred
import WeakCore.TermPlantW2
import WeakCore.TermPlantH
import WeakCore.TermPromStep
import WeakCore.TermMsgWords
import WeakCore.TermBNamed
import WeakCore.TermBoxOwn
import WeakCore.TermVwrLt
import WeakCore.TermBoxPV
import WeakCore.TermRunPay
import WeakCore.TermBiiT
import WeakCore.TermRunPayT
import WeakCore.TermRunLoc
import WeakCore.TermPtrStab
import WeakCore.TermUndefLowT
import WeakCore.TermPromAboveG
import WeakCore.TermPlantFul
import WeakCore.TermPlantOpG
import WeakCore.TermOwnCoh
import WeakCore.TermPromAlloc
import WeakCore.TermViewInvH
import WeakCore.TermUndefInv
import WeakCore.TermPlantHidOf
import WeakCore.TermOwnPub
import WeakCore.TermPlantPair
import WeakCore.TermPlantR1
import WeakCore.TermIniOpK
import WeakCore.TermFootBPK
import WeakCore.TermDBWire
import WeakCore.TermFgnCnt
import WeakCore.TermFulCntROf
import WeakCore.TermPlantAtB
import WeakCore.TermFootNCBOf
import WeakCore.TermWrSiteA
import WeakCore.TermPoolThread
import WeakCore.TermPoolResplit
import WeakCore.TermSelfPlantK
import WeakCore.TermHbiPOf
import WeakCore.TermFootBPKB
import WeakCore.TermOverCrA3
import WeakCore.TermPoolF1
import WeakCore.TermPoolTagOwn
import WeakCore.TermPoolBal
import WeakCore.TermPoolTagW
import WeakCore.TermHWbRWrap
import WeakCore.TermFgnNew
import WeakCore.TermStoreCrZE
import WeakCore.TermScopeWCk

/-!
# TermMain: a top-down skeleton of the first headline

Every proof obligation still open on the way from a machine run to the
first headline (stage B: token uniqueness at every
reachable configuration) is a field of `Obligations`.  Everything else is
wired from existing lemmas: `tstepMCF_step` (the stepping thread),
`tstepMC_promE` (the promise step), `Cut_self`/`Cut_withFp` (A-strict
exactness), `MemHeld_split`/`MemHeld_join`/`MemHeldG_of_S` (holdings), the
S8b bookkeeping lemmas (`PromsOK_thread`, `PromsDisj_thread`, ...,
`PromsOK_promise`, ..., `FrontierLe_gfoot`, `EFoot_post`), the EFoot `rini`
transport, `fpSync_self`, `threadSteps_upd`, `promise_inv`.

**The carried invariant is `SysInvN`, not `SysInvW`.**  `SysInvW`'s gross
per-key bounds (`tok`/`wd`/`own`) are not preserved by a promise step that
promises a `Give` at a visible word (the token is then counted by the
promiser's frame and by the shared holding, which reads word units promises
included).  `SysInvN` replaces them by the net form `KeyNet`; the gross form, hence
`SysInvW`, is recovered at every configuration without outstanding
promises (`SysInvN.toW`), in particular at every final one.
-/

namespace TermMain
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- `WrIniC` (`TermWrSiteA.wrIniC`), local to this file's proofs. -/
local instance instWrIniCMain : TermTyped.WrIniC := TermWrSiteA.wrIniC

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## RetPw side facts

The counted-word facts `TermStep`'s return-link carrier takes (`PwSkel`, `PwSubS`, `PwSig`),
discharged from `TermK2a`. -/

/-- Counted words read only the skeleton. -/
theorem pwSkel_ok : PwSkel := fun _ _ h ws => (TermK2a.pubWords_of_skel h).2.1 ws

/-- Subsumption keeps the counted words. -/
theorem pwSubS_ok : PwSubS := fun _ _ _ h σs c d ws => (TermK2a.pubWords_subS h σs c d).2.1 ws

/-- Counted words read only the signature. -/
theorem pwSig_ok : PwSig := TermK2a.pubWords_sig

/-! ## The obligations -/

/-- **Every open obligation of headline 1**, for runs from `c0`.  `plantOf`
is the (still to be fixed) choice of the A′ plant at a promise step.
Fields `T*` concern a thread step, `P*` a promise step. -/
structure Obligations (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop)
    (c0 : Cfg) (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop where
  /-- O0 the checker accepts the program (`progT` is `checkProg_sound`). -/
  checked : checkProg p = .ok ()
  /-- (D9) every block body passes `checkW` at its entry context (`ProgCkW`, from
  `ObligationsF.progScope`'s A1 part, `TermA4.progCkW_of_scopeW`). -/
  ckW : TermA4.ProgCkWC p
  /-- O2 (S10) the program passes the syntactic scope check: region-free interim
  (ProgScope), no `∀` in annotations (ProgIall), no ticket lock (D5 `NoTicket`); `scope`,
  `iall`, `noTicket`, `residualNoTicket` follow (TermScope/TermIall). -/
  progScope : TermScope.ProgScopeOK p = true
  /-- O3 (S10) the initial configuration satisfies the scope run invariant
  (`TermInit.runDRF_spawn` for the spawn shape). -/
  runDRF0 : TermScope.RunScopeR p k arch Sp c0
  /-- T3a (`certified_promLoc` variant) an own promise at an initialised
  (real-count) **epoch-counter** word unit has a numeric predecessor (`TermNoHold.PromPredE`, the only
  case `storeCrZ` consumes; weakened from `TermDwf.PromPred`); with T3b gives `dwf` (TermPromPred).
  Route: `TermNoHold.promPredT` from `StepPredNum` (stage A, one step) and the run premise at the
  pre-step configuration. -/
  promPred : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TermNoHold.PromPredE (CE η) (stOf c.mem c.pairs th)
  /-- T3c (U3 fix b; the initial fact behind `Obligations.seenHid`, via `TermSeenHid.seenHid_of`
  with `MemInv`, `SysInvN.promNU`, scope and `SysInvN.undefAt`) the initial configuration's
  messages and frames have views at most their timestamps (`TermViewInv.ViewInv c0`; along the run
  `TermViewInv.envVR_of_run` gives `EnvVR`; `TermViewInv.viewInv_init` discharges it at an
  empty-memory, zero-view start).  The former `FrontW` conjunct is now the invariant clause
  `undefAt` (every protocol-word unit has its `undef` allocation placeholder, which the frontier
  hides; probed by UndefAt, 0 violations). -/
  seenFacts : TermViewInv.ViewInvR p k arch Sp c0
  /-- (T3) `StoreCrZ` at every thread step.  `ObligationsF.toObligations` assembles it from the
  `StoreNI` half (`TermStoreNI.storeNI_of` with `SeenHid`) and the leaf-payment half
  `StoreLeafPayAll` (`TermPiece.storeLeafPay_of`, premise-free; PIN-D1b option 3: the fulfilled
  promises' debits are paid from the stored value, so the former field `nonEpochFree` is gone).
  Under (H) the memory-count route (TermWdCover §"`StoreCrZ` under
  (H)", the former `storeCrZ_ofM`) fails: a designated debit's block part (`BlkDb`) may carry
  `wd n`. -/
  storeCrZH : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    StoreCrZ η cx (stOf c.mem c.pairs th) th
  /-- T5 (B4/F2′) `hwp`: `FlipOK` at a publish's cell. -/
  wp : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf c.mem c.pairs th) ad.label
  /-- T6 (NoHoldPub, F2′ step 3) `hwin`, at the step's typing with its memory invariant (`TermWin.winM_of`). -/
  win : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) → PubWinT (CE η) (stOf c.mem c.pairs th) th
  /-- T7 (switch, replaces `nvp`/`rf`) `plantFulfil`: an own-path op (`OwnOpT`) on a cell
  with a frontier fulfils, i.e. the step appends no message. -/
  plantFulfil : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TermPlant.OwnFrOp (CE η) cx th → r.1 = c.mem
  /-- T7b (switch, D3 `PlantOp` v3) the plant facts at the own frontier cell the op targets,
  at the credits plus the pool credits `cr i + pl i` (R4), for pool credits covering (`OverCrG`). -/
  plantOp : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {pl : Nat → Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TermOverCr.OverCrG Eg c (fun j t => cr j t + pl j t) → TermPlant.OwnFrOp (CE η) cx th → ∀ lab cl, (CE η).sto lab = some cl → cl.owner = some (CE η).tid →
      (CE η).pfr lab ≠ none → TermPlant.OpTgt th lab →
      TermPlant.PlantOp (gOf p k arch c i) c.mem c.pairs th (CE η) (fun t => cr i t + pl i t) (· = r) lab cl
  /-- T7c (switch, `BufInitHeld`) a `bufInit` at a frontier buffer (its slot being a
  predicted one, BH1, `TermPlantWin.bh1_of`, and each predicted unit's first write is the earliest own
  promise above the coherence view there, BH2′, `TermPredHoldW.bh2_of`, are proved): the slot's
  payment (BH3) — a theorem, `TermPinBIOf.bufInitHeld_of` (PIN-D1a). -/
  bufInitHeld : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    ∀ x b ia v e, th.term = .let_ x (.bufInit b ia v) e →
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∃ Sp, TermStep.MemHeldL (CE η) (stOf c.mem c.pairs th) (HP i + HS) Sp ∧
          TermPlant.SlotPayS (CE η) (stOf c.mem c.pairs th) Sp (cr i) (db i) ad.label)
  /-- T8 (run fact P1) `hrmw`, `NoPlantRMW`. -/
  rmw : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    NoPlantRMW (CE η) th
  /-- T18 (U3 R1) `GBoxNamed` after a thread step (NoFuture or noJunkR). -/
  bnamedT : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    GBoxNamed (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')
  /-- T19 (S9) `MintOK` is closed under a thread step's mint (with the trivial
  `MintOK`: `TermBal.mintClosedT_true`); used by `TermBal.balT_proof` (`δ = 0`). -/
  mintClosedT : TermBal.MintClosedT p k arch Sp Init MintOK c0
  /-- T20b1 (F2′) an own key is minted at one of the stepping
  thread's fresh labels (used by `TermBal.knetT_rid`, `δ = 0`). -/
  allocG : TermBal.AllocGT p k arch Sp Init MintOK c0
  /-- every thread's promises are duplicate-free at a reachable
  configuration (used by `TermBal.balT_D`/`knetT_D` via `CrShift_sum`). -/
  promNodup : TermBal.PromNodupR p k arch Sp c0
  /-- P1 (B4: PromTyOK + `certified_promWordNX`) `hwu` at the promiser. -/
  hwu : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S)
  /-- P1′ (U3, to be probed later) every predicted unit has a first write
  (`PredU ⇒ ∃ FirstW`), at the promiser. -/
  hfw : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)
  /-- P2 (S7d, PlantOK) the plant choice is admissible, and (ZwIni) its counts cover every planted
  buffer of inhabited zero-width elements (`TermZwIniP.plantN_zw`), and (PredHolder) its counts are
  held by the promiser (`TermPredHoldP.plantHeld_of`). -/
  plantSpec : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PlantSpec Eg (plantOf c Eg j a v w) j c.mem.size ∧
      TermZwIni.PlantZw Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) ∧
      TermPredHoldP.PlantHeld Eg c th j (plantOf c Eg j a v w) (plantN c Eg j a v w)
  /-- P3 (S7d, `ThInvMC_promise_plant` at the cut) the promiser's part when
  the promise plants (an outstanding pointer to its private cell). -/
  selfPlant : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w → (∃ l f, plantOf c Eg j a v w l = some f) →
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' ∧
        (∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop,
          ¬ WordUnit (Cut Eg j S) m.loc → cr' t = cr j t)

  /-- T16b/T16d (B3 residual) the stepper's promises at a cell a thread step newly shares are
  initialised and typed (`promTyAPost`/`promIniPost` are theorems, `TermPlantF.promTyAPost_of`). -/
  pubPromOK : TermPlantF.PubPromOKF p k arch Sp Init MintOK c0
  /-- P4b (B3 residual) the new promise at a label shared after the promise step is initialised
  and typed. -/
  promNewOK : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 plantOf plantN
  /-- P4b (B3 residual) the promiser's promises at a label the step plants are initialised and
  typed (`promTyAPostP`/`promIniPostP` are theorems, `TermPlantF.promTyAPostP_of`). -/
  plantPromOK : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 plantOf plantN
  /-- T17 (`TermPlantF.noBoxProm_of`) the run premise along the certificate from a thread
  step's successor (scope and `NoHoldPub`); `noBoxProm` is a theorem. -/
  certRunT : TermPlantF.CertRunT p k arch Sp Init MintOK c0
  /-- P4–P7 the run premise of `certified_promLoc` (scope and `NoHoldPub` along the certificate of
  every reachable promise step); `promLoc` is `TermNoHold.promLocF_of`. -/
  certRun : TermNoHold.CertRunP p k arch Sp Init MintOK c0
  /-- P4b (plant) the planted cell's type meets `PubCpl`. -/
  plantCpl : PlantCplF p k arch Sp Init MintOK c0 plantOf
  /-- P4b (plant) the planted cell's initialised words are hidden below its frontier. -/
  plantHid : PlantHidF p k arch Sp Init MintOK c0 plantOf plantN
  /-- T16b (B2 at every offset, B5) a new message at another thread's cell is typed at the step's witness. -/
  newForeignTyped : NewForeignTypedF p k arch Sp Init MintOK c0
  /-- T16b (B5) new messages in another thread's two-word unit come as recorded pairs. -/
  newPair : NewPairF p k arch Sp Init MintOK c0
  /-- T16b (B4 PromTyOK (c) in `TwoAtT` form at the new configuration) no promise at a shared cell in a two-word unit. -/
  promNoTwoPost : PromNoTwoPostF p k arch Sp Init MintOK c0
  /-- T16b-9d at a cell the step newly shares, the stepper's coherence is at most its new `vWr`. -/
  ownCohLe : OwnCohLeF p k arch Sp Init MintOK c0
  /-- P4b (B1) inhabitants at a planted cell's predicted slots (`certified_hinhW1`). -/
  plantInh : PlantInhF p k arch Sp Init MintOK c0 plantOf plantN
  /-- P4b (plant) pairs at a planted cell are typed for every reader. -/
  plantPair : PlantPairF p k arch Sp Init MintOK c0 plantOf plantN
  /-- (named; explorer-probed) at an allocation no outstanding promise of the allocator lies at the
  new label, nor names it from a `noOwnIn`/`rgnFree` cell (`TermPromClos.PromAllocF`; keeps the
  `SysInvN` clause `promClos`). -/
  promAlloc : TermPromClos.PromAllocF p k arch Sp Init MintOK c0
  /-- a promise step keeps the `SysInvN` clause `promClos` at the plant choice
  (`TermPromClos.promClos_prom`). -/
  promClosP : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PromClosG (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w)
  /-- (D-B) the plant choice plants only labels `TermPlantF.PlantL` admits, at frontier `plantF`
  (at the choice, `TermPlantF.plantOf_some`). -/
  plantL : ∀ {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {l : AllocLabel} {f : Ts}, c.ths[j]? = some th → plantOf c Eg j a v w l = some f →
    TermPlantF.PlantL c Eg j th a v w l ∧ f = plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l
  /-- a thread step keeps the clause `plantIdx` (`TermPlantAtB.plantIdxT_of`), given the step's
  frontier tag at `publish` (`PfrG`) and its consume of the published own key (`PubConsumeC`). -/
  plantIdxT : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    (∀ t l, crS t (.own l) = cr i t (.own l)) →
    MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    TermPtrKey.PubConsumeC th C → k.storeDepRts = true →
    TermPlantAtT.PlantIdxG TermPtrRts.tminG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c'
  /-- a promise step keeps the clause `plantIdx` at the plant choice (`TermPlantAtB.plantIdxP_of`),
  from the promiser's accounting, its `ThSys` after the step and the post-step `PtrRtsG`. -/
  plantIdxP : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' →
    ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
      (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' →
    k.storeDepRts = true →
    TermPtrRts.PtrRtsGL (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) Tot (upd HP j HP')
      (promise c j a v w) →
    TermPtrRts.BoxPlantSep (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) Tot (upd HP j HP')
      (promise c j a v w) →
    TermPlantAtT.PlantIdxG TermPtrRts.tminG (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) Tot (upd HP j HP')
      (promise c j a v w)

/-! ## The fields discharged by S10/S11 (TermScope, TermDwf, TermIall, TermInit)

Each is a theorem of the removed field's type, so the wiring reads `O.<field>` unchanged. -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- O0 the program is well formed. -/
theorem Obligations.progT (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ProgT p :=
  TermScope.progT_of_check O.checked

/-- (P1) every declared return type is `∀`-free at value positions (from the
scope check's `drf d.retTy`). -/
theorem Obligations.retIall (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ProgRetIall p :=
  ⟨fun _ hd => TermScope.noIallV_of_drf _ (TermScope.ProgScopeOK.decl O.progScope hd).2.1⟩

/-- P4–P7 (`TermNoHold.promLocF_of`) a promise lies in the promiser's cut or at one of its labels yet
to allocate. -/
theorem Obligations.promLoc (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : PromLocF p k arch Sp Init MintOK c0 :=
  haveI := O.retIall
  TermNoHold.promLocF_of (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRun

/-- T17 (`TermPlantF.noBoxProm_of`) a stepper keeps no promise at a box it created. -/
theorem Obligations.noBoxProm (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    NoBoxPromF p k arch Sp Init MintOK c0 :=
  haveI := O.retIall
  TermPlantF.noBoxProm_of (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRunT

/-- P4b (`TermPlantF.promNoTwoP_of`) the promised address is in no two-word unit. -/
theorem Obligations.promNoTwoP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    PromNoTwoPF p k arch Sp Init MintOK c0 :=
  haveI := O.retIall
  TermPlantF.promNoTwoP_of (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRun

/-- T16b (B3, `TermPlantF.promTyAPost_of`) PromTyOK (a) after a thread step. -/
theorem Obligations.promTyAPost (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    PromTyAPostF p k arch Sp Init MintOK c0 :=
  TermPlantF.promTyAPost_of O.pubPromOK

/-- T16d (B3, `TermPlantF.promIniPost_of`) PromTyOK (a0) after a thread step. -/
theorem Obligations.promIniPost (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    PromIniPostF p k arch Sp Init MintOK c0 :=
  TermPlantF.promIniPost_of O.pubPromOK

/-- P4b (B3, `TermPlantF.promTyAPostP_of`) PromTyOK (a) after a promise step. -/
theorem Obligations.promTyAPostP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN :=
  TermPlantF.promTyAPostP_of (fun X => (O.plantSpec X).1) O.promNewOK O.plantPromOK

/-- P4b (B3, `TermPlantF.promIniPostP_of`) PromTyOK (a0) after a promise step. -/
theorem Obligations.promIniPostP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    PromIniPostPF p k arch Sp Init MintOK c0 plantOf plantN :=
  TermPlantF.promIniPostP_of (fun X => (O.plantSpec X).1) O.promNewOK O.plantPromOK

/-- T16d (B3) PromTyOK (a0) at a reachable configuration: the SysInvN clause. -/
theorem Obligations.promTyA0 (_O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    PromTyA0F p k arch Sp Init MintOK c0 :=
  fun _ h => h.promIni

/-- T1 (S10) the stepper's term is in scope. -/
theorem Obligations.scope (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    StepScope cx th.term ∨ StepScopeR th.σs cx th.term :=
  TermScope.scope_of O.progScope O.runDRF0

/-- T3c **`SeenHid` at every reachable store** (`TermSeenHid.seenHid_of`: `MemInv` at the stepper's
cut, `SysInvN.promNU`, scope, and the named facts `seenFacts`). -/
theorem Obligations.seenHid (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TermStoreNI.SeenHid k arch (CE η) c.mem th :=
  fun X Y => TermSeenHid.seenHid_of X (fun Y' => O.scope X Y') (TermViewInv.envVR_of_run O.seenFacts X.run X.hth)
    ⟨congrArg TEnv.sto Y.1, congrArg TEnv.pfr Y.1, congrArg TEnv.ini Y.1, congrArg TEnv.rini Y.1,
      congrArg TEnv.tid Y.1⟩ (TermUndefInv.undefAt_cut X.inv.undefAt (congrArg TEnv.sto Y.1))

/-- T2 (option ii) the stored cell's components are `IallOK`. -/
theorem Obligations.iall (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    StoreIall ρ η cx th :=
  TermIall.iall_of O.progScope O.runDRF0

/-- (switch) A deeply region- and `∀`-free type is deeply `∀`-free. -/
theorem niDeep_of_drf : ∀ t : Ty, TermScope.drf t = true → TermPlant.niDeep t = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro h; simp only [TermScope.drf, TermPlant.niDeep, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | sum a b iha ihb =>
    intro h; simp only [TermScope.drf, TermPlant.niDeep, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | code a b iha ihb =>
    intro h; simp only [TermScope.drf, TermPlant.niDeep, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | array i t ih => intro h; exact ih h
  | ptr μ t ih => intro h; simp only [TermScope.drf, TermPlant.niDeep, Bool.and_eq_true] at h ⊢; exact ih h.2
  | ptrOpt μ t ih => intro h; simp only [TermScope.drf, TermPlant.niDeep, Bool.and_eq_true] at h ⊢; exact ih h.2
  | loc μ t ih => intro h; simp only [TermScope.drf, TermPlant.niDeep, Bool.and_eq_true] at h ⊢; exact ih h.2
  | mu t ih => intro h; exact ih h
  | tex κ t ih => intro h; exact ih h
  | iex t ih => intro h; exact ih h
  | refine t ψ ih => intro h; exact ih h
  | iall t _ => intro h; simp [TermScope.drf] at h
  | _ => intro _; rfl

/-- (switch) The op's address atom is free in the term. -/
theorem opAtom_free {e : Expr} {q : At} {y : String} (h : TermPlant.opAtom e = some q)
    (hy : TermScope.freeA y q = true) : TermScope.freeB y e = true := by
  unfold TermPlant.opAtom at h
  split at h <;> (try simp at h) <;> (subst h; exact TermScope.free_let_op (by simp [TermScope.opAts]) hy)

/-- (switch, replaces `XchgIall`) **`OpNI`** at every reachable thread step of a program
passing `ProgScopeOK`, from a `RunScope` configuration (as `TermIall.iall_of`). -/
theorem opNI_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hp : TermScope.ProgScopeOK p = true) (h0 : TermScope.RunScopeR p k arch Sp c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TermPlant.OpNI cx th := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y q t hq hpk
  have h := TermScope.run_drf hp h0 X.run i th X.hth
  exact niDeep_of_drf t (TermScope.peek_drf Y.2.2.2.2.2.1 hpk (fun y hy => h.env y (opAtom_free hq hy)))

/-- (switch) `OpNI` from the obligations. -/
theorem Obligations.opNI (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TermPlant.OpNI cx th :=
  opNI_of O.progScope O.runDRF0

/-- T3 (route c′) own promises fulfilled by a plain pub store carry no unbalanced credit. -/
theorem Obligations.dwf (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    StoreCrZ η cx (stOf c.mem c.pairs th) th :=
  O.storeCrZH

/-- T20d (D5) a ticket-free program reaches only ticket-free terms. -/
theorem Obligations.residualNoTicket (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    TermBal.ResidualNoTicket p k arch Sp c0 :=
  TermScope.residualNoTicket_of O.progScope O.runDRF0

/-- O1 (D5) the program uses no `claim`/`mkTicket`. -/
theorem Obligations.noTicket (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : TermBal.NoTicket p = true :=
  TermScope.noTicket_of O.progScope

end

/-! ## The fields discharged by S8c (`TermInterf`)

Each is a theorem of the removed field's type, so the wiring below reads `O.<field>`
unchanged. -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (S8c, proved in `TermInterf`) T14 (S8b A1, the `hv` of `fpok_of`) after a thread step no thread's
  promise lies at another thread's private cell. -/
theorem Obligations.fpokVisT (_O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ (j j' : Nat) (thj thj' : TTh) (t : Ts) (m : Msg) (S' : AllocLabel → Prop), j ≠ j' → c'.ths[j]? = some thj →
      c'.ths[j']? = some thj' → t ∈ thj'.promises → c'.mem[t]? = some m → Vis (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') m.loc.label :=
  fpokVisT_holds

/-- (S8c, proved in `TermInterf`) T15 (S8b) global freshness after a thread step. -/
theorem Obligations.freshT (_O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj, c'.ths[j]? = some thj → ∀ m, thj.nalloc ≤ m →
      GFreshL (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' thj (freshLabel c'.lbase c'.n j m) :=
  freshT_holds

/-- (S8c, proved in `TermInterf`) T16a (S8c, frame part: `Cut_other` + `FInvR_ext`) an idle thread's
  frame invariants move to the new cut. -/
theorem Obligations.interfFrameT (_O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      ThInvRE p (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) thj (Tot j) ∧ ThInvE p (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) thj :=
  interfFrameT_holds

/-- (S8c, proved in `TermInterf`) T16b (S8c core, TermInterf `interf_thread`, per `MemInv` clause; uses
  `stepper_facts` B1–B5) an idle thread's `MemInv` after the step. -/
theorem Obligations.interfMemT (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      MemInv (gOf p k arch c j) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) :=
  interfMemT_of_clauses (cl1_memOKP O.promTyAPost) (cl2_ownOKPF riniFoot_holds O.newForeignTyped O.newPair) cl3_promLt cl4_freshLP cl5_seenLE
    (cl6_ownHidP riniFoot_holds) (cl7_pubDefP (TermPlantFrz.plantFrozenF_of TermPlantFrz.plantFrozenPub_holds) O.scope pubFrontier_holds O.promTyAPost)
    (cl8_ownPubV riniFoot_holds) (cl9_of_parts cl9a_seenOwn cl9b_inh cl9c_pubCpl (cl9d_pubPair O.promNoTwoPost (pairStepper_holds O.newPair O.ownCohLe (TermPlantFrz.plantFrozenF_of TermPlantFrz.plantFrozenPub_holds) O.promNoTwoPost)) cl9e_pubLive)
    (cl10_boxInv O.noBoxProm) cl11_promOK

/-- (S8c, proved in `TermInterf`) T16c (S8c, footprint B1) an idle thread's private holding is untouched. -/
theorem Obligations.interfHPT (_O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      MemHeldP (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) (HP j) :=
  interfHPT_holds

/-- (S8c, proved in `TermInterf`) T17 (S8c) box words stay latest below their frontiers. -/
theorem Obligations.boxtopT (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    BoxTopG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' :=
  boxtopT_holds O.noBoxProm

/-- (S8c, proved in `TermInterf`) P4a (S8c, frame part) idle threads' frames move to the planted cut. -/
theorem Obligations.interfFrameP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      ThInvRE p (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) thj (Tot j') ∧ ThInvE p (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) thj :=
  interfFrameP_holds (fun X => (O.plantSpec X).1)

/-- (S8c, proved in `TermInterf`) P4b (S8c core, TermInterf `interf_prom`: the new message typed in every
  cut, `certified_promWordNX`, no pair promise, the plant) idle threads'
  `MemInv` after a promise step. -/
theorem Obligations.interfMemP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      MemInv (gOf p k arch c j') (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj) :=
  interfMemP_of_clauses
    (pcl1_memOKP (fun X => (O.plantSpec X).1) O.promLoc O.promTyAPostP)
    (pcl2_ownOKPF (fun X => (O.plantSpec X).1) O.promLoc O.promTyAPostP O.promNoTwoP) (pcl3_promLt (plantOf := plantOf) (plantN := plantN))
    (pcl4_freshLP (fun X => (O.plantSpec X).1) O.promLoc) (pcl5_seenLE (fun X => (O.plantSpec X).1))
    (pcl6_ownHidP (fun X => (O.plantSpec X).1) O.promLoc O.promTyAPostP)
    (pcl7_pubDefP (fun X => (O.plantSpec X).1) O.promLoc O.promTyAPostP O.plantHid)
    (pcl8_ownPubV (fun X => (O.plantSpec X).1))
    (pcl9_of_parts (pcl9a_seenOwn (plantOf := plantOf) (plantN := plantN)) (pcl9b_inh (fun X => (O.plantSpec X).1) O.plantInh)
      (pcl9c_pubCpl (fun X => (O.plantSpec X).1) O.plantCpl) (pcl9d_pubPair (fun X => (O.plantSpec X).1) O.promNoTwoP O.plantPair)
      (pcl9e_pubLive (fun X => (O.plantSpec X).1)))
    (pcl10_boxInv (fun X => (O.plantSpec X).1) O.promLoc) (pcl11_promOK (plantOf := plantOf) (plantN := plantN))

/-- (S8c, proved in `TermInterf`) P4c idle threads' private holdings after a promise step. -/
theorem Obligations.interfHPP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      MemHeldP (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj) (HP j') :=
  interfHPP_holds (fun X => (O.plantSpec X).1) O.promLoc

/-- (S8c, proved in `TermInterf`) P5 (S8b A1, the `hv` of `fpok_of`) after a promise step no thread's
  promise lies at another thread's private cell (the plant makes a plant-pointer cell
  shared). -/
theorem Obligations.fpokVisP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (i i' : Nat) (thi thi' : TTh) (t : Ts) (m : Msg) (S : AllocLabel → Prop), i ≠ i' →
      (promise c j a v w).ths[i]? = some thi → (promise c j a v w).ths[i']? = some thi' → t ∈ thi'.promises →
      (promise c j a v w).mem[t]? = some m → Vis (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) i S) m.loc.label :=
  fpokVisP_holds O.promLoc

/-- (S8c, proved in `TermInterf`) P6 (S8b) freshness after a promise step. -/
theorem Obligations.freshP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ i thi, (promise c j a v w).ths[i]? = some thi → ∀ m, thi.nalloc ≤ m →
      GFreshL (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) thi
        (freshLabel (promise c j a v w).lbase (promise c j a v w).n i m) :=
  freshP_holds (fun X => (O.plantSpec X).1) O.promLoc

/-- (S8c, proved in `TermInterf`) P7 (S8c) box words after a promise step. -/
theorem Obligations.boxtopP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    BoxTopG (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) :=
  boxtopP_holds O.promLoc

/-- (S8c, proved in `TermInterf`) T16d′ idle threads' `PromCrK` after a thread step,
  credits shifted by `δ` (`interfCrTK_holds`: old credits by `interfCrT_mover`,
  plant credits by `PlantCr_mono`, `δ`-points by `CrShiftP`). -/
theorem Obligations.interfCrT (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    CrShiftP c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cr i δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      TermPlant.PromCrK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj)
        (fun t => cr j t + δ t) (db j) :=
  interfCrTK_holds O.promTyA0

/-- (S8c, proved in `TermInterf`) P4d′ idle threads' `PromCrK` after a promise step
  (`interfCrPK_holds`: the plant is inactive at foreign promises; plant credits
  by `PlantCr_mono`). -/
theorem Obligations.interfCrP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      TermPlant.PromCrK (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj)
        (cr j') (db j') :=
  interfCrPK_holds (fun X => (O.plantSpec X).1)

/-- (S8c, proved in `TermInterf`) P3′ the promiser's plant credits survive its own
  unplanted promise (`promSelfK_holds`: the new promise is above every window). -/
theorem Obligations.promSelfK (_O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w → (∀ l, plantOf c Eg j a v w l = none) →
    ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
    ∀ tw m, tw ∈ th.promises → c.mem[tw]? = some m →
      PlantCr (Cut Eg j S) (stOf c.mem c.pairs th) m tw (cr j tw) →
      PlantCr (Cut Eg j S) (promSt (stOf c.mem c.pairs th) a v w) m tw (cr j tw) :=
  promSelfK_holds

end

/-! ## Wiring: the thread step -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

theorem gOf_thread {c c' : Cfg} {i : Nat} (hc' : c' ∈ threadSteps p k arch c i) (j : Nat) :
    gOf p k arch c' j = gOf p k arch c j := by
  unfold gOf
  rw [TermStep.threadSteps_n hc', (threadSteps_lbase hc').1, (threadSteps_lbase hc').2]

/-- (route B) A footprint at a ghost `pf` gives the footprint at any `g` whose `pf` is
everywhere true (only `PfrG` reads `pf`). -/
theorem EFoot_unpf {g : G} {P : AllocLabel → Prop} {E E' : TEnv} {s s' : St}
    (h : EFoot { g with pf := P } E E' s s') (ht : ∀ l, g.pf l) : EFoot g E E' s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, fun l _ _ => ht l⟩
#print axioms TermMain.EFoot_unpf

/-- (route B) `MintStep` does not read `pf`. -/
theorem MintStep_unpf {g : G} {P : AllocLabel → Prop} {η : TEnv} {s s' : St} {C F : Res} :
    MintStep { g with pf := P } η s s' C F → MintStep g η s s' C F
  | .none => .none
  | .fresh => .fresh
  | .alloc h1 h2 => .alloc h1 h2
  | .consume μ ws => .consume μ ws
  | .epoch h1 h2 h3 h4 h5 h6 h7 h8 h9 => .epoch h1 h2 h3 h4 h5 h6 h7 h8 h9
  | .share h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => .share h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | .claim n j => .claim n j
  | .epoch2 h1 h2 h3 h4 h5 h6 h7 h8 h9 => .epoch2 h1 h2 h3 h4 h5 h6 h7 h8 h9
#print axioms TermMain.MintStep_unpf

/-- (R4, (A)) The credit-free part of `TOut` is antitone in the transfer, keywise. -/
theorem TOutC_mono {p : Prog} {g : G} {η : TEnv} {s : St} {r : Memory × List Ts × TTh} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' : Ts → Res} {Rf Rs H : Res} {cr db δ δ' : Ts → Res}
    (Z : TOutC p g η s r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db δ) (hle : ∀ t key, δ' t key ≤ δ t key) :
    TOutC p g η s r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db δ' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ⟨s1, s2⟩, Fd, hFd, hin, a12⟩ := Z
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9,
    ⟨fun t h => s1 t (TermPoolThread.ne_zero_of_key_le (hle t) h),
      fun t h => s2 t (TermPoolThread.ne_zero_of_key_le (hle t) h)⟩,
    Fd, fun t h => hFd t (TermPoolThread.ne_zero_of_key_le (hle t) h), hin, a12⟩
#print axioms TermMain.TOutC_mono

/-- (R4 (a‴)) **The stepper at `crS`** (`TermFootBPKB.tstepMCF_stepTKA_zfNBB`, shared by
`sysInv_threadR` and `TermSpawn.sysInvO_threadR`): credits `crS = crR cr pl i (QS ..) i`, cover bound
`cr₁ = cr i + pl i` (`crS_le`), `PromCrK` by `promCrK_R`, the `bufInit` slot pay by `slotPayS_mono`, the
pool premise by `hbiP_of`. -/
theorem stepAtCrS (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPI : TermPoolStaging.PoolInv Init MintOK c Eg Tot HP HS cr db pl)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hH : MemHeld (CE η) (stOf c.mem c.pairs th) (HP i + HS))
    (hC : TermPlant.PromCrK (CE η) (stOf c.mem c.pairs th) (cr i) (db i)) (hRP : RetPw th.σs th.stack cx.ret)
    (hpx : PAx (gOf p k arch c i) c.mem c.pairs th) (hn : 0 < (gOf p k arch c i).n) (hnd : isDone th = false)
    (hfo : FpOK (CE η) (stOf c.mem c.pairs th)) (hclo : ∀ lab cl, (CE η).sto lab = some cl → Clo cl.ty)
    (hown1 : PubLe1 th Rf Rs (HP i + HS)) (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    ∃ Tot' H' C F cr' db' Gd plh,
      TermPlant.ThInvMCFQK (fun E' => TermPlant.BiOut th E' ∧
          TermPlant.KeepQRSB (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) th
            (TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i) cr' plh ∧
          IniFixZ { ({ gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } : G) with
              zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) ∧ TermFootNC.FootNCE (CE η) E' r ∧
          TermFootBP0.FootBP { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } E' th r)
        p { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) (stOf c.mem c.pairs th)
        r.1 r.2.1 r.2.2 Tot' H' cr' db' ∧
      MintStep { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } η (stOf c.mem c.pairs th)
        (stOf r.1 r.2.1 r.2.2) C F ∧ TermStep.ClaimAtP th C F ∧
      TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd ∧
      Tot' + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf c.mem c.pairs th) (db i) + C +
          Res.sum (Gd.map TermPiece.GdE.R) + pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + (HP i + HS) + pSum (stOf c.mem c.pairs th)
          (TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i) + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (TermPiece.PubShape cx th → TermPiece.GdCovT (CE η) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
        (¬ TermPiece.PubShape cx th → Gd = []) := by
  obtain ⟨hCE, -, hE, hT, htv, hFI, hsum⟩ := id Y
  have h := X.inv
  have hth := X.hth
  haveI := O.retIall
  haveI := O.ckW
  have hleR : ∀ r' ∈ tstep { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } c.mem c.pairs th,
      r' = r → ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → t ∉ (stOf r'.1 r'.2.1 r'.2.2).promises →
      c.mem[t]? = some m → (∀ f mf, f ∈ FpAt (CE η) ⟨m.loc.label, 0⟩ → c.mem[f]? = some mf →
        mf.loc.label = m.loc.label → t < f) →
        cr i t + pl i t ≤ TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i t := by
    intro r' _ hok t m ht ht' hmt hg
    have ht2 : t ∉ r.2.2.promises := by rw [← hok]; exact ht'
    exact TermHbiPOf.crS_le hCE t m ht ht2 hmt hg
  have hCS : TermPlant.PromCrK (CE η) (stOf c.mem c.pairs th)
      (TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i) (db i) := by
    have hm0 := hm
    have hC0 := hC
    rw [hCE] at hm0 hC0 ⊢
    exact TermPoolResplit.promCrK_R hth hPI.tag hm0 (fun t ht => ht.2.2) hC0
  exact (TermFootBPKB.tstepMCF_stepTKA_zfNBB (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) (g := { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l })
    (cr₁ := fun t => cr i t + pl i t)
    (hPb := fun y a e rt ws ad h1 h2 h3 => ⟨y, a, e, rt, ws, ad, h1, h2, h3, rfl⟩) O.progT rfl hn hnd (O.scope X Y) hT.1 hT.2 hFI hE htv hm hH hpx hCS
    (O.iall X Y) (O.dwf X Y) (O.wp X Y) (O.win X Y hS hm) hfo (O.rmw X Y) h.bf (O.plantOp X Y hPI.cov) hleR (O.opNI X Y) hclo
    (fun x b ia v e hterm => ⟨TermPlantWin.bh1_of hterm hT.1 hFI hE htv hH X.hr (O.plantFulfil X Y)
      (by rw [hCE]; exact TermZwIniP.promIniE_cut h.promIni hth)
      (by rw [hCE]; exact TermZwIni.zwIniE_cut h.zwIni i S)
      (TermZwIniP.bufInit_notPubd h.ownPub hth hCE hsum hT.1 hFI (O.scope X Y) hterm),
      TermPredHoldW.bh2_of h.predHold h.promNU h.ownPub hth hCE hsum hT.1 hFI (O.scope X Y) hterm,
      fun rt w ad h1 h2 h3 => by
        obtain ⟨Sp, hL, hP⟩ := O.bufInitHeld X Y x b ia v e hterm rt w ad h1 h2 h3
        exact ⟨Sp, hL, TermPlant.slotPayS_mono (TermHbiPOf.crS_ge cr pl i _) hP⟩⟩) hRP
    (TermHbiPOf.hbiP_of hth hCE hPI.tag hC
      (fun x b ia v e hterm => TermPredHoldW.bufInit_ownNP h.ownPub hth hCE hsum hT.1 hFI (O.scope X Y) hterm)
      (O.bufInitHeld X Y))).2 r X.hr hpa ⟨O.plantFulfil X Y, rfl⟩
#print axioms TermMain.stepAtCrS

/-- (dedup) **The thread-step master** of `sysInv_threadR` and `TermSpawn.sysInvO_threadR`: the
post-step `SysInvN` at `EgT ..`, plus any property `Post` of the post-step environment that follows
from the step's context (`TCtx`, `EnvAt`, the stepper's `TOut` at `crS`, `hPub`, `PfrG`, `EFoot`). -/
theorem sysInv_threadRP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hFN : TermPoolThread.FgnNewT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hc' : c' ∈ threadSteps p k arch c i) (hcert : Certified p k arch c' i)
    {pl : Nat → Ts → Res} (hPI : TermPoolStaging.PoolInv Init MintOK c Eg Tot HP HS cr db pl)
    (Post : GEnv → Prop)
    (hPost : ∀ (th : TTh) (r : Memory × List Ts × TTh) S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ,
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
      EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs
        (HP i + HS) (TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i) (db i) δ →
      (∀ l, TermOwnG0Defs.PubAt th l → ∀ t,
        TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i t = cr i t) →
      PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
      ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) →
      Post (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c' Eg' Tot' HP' HS' cr' db' ∧ Post Eg' := by
  obtain ⟨th, r, hth, hr, e1, e2, e3, ho⟩ := threadSteps_upd hc'
  have X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r :=
    ⟨hrun, h, hth, hr, hc', e1, e2, e3, ho, hcert⟩
  obtain ⟨S, hS⟩ := h.thr i th hth
  obtain ⟨ρ, η0, cx, Rf, Rs, hCE0, htid0, hE0, hT, htv, hFI0, hsum, -, hm, hH, hC, hRP⟩ := ThSysAt.env h.clo hS
  -- (S10) repick the view above the rid counters, so that a fresh mint names an unused id
  obtain ⟨rc, hrc⟩ := hPI.rid
  obtain ⟨η, hce, htid1, hle0, -, hE, hFI, -, hwit⟩ := TermOnce.repick_fresh hE0 hFI0 rc
  replace hT : TypedK p η cx th.term := hT.wit hwit
  have hCE : CE η = Cut Eg i S := hce.trans hCE0
  have htid : η.tid = i := htid1.trans htid0
  have hle : rc i ≤ η.rid := by have h0 := hle0; rw [htid0] at h0; exact h0
  rw [← hce] at hm hH hC
  have Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs := ⟨hCE, htid, hE, hT, htv, hFI, hsum⟩
  have hfo : FpOK (CE η) (stOf c.mem c.pairs th) := by rw [hCE]; exact h.fpok i th S hth
  have hn : 0 < (gOf p k arch c i).n := by
    show 0 < c.n
    rcases Nat.lt_or_ge i c.ths.size with h1 | h1
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n h1)
    · simp [h1] at hth
  -- T9/T10/T11 are discharged here from certification and `tstep_done`.
  have hpa : PromAbove (stOf r.1 r.2.1 r.2.2) := by
    have h1 := TermTyped.certified_promAboveSt hcert e3
    rw [e1, e2] at h1
    exact h1
  have hnd : isDone th = false := by
    cases hd : isDone th
    · rfl
    · rw [tstep_done hd] at hr; simp at hr
  have hpx : PAx (gOf p k arch c i) c.mem c.pairs th := Or.inr ⟨r, hr, hpa⟩
  haveI := O.retIall
  haveI := O.ckW
  have hclo : ∀ lab cl, (CE η).sto lab = some cl → Clo cl.ty := fun lab cl hl => by
    rw [hCE] at hl; exact StoClo_Cut h.clo i S lab cl hl
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h1 | h1
    · exact h1
    · simp [h1] at hth
  have hown1 : PubLe1 th Rf Rs (HP i + HS) := PubLe1.of_le1 fun l => by
    have h1 := TermOwnNet.ownNet_one h l hi
    rw [← hsum] at h1
    simp only [Res.add_apply] at h1 ⊢
    omega
  -- (a‴) the stepper at `crS` (`stepAtCrS`)
  have hQ := TermHbiPOf.stepCrQ_of Eg c cr pl i S th r
  obtain ⟨Tot', H', C, F, cr', db', Gd, plh, ⟨E', ⟨hBiO1, hBiO2, hBiO3, hFNC, hFBP⟩, hFp, hSK, hBV, hRE, hm', hH', hC'⟩, hMS, hcl, hDr, hineq, ⟨hGc, hNP⟩⟩ :=
    TermMain.stepAtCrS O X Y hS hPI hm hH hC hRP hpx hn hnd hfo hclo hown1 hpa
  have hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) :=
    EFoot_unpf hFp fun _ => trivial
  -- (route B) for the `plantIdx_thread`: the step's consume at a `publish` (`PubCons`), and its
  -- frontier change only at the published label (`PfrG` at `pf := PubAt th`)
  have hPubC : PubCons th C := hcl.2
  have hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' := hFp.pfrG
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := hCE ▸ hF
  have hfr := h.gfresh hth r.2.2.nalloc
  have hself := Cut_self (g := gOf p k arch c i) hF0 hfr
  have hEE : CE E' = E' := by
    obtain ⟨_, η', _, _, _, hce', -⟩ := hRE
    rw [← hce']
    rfl
  have hfs : fpSync Eg c' i = Eg.fpOf i := fpSync_self h.proms h.fpfree hth ho
  have hCut : Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (gOf p k arch c i).i E'.seen = E' := by
    unfold EgT
    exact (Cut_withFp (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') (fpSync Eg c') _ E'.seen hfs).trans
      (hself.symm.trans hEE)
  obtain ⟨HP', HS', hHs, hP', hS'⟩ := MemHeld_split (E := E') (fun l cl hs hp => by
      rw [← hCut] at hs hp ⊢; exact Cut_cov hs hp) hH'
  -- the plant transfer: each dropped reading `g` pays at most one foreign
  -- promise `t` (`tgIn`) of an idle thread, the lowest of its promises in `g`'s piece, that is a
  -- key-free plant credit there when the reading carries a resource (`g.R = 0` asks no credit)
  obtain ⟨Pδ, hPδ⟩ : ∃ Pδ : TermPiece.GdE → Ts → Prop, Pδ = TermHtgW1.Pδ0 c c' Eg i th := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : Ts → Res, δ = TermPlant.plantD1 Gd TermPiece.GdE.R (TermPlant.tgIn η.fp Pδ) :=
    ⟨_, rfl⟩
  have hδ1 : ∀ t, δ t ≠ .zero → t ∈ η.fp ∧ ∃ g ∈ Gd, Pδ g t ∧ δ t = g.R := by
    intro t h0
    subst hδdef
    exact TermPlant.plantD1_tgIn h0
  have hcs : CrShift η (stOf c.mem c.pairs th) δ := ⟨fun t h0 => (hδ1 t h0).1, fun t h0 => by
    obtain ⟨-, g, -, hPg, -⟩ := hδ1 t h0
    subst hPδ
    exact hPg.1⟩
  have hFd : Res.sum ((TermPlant.nodupL η.fp).map δ) ≤ Res.sum (Gd.map TermPiece.GdE.R) := by
    subst hδdef
    exact TermPlant.plantD1_sum_le Gd TermPiece.GdE.R _ (TermPlant.nodupL_nodup η.fp)
  -- (B″) the step's write locations at every anchor: `WrSiteA` (`WrIniC`) with the `bufInit` count of `BiOut`
  have hWL : ∀ E0, TermTyped.WrLocA2 E0 (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    obtain ⟨-, ⟨ρ', η', cx', hCE', hE', hT', htv', hi', -⟩, hm0, -⟩ := id hS
    have e : CE η' = CE η := hCE'.trans hCE.symm
    have hm1 : MemInv (gOf p k arch c i) (CE η') (stOf c.mem c.pairs th) := by rw [hCE']; exact hm0
    intro E0
    rw [← e]
    refine TermTyped.wrLocA2_of (TermTyped.WrIniC.wrA hE' hT' htv' hi' hm1
      ((O.certRunT X S hS).1 th X.hth (TermStep.not_spawnT_of_mem X.hr) ρ' η' cx' hE' hT' htv' hi') (TermViewInv.envVR_of_run O.seenFacts X.run X.hth) X.hr)
      (fun x bb ib v e0 ht rt w ad rti wi n hea hw hei hn => ?_) E0
    have h := hBiO1 x bb ib v e0 rt w ad rti wi n ht hea hw hei hn
    exact ⟨Nat.le_trans h (Nat.min_le_left _ _), Nat.le_trans h (Nat.min_le_right _ _)⟩
  have Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs
      (HP i + HS) (TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i) (db i) δ := by
    refine ⟨hF, hRE, hm', hP', hS', hC', MintStep_unpf hMS, ?_, hBV, hcs, TermPlant.nodupL η.fp,
      fun t h0 => TermPlant.mem_nodupL.2 (hδ1 t h0).1, ?_, hBiO3, hWL⟩
    · rw [← hHs]
      exact Res.le_def.2 fun key => by
        have h1 := Res.le_def.1 hineq key
        simp only [Res.add_apply] at h1 ⊢
        omega
    · rw [← hHs]
      exact Res.le_def.2 fun key => by
        have h1 := Res.le_def.1 hineq key
        have h2 := Res.le_def.1 hFd key
        simp only [Res.add_apply] at h1 h2 ⊢
        omega
  -- (A) the credit-free consumers read `Z` at the thread's pre credits `cr i`
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  -- (A) at a publish the stepper keeps its promises, so `crS` is the thread's credits there
  have hPub : ∀ l, TermOwnG0Defs.PubAt th l → ∀ t,
      TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i t = cr i t := fun l hl t =>
    TermPoolResplit.crR_neg fun hq => by
      obtain ⟨y, a, e, -, -, -, hterm, -⟩ := hl
      exact hq.2.2.1 (by rw [(TermPlantAtN.tstep_publish_vWr hterm hr).2]; exact hq.2.1)
  have hKS : ∀ t l, TermPoolResplit.crR cr pl i (TermHbiPOf.QS Eg c i S th r) i t (.own l) = cr i t (.own l) :=
    fun t l => TermPoolResplit.crR_own hPI.tag hth i t l
  have hsub : ∀ t, t ∈ r.2.2.promises → t ∈ th.promises := fun t ht =>
    (TermFul.tstep_fulfil (fun t ht => h.plt i th t hth ht) (MemInv_nopair hm) hr).1.subset ht
  have hsz : c.mem.size ≤ c'.mem.size := by
    rw [e1]; exact (TermLiveProps.tstep_ext _ _ _ _ r hr).mem.size
  have hv : r.2.2.vs.vWr ≤ c'.mem.size := by rw [e1]; exact tstep_vWr hr (h.vwr i th hth)
  have proms' : PromsOK (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' :=
    PromsOK_thread h.proms h.disj hth e3 ho hsub
  have shty' := TermShty.shtyT_holds X Y ZC
  have fpfree' : FpOwnFree (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' :=
    FpOwnFree_thread h.fpfree hth e3 ho hsub
  have plt' := AllPromLt_thread h.plt hth e3 ho hsub hsz
  have held' : MemHeldG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' HS' := by
    have hS'' : MemHeldS (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (gOf p k arch c i).i E'.seen)
        (stOf r.1 r.2.1 r.2.2) HS' := by rw [hCut]; exact hS'
    exact MemHeldG_of_S e1.symm shty' (proms' i r.2.2 e3) hS''
  -- (pool) the pool route: F1T's re-split `cr2`/`pl2` of `crN`, the post-state `PoolInv`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hplM, hplK, -⟩ := id hBiO2
  obtain ⟨cr2, pl2, hcr2, hPI', hOF2, hLe2, hPK2⟩ := TermPoolThread.poolThread PS O.mintClosedT O.promNodup O.allocG
    (O.residualNoTicket O.noTicket) (fun X Y => O.scope X Y) X Y Z hQ (fun t => by rw [hδdef, hPδ]) hPI hrc hle hpa hBiO1 hBiO2 hBiO3
    (O.plantFulfil X Y) hF hSK hRE hm' hH' hC' (MintStep_unpf hMS) hDr hineq hHs
    (fun t h0 => TermPlant.mem_nodupL.2 (hδ1 t h0).1) hFd hplM hplK hPfrP hGc hNP hm hcl.1
    (TermOwnFresh.ownFresh_thread O.allocG O.promNodup X Y Z hKS h.ownF) hFN
  -- (D-B) the rts package's step facts: granW at the stepping thread (`c.ths.size > 0`), scope
  have hGW0 : k.storeDepRts = true → TermPtrRts.GranuleW Eg.sto c.mem c.pairs := fun hk =>
    (h.granW hk).resolve_left fun h0 => by rw [h0] at hi; exact Nat.not_lt_zero _ hi
  have hdrfR := TermScope.run_drf O.progScope O.runDRF0 hrun
  have hPCc : TermPtrKey.PubConsumeC th C := TermPubCons.pubCons_iff.1 hPubC
  suffices hSys : SysInvN p k arch Init MintOK c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c')
      (upd Tot i Tot') (upd HP i HP') HS' cr2 (upd db i db') from
    ⟨_, _, _, _, _, _, hSys, hPost th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPub hPfrP hS hF0⟩
  refine ⟨?thr, held', ?clo, ?cmg, shty', proms', fpok_of proms' fpfree' plt' (O.fpokVisT X Y ZC),
    O.freshT X Y ZC, (TermPoolStaging.PoolInv.old hPI').1, (TermPoolStaging.PoolInv.old hPI').2.1, ?bf, O.boxtopT X Y ZC hS hPfrP, PromsDisj_thread h.disj hth e3 ho hsub,
    fpfree', plt',
    VWrLe_thread h.vwr e3 ho hv hsz, ?frle, ?rle, ?zwIni, ?predHold, O.bnamedT X Y ZC, (TermPoolStaging.PoolInv.old hPI').2.2,
    O.promIniPost X Y Z hPub hPfrP hS, O.promTyAPost X Y Z hPub hPfrP hS, TermPromNU.promNU_thread h.promNU h.plt hc',
    hOF2,
    (haveI := O.retIall; TermB5.promNoTwoOK_thread (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRunT X Y ZC hS hPfrP h.promNoTwo), ?undefAt, ?ownKeyOwn, ?ownPub,
    TermBoxPV.boxPV_thread X Y ZC hBV (TermViewInv.viewInv_run O.seenFacts X.run) h.boxPV, TermBoxOwn.boxFrOwnT_of X Y ZC h.boxFrOwn, TermBoxOwn.boxFrLeT_of X Y ZC h.boxFrLe,
    TermVwrLt.VWrLtT_of X h.vwrLt, TermVwrLt.boxFrLtT_of X Y ZC h.vwrLt h.boxFrLt, ?frlt,
    TermBoxOwn.payOwnT_of X Y ZC h.boxSto h.payOwn, TermBoxOwn.boxStoT_of X Y ZC h.boxSto, ?ownCoh, ?riniCoh,
    TermPtrStab.promInCut_threadT X Y ZC h.promInCut,
    TermPromClos.promClos_thread O.promAlloc X Y ZC hS hPfrP, ?stoNI,
    TermUndefLow.undefLow_thread O.progT O.scope O.promAlloc X Y ZC hS hPfrP hpa h.undefLow,
    TermPromAboveG.promAboveG_step (TermLiveProps.threadSteps_ext hc') (TermPromAboveG.threadSteps_oth hc')
      hcert h.plt h.promAbove, ?msgWords, TermFgnClos.fgnClos_thread O.promAlloc X Y ZC hS hPfrP h.fgnClos,
      TermCellOwn.cellOwn_thread X Y ZC h.cellOwn,
    fun hk => TermPtrRtsK.ptrRtsGL_thread (TermK2aFin.ptrRtsThreadGL_v3d (TermFulCntROf.fulCntR_of p)) hk O.allocG O.promAlloc X Y Z hS hKS hm hPCc hPfrP hFNC
      (h.ptrGL hk) (hGW0 hk) (h.stoLay hk) (TermCertScope.scopeAt_of hdrfR th hth (TermStep.not_spawnT_of_mem hr)) (hdrfR i th hth) O.progScope
      O.progT hFBP hRP (h.boxPlantSep hk),
    fun hk => Or.inr (TermPtrRtsK.granuleW_thread (TermK2aFin.ptrRtsThreadGL_v3d (TermFulCntROf.fulCntR_of p)) hk O.allocG O.promAlloc X Y Z hS hKS hm hPCc hPfrP hFNC
      (h.ptrGL hk) (hGW0 hk) (h.stoLay hk) (TermCertScope.scopeAt_of hdrfR th hth (TermStep.not_spawnT_of_mem hr)) (hdrfR i th hth) O.progScope
      O.progT hFBP hRP (h.boxPlantSep hk)),
    fun hk => TermPtrRtsK.stoLay_thread hF0 (h.stoLay hk),
    fun hk => TermPtrRtsK.boxPlantSep_thread (TermK2aFin.ptrRtsThreadGL_v3d (TermFulCntROf.fulCntR_of p)) hk O.allocG O.promAlloc X Y Z hS hKS hm hPCc hPfrP hFNC
      (h.ptrGL hk) (hGW0 hk) (h.stoLay hk) (TermCertScope.scopeAt_of hdrfR th hth (TermStep.not_spawnT_of_mem hr)) (hdrfR i th hth) O.progScope
      O.progT hFBP hRP (h.boxPlantSep hk),
    fun hk => TermFgnCnt.fgnCnt_thread O.promAlloc X Y ZC hS hPfrP (h.fgnCnt hk),
    TermPoolThread.field_of_poolInv hPI',
    fun hk => O.plantIdxT X Y Z hS hKS hm hPfrP hPCc hk, (TermLiveProps.threadSteps_coh hc' h.cfgCoh).1, ?stoW, ?freshU⟩
  case freshU =>
    have hU := TermFreshU.freshU_thread O.allocG O.promNodup X Y Z ZC hKS
      (TermFreshU.hD_thread (p := p) (k := k) (arch := arch) hi) h.freshU
    rw [TermStep.threadSteps_n X.hc']
    intro q jj hq hqN
    obtain ⟨hU1, hU2⟩ := hU q jj hq hqN
    exact ⟨hU1, TermFreshU.ownZ_mono (fun n t => hLe2 n t _) hU2⟩
  case msgWords =>
    haveI := O.retIall
    haveI := O.ckW
    exact TermMsgWords.msgWords_thread (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRunT O.scope X Y ZC hS hPfrP h.msgWords
  case stoNI =>
    intro l cl hl
    simp only [EgT, GEnv.withFp, GEnv.post] at hl
    split at hl
    · rcases hF0.2.2.1 l with e | ⟨-, T, hT', hcT⟩
      · rw [e] at hl; exact h.stoNI l cl (cutSto_sub hl)
      · rw [hT'] at hl; cases hl; exact hcT.1.2.2.1
    · exact h.stoNI l cl hl
  case stoW =>
    intro l cl hl
    simp only [EgT, GEnv.withFp, GEnv.post] at hl
    split at hl
    · rcases hF0.2.2.1 l with e | ⟨-, T, hT', hcT⟩
      · rw [e] at hl; exact h.stoW l cl (cutSto_sub hl)
      · rw [hT'] at hl; cases hl; exact hcT.1.2.2.2
    · exact h.stoW l cl hl
  case ownCoh =>
    intro j thj Sj hj
    by_cases hji : j = i
    · subst hji
      rw [e3] at hj
      cases hj
      rw [e1, e2]
      have h1 := TermOwnCoh.ownCoh_stepper X Y ZC
      rw [← hCut] at h1
      exact TermOwnCoh.ownCoh_seen h1
    · have hj' : c.ths[j]? = some thj := by rw [← ho j hji]; exact hj
      exact TermOwnCoh.ownCoh_gfoot (TermInterf.gfoot_of X Y ZC) hji (fpSync Eg c') (h.ownCoh j thj Sj hj')
  case riniCoh =>
    intro j thj Sj hj
    by_cases hji : j = i
    · subst hji
      rw [e3] at hj
      cases hj
      rw [e1, e2]
      have h0 : TermTyped.RiniCoh (CE η) (stOf c.mem c.pairs th) := by rw [hCE]; exact h.riniCoh _ th S hth
      have hFp := TermOwnX2.finv_of htv hFI
      have hl : TermRiniCoh.HltOwn (CE η).sto (CE η).pfr (CE η).tid c.mem.size := by
        rw [hCE]; exact TermRiniCoh.hltOwn_cut (TermRiniCoh.hltOwn_sys h hth)
      have h1 := TermRiniCohW.riniCoh_thread hE hT.1 htv hFp hm
        (TermCertScope.scopeAt_of hdrfR th hth (TermStep.not_spawnT_of_mem hr) ρ η cx hE hT.1 htv hFp)
        (TermViewInv.envVR_of_run O.seenFacts X.run X.hth) hr hF hBiO1 hl h0
      rw [← hCut] at h1
      exact TermRiniCoh.riniCoh_seen h1
    · have hj' : c.ths[j]? = some thj := by rw [← ho j hji]; exact hj
      exact TermRiniCoh.riniCoh_gfoot (s := stOf c.mem c.pairs thj) (TermInterf.gfoot_of X Y ZC) hji (fpSync Eg c')
        (TermRiniCoh.hltOwn_sys h hj') rfl
        (fun t ht => by
          show c'.mem[t]? = c.mem[t]?
          rw [e1]; exact (TermLiveProps.tstep_ext _ _ _ _ r hr).mem.get t ht)
        (h.riniCoh j thj Sj hj')
  case ownKeyOwn => exact TermOwnPub.ownKeyOwn_thread O.allocG X Y Z hKS h.ownKeyOwn
  case ownPub => exact TermOwnPub.ownPub_thread O.allocG X Y Z hKS hm (by rw [← hHs]; exact hSK) h.ownKeyOwn h.ownPub
  case undefAt =>
    rw [e1]
    exact TermUndefInv.undefAtG_thread (s := stOf c.mem c.pairs th) (s' := stOf r.1 r.2.1 r.2.2) h.undefAt
      (TermStep.UndefNew_of_EFootM hm hF) (TermUndefInv.memExt_get (TermLiveProps.tstep_ext _ _ _ _ r hr).mem)
  case thr =>
    intro j thj hj
    by_cases hji : j = i
    · subst hji
      rw [e3] at hj
      cases hj
      rw [upd_self, upd_self, upd_self, hcr2, gOf_thread hc', e1, e2]
      refine ⟨E'.seen, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hCut]; exact hRE
      · rw [hCut]; exact ThInvRE.thInvE hRE
      · rw [hCut]; exact hm'
      · rw [hCut]; exact hP'
      · rw [hCut]; exact hS'
      · rw [hCut]; exact hC'
    · have hj' : c.ths[j]? = some thj := by rw [← ho j hji]; exact hj
      rw [upd_other _ _ hji, upd_other _ _ hji, upd_other _ _ hji, gOf_thread hc']
      obtain ⟨Sj, hold⟩ := h.thr j thj hj'
      obtain ⟨h1, h2⟩ := O.interfFrameT X Y ZC j thj Sj hji hj' hold
      exact ⟨Sj, h1, h2, O.interfMemT X Y Z hPub hPfrP hS j thj Sj hji hj' hold, O.interfHPT X Y ZC j thj Sj hji hj' hold,
        MemHeldS_of_G rfl shty' (proms' j thj hj) held',
        hPK2 j thj Sj hji hj (O.interfCrT X Y (TOutC_mono ZC (TermPoolThread.δc_key_le δ cr pl c c' _ i))
          (TermPoolStaging.crShiftP_δc δ cr c c' _ i) j thj Sj hji hj' hold)⟩
  case clo =>
    intro l cl hl
    simp only [EgT, GEnv.withFp, GEnv.post] at hl
    split at hl
    · rcases hF0.2.2.1 l with e | ⟨-, T, hT', hcT⟩
      · rw [e] at hl; exact h.clo l cl (cutSto_sub hl)
      · rw [hT'] at hl; cases hl; exact hcT.1.1
    · exact h.clo l cl hl
  case cmg =>
    intro l cl hl
    simp only [EgT, GEnv.withFp, GEnv.post] at hl
    split at hl
    · rcases hF0.2.2.1 l with e | ⟨-, T, hT', hcT⟩
      · rw [e] at hl; exact h.cmg l cl (cutSto_sub hl)
      · rw [hT'] at hl; cases hl; exact hcT.1.2.1
    · exact h.cmg l cl hl
  case bf =>
    rw [(threadSteps_lbase hc').2]; exact h.bf
  case frle =>
    rw [e1]
    exact FrontierLe_gfoot (EFoot_post (g := gOf p k arch c i) hF0 hfr (h.vwr i th hth)) h.frle (Nat.le_refl _)
      (TermLiveProps.tstep_ext _ _ _ _ r hr).mem.size
  case frlt =>
    rw [e1]
    exact FrontierLt_post (g := gOf p k arch c i) hF0 hfr (h.vwrLt i th hth) h.frlt
      (TermLiveProps.tstep_ext _ _ _ _ r hr).mem.size
  case rle =>
    exact fun l => hF0.2.2.2.2.2.2.2.2.2.2.1 h.rle l
  case zwIni =>
    exact TermZwIniP.zwIni_EgT h.zwIni hF0 hfr (TermZwIni.hnew_of_efoot hF0)
  case predHold =>
    exact TermPredHoldP.predHold_thread h.predHold hth e3 ho
      (fun t ht => by
        rw [e1, Array.getElem?_eq_getElem ht]
        exact (TermCert.tstep_appUp hr).2.1 t _ (Array.getElem?_eq_getElem ht)) hF0 hfr
      (TermPredHoldP.hIL_of_efoot hF0 hfr) (by rw [← hCE]; exact hm)
      (TermPredStoreFree.ownPredStoreFree_of O.scope O.seenFacts h.predHold X hF0 hBiO1)
/-- (R4 route (a‴)+(A)) **`SysInvN` across a thread step**, with the pre-step `SysInvN`/`PoolInv`
at `(cr, pl)` and the stepper run at `crS = cr i + plQ` (`TermHbiPOf.stepCrQ_of`): its pool part at
`i`'s discharged, frontier-guarded promises moves into the stepper's credits.  `hFN` is F1T's `hNew`
(the `fgnNew_of`), a LOCAL gap: it is not a field and not a premise of any final. -/
theorem sysInv_threadR (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hFN : TermPoolThread.FgnNewT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hc' : c' ∈ threadSteps p k arch c i) (hcert : Certified p k arch c' i)
    {pl : Nat → Ts → Res} (hPI : TermPoolStaging.PoolInv Init MintOK c Eg Tot HP HS cr db pl) :
    SysInvNx p k arch Init MintOK c' :=
  let ⟨Eg', Tot', HP', HS', cr', db', hS, _⟩ :=
    sysInv_threadRP O PS hFN hrun h hc' hcert hPI (fun _ => True) (by intros; trivial)
  ⟨Eg', Tot', HP', HS', cr', db', hS⟩
#print axioms TermMain.sysInv_threadRP
#print axioms TermMain.sysInv_threadR

/-! ## Wiring: the promise step -/

theorem promise_g (c : Cfg) (i : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) (j : Nat) :
    gOf p k arch (promise c i a v w) j = gOf p k arch c j := by
  unfold gOf
  rw [TermStep.promise_n]
  unfold promise
  split <;> rfl

theorem promise_bf (c : Cfg) (i : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) :
    (promise c i a v w).boxFence = c.boxFence := by
  unfold promise
  split <;> rfl


/-- **`SysInvN` across a thread step**, from `tstepMCF_step` and the obligations (R4 route
(a‴)+(A): the pre-step pool `pl` of `h.pool`, the stepper at `crS`).  `hFN`: see `sysInv_threadR`. -/
theorem sysInv_thread (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hFN : TermPoolThread.FgnNewT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hc' : c' ∈ threadSteps p k arch c i) (hcert : Certified p k arch c' i) :
    SysInvNx p k arch Init MintOK c' := by
  obtain ⟨pl, hPI⟩ := TermPoolThread.poolInv_of h.pool
  exact sysInv_threadR O PS hFN hrun h hc' hcert hPI
#print axioms TermMain.sysInv_thread

/-- **`SysInvN` across a promise step, carrying a side fact `Q` of the post-step ghost
environment**: master of `sysInv_prom` (`Q` trivial) and `TermSpawn.sysInvO_prom` (`OwnLive`/`ObsAll`). -/
theorem sysInv_promP (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN) {c : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hj : j < c.ths.size) (hw : w < c.mem.size) (hcert : Certified p k arch (promise c j a v w) j)
    (Q : GEnv → Prop)
    (hQ : ∀ th, c.ths[j]? = some th → PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      Q (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK (promise c j a v w) Eg' Tot' HP' HS' cr' db' ∧ Q Eg' := by
  obtain ⟨th, hth⟩ : ∃ th, c.ths[j]? = some th := ⟨c.ths[j], Array.getElem?_eq_getElem hj⟩
  have X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w := ⟨hrun, h, hth, hw, hcert⟩
  obtain ⟨epc, hpj, -⟩ := promise_inv (a := a) (v := v) (w := w) hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [epc]
  have hpairs : (promise c j a v w).pairs = c.pairs := by rw [epc]
  have hself : ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' ∧
        (∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop,
          ¬ WordUnit (Cut Eg j S) m.loc → cr' t = cr j t) := by
    by_cases hpl : ∃ l f, plantOf c Eg j a v w l = some f
    · exact O.selfPlant X hpl
    · have hP0 : ∀ l, plantOf c Eg j a v w l = none := fun l => by
        cases e : plantOf c Eg j a v w l with
        | none => rfl
        | some f => exact (hpl ⟨l, f, e⟩).elim
      obtain ⟨S, hRE, hTE, hm, hHP, hHS, hC⟩ := h.thr j th hth
      have hH := MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hHP hHS
      -- the step at the dropped credits; old credits are restored by `PromCrK_prom`
      obtain ⟨H', cr'', db', hag, hRE', hm', hH', hC'', heq⟩ :=
        tstepMC_promEc hRE hm hH (PromCrP_drop hC.toP) (O.hwu X S) (O.hfw X S)
      have hK := TermPlant.PromCrK_prom hC (fun t ht => h.plt j th t hth ht) hag hC''
        (O.promSelfK X hP0 ⟨hRE, hTE, hm, hHP, hHS, hC⟩)
      have hcut : Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (gOf p k arch c j).i S =
          Cut Eg (gOf p k arch c j).i S := by
        unfold EgP
        rw [plantG_none hP0]
        exact Cut_withFp _ _ _ _ (by show fpProm Eg j c.mem.size j = Eg.fpOf j; simp [fpProm])
      obtain ⟨HP', HS', hHs, hP', hS'⟩ := MemHeld_split (fun _ _ hc hp => Cut_cov hc hp) hH'
      refine ⟨HP', HS', fun t => if t < (stOf c.mem c.pairs th).mem.size then cr j t else cr'' t, db', ?_,
        ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · show _ = _
        rw [← hHs]
        refine Res.ext fun key => ?_
        have e1 := congrArg (fun R : Res => R key) heq
        have e2 := congrArg (fun R : Res => R key) hK.2
        simp only [Res.add_apply] at e1 e2 ⊢
        omega
      · rw [hcut]; exact hRE'
      · rw [hcut]; exact hTE
      · rw [hcut]; exact hm'
      · rw [hcut]; exact hP'
      · rw [hcut]; exact hS'
      · rw [hcut]; exact hK.1
      · intro t m ht _ _ _
        have hlt : t < (stOf c.mem c.pairs th).mem.size := h.plt j th t hth ht
        simp only [hlt, ↓reduceIte]
  obtain ⟨HP', HS', cr', db', hacct, hS, hcrK⟩ := hself
  obtain ⟨pl, hPIp⟩ := TermPoolThread.poolInv_of h.pool
  have hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0 := fun l => by
    obtain ⟨_, -, -, -, -, -, hK⟩ := hS; exact (TermOwnFresh.promCrK_own hK l).2
  have hPL : ∀ l0 f0, plantOf c Eg j a v w l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0 := fun _ _ e => O.plantL hth e
  have hGW0 : k.storeDepRts = true → TermPtrRts.GranuleW Eg.sto c.mem c.pairs := fun hk =>
    (h.granW hk).resolve_left fun h0 => by rw [h0] at hj; exact Nat.not_lt_zero _ hj
  have proms' : PromsOK (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) :=
    PromsOK_promise h.proms hth
  have hspec := (O.plantSpec X).1
  have shty' : SharedTyOK (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) := by
    intro l cl ⟨f, hf⟩ hs
    simp only [EgP, GEnv.withFp, plantG] at hf hs
    cases e : plantOf c Eg j a v w l with
    | none =>
      simp only [e] at hf
      exact h.shty l cl ⟨f, hf⟩ hs
    | some f' => exact (hspec l f' e).2.2.2 cl hs
  have fpfree' : FpOwnFree (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) :=
    FpOwnFree_promise h.proms h.fpfree h.plt hth
  have plt' : AllPromLt (promise c j a v w) := AllPromLt_promise h.plt hth
  have held' : MemHeldG (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) HS' := by
    obtain ⟨S', -, -, -, -, hS'', -⟩ := hS
    exact MemHeldG_of_S (by rw [hmem]; rfl) shty' (proms' j _ hpj) hS''
  suffices hSys : SysInvN p k arch Init MintOK (promise c j a v w)
      (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) Tot (upd HP j HP') HS' (upd cr j cr') (upd db j db') by
    exact ⟨_, _, _, _, _, _, hSys, hQ th hth X⟩
  refine ⟨?thr, held', h.clo, h.cmg, shty', proms', fpok_of proms' fpfree' plt' (O.fpokVisP X), O.freshP X, TermBal.balP_proof X hacct,
    TermBal.knetP_proof X hacct, ?bf, O.boxtopP X, PromsDisj_promise h.disj h.plt hth, fpfree', plt',
    VWrLe_promise h.vwr hth, ?frle, fun l => Nat.le_trans (h.rle l) (plantG_ini_le _ _ _ l), TermZwIniP.zwIni_prom h.zwIni (O.plantSpec X).2.1 _ _,
    TermPredHoldP.predHold_promX X h.predHold (O.plantSpec X).1 (O.plantSpec X).2.2, h.bnamed, TermBal.ridP_N X hacct,
    O.promIniPostP X, O.promTyAPostP X, haveI := O.retIall; TermPromNU.promNU_prom (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRun X h.promNU,
    TermOwnFresh.ownFresh_prom X hacct (fun l => by obtain ⟨_, -, -, -, -, -, hK⟩ := hS; exact (TermOwnFresh.promCrK_own hK l).2) h.ownF,
    TermB5.promNoTwoOK_promise O.promNoTwoP X h.promNoTwo _ _ _, by rw [hmem]; exact TermUndefInv.undefAtG_prom h.undefAt,
    TermOwnPub.ownKeyOwn_prom X h.ownKeyOwn _ _ _,
    TermOwnPub.ownPub_prom X hacct (fun l => by obtain ⟨_, -, -, -, -, -, hK⟩ := hS; exact (TermOwnFresh.promCrK_own hK l).2) h.ownPub _ _ _,
    TermBoxOwn.boxPV_egP h.boxPV, TermBoxOwn.boxFrOwn_promise (fun _ _ hb => hb) hth h.boxFrOwn,
    TermBoxOwn.boxFrLe_egP h.boxFrLe (by rw [hmem, Array.size_push]; exact Nat.le_succ _),
    TermVwrLt.VWrLt_promise h.vwrLt hth, TermVwrLt.BoxFrLt_promise (fun _ _ hb => hb) hth h.boxFrLt, ?frlt,
    TermBoxOwn.payOwn_egP h.payOwn, TermBoxOwn.boxSto_egP h.boxSto, ?ownCoh, ?riniCoh,
    TermPtrStab.promInCut_prom hth h.plt (fun q hq => (h.fresh j th hth q hq).1) (O.promLoc X) h.promInCut,
    O.promClosP X, h.stoNI,
    TermUndefLow.undefLow_prom (fun _ => rfl)
      (haveI := O.retIall; TermPromNU.promNU_prom (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRun X h.promNU) hth h.undefLow,
    TermPromAboveG.promAboveG_step (TermLiveProps.promise_ext c j a v w)
      (fun i0 th0 => TermPromAboveG.promise_oth i0 th0) hcert h.plt h.promAbove,
    (haveI := O.retIall; TermMsgWords.msgWords_prom (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRun X h.msgWords _ _ _),
    (haveI := O.retIall; TermFgnClos.fgnClos_prom (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRun X h.fgnClos),
    TermCellOwn.cellOwn_prom X (O.plantSpec X).1 (O.promLoc X) h.cellOwn,
    fun hk => TermPtrRtsK.ptrGL_promW X hPL hacct hdb (h.ptrGL hk) (h.fgnCnt hk),
    fun hk => Or.inr (TermPtrRtsK.granuleW_prom O.promNoTwoP O.promLoc X (hGW0 hk) _ _ _),
    fun hk => h.stoLay hk,
    fun hk => TermPtrRtsK.boxPlantSep_prom hth hPL h.plt (h.ptrGL hk).2.2.1 (TermPtrKey.ownKey_prom_le X hacct hdb)
      h.payOwn h.boxPV h.boxFrOwn (h.boxPlantSep hk),
    fun hk => (haveI := O.retIall; TermFgnCnt.fgnCnt_prom (hV0 := O.seenFacts) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) O.progT O.certRun X (h.fgnCnt hk)),
    TermPoolThread.field_of_poolInv (TermPoolThread.poolProm PS X (O.plantSpec X).1 hPIp hacct hS hcrK),
    fun hk => O.plantIdxP X hacct hS hk (TermPtrRtsK.ptrGL_promW X hPL hacct hdb (h.ptrGL hk) (h.fgnCnt hk))
      (TermPtrRtsK.boxPlantSep_prom hth hPL h.plt (h.ptrGL hk).2.2.1 (TermPtrKey.ownKey_prom_le X hacct hdb)
        h.payOwn h.boxPV h.boxFrOwn (h.boxPlantSep hk)), (TermLiveProps.promise_coh c j a v w h.cfgCoh).1, h.stoW, ?freshU⟩
  case freshU =>
    rw [TermStep.promise_n]
    exact TermFreshU.freshU_prom (plantN := plantN) (fun X => (O.plantSpec X).1) O.promLoc X hacct hdb
      (TermFreshU.hD_prom hj) h.freshU
  case ownCoh =>
    intro i thi Si hi
    by_cases hij : i = j
    · subst hij
      rw [hpj] at hi
      cases hi
      exact TermOwnCoh.ownCoh_sto (Eg := Eg) rfl (fun l hl => TermOwnCoh.plantG_pfr_none (Eg := Eg) (P := plantOf c Eg i a v w) (N := plantN c Eg i a v w) hl)
        (h.ownCoh i th Si hth)
    · have hi' : c.ths[i]? = some thi := by rw [← promise_other hth hij]; exact hi
      exact TermOwnCoh.ownCoh_sto (Eg := Eg) rfl (fun l hl => TermOwnCoh.plantG_pfr_none (Eg := Eg) (P := plantOf c Eg j a v w) (N := plantN c Eg j a v w) hl)
        (h.ownCoh i thi Si hi')
  case riniCoh =>
    intro i thi Si hi
    have hPS : ∀ l f, plantOf c Eg j a v w l = some f → Eg.pfr l = none ∧ Eg.OwnAt j l ∧ f ≤ c.mem.size :=
      fun l f e => ⟨(hspec l f e).1, (hspec l f e).2.1, (hspec l f e).2.2.1⟩
    by_cases hij : i = j
    · subst hij
      rw [hpj] at hi
      cases hi
      exact TermRiniCoh.riniCoh_prom (s := stOf c.mem c.pairs th) (fpProm Eg i c.mem.size) (TermRiniCoh.hltOwn_sys h hth) hPS
        (fun t ht => List.mem_append_left _ ht)
        (fun t ht => by
          show (promise c i a v w).mem[t]? = c.mem[t]?
          have ht' : t < c.mem.size := ht
          rw [hmem, Array.getElem?_push]; exact if_neg (Nat.ne_of_lt ht'))
        (by show (promise c i a v w).mem.size = c.mem.size + 1; rw [hmem, Array.size_push])
        (fun _ => List.mem_append_right _ (List.mem_singleton_self _))
        (TermRiniCoh.privCoh_sys h hth Si) (h.riniCoh i th Si hth)
    · have hi' : c.ths[i]? = some thi := by rw [← promise_other hth hij]; exact hi
      exact TermRiniCoh.riniCoh_prom (s := stOf c.mem c.pairs thi) (fpProm Eg j c.mem.size) (TermRiniCoh.hltOwn_sys h hi') hPS
        (fun t ht => ht)
        (fun t ht => by
          show (promise c j a v w).mem[t]? = c.mem[t]?
          have ht' : t < c.mem.size := ht
          rw [hmem, Array.getElem?_push]; exact if_neg (Nat.ne_of_lt ht'))
        (by show (promise c j a v w).mem.size = c.mem.size + 1; rw [hmem, Array.size_push])
        (fun e => absurd e hij)
        (TermRiniCoh.privCoh_sys h hi' Si) (h.riniCoh i thi Si hi')
  case thr =>
    intro i thi hi
    by_cases hij : i = j
    · subst hij
      rw [hpj] at hi
      cases hi
      rw [upd_self, upd_self, upd_self, promise_g, hmem, hpairs]
      exact hS
    · have hi' : c.ths[i]? = some thi := by rw [← promise_other hth hij]; exact hi
      rw [upd_other _ _ hij, upd_other _ _ hij, upd_other _ _ hij, promise_g, hmem, hpairs]
      obtain ⟨Sj, hold⟩ := h.thr i thi hi'
      obtain ⟨h1, h2⟩ := O.interfFrameP X i thi Sj hij hi' hold
      exact ⟨Sj, h1, h2, O.interfMemP X i thi Sj hij hi' hold, O.interfHPP X i thi Sj hij hi' hold,
        MemHeldS_of_G (by rw [hmem]; rfl) shty' (proms' i thi hi) held', O.interfCrP X i thi Sj hij hi' hold⟩
  case bf =>
    rw [promise_bf]; exact h.bf
  case frle =>
    rw [hmem, Array.size_push]
    intro l cl f hs hp
    simp only [EgP, GEnv.withFp, plantG] at hp hs
    cases e : plantOf c Eg j a v w l with
    | none =>
      simp only [e] at hp
      exact Nat.le_succ_of_le (h.frle l cl f hs hp)
    | some f' =>
      simp only [e, Option.some.injEq] at hp
      subst hp
      exact Nat.le_succ_of_le (hspec l f' e).2.2.1
  case frlt =>
    rw [hmem, Array.size_push, Nat.add_sub_cancel]
    intro l cl f hs hp
    simp only [EgP, GEnv.withFp, plantG] at hp hs
    cases e : plantOf c Eg j a v w l with
    | none =>
      simp only [e] at hp
      exact Nat.le_trans (h.frlt l cl f hs hp) (Nat.sub_le _ _)
    | some f' =>
      simp only [e, Option.some.injEq] at hp
      subst hp
      exact (hspec l f' e).2.2.1
#print axioms TermMain.sysInv_promP

/-- **`SysInvN` across a promise step**: the promiser's part from
`tstepMC_promE` when nothing is planted (`selfPlant` otherwise). -/
theorem sysInv_prom (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN) {c : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hj : j < c.ths.size) (hw : w < c.mem.size) (hcert : Certified p k arch (promise c j a v w) j) :
    SysInvNx p k arch Init MintOK (promise c j a v w)
 := by
  obtain ⟨Eg', Tot', HP', HS', cr', db', hS, -⟩ :=
    sysInv_promP O PS hrun h hj hw hcert (fun _ => True) (fun _ _ _ => trivial)
  exact ⟨Eg', Tot', HP', HS', cr', db', hS⟩

/-! ## Runs and the headline -/

/-- (R4) **The pool staging from its twelve members** (`ownC`, `ownA`, `f1T`;
`poolTagOwnT`; `fgnCov` at `wrapTop` cells from `SysInvN.stoW`). -/
theorem poolStaging_of (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) :
    TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN :=
  { hOwnA := TermOverCrA3.openOverCrOwnA_of
    hOwnC := TermOwnCMain.ownC_of_prov O.scope
    hFgnCov := TermHWbRWrap.fgnCov_of_wrap (fun X Y => O.scope X Y) (fun hA => hA.1.inv.stoW)
    hF1T := TermPoolF1.f1T_of
    hPoolTagOwnT := TermPoolTagOwn.poolTagOwnT_of
    hPoolBalT := TermPoolBal.poolBalT_of
    hPoolKnetT := TermPoolBal.poolKnetT_of
    hPoolRidT := TermPoolBal.poolRidT_of
    hPoolBalP := TermPoolBal.poolBalP_of
    hPoolKnetP := TermPoolBal.poolKnetP_of
    hPoolRidP := TermPoolBal.poolRidP_of
    hPoolTagP := TermPoolTagW.poolTagP_of }
#print axioms TermMain.poolStaging_of

/-- **`SysInvN` across one machine step** (both `Step` constructors). -/
theorem sysInv_step (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) {c c' : Cfg}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvNx p k arch Init MintOK c) (hs : Step p k arch c c') :
    SysInvNx p k arch Init MintOK c' := by
  have PS := poolStaging_of O
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN⟩ := h
  cases hs with
  | thread i hc hcert => exact sysInv_thread O PS (TermFgnNew.fgnNew_of O.scope) hrun hN hc hcert
  | prom i a v w hi hw hcert => exact sysInv_prom O PS hrun hN hi hw hcert

/-- **`SysInvN` along every run from `c0`.** -/
theorem sysInv_run (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (h0 : SysInvNx p k arch Init MintOK c0)
    {c : Cfg} (hr : TermStep.Steps p k arch c0 c) : SysInvNx p k arch Init MintOK c := by
  have key : ∀ {c1 c2 : Cfg}, TermStep.Steps p k arch c1 c2 → TermStep.Steps p k arch c0 c1 →
      SysInvNx p k arch Init MintOK c1 → SysInvNx p k arch Init MintOK c2 := by
    intro c1 c2 h12
    induction h12 with
    | refl => exact fun _ h => h
    | step hs _ ih => exact fun h01 h1 => ih (h01.tail hs) (sysInv_step O (TermSpawnStep.StepsG.ofSteps h01) h1 hs)
  exact key hr (.refl _) h0

end

/-- (D3) **The initial configuration**: `SysInv` holds and no promise is out
(S11's `SysInv_init` discharges it for the `spawn` shape). -/
def InitOK (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  (∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
    SysInvW p k arch Init MintOK c0 Eg Tot HP HS cr db ∧ (∃ rc, RidOK c0 Tot HP HS cr db rc) ∧
      OwnFreshZ c0 Tot HP HS cr ∧ TermUndefZ.UndefAtG Eg c0.mem ∧
      (∀ i th (S : AllocLabel → Prop), c0.ths[i]? = some th →
        TermOwnCohZ.OwnCohZ (Cut Eg i S) (stOf c0.mem c0.pairs th)) ∧ (∀ l, Eg.box l = none) ∧ (∀ l, Eg.pfr l = none) ∧
      OwnKeyOwnG c0 Eg Tot ∧ OwnPubG c0 Eg Tot HP HS ∧ StoNI Eg ∧
      (∀ l cl, Eg.sto l = some cl → TermA4.wrapTop cl.ty = true) ∧ TermPtrRts.LblSto Eg c0 ∧ (∀ l cl, Eg.sto l = some cl → TermSound.LayT cl.ty) ∧ c0.mem = #[] ∧
      TermViewInv.ViewInv c0 ∧
      ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → th.vs.vWr ≤ c0.mem.size - 1) ∧ AllNoProm c0 ∧
    TermLiveProps.CfgCoh c0

/-- (option (a)) Coherence views at an `InitShape` configuration are all `0`, so `CfgCoh`. -/
theorem cfgCoh_of_initShape {p : Prog} {c0 : Cfg} (hs : TermInit.InitShape p c0) :
    TermLiveProps.CfgCoh c0 :=
  fun i th h b => Or.inl (congrFun (hs.vs0 i th h).2.2.2.2.1 b)

/-- (D-B) `LblSto` at an `InitShape` configuration: empty stacks, and no argument word names a
label (`envNoLoc`; counted words are among the value's words, `pubWords_lblSub`). -/
theorem lblSto_of_initShape {p : Prog} {c0 : Cfg} (hs : TermInit.InitShape p c0) (Eg : GEnv) :
    TermPtrRts.LblSto Eg c0 := by
  intro i th hth
  refine ⟨fun x rt ws hm w hw l hn => ?_, fun f hf => ?_⟩
  · obtain ⟨w0, hw0, a, g, hv, -⟩ := (TermPtrRts.pubWords_lblSub rt).1 ws w hw l hn
    exact absurd hv (hs.envNoLoc i th hth _ hm w0 hw0 a g)
  · rw [(hs.thr i th hth).2.1] at hf; cases hf

/-- (S11) **`InitOK` at the standard initial configuration**: empty memory,
box fence on, every thread at a typed resource-free entry frame with no promises
(`TermInit.InitShape`; `TermInit.entryOK_of` for the spawn shape). -/
theorem initOK_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hs : TermInit.InitShape p c0) (hM : MintOK .zero) : InitOK p k arch Init MintOK c0 :=
  have hW := TermInit.sysInvW_init (k := k) (arch := arch) (Init := Init) hs hM
  ⟨⟨_, _, _, _, _, _, hW, ⟨fun _ => 0, TermInit.ridOK_init _⟩,
    TermOwnFresh.ownFreshZ_zero, TermUndefInv.undefAtG_empty (fun _ => rfl), TermOwnCoh.ownCoh_initW hW hs.mem, fun _ => rfl, fun _ => rfl,
    fun _ _ _ _ h => absurd rfl h, fun _ hl => hl.elim, fun _ _ h => by simp [TermInit.Eg0] at h,
    fun _ _ h => by simp [TermInit.Eg0] at h,
    lblSto_of_initShape hs _, fun _ _ h => by simp [TermInit.Eg0] at h, hs.mem,
    TermViewInv.viewInv_init hs.mem fun i th h => by
      obtain ⟨-, hst, hw, -⟩ := hs.thr i th h
      obtain ⟨h1, h2, h3, h4, -, he⟩ := hs.vs0 i th h
      exact ⟨hst, ⟨Nat.le_of_eq h1, Nat.le_of_eq hw, Nat.le_of_eq h2, Nat.le_of_eq h3, Nat.le_of_eq h4⟩, he⟩,
    fun i th h => by rw [(hs.thr i th h).2.2.1]; exact Nat.zero_le _⟩,
    fun i th h => (hs.thr i th h).1, cfgCoh_of_initShape hs⟩

/-- **Headline 1, modulo `Obligations`.**  At every configuration reachable
from an `InitOK` configuration: the system invariant with net key bounds
(each exclusive key held at most once, net of outstanding promise debts);
at every promise-free one (in particular every final one) the gross bounds,
`SysInvW`, and region-token uniqueness across threads; and every thread
typed at its cut, with `MemInv` (so every load's value is a value of its
type, stage A). -/
theorem machine_tokens_main {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (h0 : InitOK p k arch Init MintOK c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init MintOK c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) := by
  obtain ⟨⟨Eg0, T0, H0, S0, cr0, db0, hw0, hr0, hof0, hu0, hoc0, hbx0, hzw0, hko0, hop0, hni0, hsw0, hlb0, hly0, hmem0, -, hvl0⟩, hn0, hcc0⟩ := h0
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN⟩ := sysInv_run O ⟨_, _, _, _, _, _, TermMain.SysInvW.toN hw0 hn0 hr0 hof0 hu0 hoc0 hbx0 hko0 hop0 hni0 (TermUndefLow.undefLow_nil hmem0) (TermZwIni.zwIni_none hzw0) (TermPredHold.predHold_none hzw0) hvl0
      (fun t m cl hm _ => by rw [hmem0] at hm; simp at hm) hmem0 hzw0 hlb0 hly0 hcc0 hsw0⟩ hr
  refine ⟨Eg, Tot, HP, HS, cr, db, hN, hN.knet,
    fun hn => ⟨hN.toW hn, fun i j n hi hj h1 h2 => (hN.toW hn).tokUniq hi hj h1 h2⟩, fun i th hth => ?_⟩
  obtain ⟨S, ρ, η, cx, Rf, Rs, hCE, -, hE, hT, -, hFI, hsum, -, hm, -⟩ := (hN.thr i th hth).env hN.clo
  exact ⟨S, ρ, η, cx, Rf, Rs, hCE, hE, hT.1, hFI, hsum, hm⟩

/-! ## Reading guide and corollaries

The witnesses of `SysInvN` at a configuration `c` are:

- `Eg`: the global typing environment.  Thread `i` types its state at the
  cut `Cut Eg i S` (its view of `Eg`, hiding the other threads' private
  cells; `S` is the set of cells it has seen published).
- `Tot i`: the resources in thread `i`'s frame (its variables and stack).
- `HP i`: the resources memory holds in `i`'s private cells; `HS`: in the
  shared cells.
- `cr i t` / `db i t`: the credit / debit of `i`'s outstanding promise `t`:
  what the promised message already stands in for in memory / what `i`
  still owes when it fulfils.

A key (`rg n`, `wd n`, `own l`) is *exclusive*.  The net bound `KeyNet` says
that, per key, frames + holdings + credits ≤ 1 + debits.  A thread that has
promised the store handing a key over still carries the key in its frame,
but owes it; counting the promise as already performed, the key is held
once.  Without outstanding debits of a key, the bound is the gross one.

The corollaries below state the headline in that vocabulary. -/

/-- Total outstanding debit of key `key` across all threads. -/
def Debt (c : Cfg) (db : Nat → Ts → Res) (key : Key) : Nat :=
  ((List.range c.ths.size).map (fun i => pSumAt c i (db i) key)).sum

/-- **Frame tie** (conjunct (d) of `machine_tokens_main`, named): ONE global environment `Eg` and
ONE frame-total function `Tot` such that every thread `i` is typed at its cut `Cut Eg i S`, its
frame and stack hold exactly `Tot i` (`Rf + Rs = Tot i`), and memory satisfies `MemInv` there.
The corollaries below state their per-thread bounds about this `Tot`, so `Tot` cannot be chosen
freely (e.g. `Tot := 0`). -/
def FrameTie (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (Eg : GEnv) (Tot : Nat → Res) : Prop :=
  ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
    FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
    MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)

/-- (tie) The net region-token bound from `KeyNet` at `rg n` with no outstanding debit; shared by
`token_unique_net` and its spawn-era forms. -/
theorem tokUniq_of_knet {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hk : ∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) :
    ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j := by
  intro n hd i j hi hj h1 h2
  have h := hk (.rg n) trivial
  unfold KeyNet at h
  unfold Debt at hd
  rw [hd, Nat.add_zero] at h
  exact TermLiveHeld.tokUniq_of_sum (Tot := fun i => Tot i + HP i + pSumAt c i (cr i)) h hi hj
    (by rw [Res.add_apply, Res.add_apply]; omega) (by rw [Res.add_apply, Res.add_apply]; omega)

/-- **Headline 1, net form.**  At every configuration reachable from an
`InitOK` one there are a global environment `Eg`, frame totals `Tot` (tied to
every thread's frame by `FrameTie`) and the system invariant's holdings, credits
and debits `db` (`SysInvN`, which fixes each outstanding promise's debit) such
that, for every region `n`: if no thread has promised to hand `rg n` over
(`Debt c db (.rg n) = 0`), then at most one thread holds `rg n` in its frame. -/
theorem token_unique_net {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (h0 : InitOK p k arch Init MintOK c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init MintOK c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hk, -, ht⟩ := machine_tokens_main O h0 hr
  exact ⟨Eg, Tot, HP, HS, cr, db, ht, hN, tokUniq_of_knet hk⟩

/-- **Headline 1, gross form at quiescent configurations.**  At every reachable
configuration with no outstanding promise (every final one), no region token
is held by two threads' frames, where the frames' totals `Tot` are tied to the
threads by `FrameTie`. -/
theorem token_unique_final {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (h0 : InitOK p k arch Init MintOK c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, -, -, hg, ht⟩ := machine_tokens_main O h0 hr
  exact ⟨Eg, Tot, ht, (hg hn).2⟩

/-- **Every reachable thread is well typed**, all at ONE global environment `Eg`
(`FrameTie`): its term is typed, its frame satisfies the resource invariant at
its cut of `Eg` with total `Tot i`, and memory satisfies `MemInv` there (so, by
stage A, every value it loads is a value of the expected type). -/
theorem reachable_typed {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (h0 : InitOK p k arch Init MintOK c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, -, -, -, ht⟩ := machine_tokens_main O h0 hr
  exact ⟨Eg, Tot, ht⟩

/-! ## `Obligations` instantiated at the plant choice

`ObligationsF` is `Obligations` at `plantOf := TermPlantF.plantOf`, `plantN := TermPlantF.plantN`
with the six fields `plantSpec`, `plantCpl`, `promNewOK`, `plantPromOK`, `pubPromOK`, `plantInh`
replaced by the three named facts `runAgree`, `bufInitIni`, `plantClos` (proved in
`TermPromAlloc.promAllocF_of`) (each, except
`plantClos`, with a promise-step and a thread-step conjunct; since the closure fix `plantClos` is
the thread-step `PubClosT` only): 35 fields become 32.  (The W2 gap, formerly the field `w2`, is
closed in `TermPlantW2`.)  (BII) `bufInitIni` is no longer a field: its promise half is
`TermBiiF.bufInitIniF_of` (from `RunAgreeF` and the certificate-run facts), its thread-step half
`TermBiiT.bufInitIniT_of`.  `ObligationsF.toObligations`
discharges the six from the named facts (`TermPlantF.*_of`), using `AllNoProm c0` (`InitOK`'s
second half), so every headline holds modulo `ObligationsF`.  (S10) `promNodup` is not a field
of `ObligationsF`: `toObligations` proves it from `InitOK` (`promNodup_of_initOK`).  Nor is
`plantHid`: `TermPlantHidOf.plantHid_of` gives it from the promiser's post-step part
(`selfPlant`, its `OwnHidP` at the planted cell; `plantF ≥ vWr`) and the promise typing after the
step (`promTyAPostP`). -/

/-- **Every open obligation of headline 1 at the plant choice** (see above). -/
structure ObligationsF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop)
    (c0 : Cfg) : Prop where
  /-- O0 the checker accepts the program (`progT` is `checkProg_sound`). -/
  checked : checkProg p = .ok ()
  /-- O2 (S10) the program passes the syntactic scope check: region-free interim
  (ProgScope), no `∀` in annotations (ProgIall), no ticket lock (D5 `NoTicket`); `scope`,
  `iall`, `noTicket`, `residualNoTicket` follow (TermScope/TermIall). -/
  progScope : TermScope.ProgScopeOKW p = true
  /-- O3 (S10) the initial configuration satisfies the scope run invariant
  (`TermInit.runDRF_spawn` for the spawn shape). -/
  runDRF0 : TermScope.RunScope c0
  /-- T17′ (named run fact, the `NoHoldPub` half of `TermCohLe.CertRunC`) `NoHoldPub` along every
  solo run of the stepper from a thread step's PRE-step configuration.  The scope half is
  `TermCertScope.certScopeC_of` (option (3)); `toObligations` rebuilds `CertRunC` (`certRunC_of`),
  whence `certRunT` (`TermCohLe.certRunT_of`), `wp` (`TermCohLe.wp_of`) and `win` (`TermWin.winM_of`). -/
  certWinC : TermCertScope.CertWinCN p k arch Init MintOK c0
  /-- P4–P7 the `NoHoldPub` half of the run premise of `certified_promLoc` (along the
  certificate of every reachable promise step); the scope half is `TermCertScope.certScopeP_of`
  (option (3)), and `toObligations` rebuilds `TermNoHold.CertRunP` (`certRunP_of`). -/
  certWin : TermCertScope.CertWinPN p k arch Init MintOK c0

/-- (spawn) **The obligations over runs with an extra relation `Sp`**: `ObligationsF`
with the two certificate-window fields over `TCtxX`/`PCtxX … Sp` (`ofF_bot`: the old ones at `Sp := ⊥`). -/
structure ObligationsFX (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res)
    (MintOK : Res → Prop) (c0 : Cfg) : Prop where
  checked : checkProg p = .ok ()
  progScope : TermScope.ProgScopeOKW p = true
  runDRF0 : TermScope.RunScope c0
  certWinC : TermCertScope.CertWinCNX p k arch Sp Init MintOK c0
  certWin : TermCertScope.CertWinPNX p k arch Sp Init MintOK c0

/-- **The old obligations are the new ones at `Sp := ⊥`.** -/
theorem ofF_bot {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (O : ObligationsF p k arch Init MintOK c0) : ObligationsFX p k arch (fun _ _ => False) Init MintOK c0 :=
  ⟨O.checked, O.progScope, O.runDRF0, fun X => O.certWinC X.toBot, fun X => O.certWin X.toBot⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (S10) `InitOK` gives promise well-formedness at `c0` (`TermFul.PWFall`: pair starts
are messages by a thread's `MemOKP`, and there are no promises), unless `c0` has no thread. -/
theorem pwf0_of_initOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (h0 : InitOK p k arch Init MintOK c0) : c0.ths.size = 0 ∨ TermFul.PWFall c0 := by
  obtain ⟨⟨Eg, Tot, HP, HS, cr, db, hW, -⟩, hn, -⟩ := h0
  cases hth : c0.ths[0]? with
  | none => exact Or.inl (Nat.le_zero.1 (Array.getElem?_eq_none_iff.1 hth))
  | some th =>
      obtain ⟨S, -, -, hm, -⟩ := hW.thr 0 th hth
      have hpr : ∀ q, q ∈ c0.pairs → q < c0.mem.size := fun q hq => Nat.lt_of_succ_lt (hm.1.2.2 q hq)
      refine Or.inr fun i => ⟨hpr, fun t ht => ?_⟩
      unfold TermFul.promsOf at ht
      cases hc : c0.ths[i]? with
      | none => simp [hc] at ht
      | some thi => simp [hc, hn i thi hc] at ht

/-- (S10) `TermBal.PromNodupR` at an initial configuration (`InitOK`). -/
theorem promNodup_of_initOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (h0 : InitOK p k arch Init MintOK c0) :
    TermBal.PromNodupR p k arch (fun _ _ => False) c0 :=
  TermBal.promNodupR_of (fun _ _ hf _ => hf.elim) (fun n th h => by rw [h0.2.1 n th h]; exact List.nodup_nil) (pwf0_of_initOK h0)

/-- (spawn) **The run-closed start facts** of `toObligationsCX` over `StepsG … Sp` (at `Sp := ⊥`
from the old start facts, `SpArms.bot`; at `Sp := Spawn …` the arms). -/
structure SpArms (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop where
  viewInv : TermViewInv.ViewInvR p k arch Sp c0
  promNodup : TermBal.PromNodupR p k arch Sp c0
  runDRF : TermScope.RunScopeR p k arch Sp c0
  promViewLt : TermPlantF.PromViewLtR p k arch Sp c0
  promPos : TermPlantAtPos.PromPosR p k arch Sp c0

/-- `SpArms` at `Sp := ⊥` from the old start facts (no premise beyond them). -/
theorem SpArms.bot {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 : Cfg} (hps : TermScope.ProgScopeOK p = true)
    (h0 : AllNoProm c0) (hvi : TermViewInv.ViewInv c0) (hpn : TermBal.PromNodupR p k arch (fun _ _ => False) c0)
    (hdrf : TermScope.RunScope c0) : SpArms p k arch (fun _ _ => False) c0 :=
  ⟨TermViewInv.viewInvR_bot hvi, hpn, TermScope.runDRFR_bot hps hdrf,
    TermPlantF.promViewLtR_of (fun _ _ hf _ => hf.elim) h0, TermPlantAtPos.promPosR_of (fun _ _ hf _ => hf.elim) h0⟩

/-- (spawn) **`Obligations` over `StepsG … Sp` from `ObligationsFX`** and the run-closed start facts
(`SpArms`); the body of the old `ObligationsF.toObligationsC`. -/
theorem ObligationsFX.toObligationsCX (O : ObligationsFX p k arch Sp Init (fun _ => True) c0)
    (hk : k.storeDepRts = true) (A : SpArms p k arch Sp c0) :
    Obligations p k arch Sp Init (fun _ => True) c0 TermPlantF.plantOf TermPlantF.plantN := by
  obtain ⟨hvi, hpn, hdrf, h0, h0P⟩ := A
  haveI : TermTyped.WrIniC := TermWrSiteA.wrIniC
  have hPSc : TermScope.ProgScopeOK p = true := TermScope.ProgScopeOKW.scope O.progScope
  haveI hCkW : TermA4.ProgCkWC p := ⟨TermA4.progCkW_of_scopeW O.progScope⟩
  have hRC : TermCohLe.CertRunC p k arch Sp Init (fun _ => True) c0 :=
    TermCertScope.certRunC_of (TermCertScope.certScopeC_of hPSc hdrf) (TermCertScope.certWinC_of_N O.certWinC)
  have hRP : TermNoHold.CertRunP p k arch Sp Init (fun _ => True) c0 :=
    TermCertScope.certRunP_of (TermCertScope.certScopeP_of hPSc hdrf) (TermCertScope.certWinP_of_N O.certWin)
  have hP : ProgT p := TermScope.progT_of_check O.checked
  have hR : ProgRetIall p :=
    ⟨fun _ hd => TermScope.noIallV_of_drf _ (TermScope.ProgScopeOK.decl hPSc hd).2.1⟩
  -- the plant provenance from the SysInvN clause `plantIdx` (`TermPlantAtB`); K-4 is the run (v3d)
  have hNP : TermPtrKey.NoFulPlRunGL p k arch :=
    haveI := hR; TermPtrKey.noFulPlRunGL_of (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermK2aFin.ptrRtsThreadGL_v3d (TermFulCntROf.fulCntR_of p)) (TermPtrKey.footNCB_of p pwSkel_ok pwSubS_ok pwSig_ok)
  have hRA : TermPlantF.RunAgreeF p k arch Sp Init (fun _ => True) c0 := TermRunPay.runAgreeF_of (haveI := hR; TermRunLocK.runAgreeFT3_holds (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) h0 hk hP hPSc hdrf
    (TermCertScope.certScopeP_of hPSc hdrf) (TermCertScope.certWinP_of_N O.certWin) (TermCertScope.certWinC_of_N O.certWinC) hNP).1
  have hRT : TermPlantF.RunAgreeT p k arch Sp Init (fun _ => True) c0 := TermRunPayT.runAgreeT_of hvi (haveI := hR; TermRunLocK.runAgreeFT3_holds (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) h0 hk hP hPSc hdrf
    (TermCertScope.certScopeP_of hPSc hdrf) (TermCertScope.certWinP_of_N O.certWin) (TermCertScope.certWinC_of_N O.certWinC) hNP).2
  -- (iniop) the run-wide `bufInit` exclusion at published cells, from the certificate windows
  have hBP : TermPlantF.BufInitPubF p k arch Sp Init (fun _ => True) c0 :=
    haveI := hR; TermIniOpK.bufInitPubF_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCertScope.certScopeP_of hPSc hdrf) (TermCertScope.certWinP_of_N O.certWin)
  -- the run-wide `bufInit` exclusion after the run's own publish, from the certificate windows
  have hBPR : TermPlantF.BufInitPubFR p k arch Sp Init (fun _ => True) c0 :=
    haveI := hR; TermK5Z.bufInitPubFR_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCertScope.certScopeP_of hPSc hdrf) (TermCertScope.certWinP_of_N O.certWin)
  -- (BII) the promise half of the old `bufInitIni` field, from the run facts and `RunAgreeF`
  have ObufInitIni : TermPlantF.BufInitIniFT p k arch Sp Init (fun _ => True) c0 :=
    ⟨haveI := hR; TermBiiF.bufInitIniF_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP hRA hBP hBPR,
      haveI := hR; TermBiiT.bufInitIniT_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCertScope.certScopeC_of hPSc hdrf)
      (TermCertScope.certWinC_of_N O.certWinC)⟩
  have hBT : TermPlantF.BufInitPubT p k arch Sp Init (fun _ => True) c0 :=
    haveI := hR; TermIniOpK.bufInitPubT_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCertScope.certScopeC_of hPSc hdrf) (TermCertScope.certWinC_of_N O.certWinC)
  -- (runAgree) the run-wide `bufInit` exclusion after the thread-step run's publish, from the certificate windows
  have hBTR : TermPlantF.BufInitPubTR p k arch Sp Init (fun _ => True) c0 :=
    haveI := hR; TermBufPubT.bufInitPubTR_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCertScope.certScopeC_of hPSc hdrf) (TermCertScope.certWinC_of_N O.certWinC)
  have OplantAtT : TermPlantFul.PlantAtT p k arch Sp Init (fun _ => True) c0 :=
    TermPlantAtB.plantAtT_ofB (hV0 := hvi) hPSc hdrf (TermCertScope.certWinC_of_N O.certWinC) h0P hk hNP
  have hPA : TermPromClos.PromAllocF p k arch Sp Init (fun _ => True) c0 :=
    haveI := hR; TermPromAlloc.promAllocF_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCohLe.certRunT_of hRC) h0
  have hsp : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts},
      PCtxX p k arch Sp Init (fun _ => True) c0 c Eg Tot HP HS cr db j th a v w →
      (∃ l f, TermPlantF.plantOf c Eg j a v w l = some f) →
      ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
        ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
          (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
          (Tot j) HP' HS' cr' db' ∧
        (∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop,
          ¬ WordUnit (Cut Eg j S) m.loc → cr' t = cr j t) :=
    fun X _ => TermSelfPlantK.selfPlant_ofNK (hV0 := hvi) hP hRP
      (TermPlantF.plantPromOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR))
      (TermPlantF.promNewOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR))
      (TermPlantW2.plantInh_ofP (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR
      (TermPlantF.plantPromOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR))) (fun hm => hm.2.2.2.1.2) X
      (fun S => @TermPromStep.hwu_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) p k arch Init (fun _ => True) c0 Sp hR _ hP hRP _ _
        (fun X => TermPlantF.plantSpec_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP X)
        (TermPlantF.promNewOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR)) _ _ _ _ _ _ _ _ _ _ _ _ X S)
      (fun S => @TermPromStep.hfw_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) p k arch Init (fun _ => True) c0 Sp hR _ hP hRP _ _ _ _ _ _ _ _ _ _ _ _ X S)
  exact { O with
    runDRF0 := hdrf
    progScope := hPSc
    ckW := hCkW
    seenFacts := hvi
    bufInitHeld := fun X Y => TermPinBIOf.bufInitHeld_of X Y
    storeCrZH := fun X Y =>
      ⟨TermStoreNI.storeNI_of X
      (TermSeenHid.seenHid_of X (fun Y' => TermScope.scope_of hPSc hdrf X Y')
        (TermViewInv.envVR_of_run hvi X.run X.hth)
        ⟨congrArg TEnv.sto Y.1, congrArg TEnv.pfr Y.1, congrArg TEnv.ini Y.1, congrArg TEnv.rini Y.1,
          congrArg TEnv.tid Y.1⟩ (TermUndefInv.undefAt_cut X.inv.undefAt (congrArg TEnv.sto Y.1))),
        TermPiece.storeLeafPay_of⟩
    certRun := hRP
    promNodup := hpn
    plantFulfil := TermPlantFul.plantFulfil_of h0 (TermPlantFul.ownKeyT_of (TermScope.scope_of hPSc hdrf)) (TermPlantFul.plantPendT_of OplantAtT)
    plantOp := TermPlantOpG.plantOp_of h0 (TermPlantFul.ownKeyT_of (TermScope.scope_of hPSc hdrf)) OplantAtT TermOverCr.plantOpG_of
    mintClosedT := TermBal.mintClosedT_true
    promPred := haveI := hR; TermStepPred.promPred_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP h0 hRC
    allocG := TermPromStep.allocG_of
    bnamedT := TermBNamed.bnamedT_of
    rmw := TermRmw.rmw_of (TermScope.scope_of hPSc hdrf)
    wp := haveI := hR; TermCohLe.wp_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRC
    certRunT := TermCohLe.certRunT_of hRC
    win := TermWin.winM_of hRC
    ownCohLe := TermCohLe.ownCohLe_of TermOwnCoh.ownCohInvT_of
    newForeignTyped := TermB5.newForeignTyped_of (TermScope.scope_of hPSc hdrf)
    newPair := TermB5.newPair_of (TermScope.scope_of hPSc hdrf)
    promNoTwoPost := @TermB5.promNoTwoPost_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) p k arch Init (fun _ => True) c0 Sp hR _ hP (TermCohLe.certRunT_of hRC) (fun X => X.inv.promNoTwo)
    hwu := fun X S => @TermPromStep.hwu_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) p k arch Init (fun _ => True) c0 Sp hR _ hP hRP _ _
      (fun X => TermPlantF.plantSpec_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP X)
      (TermPlantF.promNewOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR)) _ _ _ _ _ _ _ _ _ _ _ _ X S
    hfw := fun X S => @TermPromStep.hfw_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) p k arch Init (fun _ => True) c0 Sp hR _ hP hRP _ _ _ _ _ _ _ _ _ _ _ _ X S
    plantSpec := fun X => ⟨TermPlantF.plantSpec_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP X,
      TermZwIniP.plantN_zw (TermPlantF.plantSpec_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP X), TermPredHoldP.plantHeld_of X⟩
    promClosP := fun X => TermPromClos.promClos_prom (TermNoHold.promLocF_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP) X
    promAlloc := hPA
    plantCpl := TermPlantF.plantCpl_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP
    promNewOK := TermPlantF.promNewOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR)
    plantPromOK := TermPlantF.plantPromOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR)
    pubPromOK := TermPlantF.pubPromOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCohLe.certRunT_of hRC) h0 hRT hBT hBTR ObufInitIni.2 (TermPromClos.pubClosT_of hPA) (TermPlantW2.pubWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP (TermCohLe.certRunT_of hRC) h0 hRT hBT hBTR (TermPromClos.pubClosT_of hPA))
    plantInh := TermPlantW2.plantInh_ofP (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR
      (TermPlantF.plantPromOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR))
    selfPlant := hsp
    plantIdxT := haveI := hR; TermPlantAtB.plantIdxT_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hPSc hdrf (TermCertScope.certWinC_of_N O.certWinC) h0 hNP
    plantIdxP := haveI := hR; TermPlantAtB.plantIdxP_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hPSc hdrf (TermCertScope.certWinP_of_N O.certWin) hNP
    plantL := fun hth h => TermPlantF.plantOf_some hth h
    plantPair := TermPlantPair.plantPair_of (fun X => TermPlantF.plantSpec_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP X)
      (fun X hpl => let ⟨a1, a2, a3, a4, b1, b2, _⟩ := hsp X hpl; ⟨a1, a2, a3, a4, b1, b2⟩)
      (haveI := hR; TermPlantF.promNoTwoP_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP)
    plantHid := TermPlantHidOf.plantHid_of (fun X => TermPlantF.plantSpec_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP X)
      (fun X hpl => let ⟨a1, a2, a3, a4, b1, b2, _⟩ := hsp X hpl; ⟨a1, a2, a3, a4, b1, b2⟩)
      (TermPlantF.promTyAPostP_of (fun X => TermPlantF.plantSpec_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP X)
        (TermPlantF.promNewOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR))
        (TermPlantF.plantPromOK_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR ObufInitIni.1 (TermPlantW2.promWordW_of (hV0 := hvi) (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP hRP h0 hRA hBP hBPR))) }

/-- **The common body of `ObligationsF.toObligations` and `TermSpawn.toObligationsS`**:
`Obligations` from `ObligationsF` given the three start facts they use (no promise, `ViewInv`,
`PromNodupR`). -/
theorem ObligationsF.toObligationsC (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : AllNoProm c0) (hvi : TermViewInv.ViewInv c0) (hpn : TermBal.PromNodupR p k arch (fun _ _ => False) c0) :
    Obligations p k arch (fun _ _ => False) Init (fun _ => True) c0 TermPlantF.plantOf TermPlantF.plantN :=
  (ofF_bot O).toObligationsCX hk (SpArms.bot (TermScope.ProgScopeOKW.scope O.progScope) h0 hvi hpn O.runDRF0)

/-- **`ObligationsF` gives `Obligations` at `TermPlantF.plantOf`/`plantN`** (at an initial
configuration, `InitOK`). -/
theorem ObligationsF.toObligations (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hI : InitOK p k arch Init (fun _ => True) c0) :
    Obligations p k arch (fun _ _ => False) Init (fun _ => True) c0 TermPlantF.plantOf TermPlantF.plantN := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := hI.1
  exact O.toObligationsC hk hI.2.1 hv (promNodup_of_initOK hI)

end

/-! ### The balance conjunct at `MintOK := fun _ => True`

The finals below instantiate `MintOK` with `fun _ => True`, so the balance conjunct of `SysInvW`
(`∃ M, MintOK M ∧ Σ(Tot + credits + HP) + HS ≤ Init + M + Σ debits`) is vacuous: any `M`
witnesses it.  Nothing is lost by this.  The per-key bounds for the exclusive keys `rg`, `wd` and
`own` are carried separately, by the `tok`, `wd` and `own` clauses of `SysInvW` (`KeySum ≤ 1`)
and by `KeyNet` (net of outstanding promise debits).  Epoch keys `ep` and share keys `sh` are
not bounded by these theorems.  No other proof consumes the balance conjunct; it is only
re-established step by step. -/

/-- `machine_tokens_main` modulo `ObligationsF`. -/
theorem machine_tokens_mainF {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  machine_tokens_main (O.toObligations hk h0) h0 hr

/-- `token_unique_net` modulo `ObligationsF`. -/
theorem token_unique_netF {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_net (O.toObligations hk h0) h0 hr

/-- `token_unique_final` modulo `ObligationsF`. -/
theorem token_unique_finalF {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_final (O.toObligations hk h0) h0 hr hn

/-- `reachable_typed` modulo `ObligationsF`. -/
theorem reachable_typedF {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot :=
  reachable_typed (O.toObligations hk h0) h0 hr

/-! ## Finals at the standard initial configuration (`TermInit.InitShape`; no `InitOK` premise) -/

/-- `machine_tokens_main` at an `InitShape` start (`initOK_of`). -/
theorem machine_tokens_main_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (hs : TermInit.InitShape p c0) (hM : MintOK .zero) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init MintOK c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  machine_tokens_main O (initOK_of hs hM) hr

/-- `token_unique_net` at an `InitShape` start (`initOK_of`). -/
theorem token_unique_net_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (hs : TermInit.InitShape p c0) (hM : MintOK .zero) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init MintOK c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_net O (initOK_of hs hM) hr

/-- `token_unique_final` at an `InitShape` start (`initOK_of`). -/
theorem token_unique_final_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (hs : TermInit.InitShape p c0) (hM : MintOK .zero) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_final O (initOK_of hs hM) hr hn

/-- `reachable_typed` at an `InitShape` start (`initOK_of`). -/
theorem reachable_typed_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
    (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (hs : TermInit.InitShape p c0) (hM : MintOK .zero) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot :=
  reachable_typed O (initOK_of hs hM) hr

/-- `machine_tokens_mainF` at an `InitShape` start (`initOK_of`). -/
theorem machine_tokens_mainF_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hs : TermInit.InitShape p c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  machine_tokens_mainF O hk (initOK_of hs trivial) hr

/-- `token_unique_netF` at an `InitShape` start (`initOK_of`). -/
theorem token_unique_netF_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hs : TermInit.InitShape p c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_netF O hk (initOK_of hs trivial) hr

/-- `token_unique_finalF` at an `InitShape` start (`initOK_of`). -/
theorem token_unique_finalF_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hs : TermInit.InitShape p c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_finalF O hk (initOK_of hs trivial) hr hn

/-- `reachable_typedF` at an `InitShape` start (`initOK_of`). -/
theorem reachable_typedF_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hs : TermInit.InitShape p c0) {c : Cfg}
    (hr : TermStep.Steps p k arch c0 c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot :=
  reachable_typedF O hk (initOK_of hs trivial) hr

#print axioms Obligations.progT
#print axioms Obligations.retIall
#print axioms Obligations.scope
#print axioms Obligations.seenHid
#print axioms Obligations.iall
#print axioms niDeep_of_drf
#print axioms opAtom_free
#print axioms opNI_of
#print axioms Obligations.opNI
#print axioms Obligations.dwf
#print axioms Obligations.residualNoTicket
#print axioms Obligations.noTicket
#print axioms initOK_of
#print axioms lblSto_of_initShape
#print axioms cfgCoh_of_initShape
#print axioms machine_tokens_main
#print axioms sysInv_step
#print axioms sysInv_run
#print axioms tokUniq_of_knet
#print axioms token_unique_net
#print axioms token_unique_final
#print axioms reachable_typed
#print axioms pwf0_of_initOK
#print axioms promNodup_of_initOK
#print axioms ObligationsF.toObligationsC
#print axioms ofF_bot
#print axioms SpArms.bot
#print axioms ObligationsFX.toObligationsCX
#print axioms ObligationsF.toObligations
#print axioms machine_tokens_mainF
#print axioms token_unique_netF
#print axioms token_unique_finalF
#print axioms reachable_typedF
#print axioms machine_tokens_main_init
#print axioms token_unique_net_init
#print axioms token_unique_final_init
#print axioms reachable_typed_init
#print axioms machine_tokens_mainF_init
#print axioms token_unique_netF_init
#print axioms token_unique_finalF_init
#print axioms reachable_typedF_init

end TermMain
