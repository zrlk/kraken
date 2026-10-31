import WeakCore.TermPlantAtJ
import WeakCore.TermPlantAtW
import WeakCore.TermPromAlloc
import WeakCore.TermPromStep
import WeakCore.TermPlantF
import WeakCore.TermCertScope
import WeakCore.TermOwnFresh
import WeakCore.TermPubOnly
import WeakCore.TermMsgWords

/-! # TermPlantAtB: the staged bridge to the `Obligations` fields `plantIdxT`/`plantIdxP`

`plantIdxT_of` / `plantIdxP_of` have exactly the types of the `Obligations` fields
`plantIdxT` / `plantIdxP` (at `TermPlantF.plantOf`/`plantN`), from the `ObligationsF` facts
`toObligations` already builds (`ProgT`, `ProgRetIall`, scope, `RunScope`, `CertWinC`/`CertWinP`,
`CertRunC`, `AllNoProm`), the `SysInvN` clause `cfgCoh`, and the staged inputs
below (named Props, hypotheses only; each becomes a theorem/`SysInvN` clause upstream):
* (`TermPtrRts.NoFulStep p` is the `TermPubOnly.noFul_step_typed`) `TermPtrKey.NoFulPlRunGL p k arch`
  (`TermPtrKey.noFulPlRunGL_of`: K-2a v3d, `FootNCB`; the return link from `ThInvE`'s `RetPw`);
* `TermPlantAtW.PtrRtsAt` is `ptrRtsAt_of` (the clause `ptrGL`); the post-promise `PtrRtsG` is an
  argument of `plantIdxP_of` (supplied at the promise site by `TermPtrRtsK.ptrGL_promW`);
* `PromInCut`: the `SysInvN.promInCut`.  Own messages in their cells: the `TermMsgWords.msgInCell_of`.
-/

namespace TermPlantAtB
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermLiveProps (CohAt CfgCoh)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (D-B) `PtrRtsAt` is the `SysInvN` clause `ptrGL` at the step's pre-state. -/
theorem ptrRtsAt_of : TermPlantAtW.PtrRtsAt p k arch Sp Init MintOK c0 := fun X hk => X.inv.ptrGL hk

/-- **The `Obligations` field `plantIdxT`**, from `plantIdx_thread`. -/
theorem plantIdxT_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hps : TermScope.ProgScopeOK p = true)
    (h0d : TermScope.RunScopeR p k arch Sp c0) (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    (∀ t l, crS t (.own l) = cr i t (.own l)) →
    MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    (∀ l, TermOwnG0Defs.PubAt th l → 1 ≤ C (.own l)) → k.storeDepRts = true →
    TermPlantAtT.PlantIdxG TermPtrRts.tminG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c' :=
  fun X Y Z hS hK hm hPfr hPC hk =>
    TermPlantAtJ.plantIdx_thread X Y Z hS hK hk hm TermPromStep.allocG_of hPfr hPC
      (TermPromAlloc.promAllocF_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP
        (TermCohLe.certRunT_of (TermCertScope.certRunC_of (TermCertScope.certScopeC_of hps h0d) hCW)) h0)
      (TermPlantAtW.noFulT_tminG (hV0 := hV0) hps h0d hCW (TermPubOnly.noFul_step_typed p) hNP ptrRtsAt_of)
      X.inv.cfgCoh (X.inv.plantIdx hk)

/-- `gOf` is unchanged by a promise step (`TermMain.promise_g`, which is downstream). -/
theorem promise_gB (c : Cfg) (i : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) (j : Nat) :
    gOf p k arch (promise c i a v w) j = gOf p k arch c j := by
  unfold gOf
  rw [TermStep.promise_n, tysOf_promise]
  unfold promise
  split <;> rfl

/-- **The `Obligations` field `plantIdxP`** at `TermPlantF.plantOf`/`plantN`, from `plantIdx_prom`. -/
theorem plantIdxP_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hps : TermScope.ProgScopeOK p = true)
    (h0d : TermScope.RunScopeR p k arch Sp c0) (hCWP : TermCertScope.CertWinP p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' →
    ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
      (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' →
    k.storeDepRts = true →
    TermPtrRts.PtrRtsGL (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      Tot (upd HP j HP') (promise c j a v w) →
    TermPtrRts.BoxPlantSep (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
      Tot (upd HP j HP') (promise c j a v w) →
    TermPlantAtT.PlantIdxG TermPtrRts.tminG (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) Tot (upd HP j HP')
      (promise c j a v w) := by
  intro c Eg Tot HP HS cr db j th a v w HP' HS' cr' db' X hA hS hk hPG hBP
  have hRP : TermNoHold.CertRunP p k arch Sp Init MintOK c0 :=
    TermCertScope.certRunP_of (TermCertScope.certScopeP_of hps h0d) hCWP
  obtain ⟨S1, hSA⟩ := hS
  have hwin1 := (hCWP X).2 HP' HS' cr' db' S1 hSA
  obtain ⟨hRE, hTE, hm, hHP, hHS, hK⟩ := hSA
  obtain ⟨epc, -, -⟩ := promise_inv (a := a) (v := v) (w := w) X.hth
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [epc]
  have hpairs : (promise c j a v w).pairs = c.pairs := by rw [epc]
  have hm1 : MemInv (gOf p k arch (promise c j a v w) j)
      (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S1)
      (stOf (promise c j a v w).mem (promise c j a v w).pairs { th with promises := th.promises ++ [c.mem.size] }) := by
    rw [promise_gB, hmem, hpairs]; exact hm
  exact TermPlantAtJ.plantIdx_prom (hV0 := hV0) X hk hA (fun l => (TermOwnFresh.promCrK_own hK l).2)
    (TermPlantF.plantSpec_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hRP X) (TermPtrStab.noEdgeUnpl_of X.inv.promClos X.inv.promInCut) (fun S => TermMsgWords.msgInCell_of X.inv X.hth S)
    hNP hwin1 hps h0d hTE hm1 hPG hBP
    (X.inv.plantIdx hk)

/-- **The removed `ObligationsF` field `plantAtT`**, from the `SysInvN` clause `plantIdx`
(`TermPlantAtT.plantAtT_of` at `tminG`). -/
theorem plantAtT_ofB (hV0 : TermViewInv.ViewInvR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true)
    (h0d : TermScope.RunScopeR p k arch Sp c0) (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0)
    (h0 : TermPlantAtPos.PromPosR p k arch Sp c0) (hk : k.storeDepRts = true) (hNP : TermPtrKey.NoFulPlRunGL p k arch) :
    TermPlantFul.PlantAtT p k arch Sp Init MintOK c0 :=
  TermPlantAtT.plantAtT_of hk h0 (fun X => X.inv.plantIdx hk)
    (TermPlantAtW.noFulT_tminG (hV0 := hV0) hps h0d hCW (TermPubOnly.noFul_step_typed p) hNP ptrRtsAt_of)

end

#print axioms plantIdxT_of
#print axioms plantIdxP_of
#print axioms plantAtT_ofB

end TermPlantAtB
