/-
(selfPlantK) **The self plant keeps old credits at non-word units.**  `K`-copies of the
plant chain (`PromCrK_lift(Q)` → `ThSysAt_flip1/plant1/plantQ` → `ThSysAt_plantL` →
`ThSys_plantR` → `selfPlant_ofN`), each exporting `KeepNW`: an old promise at a non-word unit
keeps its credit.  Credits move only inside `PromCrK_lift(Q)`, where a non-word unit's credit
is `OldCr` (zero) on both sides or untouched.  Proof bodies otherwise verbatim.
-/
import WeakCore.TermPlantR1
import WeakCore.TermK2aRet
import WeakCore.TermOverCr4
namespace TermSelfPlantK
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermMain TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (RetPw merge) local copies of TermMain's `pwSkel_ok` / `pwSubS_ok` / `pwSig_ok`. -/
theorem pwSkelK : PwSkel := fun _ _ h ws => (TermK2a.pubWords_of_skel h).2.1 ws
/-- (copy) -/
theorem pwSubSK : PwSubS := fun _ _ _ h σs c d ws => (TermK2a.pubWords_subS h σs c d).2.1 ws
/-- (copy) -/
theorem pwSigK : PwSig := TermK2a.pubWords_sig

section Lift
open TermPlant

end Lift

section At

end At

section PlantQ
open TermPlantR1

end PlantQ

section Steps
open TermPlantR1
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}

end Steps

section PlantR
open TermCut TermSys TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS TermPlantP TermPlantR1
open WeakMem (Val VState Arch)
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (selfPlantK) **`selfPlant` with old credits kept at non-word units**: `selfPlant_ofN`
without `SelfPlantRestN` (vacuous by `stoNI`), exporting `KeepNW` at every cut of `j`. -/
theorem selfPlant_ofNK (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hPC : ∀ {g : G} {E : TEnv} {s : St}, MemInv g E s → PrivCoh E s)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hwu : ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfw : ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) :
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' ∧
      (∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop,
        ¬ WordUnit (Cut Eg j S) m.loc → cr' t = cr j t) := by
  refine ThSys_plantRK (hV0 := hV0) (hPS := pwSkelK) (hSub := pwSubSK) (hSig := pwSigK) hP hrun X hwu hfw hPO hNO hInh (fun l f cl hf hno hcl => ?_) (privSlot_any (hV0 := hV0) (hPS := pwSkelK) (hSub := pwSubSK) (hSig := pwSigK) hP hrun hPC X)
  obtain ⟨N, e, us, hT, hu, hR⟩ := plantNew_shape (hV0 := hV0) (hPS := pwSkelK) (hSub := pwSubSK) (hSig := pwSigK) hP hrun X hf hno hcl
  by_cases hb : WordBufT cl.ty
  · exact .inl hb
  · by_cases hU : UnitT cl.ty
    · exact .inr (.inl hU)
    · refine .inr (.inr (hR hU ?_))
      have h := X.inv.stoNI l cl hcl
      rw [hT] at h
      simpa only [noIallV] using h

/-- (selfPlantK, the `Obligations` form) `selfPlant_ofNK` at every promise context planting a
label, from per-context `HWU`/`HFW` (as at `TermMain`'s `selfPlant` call). -/
theorem selfPlantK_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPO : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hNO : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hInh : TermInterf.PlantInhF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN)
    (hPC : ∀ {g : G} {E : TEnv} {s : St}, MemInv g E s → PrivCoh E s)
    (hwuF : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
      {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts},
      PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, HWU p (gOf p k arch c j) c.mem c.pairs th (Tot j) a v w (Cut Eg j S))
    (hfwF : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
      {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts},
      PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, HFW p (gOf p k arch c j) c.mem c.pairs th (Tot j) a (Cut Eg j S)) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
      {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts},
      PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      (∃ l f, TermPlantF.plantOf c Eg j a v w l = some f) →
      ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
        ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
          (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
          (Tot j) HP' HS' cr' db' ∧
        (∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop,
          ¬ WordUnit (Cut Eg j S) m.loc → cr' t = cr j t) :=
  fun X _ => selfPlant_ofNK (hV0 := hV0) hP hrun hPO hNO hInh hPC X (hwuF X) (hfwF X)

end PlantR

#print axioms selfPlantK_of
#print axioms selfPlant_ofNK

end TermSelfPlantK
