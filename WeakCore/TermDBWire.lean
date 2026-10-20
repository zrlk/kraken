import WeakCore.TermBoxPlantSep
import WeakCore.TermK2aFin
import WeakCore.TermMemRtsProm
import WeakCore.TermPtrRtsK

/-!
# TermDBWire (D-B): the thread-step supplies of `granW` and the wiring wrappers

* `granuleW_T` — `GranuleW` across a thread step of `i`, at `EgT` (`TermGranStep.granuleW_stepNF` with
  the context facts of `GLT`: `FootNCE`, `ownProm_sto_keep` for outstanding promises).
* `granuleW_thread` — the same at `ptrRtsGL_thread`'s hypotheses.
* `ptrGL_promW` — `PtrRtsGL` across a promise step at a `PCtx`, from `SysInvN` (`promClos`/`promInCut`,
  `fgnClos`, `cellOwn`, `boxSto`) and the clause `FgnPromCntG` (`TermMemRtsProm.memRtsCG_promX`).
-/

namespace TermPtrRtsK

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermInterf TermPlantF TermPromClos TermCert TermGlob TermTyped TermPtrRts TermGranW TermBal
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
  {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
  {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`granW` across a thread step** of `i`, at `EgT`. -/
theorem granuleW_T
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS) :
    GranuleW (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto c'.mem c'.pairs := by
  have h1 : ∀ l cl, (CE η).sto l = some cl → Eg.sto l = some cl :=
    fun l cl h => by rw [H.Y.1] at h; exact cut_sto_le Eg i S l cl h
  have h4 : ∀ l cl, (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl → Eg.sto l = none →
      (CE η).sto l = none ∧ E'.sto l = some cl := by
    intro l cl h hS
    by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
    · exact ⟨(ceFresh H hf).1, (egT_sto_fresh hf).symm.trans h⟩
    · rw [TermPtrStab.EgT_sto_old hf] at h; rw [h] at hS; cases hS
  have hRE : ThInvRE p (CE η) th (Tot i) :=
    ⟨ρ, η, cx, Rf, Rs, rfl, H.Y.2.2.1, H.Y.2.2.2.1, H.Y.2.2.2.2.1, H.Y.2.2.2.2.2.1, H.Y.2.2.2.2.2.2, H.hRP⟩
  rw [H.X.e1, H.X.e2]
  exact TermGranStep.granuleW_stepNF h1
    (fun l cl h => by
      by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
      · rw [(gfreshL_of H hf).1] at h; cases h
      · rw [TermPtrStab.EgT_sto_old hf]; exact h)
    hRE.thInvE H.hm H.X.hr H.hsc H.hGW (fun l hf => (gfreshL_of H hf).1)
    (fun l cl h => H.hLay l cl (h1 l cl h))
    (fun u hu m hmu hS => by
      rw [ownProm_sto_keep H.hA H.X H.Y (H.Z.toC _ _ _ _ _) H.hS H.hPfrP hu (by rw [H.X.e1]; exact hmu)]; exact hS)
    (fun q hq m0 cl h0 hc hS => H.hNCE.1 q hq m0 cl h0 (h4 _ _ hc hS).2 (h4 _ _ hc hS).1)
    (fun v mv cl o hv hP hc hS ho hT => H.hNCE.2 v mv cl o hv hP (h4 _ _ hc hS).2 (h4 _ _ hc hS).1 ho hT)

/-- **`granuleW_thread`**: `granuleW_T` at `ptrRtsGL_thread`'s hypotheses. -/
theorem granuleW_thread (hK : PtrRtsThreadGL p) (hk : k.storeDepRts = true)
    (hb1 : AllocGT p k arch Sp Init MintOK c0) (hA : PromAllocF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hKS : ∀ t l, crS t (.own l) = cr i t (.own l))
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hPC : TermPtrKey.PubConsumeC th C)
    (hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hNCE : FootNCE (CE η) E' r) (hG : PtrRtsGL Eg Tot HP c) (hGW : GranuleW Eg.sto c.mem c.pairs)
    (hLay : ∀ l cl, Eg.sto l = some cl → LayT cl.ty) (hsc : TermTyped.ScopeOK p th)
    (hdrf : TermScope.ThScope th) (hps : TermScope.ProgScopeOK p = true) (hPT : ProgT p)
    (hFBP : TermFootBP0.FootBP { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } E' th r)
    (hRP : RetPw th.σs th.stack cx.ret) (hBP : BoxPlantSep Eg Tot HP c) :
    GranuleW (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto c'.mem c'.pairs :=
  granuleW_T (S := S) (ρ := ρ) (cx := cx) (F := F)
    ⟨hK, hk, hb1, hA, X, Y, Z, hS, hKS, hm, hPC, hPfrP, hNCE, hG, hGW, hLay, hsc, hdrf, hps, hPT, hFBP, hRP, hBP⟩

/-- **`ptrGL` across a promise step** at a `PCtx`, at the plant map `P` (`hPL`, the `Obligations`
field `plantL`). -/
theorem ptrGL_promW {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res}
    {cr' db' : Ts → Res} {N : AllocLabel → Nat} {n : Nat}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    (hG : PtrRtsGL Eg Tot HP c) (hFC : FgnPromCntG Eg c) :
    PtrRtsGL (EgP Eg P N j n) Tot (upd HP j HP') (promise c j a v w) :=
  TermPtrStab.ptrRtsGL_prom X.hth hPL X.inv.plt hG (TermPtrKey.ownKey_prom_le X hA hdb)
    (TermPtrStab.noEdgeUnpl_of X.inv.promClos X.inv.promInCut) X.inv.fgnClos
    (TermCellOwn.nonPromLbl_ofM X.inv X.inv.cellOwn X.hth) X.inv.boxSto
    (TermMemRtsProm.memRtsCG_promX X hPL hA hdb hG hFC)

end

end TermPtrRtsK

#print axioms TermPtrRtsK.granuleW_T
#print axioms TermPtrRtsK.granuleW_thread
#print axioms TermPtrRtsK.ptrGL_promW
