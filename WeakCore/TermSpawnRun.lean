import WeakCore.TermWrSiteA
import WeakCore.TermSpawn
import WeakCore.TermInterfObs
/-!
# TermSpawnRun — J-a: `OwnLive` and the observer clauses along any run

Copies of `TermMain.sysInv_thread` / `sysInv_prom` (proof text verbatim) with the new invariant's
witness named (`suffices`), so the ghost-owner and observer facts can be carried.
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermInterf TermMain TermInterfObs
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

local instance instWrIniCSpawnRun : TermTyped.WrIniC := TermWrSiteA.wrIniC

/-- (R1) Every non-thread index is an observer whose reader clauses hold at the empty `seen`. -/
def ObsAll (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ j, c.ths.size ≤ j → PubDefP (Cut Eg j (fun _ => False)) c.mem [] ∧
    PubPair (Cut Eg j (fun _ => False)) c.mem c.pairs [] ∧ PubLive (Cut Eg j (fun _ => False)) c.mem

/-- `SysInvNx` with live ghost owners and the observers. -/
def SysInvO (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c : Cfg) : Prop :=
  ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
    SysInvN p k arch Init MintOK c Eg Tot HP HS cr db ∧ OwnLive Eg c ∧ ObsAll Eg c

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`sysInvO_threadR` with a side fact and the witness frame**: the post-step `SysInvN` with
`OwnLive`/`ObsAll`, any property `Post` of the post-step environment (as `TermMain.sysInv_threadRP`), and every
other existing thread keeps its frame bound and debits.  Used by `TermLiveC.sysInvO_mstepE_ext`. -/
theorem sysInvO_threadRW (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hFN : TermPoolThread.FgnNewT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hc' : c' ∈ threadSteps p k arch c i) (hcert : Certified p k arch c' i)
    {pl : Nat → Ts → Res} (hPI : TermPoolStaging.PoolInv Init MintOK c Eg Tot HP HS cr db pl)
    (hOL : OwnLive Eg c) (hOb : ObsAll Eg c)
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
      SysInvN p k arch Init MintOK c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' ∧ Post Eg' ∧
        ∀ j, j ≠ i → j < c.ths.size → Tot' j = Tot j ∧ db' j = db j := by
  obtain ⟨Eg', Tot', HP', HS', cr', db', hSys, hP, hW⟩ := TermMain.sysInv_threadRPW O PS hFN hrun h hc' hcert hPI
    (fun Eg' => (OwnLive Eg' c' ∧ ObsAll Eg' c') ∧ Post Eg')
    (fun th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPub hPfrP hS hF0 => ⟨by
      have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
      have hi : i < c.ths.size := by
        rcases Nat.lt_or_ge i c.ths.size with h1 | h1
        · exact h1
        · have hth := X.hth; simp [h1] at hth
      refine ⟨⟨fun l cl j hs ho => ?_, fun l B hB => ?_⟩, fun j hj => ?_⟩
      · rw [TermStep.threadSteps_size hc']
        simp only [EgT, GEnv.withFp, GEnv.post] at hs
        split at hs
        · rcases hF0.2.2.1 l with e | ⟨-, T, hT', -⟩
          · rw [e] at hs; exact hOL.1 l cl j (cutSto_sub hs) ho
          · rw [hT'] at hs; cases hs; cases ho; exact hi
        · exact hOL.1 l cl j hs ho
      · rw [TermStep.threadSteps_size hc']
        simp only [EgT, GEnv.withFp, GEnv.post] at hB
        split at hB
        · rcases hF0.2.2.2.1 l with e | ⟨-, B', hB', ho', -⟩
          · rw [e] at hB; exact hOL.2 l B hB
          · rw [hB'] at hB; cases hB; rw [ho']; exact hi
        · exact hOL.2 l B hB
      · rw [TermStep.threadSteps_size hc'] at hj
        have hji : j ≠ i := by omega
        obtain ⟨d, pp, -⟩ := hOb j hj
        exact ⟨cl7_pubDefP_obs (TermPlantFrz.plantFrozenF_of TermPlantFrz.plantFrozenPub_holds) O.scope
            pubFrontier_holds O.promTyAPost X Y Z hPub hPfrP hS j _ hji d,
          cl9d_pubPair_obs O.newPair O.ownCohLe (TermPlantFrz.plantFrozenF_of TermPlantFrz.plantFrozenPub_holds)
            O.promNoTwoPost X Y ZC hS hPfrP j _ hji pp,
          cl9e_pubLive_obs X Y ZC j _ hji trivial⟩,
      hPost th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPub hPfrP hS hF0⟩)
  exact ⟨Eg', Tot', HP', HS', cr', db', hSys, hP.1.1, hP.1.2, hP.2, hW⟩

theorem sysInvO_threadR (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hFN : TermPoolThread.FgnNewT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hc' : c' ∈ threadSteps p k arch c i) (hcert : Certified p k arch c' i)
    {pl : Nat → Ts → Res} (hPI : TermPoolStaging.PoolInv Init MintOK c Eg Tot HP HS cr db pl)
    (hOL : OwnLive Eg c) (hOb : ObsAll Eg c) :
    SysInvO p k arch Init MintOK c' :=
  let ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hB, _, _⟩ :=
    sysInvO_threadRW O PS hFN hrun h hc' hcert hPI hOL hOb (fun _ => True) (by intros; trivial)
  ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hB⟩

/-- (R4 (a‴)+(A)) the thread-step wrapper (copy of `TermMain.sysInv_thread`). -/
theorem sysInvO_thread (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hFN : TermPoolThread.FgnNewT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hc' : c' ∈ threadSteps p k arch c i) (hcert : Certified p k arch c' i)
    (hOL : OwnLive Eg c) (hOb : ObsAll Eg c) :
    SysInvO p k arch Init MintOK c' := by
  obtain ⟨pl, hPI⟩ := TermPoolThread.poolInv_of h.pool
  exact sysInvO_threadR O PS hFN hrun h hc' hcert hPI hOL hOb

/-! ## Wiring: the promise step -/


/-- **`sysInvO_prom` with a side fact and the witness frame** (as `TermMain.sysInv_promPW`).
Used by `TermLiveC.sysInvO_mstepE_ext`. -/
theorem sysInvO_promW (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN) {c : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hj : j < c.ths.size) (hw : w < c.mem.size) (hcert : Certified p k arch (promise c j a v w) j)
    (hOL : OwnLive Eg c) (hOb : ObsAll Eg c) (Q : GEnv → Prop)
    (hQ0 : ∀ th, c.ths[j]? = some th → PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      Q (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK (promise c j a v w) Eg' Tot' HP' HS' cr' db' ∧
        OwnLive Eg' (promise c j a v w) ∧ ObsAll Eg' (promise c j a v w) ∧ Q Eg' ∧
        ∀ j', j' ≠ j → j' < c.ths.size → Tot' j' = Tot j' ∧ db' j' = db j' := by
  obtain ⟨Eg', Tot', HP', HS', cr', db', hSys, hQ, hW⟩ := sysInv_promPW O PS hrun h hj hw hcert
    (fun Eg' => (OwnLive Eg' (promise c j a v w) ∧ ObsAll Eg' (promise c j a v w)) ∧ Q Eg') (fun th hth X => ⟨by
      obtain ⟨epc, -, -⟩ := promise_inv (a := a) (v := v) (w := w) hth
      have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [epc]
      have hpairs : (promise c j a v w).pairs = c.pairs := by rw [epc]
      refine ⟨⟨fun l cl i hs ho => ?_, fun l B hB => ?_⟩, fun j' hj' => ?_⟩
      · rw [TermStep.promise_size]; exact hOL.1 l cl i hs ho
      · rw [TermStep.promise_size]; exact hOL.2 l B hB
      · rw [TermStep.promise_size] at hj'
        have hjj : j' ≠ j := by omega
        obtain ⟨d, pp, pl⟩ := hOb j' hj'
        rw [hmem, hpairs]
        exact ⟨pcl7_pubDefP_obs (fun X => (O.plantSpec X).1) O.promLoc O.promTyAPostP O.plantHid X j' _ hjj d,
          pcl9d_pubPair_obs (fun X => (O.plantSpec X).1) O.promNoTwoP O.plantPair X j' _ hjj pp,
          pcl9e_pubLive_obs (fun X => (O.plantSpec X).1) X j' _ hjj pl⟩, hQ0 th hth X⟩)
  exact ⟨Eg', Tot', HP', HS', cr', db', hSys, hQ.1.1, hQ.1.2, hQ.2, hW⟩

theorem sysInvO_prom (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN) {c : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hj : j < c.ths.size) (hw : w < c.mem.size) (hcert : Certified p k arch (promise c j a v w) j)
    (hOL : OwnLive Eg c) (hOb : ObsAll Eg c) :
    SysInvO p k arch Init MintOK (promise c j a v w) :=
  let ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hB, _, _⟩ :=
    sysInvO_promW O PS hrun h hj hw hcert hOL hOb (fun _ => True) (fun _ _ _ => trivial)
  ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hB⟩

/-! ## Runs and the headline -/


theorem sysInvO_step (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) {c c' : Cfg}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvO p k arch Init MintOK c) (hs : Step p k arch c c') :
    SysInvO p k arch Init MintOK c' := by
  have PS := TermMain.poolStaging_of O
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hOb⟩ := h
  cases hs with
  | thread i hc hcert => exact sysInvO_thread O PS (TermFgnNew.fgnNew_of O.scope) hrun hN hc hcert hOL hOb
  | prom i a v w hi hw hcert => exact sysInvO_prom O PS hrun hN hi hw hcert hOL hOb

theorem sysInvO_run (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN) (h0 : SysInvO p k arch Init MintOK c0)
    {c : Cfg} (hr : TermStep.Steps p k arch c0 c) : SysInvO p k arch Init MintOK c := by
  have key : ∀ {c1 c2 : Cfg}, TermStep.Steps p k arch c1 c2 → TermStep.Steps p k arch c0 c1 →
      SysInvO p k arch Init MintOK c1 → SysInvO p k arch Init MintOK c2 := by
    intro c1 c2 h12
    induction h12 with
    | refl => exact fun _ h => h
    | step hs _ ih => exact fun h01 h1 => ih (h01.tail hs) (sysInvO_step O (TermSpawnStep.StepsG.ofSteps h01) h1 hs)
  exact key hr (.refl _) h0

end

#print axioms TermSpawn.sysInvO_run
#print axioms TermSpawn.sysInvO_threadRW
#print axioms TermSpawn.sysInvO_promW
end TermSpawn
