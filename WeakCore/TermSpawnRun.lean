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

theorem sysInvO_threadR (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hFN : TermPoolThread.FgnNewT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hc' : c' ∈ threadSteps p k arch c i) (hcert : Certified p k arch c' i)
    {pl : Nat → Ts → Res} (hPI : TermPoolStaging.PoolInv Init MintOK c Eg Tot HP HS cr db pl)
    (hOL : OwnLive Eg c) (hOb : ObsAll Eg c) :
    SysInvO p k arch Init MintOK c' := by
  obtain ⟨Eg', Tot', HP', HS', cr', db', hSys, hP⟩ := TermMain.sysInv_threadRP O PS hFN hrun h hc' hcert hPI
    (fun Eg' => OwnLive Eg' c' ∧ ObsAll Eg' c')
    (fun th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPub hPfrP hS hF0 => by
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
          cl9e_pubLive_obs X Y ZC j _ hji trivial⟩)
  exact ⟨Eg', Tot', HP', HS', cr', db', hSys, hP⟩

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


theorem sysInvO_prom (O : Obligations p k arch Sp Init MintOK c0 plantOf plantN)
    (PS : TermPoolStaging.PoolStaging p k arch Sp Init MintOK c0 plantOf plantN) {c : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hrun : TermSpawnStep.StepsG p k arch Sp c0 c) (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hj : j < c.ths.size) (hw : w < c.mem.size) (hcert : Certified p k arch (promise c j a v w) j)
    (hOL : OwnLive Eg c) (hOb : ObsAll Eg c) :
    SysInvO p k arch Init MintOK (promise c j a v w)
 := by
  obtain ⟨Eg', Tot', HP', HS', cr', db', hSys, hQ⟩ := sysInv_promP O PS hrun h hj hw hcert
    (fun Eg' => OwnLive Eg' (promise c j a v w) ∧ ObsAll Eg' (promise c j a v w)) (fun th hth X => by
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
          pcl9e_pubLive_obs (fun X => (O.plantSpec X).1) X j' _ hjj pl⟩)
  exact ⟨Eg', Tot', HP', HS', cr', db', hSys, hQ⟩

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
end TermSpawn
