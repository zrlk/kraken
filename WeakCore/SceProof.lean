/-
# SceProof — the liveness instance behind `live def`

`sce` reports `live def f: PROVED (under the standard obligations)` when `robustOK` holds of the program's
protocols (and, for `live[S]`, of the scenario kids' protocols).  This module is what that report rests on:

* `robustOK ms` decides `TermLiveL3.ProgRobustPwf (· ∈ ms)` (`progRobustPwf_of_robustOK`): every protocol is
  `robust` and `pwf`, or `pwf` and an epoch counter;
* `MainInst p` / `ScenInst p kids` state the two facts of §4 for the program from `main`'s start
  (`TermStartW.startW`), resp. no held-word-induced livelock from the scenario start with the kids `kids`
  (`TermLiveL3.ScenarioStartK`): for every architecture and initial resources, on the default machine
  (`Promises.Knobs.all`, `storeDepRts = true`), with the standard obligations (`ObligationsFX`, `InitOK`, resp. the
  scenario-start premises) as hypotheses;
* `mainInst` / `scenInst` prove them from `robustOK … = true` (`TermLiveL3.robust_touchedFree_thm`,
  `no_induced_livelock_robust2_thm`, `no_induced_livelock_robust2_scenario`).

`sce` evaluates `robustOK` in compiled code (the one trusted step of the default mode); `sce --live-proof` writes
`root.live.lean`, which re-checks `robustOK … = true` in the kernel (`by decide`) and applies `mainInst`/`scenInst`.
-/
import WeakCore.TermLiveL3

-- The instance files of `sce --live-proof` (`SceRun.proofText`) print the program and the kids as Lean data.
deriving instance Repr for CoreTerm.Decl
deriving instance Repr for TermSpawn.Kid

namespace SceProof
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermLiveMach TermProgress TermLiveL3
open WeakMem (Arch Address)

/-- A protocol `live def` accepts: robust and well formed, or a well-formed epoch counter. -/
def robustChk (P : Proto) : Bool := (P.robust && pwf P) || (pwf P && P.epoch)

/-- Every protocol of `ms` is accepted. -/
def robustOK (ms : List Proto) : Bool := ms.all robustChk

/-- The first protocol of `ms` that is not accepted (what the refusal names). -/
def firstBad (ms : List Proto) : Option Proto := ms.find? fun P => !robustChk P

theorem progRobustPwf_of_robustOK (ms : List Proto) (h : robustOK ms = true) : ProgRobustPwf (· ∈ ms) := by
  intro P hP
  have hc : robustChk P = true := List.all_eq_true.mp h P hP
  unfold robustChk at hc
  cases hr : P.robust <;> cases hp : pwf P <;> cases he : P.epoch <;> simp_all

theorem firstBad_none (ms : List Proto) (h : firstBad ms = none) : robustOK ms = true := by
  unfold firstBad at h
  unfold robustOK
  apply List.all_eq_true.mpr
  intro P hP
  have := List.find?_eq_none.mp h P hP
  simpa using this

/-- `main`'s start (`TermStartW.startW p cap`), for every architecture, initial resources and thread capacity, on
the default machine, under the standard obligations: (1) no thread ever accesses a protocol word in a held state;
(2) no held-word-induced livelock. -/
def MainInst (p : Prog) : Prop :=
  ∀ (arch : Arch) (Init : TermSound.Res) (cap : Nat),
    TermMain.ObligationsFX p Promises.Knobs.all arch
      (fun c c' => Spawn p Promises.Knobs.all arch cap c c' ∨ Ext p Promises.Knobs.all arch c c') Init
      (fun _ => True) (TermStartW.startW p cap) →
    TermMain.InitOK p Promises.Knobs.all arch Init (fun _ => True) (TermStartW.startW p cap) →
    (∀ (r : LRun (machineE p Promises.Knobs.all arch).L), (machineE p Promises.Knobs.all arch).Run r →
      r.cfg 0 = TermStartW.startW p cap →
      ∀ m i b n P, TouchesW (r.cfg m) i b → ¬ (hvI p Promises.Knobs.all arch Init).heldAt (r.cfg m) b n P) ∧
    (∀ (r : LRun (machineE p Promises.Knobs.all arch).L) (D : Nat → Option Nat),
      (machineE p Promises.Knobs.all arch).Run r → r.cfg 0 = TermStartW.startW p cap →
      ¬ InducedW (machineE p Promises.Knobs.all arch) (hvI p Promises.Knobs.all arch Init) r D)

theorem mainInst (p : Prog) (h : robustOK (protosOf p) = true) : MainInst p := by
  intro arch Init cap O h0
  have S := setting_of_startW (k := Promises.Knobs.all) O rfl h0
  have R := progRobustPwf_of_robustOK _ h
  exact ⟨robust_touchedFree_thm p _ arch Init _ S R, no_induced_livelock_robust2_thm p _ arch Init _ S R⟩

/-- The scenario start with kids `kids` (`TermLiveL3.ScenarioStartK`), for every architecture and initial resources,
on the default machine, under the standard obligations: no held-word-induced livelock. -/
def ScenInst (p : Prog) (kids : List TermSpawn.Kid) : Prop :=
  ∀ (arch : Arch) (Init : TermSound.Res) (c0 : Cfg),
    TermMain.ObligationsFX p Promises.Knobs.all arch
      (fun c c' => Spawn p Promises.Knobs.all arch c0.cap c c' ∨ Ext p Promises.Knobs.all arch c c') Init
      (fun _ => True) c0 →
    ScenarioStartK p Promises.Knobs.all arch Init kids c0 →
    ∀ (r : LRun (machineE p Promises.Knobs.all arch).L) (D : Nat → Option Nat),
      (machineE p Promises.Knobs.all arch).Run r → r.cfg 0 = c0 →
      ¬ InducedW (machineE p Promises.Knobs.all arch) (hvI p Promises.Knobs.all arch Init) r D

theorem scenInst (p : Prog) (kids : List TermSpawn.Kid) (h : robustOK (protosOf p ++ kidProtos kids) = true) :
    ScenInst p kids := by
  intro arch Init c0 O hS
  exact no_induced_livelock_robust2_scenario p _ arch Init kids c0 ⟨O, hS⟩ (progRobustPwf_of_robustOK _ h)

#guard robustChk mutexP == false
#guard robustChk seqP == false

end SceProof

#print axioms SceProof.progRobustPwf_of_robustOK
#print axioms SceProof.firstBad_none
#print axioms SceProof.mainInst
#print axioms SceProof.scenInst
