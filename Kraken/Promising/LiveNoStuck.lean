/-
**A stuck configuration has a dead promise**
(ISA-neutral, architecture-neutral, program-independent).

On the semantic machine (`LiveSem.lean`) a configuration is *stuck* when it
is not final and no thread can take a step (`StuckSem`). The existing liveness
theorems quantify over traces, which stutter only at final configurations; a
stuck configuration has no trace through it, so a liveness theorem is vacuous
on runs that reach one. This file states the absence of stuck configurations
(`NoStuckFrom`) and proves the generic half of it:

- `EnabledOfConsistent`, **`enabledOfConsistent`**: a non-final
  configuration in which every thread is certifiable within `fuel`
  (`ConsistentSem`) and every running promise-free thread has a successful
  outcome for its next instruction (`OkStepsPF`) has an enabled thread.
- `StuckHasDeadPromise`, **`stuckHasDeadPromise`**: the contrapositive form:
  in a stuck configuration with `OkStepsPF`, some thread has an outstanding
  promise and cannot empty its promise set alone within `fuel`.
- `DeadProm`, `not_certOkN_of_deadProm`, `deadProm_threadNPn`,
  `deadProm_reachableSem`: a *dead* promise (an outstanding promise at or
  below the thread's `coh` of its location) makes the thread uncertifiable at
  every fuel and stays so forever: the thread never steps again and keeps the
  dead promise along every semantic run. Reusable for certification bounds.
- `MaxRunSem`, `liveFromSemMax_of`, `progressFromSemMax_of`: with
  `NoStuckFrom`, a liveness theorem over traces holds over every *maximal*
  run (one that stutters only where no thread is enabled).

`OkStepsPF` is a per-configuration hypothesis (from fault freedom plus
non-empty outcome lists); it is not discharged generically here. No `Wf`
hypothesis is needed: a promise-free thread stays promise-free
(`RunnerSim.stepOne_prom_nil`).
-/
import Kraken.Promising.LiveBridge
import Kraken.Promising.LiveRunnerSim

namespace Kraken.Promising.Live.NoStuck

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge

variable {I : ISA}

/-! ## Statements -/

/-- **Stuck** (semantic machine, fuel `fuel`): not final, and no thread can
take a semantic step (instruction or promise). -/
def StuckSem (A : Arch) (fuel : Nat) (c : Config I) : Prop :=
  c.final = false ∧ ∀ tid, ¬ EnabledSem A fuel tid c

/-- **No stuck configuration is reachable** from `c0` on the semantic machine
at certification fuel `fuel`. -/
def NoStuckFrom (A : Arch) (fuel : Nat) (c0 : Config I) : Prop :=
  ∀ c, ReachableSem A fuel c0 c → ¬ StuckSem A fuel c

/-- **Every thread is certifiable** within `fuel` against the current memory
(a promise-free thread trivially is). -/
def ConsistentSem (A : Arch) (fuel : Nat) (c : Config I) : Prop :=
  ∀ tid t, c.threads[tid]? = some t → CertOkN A tid t c.mem fuel

/-- Every running promise-free thread has a successful outcome for its next
instruction (no fault-only and no outcome-free instruction). -/
def OkStepsPF (A : Arch) (c : Config I) : Prop :=
  ∀ tid t, c.threads[tid]? = some t → t.halted = false → t.prom = [] →
    ∃ outs o, stepOne A t tid c.mem = some outs ∧ .ok o ∈ outs

/-- N1: a consistent, non-final configuration with `OkStepsPF` has an enabled
thread. -/
def EnabledOfConsistent (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel : Nat) (c : Config I), c.final = false → ConsistentSem A fuel c → OkStepsPF A c →
    ∃ tid, EnabledSem A fuel tid c

/-- N1' (the contrapositive form to cite): a stuck configuration has a thread
with an outstanding promise that it cannot fulfil alone within `fuel`. -/
def StuckHasDeadPromise (A : Arch) (I : ISA) : Prop :=
  ∀ (fuel : Nat) (c : Config I), StuckSem A fuel c → OkStepsPF A c →
    ∃ tid t, c.threads[tid]? = some t ∧ t.prom ≠ [] ∧ ¬ CertOkN A tid t c.mem fuel

/-! ## N1 -/

/-- A non-final configuration has a thread that is running or has an
outstanding promise. -/
theorem exists_unfinished {c : Config I} (hf : c.final = false) :
    ∃ (tid : Nat) (t : Thread I), c.threads[tid]? = some t ∧ (t.halted = false ∨ t.prom ≠ []) := by
  refine Classical.byContradiction fun hne => ?_
  have : c.final = true := Array.all_eq_true.mpr fun i hi => by
    by_cases h1 : c.threads[i].halted = true
    · by_cases h2 : c.threads[i].prom = []
      · simp [h1, h2]
      · exact absurd ⟨i, _, Array.getElem?_eq_getElem hi, .inr h2⟩ hne
    · exact absurd ⟨i, _, Array.getElem?_eq_getElem hi, .inl (by simpa using h1)⟩ hne
  rw [this] at hf; cases hf

/-- A thread with an outstanding promise that is certifiable within `fuel`
can take an instruction step. -/
theorem instrEnabledSem_of_certOkN {A : Arch} {fuel tid : Nat} {c : Config I} {t : Thread I}
    (ht : c.threads[tid]? = some t) (hp : t.prom ≠ []) (hc : CertOkN A tid t c.mem fuel) :
    InstrEnabledSem A fuel tid c := by
  obtain ⟨t', mem', h, hp'⟩ := hc
  cases h with
  | refl => exact absurd hp' hp
  | @step n _ q _ hs h =>
    obtain ⟨outs, o, hs', ho, rfl⟩ := hs
    exact ⟨_, t, outs, o, ht, hs', ho, ⟨t', mem', h.mono (Nat.le_succ n), hp'⟩, rfl⟩

/-- **A thread that is running or has a promise, and is certifiable if it has
a promise, is enabled** (under `OkStepsPF`). -/
theorem enabledSem_of_thread {A : Arch} {fuel tid : Nat} {c : Config I} {t : Thread I}
    (hok : OkStepsPF A c) (ht : c.threads[tid]? = some t) (hu : t.halted = false ∨ t.prom ≠ [])
    (hc : t.prom ≠ [] → CertOkN A tid t c.mem fuel) : EnabledSem A fuel tid c := by
  by_cases hp : t.prom = []
  · have hh : t.halted = false := hu.resolve_right (fun h => h hp)
    obtain ⟨outs, o, hs, ho⟩ := hok tid t ht hh hp
    obtain ⟨c', h⟩ := instrEnabledSem_of_step (fuel := fuel) ht hs ho
      (RunnerSim.stepOne_prom_nil A hp hs ho)
    exact ⟨c', .inl h⟩
  · obtain ⟨c', h⟩ := instrEnabledSem_of_certOkN ht hp (hc hp)
    exact ⟨c', .inl h⟩

/-- **N1**: a consistent, non-final configuration with `OkStepsPF` has an
enabled thread. -/
theorem enabledOfConsistent (A : Arch) (I : ISA) : EnabledOfConsistent A I := by
  intro fuel c hf hcons hok
  obtain ⟨tid, t, ht, hu⟩ := exists_unfinished hf
  exact ⟨tid, enabledSem_of_thread hok ht hu fun _ => hcons tid t ht⟩

/-- **N1'**: a stuck configuration with `OkStepsPF` has a thread with an
outstanding promise that is not certifiable within `fuel`. -/
theorem stuckHasDeadPromise (A : Arch) (I : ISA) : StuckHasDeadPromise A I := by
  intro fuel c ⟨hf, hst⟩ hok
  obtain ⟨tid, t, ht, hu⟩ := exists_unfinished hf
  by_cases hp : t.prom = []
  · exact absurd (enabledSem_of_thread hok ht hu fun h => absurd hp h) (hst tid)
  · exact ⟨tid, t, ht, hp, fun hc => hst tid (enabledSem_of_thread hok ht hu fun _ => hc)⟩

/-- **No stuck configuration from consistency**: if every configuration
reachable from `c0` is `ConsistentSem` and `OkStepsPF`, none is stuck. -/
theorem noStuckFrom_of_consistent {A : Arch} {fuel : Nat} {c0 : Config I}
    (hcons : ∀ c, ReachableSem A fuel c0 c → ConsistentSem A fuel c)
    (hok : ∀ c, ReachableSem A fuel c0 c → OkStepsPF A c) : NoStuckFrom A fuel c0 := by
  intro c hr ⟨hf, hst⟩
  obtain ⟨tid, h⟩ := enabledOfConsistent A I fuel c hf (hcons c hr) (hok c hr)
  exact hst tid h

/-! ## Maximal runs

A *maximal run* takes a step at every index, or stutters at a configuration
where no thread is enabled: final, or stuck. A `TraceSem` stutters only at
final configurations, so it is a maximal run; with `NoStuckFrom` every maximal
run from `c0` is a `TraceSem` (`MaxRunSem.toTraceSem`), so a liveness theorem
over traces covers every maximal run (`liveFromSemMax_of`,
`progressFromSemMax_of`). -/

/-- **A maximal run of the semantic machine**: at every index a step, or a
stutter at a configuration where no thread is enabled (final or stuck). -/
structure MaxRunSem (A : Arch) (fuel : Nat) (I : ISA) where
  cfg : Nat → Config I
  step : ∀ i, (∃ tid, StepSem A fuel tid (cfg i) (cfg (i + 1))) ∨
    ((∀ tid, ¬ EnabledSem A fuel tid (cfg i)) ∧ cfg (i + 1) = cfg i)

/-- **Liveness from `c0` over every maximal run** (`LiveFromSem` over
`MaxRunSem`). -/
def LiveFromSemMax (A : Arch) (fuel : Nat) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : MaxRunSem A fuel I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ Done tid (tr.cfg j)

/-- **Deadlock-freedom from `c0` over every maximal run**
(`SpinSem.ProgressFromSem` over `MaxRunSem`). -/
def ProgressFromSemMax (A : Arch) (fuel : Nat) (c0 : Config I) (Fair : (Nat → Config I) → Prop)
    (Waiting Done : Nat → Config I → Prop) : Prop :=
  ∀ tr : MaxRunSem A fuel I, tr.cfg 0 = c0 → Fair tr.cfg →
    ∀ tid i, Waiting tid (tr.cfg i) → ∃ j, i ≤ j ∧ ∃ tid', ¬ Done tid' (tr.cfg i) ∧ Done tid' (tr.cfg j)

theorem reachableSem_snoc {A : Arch} {fuel tid : Nat} {c0 c c' : Config I} (hr : ReachableSem A fuel c0 c)
    (hs : StepSem A fuel tid c c') : ReachableSem A fuel c0 c' := by
  induction hr with
  | refl => exact .step tid hs (.refl _)
  | step j h _ ih => exact .step j h (ih hs)

/-- Every configuration of a maximal run from `c0` is reachable from `c0`. -/
theorem MaxRunSem.reach {A : Arch} {fuel : Nat} {c0 : Config I} (tr : MaxRunSem A fuel I) (h0 : tr.cfg 0 = c0) :
    ∀ i, ReachableSem A fuel c0 (tr.cfg i)
  | 0 => h0 ▸ .refl _
  | i + 1 => by
    rcases tr.step i with ⟨tid, hs⟩ | ⟨-, he⟩
    · exact reachableSem_snoc (tr.reach h0 i) hs
    · rw [he]; exact tr.reach h0 i

/-- **With no stuck configuration, a maximal run is a trace.** -/
def MaxRunSem.toTraceSem {A : Arch} {fuel : Nat} {c0 : Config I} (hns : NoStuckFrom A fuel c0)
    (tr : MaxRunSem A fuel I) (h0 : tr.cfg 0 = c0) : TraceSem A fuel I where
  cfg := tr.cfg
  step i := (tr.step i).imp id fun ⟨hne, he⟩ =>
    ⟨by cases e : (tr.cfg i).final
        · exact absurd ⟨e, hne⟩ (hns _ (tr.reach h0 i))
        · rfl, he⟩

/-- **Liveness over traces is liveness over maximal runs**, without stuck
configurations. -/
theorem liveFromSemMax_of {A : Arch} {fuel : Nat} {c0 : Config I} {Fair : (Nat → Config I) → Prop}
    {Waiting Done : Nat → Config I → Prop} (hns : NoStuckFrom A fuel c0)
    (h : LiveFromSem A fuel c0 Fair Waiting Done) : LiveFromSemMax A fuel c0 Fair Waiting Done :=
  fun tr h0 hf => h (tr.toTraceSem hns h0) h0 hf

/-- **Deadlock-freedom over traces is deadlock-freedom over maximal runs**,
without stuck configurations. -/
theorem progressFromSemMax_of {A : Arch} {fuel : Nat} {c0 : Config I} {Fair : (Nat → Config I) → Prop}
    {Waiting Done : Nat → Config I → Prop} (hns : NoStuckFrom A fuel c0)
    (h : SpinSem.ProgressFromSem A fuel c0 Fair Waiting Done) : ProgressFromSemMax A fuel c0 Fair Waiting Done :=
  fun tr h0 hf => h (tr.toTraceSem hns h0) h0 hf

/-! ## Helpers for per-program instances -/

/-- An invariant kept by every semantic step holds along every semantic run. -/
theorem reachableSem_inv {A : Arch} {fuel : Nat} (Inv : Config I → Prop)
    (hstep : ∀ tid c c', Inv c → StepSem A fuel tid c c' → Inv c') {c0 c : Config I}
    (hr : ReachableSem A fuel c0 c) (h0 : Inv c0) : Inv c := by
  induction hr with
  | refl => exact h0
  | step tid hs _ ih => exact ih (hstep tid _ _ h0 hs)

/-- A thread whose instruction has no outcome list has halted. -/
theorem halted_of_stepOne_none {A : Arch} {t : Thread I} {tid : Nat} {mem : Memory}
    (h : stepOne A t tid mem = none) : t.halted = true := by
  unfold stepOne at h
  unfold Thread.halted
  cases hex : I.exec t.st with
  | none => rfl
  | some tree => rw [hex] at h; cases h

/-- The threads of an initial configuration have no promise. -/
theorem Config.init_prom {states : List I.State} {initMem : List (Loc × Val)} {i : Nat} {t : Thread I}
    (h : (Config.init states initMem).threads[i]? = some t) : t.prom = [] := by
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨s, -, rfl⟩ := h
  rfl

/-! ## Dead promises

A promise at or below the thread's `coh` of its location can never be
fulfilled (`coh_lt_of_certOkN`), and `coh` only grows. -/

/-- Thread `t` has a **dead promise** against `mem`: an outstanding promise
whose message lies at or below `t`'s `coh` of its location. -/
def DeadProm (t : Thread I) (mem : Memory) : Prop :=
  ∃ ts w, ts ∈ t.prom ∧ mem.get? ts = some w ∧ ts ≤ t.views.getCoh w.loc

/-- A thread with a dead promise is not certifiable, at any fuel. -/
theorem not_certOkN_of_deadProm {A : Arch} {tid n : Nat} {t : Thread I} {mem : Memory}
    (hd : DeadProm t mem) : ¬ CertOkN A tid t mem n := by
  rintro hc
  obtain ⟨ts, w, hts, hw, hle⟩ := hd
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle (coh_lt_of_certOkN hc hts hw))

/-- A dead promise survives a larger memory. -/
theorem DeadProm.mono {t : Thread I} {mem mem' : Memory} (hd : DeadProm t mem) (hp : mem.Prefix mem') :
    DeadProm t mem' := by
  obtain ⟨ts, w, hts, hw, hle⟩ := hd
  exact ⟨ts, w, hts, by rw [hp.get? (mem.last_le_of_get?_eq_some hw)]; exact hw, hle⟩

/-- A dead promise survives an instruction of its thread. -/
theorem DeadProm.step {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Outcome I))} {o : Outcome I} (hd : DeadProm t mem)
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) : DeadProm o.thread o.mem := by
  obtain ⟨-, hcoh, hpre, hful⟩ := stepOne_dord A hs ho
  obtain ⟨ts, w, hts, hw, hle⟩ := hd
  have hin : ts ∈ o.thread.prom := Classical.byContradiction fun hn =>
    Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle ((hful ts hts hn).2 w hw))
  exact ⟨ts, w, hin, by rw [hpre.get? (mem.last_le_of_get?_eq_some hw)]; exact hw,
    Nat.le_trans hle (hcoh _)⟩

/-- A dead promise survives every solo run. -/
theorem deadProm_threadNPn {A : Arch} {tid n : Nat} {p q : Thread I × Memory}
    (h : ThreadNPn A tid n p q) (hd : DeadProm p.1 p.2) : DeadProm q.1 q.2 := by
  induction h with
  | refl => exact hd
  | step hs _ ih =>
    obtain ⟨outs, o, hs, ho, rfl⟩ := hs
    exact ih (hd.step hs ho)

/-- A thread with a dead promise is not enabled. -/
theorem not_enabledSem_of_deadProm {A : Arch} {fuel tid : Nat} {c : Config I} {t : Thread I}
    (ht : c.threads[tid]? = some t) (hd : DeadProm t c.mem) : ¬ EnabledSem A fuel tid c := by
  rintro ⟨c', ⟨t1, outs, o, ht1, hs, ho, hc, -⟩ | ⟨t1, w, ht1, -, hc, -⟩⟩
  · rw [ht] at ht1; cases ht1
    exact not_certOkN_of_deadProm (hd.step hs ho) hc
  · rw [ht] at ht1; cases ht1
    obtain ⟨ts, w', hts, hw, hle⟩ := hd.mono (Memory.Prefix.append c.mem w)
    exact not_certOkN_of_deadProm (t := promThread t c.mem w)
      ⟨ts, w', List.mem_append_left _ hts, hw, hle⟩ hc

/-- **A dead promise is dead forever**: along every semantic run, the thread
does not change and keeps its dead promise. -/
theorem deadProm_reachableSem {A : Arch} {fuel tid : Nat} {c c' : Config I} {t : Thread I}
    (hr : ReachableSem A fuel c c') (ht : c.threads[tid]? = some t) (hd : DeadProm t c.mem) :
    c'.threads[tid]? = some t ∧ DeadProm t c'.mem := by
  induction hr with
  | refl => exact ⟨ht, hd⟩
  | @step c c1 c2 j hs _ ih =>
    by_cases e : j = tid
    · subst e; exact absurd ⟨c1, hs⟩ (not_enabledSem_of_deadProm ht hd)
    · rcases hs with ⟨t1, outs, o, ht1, hs1, ho, -, rfl⟩ | ⟨t1, w, ht1, -, -, rfl⟩
      · exact ih (by rw [withThread_get_ne ht1 (Ne.symm e)]; exact ht)
          (hd.mono (stepOne_dord _ hs1 ho).2.2.1)
      · exact ih (by rw [withThread_get_ne ht1 (Ne.symm e)]; exact ht)
          (hd.mono (Memory.Prefix.append _ _))

end Kraken.Promising.Live.NoStuck
