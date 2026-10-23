import Scc.Sem.Correct

/-!
# `Correct` from a step-wise simulation, for any target

The spike's `Correct` theorems (`Spike/Bridge`, `Spike/Lib/Thread.lean`)
reach Kraken's machine through `ExtMachine.ofBase_run_inv` (a run of the
base target is a Kraken run), which only the target with no extensions has.
For a target with system calls, spawns and range transfers (the canonical
targets, `Scc/Sem/TargetA64.lean`), the simulation is stated per step of the
extended machine instead (`StepSim`): every step `t —es→ t'` of a related
target configuration is matched by a source run with exactly the observable
events `obs es`, landing in a related configuration.

- `StepSim.reach`: every reachable target configuration is related to a
  source configuration reachable with exactly the target's observable trace.
- `correct_of_stepSim`: `Correct` from a `StepSim`, progress, an abort
  justification at each abort step (given the related reachable source
  configuration) and the explicit witness.

Nothing here depends on the ISA or the hooks.
-/

namespace Scc.Sem

variable {T : Target} {S : SrcSem} {Λ : Layout} {asm : T.Asm}

theorem obs_append (es tr : List Ev) : obs (es ++ tr) = obs es ++ obs tr := List.filter_append ..

/-- **A step-wise simulation** of `asm` loaded under `Λ` by `S`: the
loaded configuration is related to a start configuration, and every step of
a related configuration (under the loaded program's marks) is matched by a
source run with its observable events. -/
structure StepSim (T : Target) (S : SrcSem) (Λ : Layout) (asm : T.Asm) (R : T.M.Cfg → S.Cfg → Prop) : Prop where
  init : ∀ t0, T.load asm Λ = some t0 → ∃ s0, S.init s0 ∧ R t0 s0
  step : ∀ tid t es t' s, R t s → T.M.Step (T.marks asm Λ) tid t es t' → ∃ s', S.Run s (obs es) s' ∧ R t' s'

namespace StepSim

variable {R : T.M.Cfg → S.Cfg → Prop}

/-- A run from a related configuration is matched by a source run with its
observable trace. -/
theorem run (h : StepSim T S Λ asm R) {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run (T.marks asm Λ) t tr t')
    {s : S.Cfg} (hR : R t s) : ∃ s', S.Run s (obs tr) s' ∧ R t' s' := by
  induction hr generalizing s with
  | refl => exact ⟨s, .refl _, hR⟩
  | step hs _ ih =>
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s1, hr1, hR1⟩ := h.step _ _ _ _ _ hR hs
    obtain ⟨s2, hr2, hR2⟩ := ih hR1
    exact ⟨s2, obs_append .. ▸ hr1.trans hr2, hR2⟩

/-- **Every reachable target configuration is related** to a source
configuration reachable with exactly its observable trace. -/
theorem reach (h : StepSim T S Λ asm R) {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0)
    (hr : T.M.Run (T.marks asm Λ) t0 tr t) : ∃ s, S.Reach (obs tr) s ∧ R t s := by
  obtain ⟨s0, hi, hR0⟩ := h.init t0 h0
  obtain ⟨s, hrun, hR⟩ := h.run hr hR0
  exact ⟨s, ⟨s0, hi, hrun⟩, hR⟩

end StepSim

/-- **`Correct` from a step-wise simulation.** Besides the `StepSim`: the
layout is well formed, every reachable configuration has progress and stays
in the layout, each abort step from a reachable configuration is justified
at any related source configuration reachable with the target's observable
trace, and `R` is explicit. -/
theorem correct_of_stepSim {B : Budget} {R : T.M.Cfg → S.Cfg → Prop} (h : StepSim T S Λ asm R) (hwf : Λ.WF)
    (hstart : ∃ t0, T.load asm Λ = some t0)
    (hprog : ∀ t0 tr t, T.load asm Λ = some t0 → T.M.Run (T.marks asm Λ) t0 tr t →
      T.M.Progress (T.marks asm Λ) t ∧ InLayout Λ t)
    (habort : ∀ t0 tr t tid es t' k s, T.load asm Λ = some t0 → T.M.Run (T.marks asm Λ) t0 tr t →
      S.Reach (obs tr) s → R t s → T.M.Step (T.marks asm Λ) tid t es t' → Ev.abort k ∈ es →
      ∃ w i, Components T.M Λ w t (S.core s) ∧ w.thr i = some tid ∧ AbortJustified B S tr s i k)
    (hexp : ∀ t s, R t s → ∃ w : Witness T.M, Components T.M Λ w t (S.core s)) :
    Correct T S Λ B asm := by
  obtain ⟨t0, h0⟩ := hstart
  refine ⟨{
    R := R
    layout := hwf
    start := let ⟨s0, hi, hR⟩ := h.init t0 h0; ⟨t0, s0, h0, hi, hR⟩
    progress := hprog
    sim := fun t0 tr t h0 hr => let ⟨s, hs, hR⟩ := h.reach h0 hr; ⟨obs tr, s, hs, hR, List.prefix_refl _⟩
    abort := fun t0 tr t tid es t' k h0 hr hs hk => ?_
    explicit := hexp }⟩
  obtain ⟨s, hreach, hR⟩ := h.reach h0 hr
  obtain ⟨w, i, hc, hi, hj⟩ := habort t0 tr t tid es t' k s h0 hr hreach hR hs hk
  exact ⟨s, w, i, hreach, hR, hc, hi, hj⟩

end Scc.Sem
