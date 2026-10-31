/-
# TermArchE — TSO ⊆ ARM for runs with extern steps, traces included

Extends `TermArch` (machine steps `Step`) to the runs `StepsG p k arch Sp` with an extra
configuration step `Sp`, in particular `TermExtStep.StepsE` (`Spawn ∨ Ext`).

* `CfgLeT`: `TermArch.CfgLe` and equal traces.  `CfgLe` already equates `cap`, `lbase`,
  `boxFence`, `pairs` and, per thread, `tidLbl`/`nalloc` (`ThsLe`); only `trace` is new.
* `Step_simT`: `Step` leaves the trace alone, so `TermArch.Step_sim` lifts.
* `Ext_sim`: the extern step `TermExtStep.Ext` simulates (all three calls, including the
  `ExtNeedsNoProm` ones (`exitEv`, `emit`, a boxless `current()`, a device choice) that `TermArch.extSteps_sim` excludes), with the same events, by the shared
  per-call lemma `TermArch.extCfg_sim` (shared with `TermArch`); the
  certificate is `TermArch.Certified_sim` (whose `Solo_sim` already has the `Solo.ext` arm).
* `stepsG_sim`: any extra step that simulates lifts to runs.
* Headlines: `tso_extRuns_subset_arm` (machine and extern steps, no `SpawnSim` premise) and
  `tso_stepsE_subset_arm` (all of `StepsE`, under the premise `SpawnSim`).

**`Spawn` is a premise here, discharged in `TermArchS`.**  `spawnKid` binds `ws.map (bumpW V)`
with `bumpW V w = {w with view := max w.view V, rts := max w.rts V}` and `V` the parent's
post-barrier `vRelSt`, which is only `≤` on ARM.  `Promises.TValLe` relates `rts` by `≤`, so the
child relates; `TermArchS.spawn_sim` proves `SpawnSim`, and `TermArchS.tso_stepsE_subset_arm_full`
(and the `_full` versions of the trace and final corollaries) state the headlines with no `SpawnSim` premise.

`hwf` (the initial outstanding promises are in memory) stays the only side condition;
`hwf_of_noProm` discharges it when no promise is out (`TermMainDefs.AllNoProm`, part of `InitOK`).
-/
import WeakCore.TermArch
import WeakCore.TermExtStep

namespace TermArchE
open CoreLang CoreTerm TermRun TermArch TermSpawnStep TermExtStep
open WeakMem (Val Address Ts Arch)

/-! ## The relation -/

/-- `CfgLe` (ARM on the left, TSO on the right) and the same observable trace. -/
def CfgLeT (ca ct : Cfg) : Prop := CfgLe ca ct ∧ ca.trace = ct.trace

theorem CfgLeT.refl (c : Cfg) (hwf : ∀ t ∈ allP c, t < c.mem.size) : CfgLeT c c :=
  ⟨CfgLe.refl c hwf, rfl⟩

/-- With no promise out, `hwf` holds vacuously. -/
theorem hwf_of_noProm {c : Cfg} (h : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = []) :
    ∀ t ∈ allP c, t < c.mem.size := by
  intro t ht
  simp only [allP, List.mem_flatMap] at ht
  obtain ⟨th, hth, htp⟩ := ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hth
  have hi' : i < c.ths.size := by simpa using hi
  have hg : c.ths[i]? = some c.ths.toList[i] := by simp [hi']
  rw [h i _ hg] at htp
  cases htp

/-! ## Machine steps keep the trace -/

theorem threadSteps_trace {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) : c'.trace = c.trace := by
  unfold threadSteps at h
  rcases hb : c.ths[i]? with _ | th
  · rw [hb] at h; simp at h
  · rw [hb] at h
    simp only [List.mem_map] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl

theorem promise_trace (c : Cfg) (i : Nat) (a : Address) (v : Val) (w : Ts) :
    (promise c i a v w).trace = c.trace := by
  unfold promise; split <;> rfl

theorem Step_trace {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Step p k arch c c') : c'.trace = c.trace := by
  cases h with
  | thread i hin _ => exact threadSteps_trace hin
  | prom i a v w _ _ _ => exact promise_trace c i a v w

theorem Step_simT {p : Prog} {k : Promises.Knobs} {ca ct ct' : Cfg} (h : CfgLeT ca ct)
    (hs : Step p k .tso ct ct') : ∃ ca', Step p k .arm ca ca' ∧ CfgLeT ca' ct' := by
  obtain ⟨ca', hs', hl⟩ := Step_sim h.1 hs
  exact ⟨ca', hs', hl, by rw [Step_trace hs', Step_trace hs]; exact h.2⟩

/-! ## The extern step -/

/-- **The extern step simulates**, with the same events. -/
theorem Ext_sim {p : Prog} {k : Promises.Knobs} {ca ct ct' : Cfg} (h : CfgLeT ca ct)
    (hs : Ext p k .tso ct ct') : ∃ ca', Ext p k .arm ca ca' ∧ CfgLeT ca' ct' := by
  obtain ⟨i, x, n, a, e, tt, rt, wt, rs, hb, hterm, hnp, hev, hadm, hc, rfl⟩ := hs.elim
  obtain ⟨ta, ha, hta, htl⟩ := ths_some_tid h.1.ths hb
  obtain ⟨wa, hqa, hw⟩ := evalAt_tso hta.env hev
  have hadm' : n.Admits i wa ca.trace rs := by
    rw [← mem_resultsL, resultsL_congr n i hw, h.1.trace, mem_resultsL]; exact hadm
  have hs := extCfg_sim h.1 hb hta htl x n e hw rs
  have hl : CfgLeT _ _ := ⟨hs.1, hs.2 h.2⟩
  refine ⟨_, .mk i x n a e ta rt wa rs ha (hta.term.trans hterm) ?_ hqa hadm' (Certified_sim hl.1 hc),
    wake_sim hl.1 i (relView_le hta.vs) n hw, by rw [wake_trace, wake_trace]; exact hl.2⟩
  intro hN
  rw [hta.promises]
  exact hnp (by simpa only [ExtNeedsNoProm, htl] using hN)

/-! ## Runs -/

/-- **Runs simulate**, for any extra step `SpT` (TSO) / `SpA` (ARM) that simulates. -/
theorem stepsG_sim {p : Prog} {k : Promises.Knobs} {SpT SpA : Cfg → Cfg → Prop}
    (HSp : ∀ ca ct ct', CfgLeT ca ct → SpT ct ct' → ∃ ca', SpA ca ca' ∧ CfgLeT ca' ct')
    {ct ct' : Cfg} (hr : StepsG p k .tso SpT ct ct') :
    ∀ {ca}, CfgLeT ca ct → ∃ ca', StepsG p k .arm SpA ca ca' ∧ CfgLeT ca' ct' := by
  induction hr with
  | refl c => intro ca h; exact ⟨ca, .refl _, h⟩
  | step hs _ ih =>
      intro ca h
      rcases hs with hs | hs
      · obtain ⟨ca1, h1, hl⟩ := Step_simT h hs
        obtain ⟨ca2, h2, hl2⟩ := ih hl
        exact ⟨ca2, .step (.inl h1) h2, hl2⟩
      · obtain ⟨ca1, h1, hl⟩ := HSp _ _ _ h hs
        obtain ⟨ca2, h2, hl2⟩ := ih hl
        exact ⟨ca2, .step (.inr h1) h2, hl2⟩

/-- The run statement from an initial configuration, for any simulating extra step. -/
theorem tso_stepsG_subset_arm {p : Prog} {k : Promises.Knobs} {SpT SpA : Cfg → Cfg → Prop}
    (HSp : ∀ ca ct ct', CfgLeT ca ct → SpT ct ct' → ∃ ca', SpA ca ca' ∧ CfgLeT ca' ct')
    {c0 c : Cfg} (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (h : StepsG p k .tso SpT c0 c) :
    ∃ c', StepsG p k .arm SpA c0 c' ∧ CfgLe c' c ∧ c'.trace = c.trace := by
  obtain ⟨c', hr, hl, ht⟩ := stepsG_sim HSp h (CfgLeT.refl c0 hwf)
  exact ⟨c', hr, hl, ht⟩

/-- **Headline (spawn-free runs).**  Every run of machine and extern steps under TSO is matched by
an ARM run with the same trace, terms, values, promises and counters, and views no higher. -/
theorem tso_extRuns_subset_arm (p : Prog) (k : Promises.Knobs) {c0 c : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (h : StepsG p k .tso (Ext p k .tso) c0 c) :
    ∃ c', StepsG p k .arm (Ext p k .arm) c0 c' ∧ CfgLe c' c ∧ c'.trace = c.trace :=
  tso_stepsG_subset_arm (fun _ _ _ h hs => Ext_sim h hs) hwf h

/-- What a spawn simulation must provide (proved: `TermArchS.spawn_sim`). -/
def SpawnSim (p : Prog) (k : Promises.Knobs) (cap : Nat) : Prop :=
  ∀ ca ct ct', CfgLeT ca ct → Spawn p k .tso cap ct ct' → ∃ ca', Spawn p k .arm cap ca ca' ∧ CfgLeT ca' ct'

/-- **Headline (`StepsE`), under `SpawnSim`.** -/
theorem tso_stepsE_subset_arm (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 c : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (HSp : SpawnSim p k cap) (h : StepsE p k .tso cap c0 c) :
    ∃ c', StepsE p k .arm cap c0 c' ∧ CfgLe c' c ∧ c'.trace = c.trace :=
  tso_stepsG_subset_arm (fun ca ct ct' h hs => hs.elim
    (fun hs => (HSp ca ct ct' h hs).elim fun ca' ⟨h1, h2⟩ => ⟨ca', .inl h1, h2⟩)
    (fun hs => (Ext_sim h hs).elim fun ca' ⟨h1, h2⟩ => ⟨ca', .inr h1, h2⟩)) hwf h

/-! ## Trace sets -/

/-- The traces of the runs from `c0` (any extra step `Sp`). -/
def STrG (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg)
    (tr : List Event) : Prop :=
  ∃ c, StepsG p k arch Sp c0 c ∧ c.trace = tr

/-- The traces of `StepsE` runs from `c0`. -/
abbrev STrE (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) (c0 : Cfg) (tr : List Event) : Prop :=
  STrG p k arch (fun c c' => Spawn p k arch cap c c' ∨ Ext p k arch c c') c0 tr

/-- Every TSO trace of a spawn-free run is an ARM trace. -/
theorem tso_extTraces_subset_arm (p : Prog) (k : Promises.Knobs) {c0 : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) {tr : List Event} (h : STrG p k .tso (Ext p k .tso) c0 tr) :
    STrG p k .arm (Ext p k .arm) c0 tr := by
  obtain ⟨c, hr, rfl⟩ := h
  obtain ⟨c', hr', -, ht⟩ := tso_extRuns_subset_arm p k hwf hr
  exact ⟨c', hr', ht⟩

/-- Every TSO trace is an ARM trace, under `SpawnSim`. -/
theorem tso_traces_subset_arm (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (HSp : SpawnSim p k cap) {tr : List Event}
    (h : STrE p k .tso cap c0 tr) : STrE p k .arm cap c0 tr := by
  obtain ⟨c, hr, rfl⟩ := h
  obtain ⟨c', hr', -, ht⟩ := tso_stepsE_subset_arm p k cap hwf HSp hr
  exact ⟨c', hr', ht⟩

/-- Final configurations: a TSO final run is matched by an ARM final run, same trace. -/
theorem tso_stepsE_final_subset_arm (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 c : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (HSp : SpawnSim p k cap) (h : StepsE p k .tso cap c0 c)
    (hf : c.final = true) :
    ∃ c', StepsE p k .arm cap c0 c' ∧ CfgLe c' c ∧ c'.trace = c.trace ∧ c'.final = true := by
  obtain ⟨c', hr, hl, ht⟩ := tso_stepsE_subset_arm p k cap hwf HSp h
  exact ⟨c', hr, hl, ht, by rw [final_congr hl]; exact hf⟩

end TermArchE

#print axioms TermArchE.hwf_of_noProm
#print axioms TermArchE.Step_simT
#print axioms TermArchE.Ext_sim
#print axioms TermArchE.stepsG_sim
#print axioms TermArchE.tso_stepsG_subset_arm
#print axioms TermArchE.tso_extRuns_subset_arm
#print axioms TermArchE.tso_stepsE_subset_arm
#print axioms TermArchE.tso_extTraces_subset_arm
#print axioms TermArchE.tso_traces_subset_arm
#print axioms TermArchE.tso_stepsE_final_subset_arm
