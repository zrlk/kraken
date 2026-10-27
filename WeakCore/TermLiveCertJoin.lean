import WeakCore.TermLiveCertScen
/-! # TermLiveCertJoin — item 38 mode B glue: chunk join, start transfer, scenario instances

`sce --live-proof` re-checks an accepted certificate in Lean's kernel: the
generated files under `root.cert/S/` prove `check … certK c0K = true` chunk by chunk (`all_range_join`,
`check_intro`), the flags from their node ranges (`noSpawnB_intro`, `noStuckB_intro`), and then state the
conclusions for every `ScenarioStartK` start whose configuration has the certificate's start key (`scen_*`). -/
namespace TermLiveCert
open CoreLang CoreTerm TermRun TermLiveMach TermLiveL3 TermProgress TermLiveProps
open WeakMem (Arch)

/-- Two adjacent chunk theorems give the joined range. -/
theorem all_range_join {f : Nat → Bool} {a b c : Nat} (h1 : (List.range' a b).all f = true)
    (h2 : (List.range' (a + b) c).all f = true) : (List.range' a (b + c)).all f = true := by
  rw [← List.range'_append_1] at *
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h1, h2⟩

/-- `check` from its parts (the instance file proves the last part chunk by chunk). -/
theorem check_intro {p : Prog} {k : Promises.Knobs} {arch : Arch} {X V : List Nat} {ct : Cert} {c0 : Cfg}
    (h0 : 0 < ct.nodes.size) (hs : ct.succ.size = ct.nodes.size) (hr : ct.rank.size = ct.nodes.size)
    (hk : cfgKey c0 = cfgKey (ct.nodes[0]?.getD default))
    (ha : (List.range' 0 ct.nodes.size).all (ct.nodeOK p k arch X V) = true) : check p k arch X V ct c0 = true := by
  unfold check
  rw [← List.range_eq_range'] at ha
  simp [h0, hs, hr, hk, ha]

/-- `check` uses the start only through `cfgKey`. -/
theorem check_congr {p : Prog} {k : Promises.Knobs} {arch : Arch} {X V : List Nat} {ct : Cert} {c0 c1 : Cfg}
    (h : check p k arch X V ct c0 = true) (hk : cfgKey c1 = cfgKey c0) : check p k arch X V ct c1 = true := by
  unfold check at *
  rw [hk]; exact h

/-- The per-scenario mode-B statement (ScenInst-style): every scenario start of the run's arch whose key is the
certificate's start key is coherent and checked, so the conclusions of `check` hold there. -/
theorem scen_no_livelock {p : Prog} {arch : Arch} {X V : List Nat} {ct : Cert} {c0K : Cfg}
    {kids : List TermSpawn.Kid} (hc : check p Promises.Knobs.all arch X V ct c0K = true)
    (Init : TermSound.Res) (c0 : Cfg)
    (hS : ScenarioStartK p Promises.Knobs.all arch Init kids c0) (hk : cfgKey c0 = cfgKey c0K)
    (r : LRun (machineE p Promises.Knobs.all arch).L) (D : Nat → Option Nat)
    (hr : (machineE p Promises.Knobs.all arch).Run r) (hs : r.cfg 0 = c0)
    (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (hD : ∀ i, D i ≠ none → i ∈ X) (hf : FairS (machineE p Promises.Knobs.all arch) r D) :
    ¬ LivelockS (machineE p Promises.Knobs.all arch) r D :=
  no_livelock_of_check (check_congr hc hk) (cfgCoh_scenario hS) r D hr hs hpf hsr hD hf

/-- The fair form (no spawn move in the certificate): `Fair`, not `FairS`. -/
theorem scen_no_livelock_fair {p : Prog} {arch : Arch} {X V : List Nat} {ct : Cert} {c0K : Cfg}
    {kids : List TermSpawn.Kid} (hc : check p Promises.Knobs.all arch X V ct c0K = true) (hns : noSpawnB ct = true)
    (Init : TermSound.Res) (c0 : Cfg)
    (hS : ScenarioStartK p Promises.Knobs.all arch Init kids c0) (hk : cfgKey c0 = cfgKey c0K)
    (r : LRun (machineE p Promises.Knobs.all arch).L) (D : Nat → Option Nat)
    (hr : (machineE p Promises.Knobs.all arch).Run r) (hs : r.cfg 0 = c0)
    (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (hD : ∀ i, D i ≠ none → i ∈ X)
    (hf : Fair (machineE p Promises.Knobs.all arch) r D (fun _ => True)) :
    ¬ Livelock (machineE p Promises.Knobs.all arch) r D :=
  no_livelock_of_check_fair (check_congr hc hk) hns (cfgCoh_scenario hS) r D hr hs hpf hsr hD hf

/-- Final states: every final configuration of a run from such a start has the outcome of a final node. -/
theorem scen_outcome {p : Prog} {arch : Arch} {X V : List Nat} {ct : Cert} {c0K : Cfg}
    {kids : List TermSpawn.Kid} (hc : check p Promises.Knobs.all arch X V ct c0K = true)
    (Init : TermSound.Res) (c0 : Cfg)
    (hS : ScenarioStartK p Promises.Knobs.all arch Init kids c0) (hk : cfgKey c0 = cfgKey c0K)
    (r : LRun (machineE p Promises.Knobs.all arch).L) (hr : (machineE p Promises.Knobs.all arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n : Nat) (hfin : (r.cfg n).final = true)
    (m : Nat) (watch : List (Nat × Nat)) :
    ∃ v, v < ct.nodes.size ∧ (ct.nodes[v]?.getD default).final = true ∧
      outcome m watch (r.cfg n) = outcome m watch (ct.nodes[v]?.getD default) :=
  outcome_of_check (check_congr hc hk) (cfgCoh_scenario hS) r hr hs hpf hsr n hfin m watch

/-- Termination: with no crash thread and no stuck node, every fair run reaches a final state. -/
theorem scen_terminates {p : Prog} {arch : Arch} {V : List Nat} {ct : Cert} {c0K : Cfg}
    {kids : List TermSpawn.Kid} (hc : check p Promises.Knobs.all arch [] V ct c0K = true)
    (hst : noStuckB p Promises.Knobs.all arch V ct = true)
    (Init : TermSound.Res) (c0 : Cfg)
    (hS : ScenarioStartK p Promises.Knobs.all arch Init kids c0) (hk : cfgKey c0 = cfgKey c0K)
    (r : LRun (machineE p Promises.Knobs.all arch).L) (hr : (machineE p Promises.Knobs.all arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (hf : FairS (machineE p Promises.Knobs.all arch) r (fun _ => none)) :
    ∃ n, (r.cfg n).final = true :=
  terminates_of_check (check_congr hc hk) hst (cfgCoh_scenario hS) r hr hs hpf hsr hf

/-- `noSpawnB`'s per-node test (the generated `s{a}.lean` files prove it on a node range). -/
def spawnOK (ct : Cert) (v : Nat) : Bool :=
  (List.range (ct.nd v).ths.size).all fun i => (TermSpawnSuccs.spawnSuccsAt (ct.nd v) i).isEmpty

/-- `noStuckB`'s per-node test. -/
def stuckOK (p : Prog) (k : Promises.Knobs) (arch : Arch) (V : List Nat) (ct : Cert) (v : Nat) : Bool :=
  (ct.nd v).final || (List.range (ct.nd v).ths.size).any fun i => !(movesPF p k arch V (ct.nd v) i).isEmpty

/-- `noSpawnB` from its node range (proved chunk by chunk, joined by `all_range_join`). -/
theorem noSpawnB_intro {ct : Cert}
    (h : (List.range' 0 ct.nodes.size).all (spawnOK ct) = true) :
    noSpawnB ct = true := by
  unfold noSpawnB; rw [List.range_eq_range']; exact h

/-- `noStuckB` from its node range. -/
theorem noStuckB_intro {p : Prog} {k : Promises.Knobs} {arch : Arch} {V : List Nat} {ct : Cert}
    (h : (List.range' 0 ct.nodes.size).all (stuckOK p k arch V ct) = true) :
    noStuckB p k arch V ct = true := by
  unfold noStuckB; rw [List.range_eq_range']; exact h

/-! ### The statements at sce's computed start (the generated `main.lean` instantiates these)

`cs` is the start sce computed (`Doc.spawnStart` on the program literal); `start.lean` proves
`cfgKey cs = cfgKey c0K` in the kernel.  Each statement quantifies over every scenario start (`ScenarioStartK`, the
standard obligations) whose configuration has that key. -/

/-- No fair livelock (spawned threads scheduled fairly: `FairS`). -/
def NoLivelockAt (p : Prog) (X : List Nat) (kids : List TermSpawn.Kid) (cs : Cfg) : Prop :=
  ∀ (Init : TermSound.Res) (c0 : Cfg), ScenarioStartK p Promises.Knobs.all .arm Init kids c0 →
    cfgKey c0 = cfgKey cs → ∀ (r : LRun (machineE p Promises.Knobs.all .arm).L) (D : Nat → Option Nat),
      (machineE p Promises.Knobs.all .arm).Run r → r.cfg 0 = c0 → PromiseFreeRun r → ScriptedRun [] r → (∀ i, D i ≠ none → i ∈ X) →
      FairS (machineE p Promises.Knobs.all .arm) r D → ¬ LivelockS (machineE p Promises.Knobs.all .arm) r D

/-- No fair livelock (`Fair`: the certificate has no spawn move). -/
def NoLivelockFairAt (p : Prog) (X : List Nat) (kids : List TermSpawn.Kid) (cs : Cfg) : Prop :=
  ∀ (Init : TermSound.Res) (c0 : Cfg), ScenarioStartK p Promises.Knobs.all .arm Init kids c0 →
    cfgKey c0 = cfgKey cs → ∀ (r : LRun (machineE p Promises.Knobs.all .arm).L) (D : Nat → Option Nat),
      (machineE p Promises.Knobs.all .arm).Run r → r.cfg 0 = c0 → PromiseFreeRun r → ScriptedRun [] r → (∀ i, D i ≠ none → i ∈ X) →
      Fair (machineE p Promises.Knobs.all .arm) r D (fun _ => True) → ¬ Livelock (machineE p Promises.Knobs.all .arm) r D

/-- Final states: every final configuration has the outcome (`m` threads, `watch`) of a final node of `ct`. -/
def OutcomesAt (p : Prog) (kids : List TermSpawn.Kid) (cs : Cfg) (ct : Cert) (m : Nat) (watch : List (Nat × Nat)) :
    Prop :=
  ∀ (Init : TermSound.Res) (c0 : Cfg), ScenarioStartK p Promises.Knobs.all .arm Init kids c0 →
    cfgKey c0 = cfgKey cs → ∀ (r : LRun (machineE p Promises.Knobs.all .arm).L),
      (machineE p Promises.Knobs.all .arm).Run r → r.cfg 0 = c0 → PromiseFreeRun r → ScriptedRun [] r →
      ∀ n, (r.cfg n).final = true → ∃ v, v < ct.nodes.size ∧ (ct.nodes[v]?.getD default).final = true ∧
        outcome m watch (r.cfg n) = outcome m watch (ct.nodes[v]?.getD default)

/-- Every fair run reaches a final state. -/
def TerminatesAt (p : Prog) (kids : List TermSpawn.Kid) (cs : Cfg) : Prop :=
  ∀ (Init : TermSound.Res) (c0 : Cfg), ScenarioStartK p Promises.Knobs.all .arm Init kids c0 →
    cfgKey c0 = cfgKey cs → ∀ (r : LRun (machineE p Promises.Knobs.all .arm).L),
      (machineE p Promises.Knobs.all .arm).Run r → r.cfg 0 = c0 → PromiseFreeRun r → ScriptedRun [] r →
      FairS (machineE p Promises.Knobs.all .arm) r (fun _ => none) → ∃ n, (r.cfg n).final = true

theorem noLivelockAt_of_check {p : Prog} {X : List Nat} {ct : Cert} {c0K cs : Cfg} {kids : List TermSpawn.Kid}
    (hc : check p Promises.Knobs.all .arm X [] ct c0K = true) (hk : cfgKey cs = cfgKey c0K) :
    NoLivelockAt p X kids cs :=
  fun Init c0 hS h0 r D hr hs hpf hsr hD hf => scen_no_livelock hc Init c0 hS (h0.trans hk) r D hr hs hpf hsr hD hf

theorem noLivelockFairAt_of_check {p : Prog} {X : List Nat} {ct : Cert} {c0K cs : Cfg} {kids : List TermSpawn.Kid}
    (hc : check p Promises.Knobs.all .arm X [] ct c0K = true) (hns : noSpawnB ct = true) (hk : cfgKey cs = cfgKey c0K) :
    NoLivelockFairAt p X kids cs :=
  fun Init c0 hS h0 r D hr hs hpf hsr hD hf =>
    scen_no_livelock_fair hc hns Init c0 hS (h0.trans hk) r D hr hs hpf hsr hD hf

theorem outcomesAt_of_check {p : Prog} {X : List Nat} {ct : Cert} {c0K cs : Cfg} {kids : List TermSpawn.Kid}
    (hc : check p Promises.Knobs.all .arm X [] ct c0K = true) (hk : cfgKey cs = cfgKey c0K) (m : Nat)
    (watch : List (Nat × Nat)) : OutcomesAt p kids cs ct m watch :=
  fun Init c0 hS h0 r hr hs hpf hsr n hfin =>
    scen_outcome hc Init c0 hS (h0.trans hk) r hr hs hpf hsr n hfin m watch

theorem terminatesAt_of_check {p : Prog} {ct : Cert} {c0K cs : Cfg} {kids : List TermSpawn.Kid}
    (hc : check p Promises.Knobs.all .arm [] [] ct c0K = true) (hst : noStuckB p Promises.Knobs.all .arm [] ct = true)
    (hk : cfgKey cs = cfgKey c0K) : TerminatesAt p kids cs :=
  fun Init c0 hS h0 r hr hs hpf hsr hf => scen_terminates hc hst Init c0 hS (h0.trans hk) r hr hs hpf hsr hf

end TermLiveCert
#print axioms TermLiveCert.all_range_join
#print axioms TermLiveCert.check_intro
#print axioms TermLiveCert.check_congr
#print axioms TermLiveCert.scen_no_livelock
#print axioms TermLiveCert.noSpawnB_intro
#print axioms TermLiveCert.noStuckB_intro
#print axioms TermLiveCert.scen_no_livelock_fair
#print axioms TermLiveCert.scen_outcome
#print axioms TermLiveCert.scen_terminates
#print axioms TermLiveCert.noLivelockAt_of_check
#print axioms TermLiveCert.noLivelockFairAt_of_check
#print axioms TermLiveCert.outcomesAt_of_check
#print axioms TermLiveCert.terminatesAt_of_check
