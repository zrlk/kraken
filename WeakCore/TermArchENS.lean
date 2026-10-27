/-
# TermArchENS — TSO ⊆ ARM for every `StepsE` run of a spawn-free program

`TermArchE.tso_stepsE_subset_arm` needs a spawn simulation (`SpawnSim`; proved in
`TermArchS.spawn_sim`, which subsumes this module's headlines; kept as the direct route).
A spawn-free program (`NoSpawnP`) from a spawn-free configuration (`NoSpawnC`) takes
no `Spawn` step, so its `StepsE` runs are runs of machine and extern steps, and
`TermArchE.tso_extRuns_subset_arm` applies with no premise.

* `cfgNoS_ext`: the extern step keeps a configuration spawn-free (`A9NoSpawn.cfgNoS_step` covers
  `Step`; `A9NoSpawn.no_spawn` rules out `Spawn`).
* `stepsE_extRuns_of_noSpawn`: such a `StepsE` run is a `StepsG … (Ext …)` run.
* Headlines `tso_stepsE_subset_arm_noSpawn` and `tso_traces_subset_arm_noSpawn`.
-/
import WeakCore.TermArchE
import WeakCore.SpawnNoSpawn

namespace TermArchENS
open CoreLang CoreTerm TermRun TermArch TermSpawnStep TermExtStep TermArchE A9NoSpawn
open WeakMem (Arch)

/-- The extern step keeps a configuration spawn-free. -/
theorem cfgNoS_ext {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) {x : String} {n : ExtName}
    {a : At} {e : Expr} (hterm : th.term = .let_ x (.ext n a) e) (hc : CfgNoS isSpawn c) (ws rs : List Word) :
    CfgNoS isSpawn (extCfg c i th x n e ws rs) := by
  have hT := hc i th hth
  have he : NoS isSpawn e := by
    have h1 := hT.1
    rw [hterm] at h1
    exact h1.2
  have key : ∀ {th' : TTh} (j : Nat) (th0 : TTh), (c.ths.set! i th')[j]? = some th0 →
      th'.term = e → th'.stack = th.stack → ThNoS isSpawn th0 := by
    intro th' j th0 hj ht hs
    rcases getElem?_set!_or hj with rfl | hj
    · exact ⟨ht ▸ he, hs ▸ hT.2⟩
    · exact hc j th0 hj
  intro j th0 hj
  cases n with
  | current =>
      cases hl : th.tidLbl with
      | some l => simp only [extCfg, curCfg, hl] at hj; exact key j th0 hj rfl rfl
      | none => simp only [extCfg, curCfg, hl] at hj; exact key j th0 hj rfl rfl
  | _ => exact key j th0 hj rfl rfl

/-- (D4) `wake` keeps a configuration spawn-free (it changes only permits). -/
theorem cfgNoS_wake {c : Cfg} (i : Nat) (v : WeakMem.Ts) (n : ExtName) (ws : List Word) (hc : CfgNoS isSpawn c) :
    CfgNoS isSpawn (wake c i v n ws) := fun j th0 hj => by
  rcases wake_get c i v n ws j with h | ⟨th, u, h1, h2⟩
  · rw [h] at hj; exact hc j th0 hj
  · rw [h2] at hj; cases hj; exact hc j th h1

/-- A `StepsE` run of a spawn-free program from a spawn-free configuration has no `Spawn` step. -/
theorem stepsE_extRuns_of_noSpawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (hp : NoSpawnP p) (h0 : NoSpawnC c0) (h : StepsE p k arch cap c0 c) :
    StepsG p k arch (Ext p k arch) c0 c := by
  have hp' : ProgNoS isSpawn p := fun d hd => noS_of_expr (hp d hd)
  have key : ∀ {c1 c2 : Cfg}, StepsE p k arch cap c1 c2 → CfgNoS isSpawn c1 →
      StepsG p k arch (Ext p k arch) c1 c2 := by
    intro c1 c2 h12
    induction h12 with
    | refl => exact fun _ => .refl _
    | step hs _ ih =>
        intro hc
        rcases hs with hs | hs | hs
        · exact .step (.inl hs) (ih (cfgNoS_step hp' hc hs))
        · exact (no_spawn hc hs).elim
        · obtain ⟨i, x, n, a, e, th, rt, ws, rs, hth, hterm, -, -, -, -, rfl⟩ := hs.elim
          exact .step (.inr hs) (ih (cfgNoS_wake i _ n ws (cfgNoS_ext hth hterm hc ws rs)))
  exact key h (cfgNoS_iff.1 h0)

/-- **Headline (spawn-free programs).**  Every TSO `StepsE` run is matched by an ARM `StepsE` run
with the same trace, terms, values, promises and counters, and views no higher. -/
theorem tso_stepsE_subset_arm_noSpawn (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 c : Cfg}
    (hp : NoSpawnP p) (h0 : NoSpawnC c0) (hwf : ∀ t ∈ allP c0, t < c0.mem.size)
    (h : StepsE p k .tso cap c0 c) :
    ∃ c', StepsE p k .arm cap c0 c' ∧ CfgLe c' c ∧ c'.trace = c.trace := by
  obtain ⟨c', hr, hl, ht⟩ := tso_extRuns_subset_arm p k hwf (stepsE_extRuns_of_noSpawn hp h0 h)
  exact ⟨c', StepsG.mono (fun _ _ h => .inr h) hr, hl, ht⟩

/-- Every TSO trace of a spawn-free program is an ARM trace. -/
theorem tso_traces_subset_arm_noSpawn (p : Prog) (k : Promises.Knobs) (cap : Nat) {c0 : Cfg}
    (hp : NoSpawnP p) (h0 : NoSpawnC c0) (hwf : ∀ t ∈ allP c0, t < c0.mem.size) {tr : List Event}
    (h : STrE p k .tso cap c0 tr) : STrE p k .arm cap c0 tr := by
  obtain ⟨c, hr, rfl⟩ := h
  obtain ⟨c', hr', -, ht⟩ := tso_stepsE_subset_arm_noSpawn p k cap hp h0 hwf hr
  exact ⟨c', hr', ht⟩

end TermArchENS

#print axioms TermArchENS.cfgNoS_ext
#print axioms TermArchENS.stepsE_extRuns_of_noSpawn
#print axioms TermArchENS.tso_stepsE_subset_arm_noSpawn
#print axioms TermArchENS.tso_traces_subset_arm_noSpawn
