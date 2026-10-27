import WeakCore.TermSpawnStep

/-! # TermSpawnSuccs: explorer successors for the `Spawn` step (E3)

The bounded explorer (`TermRun.successorsAll`) takes thread steps, promises and extern steps, but no
`Spawn` (a configuration step beside `Step`, `TermSpawnStep.Spawn`).  This module adds the missing
successors as a separate function, **not** wired into `successorsAll`:

* `spawnSuccs c`: for every thread at `let x = spawn f a T ts in e` with no promises, while
  `c.ths.size < c.cap`, the configuration `spawnCfg …` (exactly `Spawn.mk`'s side conditions).
* `spawnSuccs_sound`: every such successor is a `Spawn … c.cap` step.
* `exploreMS`: `TermRun.exploreM`'s breadth-first search over `successors ++ spawnSuccs` (same keys,
  same bound), returning the finals, the number of configurations seen, and whether the bound cut it.

Programs that spawn (EM0, `EM0.lean`) are explored with `exploreMS`.
-/

namespace TermSpawnSuccs

open CoreLang CoreTerm TermRun TermSpawnStep
open WeakMem (Arch)

/-- The `Spawn` moves of thread `i` (`Spawn.mk`'s side conditions, capacity `c.cap`). -/
def spawnSuccsAt (c : Cfg) (i : Nat) : List Cfg :=
  match c.ths[i]? with
  | some th => match th.term with
    | .let_ x (.spawn f a T ts) e =>
        if th.promises.isEmpty && decide (c.ths.size < c.cap) then
          match evalAt th.env a with
          | some (_, ws) => [spawnCfg c i th x e f ts T ws]
          | none => []
        else []
    | _ => []
  | none => []

/-- The `Spawn` moves of every thread. -/
def spawnSuccs (c : Cfg) : List Cfg :=
  (List.range c.ths.size).flatMap (spawnSuccsAt c)

/-- **Every `spawnSuccs` successor is a `Spawn` step** at capacity `c.cap`. -/
theorem spawnSuccs_sound {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : c' ∈ spawnSuccs c) : Spawn p k arch c.cap c c' := by
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 h
  unfold spawnSuccsAt at hi
  split at hi
  · rename_i th hth
    split at hi
    · rename_i x f a T ts e hterm
      split at hi
      · rename_i hc
        simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hc
        split at hi
        · rename_i rt ws hev
          simp only [List.mem_singleton] at hi
          subst hi
          exact Spawn.mk i x f a T ts e th rt ws hth hterm hc.1 hc.2 hev
        · cases hi
      · cases hi
    · cases hi
  · cases hi

/-- `TermRun.exploreM` over `successors ++ spawnSuccs`: the finals, the configurations seen, and
whether the search was cut (`TermRun.exploreMT`: the depth bound or another truncation; spawn
sites are not one, their moves are offered). -/
def exploreMS (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (fuel : Nat) (c : Cfg) :
    Explored :=
  (exploreMT (fun d => let r := successorsT p k arch b false d; (r.1 ++ spawnSuccs d, r.2)) fuel c).1

end TermSpawnSuccs

#print axioms TermSpawnSuccs.spawnSuccs_sound
