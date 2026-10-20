import WeakCore.TermSpawnStep
/-!
# SpawnShapeZ — `Spawn` steps are promise-shaped `spawnT`s (the real `Spawn`)

Feeds `SpawnLeaf.spLeafArms_of_shape` (there `SpawnShapeT` must be stated over
`TermSpawnStep.spawnT`).
-/
namespace SpawnShapeZ
open CoreLang CoreTerm TermRun TermSpawn TermSpawnStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem spawn_shapeT {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : Spawn p k arch cap c c') : ∃ (i : Nat) (th par kid : TTh), c.ths[i]? = some th ∧
      par.promises = th.promises ∧ kid.promises = [] ∧ c' = spawnT c i par kid := by
  cases h
  rename_i i _ _ _ _ _ _ th _ _ hth _ _ _ _
  exact ⟨i, th, _, _, hth, by simp [spawnPar, withS, spawnS, fenceS, stOf], rfl, rfl⟩

#print axioms spawn_shapeT
end SpawnShapeZ
