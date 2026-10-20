import WeakCore.SpawnLeaf
import WeakCore.SpawnShapeZ
import WeakCore.SpawnVZ
import WeakCore.TermSpawnScope
/-!
# SpawnLeafZ — `spLeafArms_spawn : SpLeafArms (Spawn p k arch cap)`

Pure glue, no new proof:
* shape    — `SpawnShapeZ.spawn_shapeT` (over the `TermSpawnStep.spawnT`);
* L1 view  — `Z2SpawnV.viewInv_spawnStep` (SpawnVZ);
* L2 scope — `TermSpawnScope.runScope_spawnStep` (M0 name);
  requires `SpLeafArms.runDRF` to be over `TermScope.RunScope` (M0 rename of SpawnFinalX).
* L3–L5    — the `promViewLt/promPos/promNodupI_spawnT` via `SpawnLeaf.spLeafArms_of_shape`.

PRECONDITION: `SpawnLeaf.SpawnShapeT` and the TermSpawnArms must be stated over
`TermSpawnStep.spawnT` (not `TermSpawnStep.spawnT`, copy rule).
-/
namespace SpawnLeafZ
open CoreLang CoreTerm TermRun TermStep TermMain TermSpawnStep A9SpawnFinal
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem spLeafArms_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} :
    SpLeafArms (Spawn p k arch cap) :=
  SpawnLeaf.spLeafArms_of_shape (fun _ _ h => SpawnShapeZ.spawn_shapeT h)
    (fun _ _ h hv => Z2SpawnV.viewInv_spawnStep h hv)
    (fun _ _ h hd => TermSpawnScope.runScope_spawnStep h hd)

#print axioms spLeafArms_spawn
end SpawnLeafZ
