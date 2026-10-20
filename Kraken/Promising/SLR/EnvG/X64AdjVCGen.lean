/-
**Part 2: `vcgen` over the x64 adjacency
environment `EnvGCAdjX`** (`EnvG/X64AdjLink.lean`); the x64 counterpart of
`EnvG/AdjVCGenA64.lean`, as `EnvG/X64RmwGhostVCGen.lean` is of
`EnvG/RmwGhostVCGen.lean`.

- The `@[simp]` `ok`/`step` lemmas of `EnvGCAdj` at the env-state type are
  ISA-neutral (`EnvG/AdjVCGenCommon.lean`: `envGCAdj_ok_*_st`,
  `envGCAdj_step_*`) and imported as they are; through `within S` (`EnvGCAdjX`)
  `ok` gains `AccessIn S` and `step` is unchanged.
- **`SharedEnv.FenceMonoX`** for `EnvGCAdj` with `le = FenceLe` (its fences
  are `EnvG`'s: `fenceInv_fenceLe`), and `fenceMonoX_le_envGCAdjX`
  (`@[simp]`). With the existing `within` and `counted` instances
  (`EnvG/X64VCGen.lean`), `envMonoX_lift_spec` runs the silent cells of
  `SharedEnv.counted (EnvGCAdjX …)`.
- The x64 RMW rules (`lock_cmpxchg_shared_spec`, `xchg_shared_spec`, …,
  `Kraken/EnvVCGen.lean`, and the absolute ones in `Kraken/EnvVCGenAbs*.lean`)
  are stated for any environment; no new spec is needed.
-/
import Kraken.Promising.SLR.EnvG.X64AdjLink
import Kraken.Promising.SLR.EnvG.X64RmwGhostVCGen
import Kraken.Promising.SLR.EnvG.AdjVCGenCommon

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

instance instFenceMonoXEnvGCAdj (A : Arch) (tid : Nat) (pl : Plan) : (EnvGCAdj I A tid pl).FenceMonoX :=
  ⟨FenceLe, FenceLe.refl, fun σ => fenceInv_fenceLe A tid pl σ⟩

@[simp] theorem fenceMonoX_le_envGCAdjX (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMonoX.le (env := EnvGCAdj I A tid pl)) = FenceLe := rfl

end Kraken.Promising.X64.EnvG
