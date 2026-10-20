/-
Environments whose fences are all permitted: `FenceInv (fun _ => True)` for
every `Skips` environment (fences change nothing) and every `FenceMono`
environment (fences move the state up a preorder). These are the fence side
conditions under which a sequential procedure specification lifts to a
fragment specification (`FragSpecEnvL.ofProcSpec`, `Lower/FragSpecProc.lean`).
-/
import Kraken.Promising.SLR.EnvG.VCGenCommon

namespace Kraken.SharedEnv

/-- A `Skips` environment permits every fence. -/
theorem Skips.fenceInv_true (env : SharedEnv) [env.Skips] : env.FenceInv (fun _ => True) :=
  Skips.fencesSkip.fenceInv_true

/-- Every fence-monotone environment permits every fence. -/
theorem FenceMono.fenceInv_true (env : SharedEnv) [env.FenceMono] : env.FenceInv (fun _ => True) :=
  fun k g _ => ⟨(FenceMono.fenceInv g k g (FenceMono.refl g)).1, fun _ _ => trivial⟩

end Kraken.SharedEnv
