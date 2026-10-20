/-
**The barrier VCs of a monotone-fence environment.**
ISA-neutral, generic (no pilot names).

Over a `SharedEnv` with no `Skips` instance (`EnvG`, `EnvGCAdj`,
`SharedEnv.counted …`), `vcgen` runs a barrier (`DMB`/`DSB`/`ISB` on
AArch64) by `MachineWP.dmb_shared_spec` and friends, which leave two VCs:

- `env.ok (.fence k) g`: closed by `SharedEnv.FenceMono.ok_fence`;
- a step hypothesis `env.step (.fence k) g () g'`: turned into
  `SharedEnv.FenceMono.le g g'` by `SharedEnv.FenceMono.le_of_fence_step`,
  the same relation the non-memory instructions already leave
  (`envMono_lift_spec`), so the protocol's existing fence monotonicity
  (`Treiber2.Pu.fence`, `Po.fence`, …) closes the rest.

Both are the class field `FenceMono.fenceInv` at the reflexive start. Any
fence kind; first used for WeakCore's `publish` barrier `dmb ishst`
(`Lower/PublishSpecs.lean`).
-/
import Kraken.Promising.SLR.EnvG.VCGenCommon

namespace Kraken.SharedEnv.FenceMono

open Kraken

/-- **Every fence is permitted** in a monotone-fence environment. -/
theorem ok_fence {env : SharedEnv} [env.FenceMono] (k : FenceKind) (g : env.State) : env.ok (.fence k) g :=
  (SharedEnv.FenceMono.fenceInv g k g (SharedEnv.FenceMono.refl g)).1

/-- **A fence step moves the state up the fence order** `FenceMono.le`. -/
theorem le_of_fence_step {env : SharedEnv} [env.FenceMono] {k : FenceKind} {g g' : env.State}
    (h : env.step (.fence k) g () g') : SharedEnv.FenceMono.le g g' :=
  (SharedEnv.FenceMono.fenceInv g k g (SharedEnv.FenceMono.refl g)).2 g' h

end Kraken.SharedEnv.FenceMono
