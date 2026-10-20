/-
**Part 2: `vcgen` over `EnvGCX`/`EnvGTCX`**
(the x64 copy of the `swpl` relay's `EnvG/RmwGhostVCGen.lean`, which imports
AArch64 files and so cannot serve x64 files; the `EnvG/TakeX64VCGen.lean`
pattern).

- **`@[simp]` `ok`/`step`** at states typed `(EnvGC I A tid pl).State` /
  `(EnvGTCI I A tid pl).State` (as `vcgen` goals carry them), with an `X`
  suffix: `ok` is `StoreOk`/`RmwOkC` (trivial for loads and fences); a load
  step is `LoadOut` (`EnvGC`) or `LoadOutT` (`EnvGTCI`), a store `StoreOut`,
  an RMW `RmwOutC`, a fence `FenceOut`. Through `within` (`EnvGCX`,
  `EnvGTCX`) `ok` gains `AccessIn S` and `step` is unchanged.
- **Step facts** of `EnvGTCI`: `step_loadFactsTCX` (`loadOutT_facts`),
  `step_storeFactsTCX` (`storeOut_facts`), `step_rmwFactsTCX`
  (`rmwOutC_facts`).
- **`SharedEnv.FenceMonoX`** for both, with `le = FenceLe` (their fences are
  `EnvG`'s, so `fenceInv_fenceLe` is the proof); `fenceMonoX_le_envGCX`,
  `fenceMonoX_le_envGTCX` (`@[simp]`). With the existing `within` and `counted`
  instances (`EnvG/X64VCGen.lean`), `envMonoX_lift_spec` runs silent
  instructions of `SharedEnv.counted (EnvGTCX …)`.
- **x64 RMWs claim**: `claimSlotsC_acqRel` (`@[simp]`,
  `EnvG/X64RmwGhostLink.lean`) turns an x64 RMW outcome's resource into
  `pl.after … ⋅ prod (claimedSlots …)`; `Res.op_wr_q_ge` bounds the
  fractions after it from below (the claim only adds). The `vcgen` rule for
  `xchg` and the locked RMWs is the generic one (`X64/EnvVCGen.lean`), stated
  for any environment; no new spec is needed.

Phase-1 limits as `EnvG/X64RmwGhostLink.lean`.
-/
import Kraken.Promising.SLR.EnvG.X64RmwGhostLink
import Kraken.Promising.SLR.EnvG.TakeX64VCGen
import Kraken.Promising.SLR.EnvG.RmwGhostVCGenCommon

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-! ## `ok` and `step` of `EnvGC` and `EnvGTCI`, step facts of `EnvGTCI`

Aliases of the ISA-neutral originals in `EnvG/RmwGhostVCGenCommon.lean`
(`envGC_*_st`/`envGC_step_*`, `envGTC_*`, `step_*FactsTC`), with
their statements (`EnvGTCI` is `EnvGTC`'s alias). -/

hoist_alias [Kraken.Promising.SLR.EnvGTC ↦ Kraken.Promising.X64.EnvG.EnvGTCI,
  Kraken.Promising.SLR.EnvG.envGC_ok_load_st ↦ Kraken.Promising.X64.EnvG.envGC_ok_load_stX,
  Kraken.Promising.SLR.EnvG.envGC_ok_fence_st ↦ Kraken.Promising.X64.EnvG.envGC_ok_fence_stX,
  Kraken.Promising.SLR.EnvG.envGC_ok_store_st ↦ Kraken.Promising.X64.EnvG.envGC_ok_storeX,
  Kraken.Promising.SLR.EnvG.envGC_ok_rmw_st ↦ Kraken.Promising.X64.EnvG.envGC_ok_rmwX,
  Kraken.Promising.SLR.EnvG.envGC_step_load ↦ Kraken.Promising.X64.EnvG.envGC_step_loadX,
  Kraken.Promising.SLR.EnvG.envGC_step_store ↦ Kraken.Promising.X64.EnvG.envGC_step_storeX,
  Kraken.Promising.SLR.EnvG.envGC_step_rmw ↦ Kraken.Promising.X64.EnvG.envGC_step_rmwX,
  Kraken.Promising.SLR.EnvG.envGC_step_fence ↦ Kraken.Promising.X64.EnvG.envGC_step_fenceX,
  Kraken.Promising.SLR.EnvG.envGTC_ok_load_st ↦ Kraken.Promising.X64.EnvG.envGTCI_ok_load_stX,
  Kraken.Promising.SLR.EnvG.envGTC_ok_fence_st ↦ Kraken.Promising.X64.EnvG.envGTCI_ok_fence_stX,
  Kraken.Promising.SLR.EnvG.envGTC_ok_store_st ↦ Kraken.Promising.X64.EnvG.envGTCI_ok_storeX,
  Kraken.Promising.SLR.EnvG.envGTC_ok_rmw_st ↦ Kraken.Promising.X64.EnvG.envGTCI_ok_rmwX,
  Kraken.Promising.SLR.EnvG.envGTC_step_load ↦ Kraken.Promising.X64.EnvG.envGTCI_step_loadX,
  Kraken.Promising.SLR.EnvG.envGTC_step_store ↦ Kraken.Promising.X64.EnvG.envGTCI_step_storeX,
  Kraken.Promising.SLR.EnvG.envGTC_step_rmw ↦ Kraken.Promising.X64.EnvG.envGTCI_step_rmwX,
  Kraken.Promising.SLR.EnvG.envGTC_step_fence ↦ Kraken.Promising.X64.EnvG.envGTCI_step_fenceX,
  Kraken.Promising.SLR.EnvG.step_loadFactsTC ↦ Kraken.Promising.X64.EnvG.step_loadFactsTCX,
  Kraken.Promising.SLR.EnvG.step_storeFactsTC ↦ Kraken.Promising.X64.EnvG.step_storeFactsTCX,
  Kraken.Promising.SLR.EnvG.step_rmwFactsTC ↦ Kraken.Promising.X64.EnvG.step_rmwFactsTCX]

attribute [simp] envGC_ok_load_stX envGC_ok_fence_stX envGC_ok_storeX envGC_ok_rmwX envGC_step_loadX envGC_step_storeX envGC_step_rmwX envGC_step_fenceX envGTCI_ok_load_stX envGTCI_ok_fence_stX envGTCI_ok_storeX envGTCI_ok_rmwX envGTCI_step_loadX envGTCI_step_storeX envGTCI_step_rmwX envGTCI_step_fenceX

/-! ## Claims only add -/

/-- The claimed slots' product never lowers a write fraction. -/
theorem Res.op_wr_q_ge (r C : Res) (x : Loc) (hC : 0 ≤ (C.wr x).q) : (r.wr x).q ≤ ((r.op C).wr x).q := by
  show (r.wr x).q ≤ (r.wr x).q + (C.wr x).q
  grind

/-! ## Fences -/

instance instFenceMonoXEnvGC (A : Arch) (tid : Nat) (pl : Plan) : (EnvGC I A tid pl).FenceMonoX :=
  ⟨FenceLe, FenceLe.refl, fun σ => fenceInv_fenceLe A tid pl σ⟩

instance instFenceMonoXEnvGTCI (A : Arch) (tid : Nat) (pl : Plan) : (EnvGTCI I A tid pl).FenceMonoX :=
  ⟨FenceLe, FenceLe.refl, fun σ => fenceInv_fenceLe A tid pl σ⟩

@[simp] theorem fenceMonoX_le_envGCX (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMonoX.le (env := EnvGC I A tid pl)) = FenceLe := rfl

@[simp] theorem fenceMonoX_le_envGTCX (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMonoX.le (env := EnvGTCI I A tid pl)) = FenceLe := rfl

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.X64.EnvG.step_rmwFactsTCX
#print axioms Kraken.Promising.X64.EnvG.instFenceMonoXEnvGTCI
