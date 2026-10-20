/-
**Part 2: `vcgen` over `EnvGTX`** (the x64
copy of `EnvG/TakeVCGen.lean`, which imports `EnvG/A64VCGen.lean` and so
cannot serve x64 files).

- **`@[simp]` `ok`/`step`** at states typed `(EnvGT I A tid pl).State`:
  `ok` is `EnvG`'s (`StoreOk`/`RmwOk`, trivial for loads and fences); a load
  step is `LoadOutT`, the others are `StoreOut`/`RmwOut`/`FenceOut` (the
  statements of `TakeVCGen`'s lemmas, here with an `X` suffix;
  aliases of the originals in the ISA-neutral `EnvG/TakeVCGenCommon.lean`,
  which this module imports, so the originals are the simp lemmas). Through
  `within` (`EnvGTX`) `ok` gains `AccessIn S` and `step` is unchanged.
- **`SharedEnv.FenceMonoX (EnvGT I A tid pl)`** with `le = FenceLe` (fences
  are `EnvG`'s; the instance is `TakeVCGenCommon`'s
  `instFenceMonoEnvGT`). With the existing `within`
  and `counted` instances (`EnvG/X64VCGen.lean`), `envMonoX_lift_spec` runs
  silent instructions of `SharedEnv.counted (EnvGTX …)`; `simp only
  [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGTX]` turns
  the lifted invariant into `FenceLe`.
- **`takeEff_wr_full`** (ISA-neutral): a load by a thread that already holds
  all of `x` leaves its write permission of `x` exactly as it was, whether or
  not it takes. Under `Arch.tso` every non-forwarded load takes, so an x64
  program that reads back a location it owns needs this (the AArch64 take
  route used a plain `ldr` there, `takeEff_of_not_acq`).

Phase-1 limits as `EnvG/TakeEnv.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeVCGenCommon
import Kraken.Promising.SLR.EnvG.TakeAllWr
import Kraken.Promising.SLR.EnvG.X64VCGen

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-! ## `ok` and `step`

The `X` lemmas were a copy of `TakeVCGen`'s; the originals are
in the ISA-neutral `EnvG/TakeVCGenCommon.lean` (imported here, `@[simp]`) and
these names are their aliases (`hoist_alias`, same statements, not
re-registered as simp lemmas). -/

hoist_alias [
  Kraken.Promising.SLR.EnvG.envGT_ok_load_st ↦ Kraken.Promising.X64.EnvG.envGT_ok_load_stX,
  Kraken.Promising.SLR.EnvG.envGT_ok_fence_st ↦ Kraken.Promising.X64.EnvG.envGT_ok_fence_stX,
  Kraken.Promising.SLR.EnvG.envGT_ok_store ↦ Kraken.Promising.X64.EnvG.envGT_ok_storeX,
  Kraken.Promising.SLR.EnvG.envGT_ok_rmw ↦ Kraken.Promising.X64.EnvG.envGT_ok_rmwX,
  Kraken.Promising.SLR.EnvG.envGT_step_load ↦ Kraken.Promising.X64.EnvG.envGT_step_loadX,
  Kraken.Promising.SLR.EnvG.envGT_step_store' ↦ Kraken.Promising.X64.EnvG.envGT_step_storeX,
  Kraken.Promising.SLR.EnvG.envGT_step_rmw' ↦ Kraken.Promising.X64.EnvG.envGT_step_rmwX,
  Kraken.Promising.SLR.EnvG.envGT_step_fence' ↦ Kraken.Promising.X64.EnvG.envGT_step_fenceX]

/-! ## Fences -/

/-- `SharedEnv.FenceMonoX` is an alias of `SharedEnv.FenceMono`: this is
`TakeVCGenCommon`'s `EnvGT` instance. -/
instance instFenceMonoXEnvGT (A : Arch) (tid : Nat) (pl : Plan) : (EnvGT I A tid pl).FenceMonoX :=
  instFenceMonoEnvGT A tid pl

@[simp] theorem fenceMonoX_le_envGTX (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMonoX.le (env := EnvGT I A tid pl)) = FenceLe := rfl

/-! ## A load by a thread that holds all of a location -/

/-- **A load keeps a full write permission**: if the thread holds all of `x`
(and erasure at the load's anchor ghost holds), the load's resource effect,
take or no take, leaves the thread's permission of `x` unchanged
(`EnvG.takeEff_wr_fullG`, `EnvG/TakeVCGenCommon.lean`). -/
theorem takeEff_wr_full {rF : Nat → Res} {c : Config I} {tid : Nat} {A : Arch} {k : LoadKind} {vs : Views}
    {l : Loc} {tr : Time} {r : Res} {ga : Ghost} {a : TakeAcc} (hn : tid < c.threads.size)
    (E : Erase (setRes rF tid r) ga (fun _ => True) c) (ha : TakeEff A k vs l tr r ga a) {x : Loc}
    (hq : (r.wr x).q = 1) : (a.r.wr x).q = 1 ∧ ∀ p, (a.r.wr x).X p ↔ (r.wr x).X p :=
  takeEff_wr_fullG hn E ha hq

end Kraken.Promising.X64.EnvG

#print axioms Kraken.Promising.X64.EnvG.takeEff_wr_full
