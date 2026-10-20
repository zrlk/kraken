/-
**Part 2: `vcgen` over `EnvGT`** (the
`EnvG/Simp.lean` and `EnvG/A64VCGen.lean` support, for the environment with
taking loads, `EnvG/TakeEnv.lean`).

- **`@[simp]` `ok`/`step`** at states typed `(EnvGT I A tid pl).State` (as
  `vcgen` goals carry them): `ok` is `EnvG`'s (`StoreOk`/`RmwOk`, trivial
  for loads and fences); a load step is `LoadOutT`, the others are
  `StoreOut`/`RmwOut`/`FenceOut`. So every `EnvG` store/RMW/fence fact
  (`step_storeFacts`, …) applies to an `EnvGT` goal after `simp`.
- **`SharedEnv.FenceMono (EnvGT I A tid pl)`** with `le = FenceLe`: fences
  are `EnvG`'s, so `fenceInv_fenceLe` is the proof; `envMono_lift_spec`
  (`@[spec 40]`) then runs silent instructions, also under
  `SharedEnv.counted` (the generic instance).
- `takeEff_of_not_acq`: a non-acquire load takes nothing (the resource and
  ghost of the anchor), the form a plain `ldr` VC uses.

Everything here is ISA-neutral and lives, with the same names
and statements, in `EnvG/TakeVCGenCommon.lean`; this module re-exports it
together with the AArch64 `vcgen` rule (`EnvG/A64VCGen.lean`).

Phase-1 limits as `EnvG/TakeEnv.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeVCGenCommon
import Kraken.Promising.SLR.EnvG.A64VCGen
