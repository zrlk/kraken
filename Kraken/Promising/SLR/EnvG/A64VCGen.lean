/-
**`vcgen` over `EnvG`, AArch64**.

`vcgen` runs non-memory instructions (`MOV`, `CBZ`, `ADD`, …) in an
environment through the generic rule `MachineWP.env_lift_spec`, which needs
`[env.Skips]`: fences change nothing. `EnvG` is not `Skips`: a fence raises
`vrNew`/`vwNew` and sets the fence bits (`FenceOut`). Without a replacement
`vcgen` stops at the first `MOV` ("No spec applicable"), so this file is
needed by every per-program `EnvG` proof.

(`FenceLe` and `SharedEnv.FenceMono` with its instances are ISA-neutral and
live in `EnvG/VCGenCommon.lean`, imported here; this file keeps the
AArch64-specific rule `envMono_lift_spec`.)

- `FenceLe σ σ'`: `σ'` is `σ` after fences: only `vrNew`/`vwNew` grow and the
  fence bits are only set; anchor, resource, ghost, `cl` and `seen` are
  unchanged. Reflexive, transitive, and stable under every `EnvG` fence
  (`fenceInv_fenceLe`).
- `SharedEnv.FenceMono env` (class, ISA-neutral): fences move the state up a
  reflexive relation `le` that is fence-stable (`Skips` is `le = Eq`).
  Instances: `EnvG` (`le = FenceLe`) and `SharedEnv.counted env` (the counter
  does not tick at fences; needed for `cfgEnv_partial`'s back edges).
- `envMono_lift_spec` (`@[spec 40]`, `[env.FenceMono]`): the generic rule
  with the invariant `le σ` instead of `(· = σ)`. The continuation is asked at
  every `σ'` with `le σ σ'`. A `vcgen` goal after a silent instruction
  therefore carries `FenceMono.le σ σ'` (`simp only [fenceMono_le_envG,
  fenceMono_le_counted]` turns it into `FenceLe`); the per-program table
  predicates are monotone in it (lower bounds on views), via the projections
  `FenceLe.r`, `.g`, `.snap`, `.vwOld`, `.getFwd`, ….
  Its priority (40) is below the barrier rules (`dmb_shared_spec` etc., 50):
  `DMB`/`DSB`/`ISB` keep their precise `FenceOut` step. The memory rules
  (`str_env_spec`, `stlr_shared_spec`, `ldar_shared_spec`, …) are above it.
  The rule is keyed on a variable `env` with a class argument, like
  `env_lift_spec`: a variant stated directly on `EnvProgram (EnvG I A tid pl)`
  was listed as a candidate by `vcgen` but never applied.
-/
import Kraken.AArch64.EnvVCGen
import Kraken.Promising.SLR.EnvG.VCGenCommon

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

section Specs

open Std.WP MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- **The generic rule for monotone-fence environments** (`EnvG`). Any cell:
run it by the `MachineWP` rules, with the tail's environment wp at every `σ'`
above `σ` as its postcondition (lifting with the invariant `le σ`). -/
@[spec 40] theorem envMono_lift_spec [env.FenceMono] (d : Directive) :
    ⦃ fun s σ => WP.wp ([d] : Program)
        (fun _ s' => ∀ σ', SharedEnv.FenceMono.le σ σ' → WP.wp (⟨p⟩ : EnvProgram env) Q E s' σ')
        (fun a s' => ∀ σ', SharedEnv.FenceMono.le σ σ' → E a s' σ') s ⦄
      (⟨d :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s σ h => by
    apply Executable.wpEnv_cons
    exact Executable.wpEnv_mono (fun _ σ' ⟨h1, h2⟩ => h1 σ' h2) (fun _ _ σ' ⟨h1, h2⟩ => h1 σ' h2)
      (Executable.wpEnv_of_wp
        (Q := fun s' => ∀ σ', SharedEnv.FenceMono.le σ σ' → cenv.wpEnv env p (Q ()) E s' σ')
        (E := fun a s' => ∀ σ', SharedEnv.FenceMono.le σ σ' → E a s' σ')
        (SharedEnv.FenceMono.fenceInv σ) h σ (SharedEnv.FenceMono.refl σ))

end Specs

end Kraken.Promising.SLR.EnvG
