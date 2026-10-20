/-
**`vcgen` over `EnvG`, x64**: the x64 copy of
`EnvG/A64VCGen.lean`, which imports `Kraken.AArch64.EnvVCGen` and so cannot
serve x64 files. Everything here but the import is ISA-neutral; the names
carry an `X` where the AArch64 file's would clash in a module importing both
(`SharedEnv.FenceMonoX`, `envMonoX_lift_spec`). The neutral half is now
shared: `FenceLe`, `fenceInv_fenceLe`,
`SharedEnv.FenceMonoX` and the `EnvG`/`counted` instances and simp lemmas are
statement-preserving aliases of the originals in `EnvG/VCGenCommon.lean`.
The `within` instance and `envMonoX_lift_spec` are x64's own.

x64's generic rule `MachineWP.env_lift_spec` (`Kraken/EnvVCGen.lean`) needs
`[env.Skips]`; `EnvG` is not `Skips` (a fence raises `vrNew`/`vwNew`).

- `FenceLe σ σ'` (in `Kraken.Promising.X64.EnvG`): `σ'` is `σ` after fences;
  reflexive, transitive, stable under every `EnvG` fence.
- `SharedEnv.FenceMonoX env` (class): fences move the state up a reflexive,
  fence-stable relation. Instances: `EnvG` (`FenceLe`), `SharedEnv.counted env`
  (the counter does not tick at fences), and `env.within S` (the same
  relation: a restriction to a layout permits every fence).
- `SharedEnv.FenceMonoX.fenceInv_true`: every `FenceMonoX` environment
  permits every fence (`FenceInv` of `True`).
- `envMonoX_lift_spec` (`@[spec 40]`): the generic rule with the invariant
  `le σ`. After a silent instruction a goal is at every `σ'` with
  `FenceMonoX.le σ σ'`; `simp only [fenceMonoX_le_envG, fenceMonoX_le_within,
  fenceMonoX_le_counted]` turns it into `FenceLe`. Priority 40 is below the
  x64 fence rules (`mfence_shared_spec` etc., 50); the memory rules
  (`mov32_store_env_spec`, …, default priority) are above it.
-/
import Kraken.EnvVCGen
import Kraken.Promising.SLR.EnvG.VCGenCommon
import Kraken.Promising.SLR.EnvG.Alias
import Kraken.Promising.SLR.EnvG.X64LiveRun

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-! ## The fence order and the class: aliases of `EnvG/VCGenCommon.lean`

The x64 names below were a verbatim copy of the ISA-neutral half of
`EnvG/A64VCGen.lean`; they are now aliases of the originals in
`EnvG/VCGenCommon.lean` (`hoist_alias`, `EnvG/Alias.lean`), each with its
original statement: `FenceLe` (= `SLR.EnvG.FenceLe`) with its constructor,
fields and lemmas, `fenceInv_fenceLe`, the class `SharedEnv.FenceMonoX`
(= `SharedEnv.FenceMono`) with its fields, the instances for `EnvG` and
`SharedEnv.counted`, and the simp lemmas `fenceMonoX_le_envG`,
`fenceMonoX_le_counted`. -/

hoist_alias [
  Kraken.Promising.SLR.EnvG.FenceLe ↦ Kraken.Promising.X64.EnvG.FenceLe,
  Kraken.Promising.SLR.EnvG.FenceLe.mk ↦ Kraken.Promising.X64.EnvG.FenceLe.mk,
  Kraken.Promising.SLR.EnvG.FenceLe.rec ↦ Kraken.Promising.X64.EnvG.FenceLe.rec,
  Kraken.Promising.SLR.EnvG.FenceLe.recOn ↦ Kraken.Promising.X64.EnvG.FenceLe.recOn,
  Kraken.Promising.SLR.EnvG.FenceLe.casesOn ↦ Kraken.Promising.X64.EnvG.FenceLe.casesOn,
  Kraken.Promising.SLR.EnvG.FenceLe.snap ↦ Kraken.Promising.X64.EnvG.FenceLe.snap,
  Kraken.Promising.SLR.EnvG.FenceLe.r ↦ Kraken.Promising.X64.EnvG.FenceLe.r,
  Kraken.Promising.SLR.EnvG.FenceLe.g ↦ Kraken.Promising.X64.EnvG.FenceLe.g,
  Kraken.Promising.SLR.EnvG.FenceLe.cl ↦ Kraken.Promising.X64.EnvG.FenceLe.cl,
  Kraken.Promising.SLR.EnvG.FenceLe.seen ↦ Kraken.Promising.X64.EnvG.FenceLe.seen,
  Kraken.Promising.SLR.EnvG.FenceLe.vs ↦ Kraken.Promising.X64.EnvG.FenceLe.vs,
  Kraken.Promising.SLR.EnvG.FenceLe.vrNew ↦ Kraken.Promising.X64.EnvG.FenceLe.vrNew,
  Kraken.Promising.SLR.EnvG.FenceLe.vwNew ↦ Kraken.Promising.X64.EnvG.FenceLe.vwNew,
  Kraken.Promising.SLR.EnvG.FenceLe.fencedR ↦ Kraken.Promising.X64.EnvG.FenceLe.fencedR,
  Kraken.Promising.SLR.EnvG.FenceLe.fencedW ↦ Kraken.Promising.X64.EnvG.FenceLe.fencedW,
  Kraken.Promising.SLR.EnvG.FenceLe.refl ↦ Kraken.Promising.X64.EnvG.FenceLe.refl,
  Kraken.Promising.SLR.EnvG.FenceLe.trans ↦ Kraken.Promising.X64.EnvG.FenceLe.trans,
  Kraken.Promising.SLR.EnvG.FenceLe.vwOld ↦ Kraken.Promising.X64.EnvG.FenceLe.vwOld,
  Kraken.Promising.SLR.EnvG.FenceLe.vrOld ↦ Kraken.Promising.X64.EnvG.FenceLe.vrOld,
  Kraken.Promising.SLR.EnvG.FenceLe.vRel ↦ Kraken.Promising.X64.EnvG.FenceLe.vRel,
  Kraken.Promising.SLR.EnvG.FenceLe.vCAP ↦ Kraken.Promising.X64.EnvG.FenceLe.vCAP,
  Kraken.Promising.SLR.EnvG.FenceLe.getCoh ↦ Kraken.Promising.X64.EnvG.FenceLe.getCoh,
  Kraken.Promising.SLR.EnvG.FenceLe.getFwd ↦ Kraken.Promising.X64.EnvG.FenceLe.getFwd,
  Kraken.Promising.SLR.EnvG.fenceInv_fenceLe ↦ Kraken.Promising.X64.EnvG.fenceInv_fenceLe,
  Kraken.SharedEnv.FenceMono ↦ Kraken.SharedEnv.FenceMonoX,
  Kraken.SharedEnv.FenceMono.mk ↦ Kraken.SharedEnv.FenceMonoX.mk,
  Kraken.SharedEnv.FenceMono.rec ↦ Kraken.SharedEnv.FenceMonoX.rec,
  Kraken.SharedEnv.FenceMono.recOn ↦ Kraken.SharedEnv.FenceMonoX.recOn,
  Kraken.SharedEnv.FenceMono.casesOn ↦ Kraken.SharedEnv.FenceMonoX.casesOn,
  Kraken.SharedEnv.FenceMono.ctorIdx ↦ Kraken.SharedEnv.FenceMonoX.ctorIdx,
  Kraken.SharedEnv.FenceMono.noConfusionType ↦ Kraken.SharedEnv.FenceMonoX.noConfusionType,
  Kraken.SharedEnv.FenceMono.noConfusion ↦ Kraken.SharedEnv.FenceMonoX.noConfusion,
  Kraken.SharedEnv.FenceMono.mk.noConfusion ↦ Kraken.SharedEnv.FenceMonoX.mk.noConfusion,
  Kraken.SharedEnv.FenceMono.le ↦ Kraken.SharedEnv.FenceMonoX.le,
  Kraken.SharedEnv.FenceMono.refl ↦ Kraken.SharedEnv.FenceMonoX.refl,
  Kraken.SharedEnv.FenceMono.fenceInv ↦ Kraken.SharedEnv.FenceMonoX.fenceInv,
  Kraken.Promising.SLR.EnvG.instFenceMono ↦ Kraken.Promising.X64.EnvG.instFenceMonoXEnvG,
  Kraken.Promising.SLR.EnvG.fenceMono_le_envG ↦ Kraken.Promising.X64.EnvG.fenceMonoX_le_envG,
  Kraken.Promising.SLR.EnvG.instFenceMonoCounted ↦ Kraken.Promising.X64.EnvG.instFenceMonoXCounted,
  Kraken.Promising.SLR.EnvG.fenceMono_le_counted ↦ Kraken.Promising.X64.EnvG.fenceMonoX_le_counted]

attribute [instance] instFenceMonoXEnvG instFenceMonoXCounted
attribute [simp] fenceMonoX_le_envG fenceMonoX_le_counted

/-- A restriction to a layout keeps the fence order (every fence is in the
layout). -/
instance (env : SharedEnv) [env.FenceMonoX] (S : SharedEnv.Layout) : (env.within S).FenceMonoX where
  le := SharedEnv.FenceMonoX.le (env := env)
  refl := SharedEnv.FenceMonoX.refl (env := env)
  fenceInv σ k g h :=
    ⟨⟨(SharedEnv.FenceMonoX.fenceInv (env := env) σ k g h).1, trivial⟩,
      (SharedEnv.FenceMonoX.fenceInv (env := env) σ k g h).2⟩

@[simp] theorem fenceMonoX_le_within (env : SharedEnv) [env.FenceMonoX] (S : SharedEnv.Layout)
    (σ σ' : (env.within S).State) :
    SharedEnv.FenceMonoX.le (env := env.within S) σ σ' ↔ SharedEnv.FenceMonoX.le (env := env) σ σ' := Iff.rfl

/-- Every fence-monotone environment permits every fence (x64; the AArch64
`SharedEnv.FenceMono.fenceInv_true`, `SLR/EnvG/FenceInvTrue.lean`). -/
theorem _root_.Kraken.SharedEnv.FenceMonoX.fenceInv_true (env : SharedEnv) [env.FenceMonoX] :
    env.FenceInv (fun _ => True) :=
  fun k g _ => ⟨(SharedEnv.FenceMonoX.fenceInv g k g (SharedEnv.FenceMonoX.refl g)).1, fun _ _ => trivial⟩


section Specs

open Std.WP MachineWP

variable [CodeEnv] {env : SharedEnv} {Q : Unit → MachineData → env.State → Prop}
  {E : Int64 → MachineData → env.State → Prop} {p : Program}

/-- **The generic rule for monotone-fence environments** (`EnvG`, x64). Any
cell: run it by the `MachineWP` rules, with the tail's environment wp at every
`σ'` above `σ` as its postcondition (lifting with the invariant `le σ`). -/
@[spec 40] theorem envMonoX_lift_spec [env.FenceMonoX] (d : Directive) :
    ⦃ fun s σ => WP.wp ([d] : Program)
        (fun _ s' => ∀ σ', SharedEnv.FenceMonoX.le σ σ' → WP.wp (⟨p⟩ : EnvProgram env) Q E s' σ')
        (fun a s' => ∀ σ', SharedEnv.FenceMonoX.le σ σ' → E a s' σ') s ⦄
      (⟨d :: p⟩ : EnvProgram env) ⦃ Q; E ⦄ :=
  Triple.intro fun s σ h => by
    apply Executable.wpEnv_cons
    exact Executable.wpEnv_mono (fun _ σ' ⟨h1, h2⟩ => h1 σ' h2) (fun _ _ σ' ⟨h1, h2⟩ => h1 σ' h2)
      (Executable.wpEnv_of_wp
        (Q := fun s' => ∀ σ', SharedEnv.FenceMonoX.le σ σ' → cenv.wpEnv env p (Q ()) E s' σ')
        (E := fun a s' => ∀ σ', SharedEnv.FenceMonoX.le σ σ' → E a s' σ')
        (SharedEnv.FenceMonoX.fenceInv σ) h σ (SharedEnv.FenceMonoX.refl σ))

end Specs

end Kraken.Promising.X64.EnvG
