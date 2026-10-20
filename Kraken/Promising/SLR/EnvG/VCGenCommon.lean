/-
**`vcgen` over `EnvG`, the ISA-neutral half**.

- `FenceLe σ σ'`: `σ'` is `σ` after fences (only `vrNew`/`vwNew` grow and the
  fence bits are only set). Reflexive, transitive, stable under every `EnvG`
  fence (`fenceInv_fenceLe`), with the view projections `FenceLe.vwOld`, ….
- `SharedEnv.FenceMono env` (class): fences move the state up a reflexive,
  fence-stable relation. Instances: `EnvG` (`le = FenceLe`) and
  `SharedEnv.counted env`.

The generic `vcgen` rule built on the class is ISA-specific (it is stated over
the ISA's `Program`/`Directive`): `envMono_lift_spec` (`EnvG/A64VCGen.lean`)
and `envMonoX_lift_spec` (`EnvG/X64VCGen.lean`). The x64 names
`X64.EnvG.FenceLe`, `SharedEnv.FenceMonoX`, … are aliases of the ones here,
with their original statements (`EnvG/X64VCGen.lean`, via `EnvG/Alias.lean`).

This file imports no ISA syntax.
-/
import Kraken.SharedEnvCounted
import Kraken.Promising.SLR.EnvG.Env

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## The fence order -/

/-- **`σ'` is `σ` after fences** (any number, any kinds). -/
structure FenceLe (σ σ' : State I) : Prop where
  snap : σ'.snap = σ.snap
  r : σ'.r = σ.r
  g : σ'.g = σ.g
  cl : σ'.cl = σ.cl
  seen : σ'.seen = σ.seen
  vs : σ'.vs = { σ.vs with vrNew := σ'.vs.vrNew, vwNew := σ'.vs.vwNew }
  vrNew : σ.vs.vrNew ≤ σ'.vs.vrNew
  vwNew : σ.vs.vwNew ≤ σ'.vs.vwNew
  fencedR : σ.fencedR = true → σ'.fencedR = true
  fencedW : σ.fencedW = true → σ'.fencedW = true

namespace FenceLe

theorem refl (σ : State I) : FenceLe σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, id, id⟩

theorem trans {σ₁ σ₂ σ₃ : State I} (h₁ : FenceLe σ₁ σ₂) (h₂ : FenceLe σ₂ σ₃) : FenceLe σ₁ σ₃ :=
  ⟨h₂.snap.trans h₁.snap, h₂.r.trans h₁.r, h₂.g.trans h₁.g, h₂.cl.trans h₁.cl, h₂.seen.trans h₁.seen,
    by rw [h₂.vs, h₁.vs], Nat.le_trans h₁.vrNew h₂.vrNew, Nat.le_trans h₁.vwNew h₂.vwNew,
    fun h => h₂.fencedR (h₁.fencedR h), fun h => h₂.fencedW (h₁.fencedW h)⟩

/-! Projections of the views a program proof reads. -/

theorem vwOld {σ σ' : State I} (h : FenceLe σ σ') : σ'.vs.vwOld = σ.vs.vwOld := by rw [h.vs]
theorem vrOld {σ σ' : State I} (h : FenceLe σ σ') : σ'.vs.vrOld = σ.vs.vrOld := by rw [h.vs]
theorem vRel {σ σ' : State I} (h : FenceLe σ σ') : σ'.vs.vRel = σ.vs.vRel := by rw [h.vs]
theorem vCAP {σ σ' : State I} (h : FenceLe σ σ') : σ'.vs.vCAP = σ.vs.vCAP := by rw [h.vs]
theorem getCoh {σ σ' : State I} (h : FenceLe σ σ') (l : Loc) : σ'.vs.getCoh l = σ.vs.getCoh l := by
  rw [h.vs]; rfl
theorem getFwd {σ σ' : State I} (h : FenceLe σ σ') (l : Loc) : σ'.vs.getFwd l = σ.vs.getFwd l := by
  rw [h.vs]; rfl

end FenceLe

/-- Every `EnvG` fence is permitted and stays in `FenceLe σ`. -/
theorem fenceInv_fenceLe (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvG I A tid pl).FenceInv (FenceLe σ) := by
  intro k σ₁ h₁
  refine ⟨trivial, fun σ₂ (h₂ : FenceOut σ₁ σ₂ k) => h₁.trans ?_⟩
  subst h₂
  have hv := vle_fenceViews σ₁.vs k
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, hv.vrNew, hv.vwNew, fun h => by simp [h], fun h => by simp [h]⟩
  cases k <;> rfl

/-! ## The generic rule for monotone-fence environments -/

/-- **Fences move the state up a preorder** (`Skips` is the case `le = Eq`).
The class argument of `envMono_lift_spec`. -/
class _root_.Kraken.SharedEnv.FenceMono (env : SharedEnv) where
  le : env.State → env.State → Prop
  refl : ∀ σ, le σ σ
  fenceInv : ∀ σ, env.FenceInv (le σ)

instance (A : Arch) (tid : Nat) (pl : Plan) : (EnvG I A tid pl).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLe A tid pl⟩

@[simp] theorem fenceMono_le_envG (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMono.le (env := EnvG I A tid pl)) = FenceLe := rfl

/-- The ghost access counter (`SharedEnv.counted`, needed by the back edges
of `cfgEnv_partial`) keeps the fence order: fences do not tick. -/
instance (env : SharedEnv) [env.FenceMono] : (SharedEnv.counted env).FenceMono where
  le g g' := SharedEnv.FenceMono.le g.1 g'.1 ∧ g'.2 = g.2
  refl g := ⟨SharedEnv.FenceMono.refl g.1, rfl⟩
  fenceInv g k g₁ h₁ :=
    ⟨(SharedEnv.FenceMono.fenceInv g.1 k g₁.1 h₁.1).1, fun g₂ ⟨hs, hn⟩ =>
      ⟨(SharedEnv.FenceMono.fenceInv g.1 k g₁.1 h₁.1).2 g₂.1 hs, by rw [hn, h₁.2]; rfl⟩⟩

@[simp] theorem fenceMono_le_counted (env : SharedEnv) [env.FenceMono] (g g' : (SharedEnv.counted env).State) :
    SharedEnv.FenceMono.le g g' ↔ SharedEnv.FenceMono.le g.1 g'.1 ∧ g'.2 = g.2 := Iff.rfl

end Kraken.Promising.SLR.EnvG
