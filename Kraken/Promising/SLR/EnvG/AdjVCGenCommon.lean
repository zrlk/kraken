/-
**`vcgen` support for the adjacency environment `EnvGCAdj`**
(`EnvG/AdjCore.lean`), ISA-neutral. These moved here unchanged (same
names and statements) from `EnvG/Treiber2VC.lean`, where the Treiber node proof stated
them as copies of `EnvG/RmwGhostVCGenCommon.lean`'s `EnvGC` lemmas, so that
every `EnvGCAdj` program (Treiber2, the MS queue) imports them without a
Treiber file.

- `@[simp]` `ok`/`step` lemmas at the env-state type: `envGCAdj_ok_load_st`,
  `envGCAdj_ok_fence_st`, `envGCAdj_ok_store_st`, `envGCAdj_ok_rmw_st`,
  `envGCAdj_step_load`, `envGCAdj_step_store`, `envGCAdj_step_rmw`,
  `envGCAdj_step_fence`;
- **`SharedEnv.FenceMono`** with `le = FenceLe` (its fences are `EnvG`'s:
  `fenceInv_fenceLeCAdj`), and `fenceMono_le_envGCAdj` (`@[simp]`).
-/
import Kraken.Promising.SLR.EnvG.AdjCore
import Kraken.Promising.SLR.EnvG.RmwGhostVCGenCommon

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

@[simp] theorem envGCAdj_ok_load_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGCAdj I A tid pl).State)
    (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) : (EnvGCAdj I A tid pl).ok (.load k xcl addr n) σ :=
  trivial

@[simp] theorem envGCAdj_ok_fence_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGCAdj I A tid pl).State)
    (k : FenceKind) : (EnvGCAdj I A tid pl).ok (.fence k) σ := trivial

@[simp] theorem envGCAdj_ok_store_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGCAdj I A tid pl).State)
    (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGCAdj I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGCAdj_ok_rmw_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGCAdj I A tid pl).State)
    (k : RmwKind) (addr : BitVec 64) (n : Nat) (op : Val → Option Val) :
    (EnvGCAdj I A tid pl).ok (.rmw k addr n op) σ = RmwOkCAdj A tid pl σ k ⟨addr, n⟩ op := rfl

@[simp] theorem envGCAdj_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGCAdj I A tid pl).State)
    (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGCAdj I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOut A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGCAdj_step_store (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGCAdj I A tid pl).State)
    (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (EnvGCAdj I A tid pl).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envGCAdj_step_rmw (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGCAdj I A tid pl).State)
    (k : RmwKind) (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val) :
    (EnvGCAdj I A tid pl).step (.rmw k addr n op) σ old σ' = RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old := rfl

@[simp] theorem envGCAdj_step_fence (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGCAdj I A tid pl).State)
    (k : FenceKind) (u : Unit) : (EnvGCAdj I A tid pl).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-- Every `EnvGCAdj` fence is permitted and stays in `FenceLe σ`. -/
theorem fenceInv_fenceLeCAdj (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvGCAdj I A tid pl).FenceInv (FenceLe σ) :=
  fenceInv_fenceLe A tid pl σ

instance (A : Arch) (tid : Nat) (pl : Plan) : (EnvGCAdj I A tid pl).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLeCAdj A tid pl⟩

@[simp] theorem fenceMono_le_envGCAdj (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMono.le (env := EnvGCAdj I A tid pl)) = FenceLe := rfl

end Kraken.Promising.SLR.EnvG
