/-
**`vcgen` over `EnvGLRV`**: `EnvGLRV`'s fences are `EnvG`'s, so it has `EnvG`'s fence order
and `vcgen`'s rule for monotone-fence environments applies in `EnvGLRVX`.
`inc32_shared_spec` (`LRX64VCGen.lean`) is generic in the environment and is
reused.

- `fenceInv_fenceLe_LRV`, the instance `instFenceMonoXEnvGLRV`, `@[simp]`
  `fenceMonoX_le_envGLRV`, `envGLRV_ok_store`, `envGLRV_step_load`;
- `stepLRV_storeFacts`, `stepLRV_store_true`.
-/
import Kraken.Promising.SLR.EnvG.LRValX64
import Kraken.Promising.SLR.EnvG.LRX64VCGen

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- Every `EnvGLRV` fence is permitted and stays in `FenceLe σ`. -/
theorem fenceInv_fenceLe_LRV (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvGLRV I A tid pl).FenceInv (FenceLe σ) :=
  fenceInv_fenceLe A tid pl σ

instance instFenceMonoXEnvGLRV (A : Arch) (tid : Nat) (pl : Plan) : (EnvGLRV I A tid pl).FenceMonoX :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLe_LRV A tid pl⟩

@[simp] theorem fenceMonoX_le_envGLRV (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMonoX.le (env := EnvGLRV I A tid pl)) = FenceLe := rfl

@[simp] theorem envGLRV_ok_store (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : StoreKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGLRV I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGLRV_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : LoadKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGLRV I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOutLRV A tid pl σ σ' k xcl ⟨addr, n⟩ v := rfl

/-- **What a store of `EnvGLRV` exposes** (`EnvG`'s). -/
theorem stepLRV_storeFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (h : (EnvGLRV I A tid pl).step (.store k xcl addr n v) σ b σ') : StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

end Kraken.Promising.SLR.EnvG
