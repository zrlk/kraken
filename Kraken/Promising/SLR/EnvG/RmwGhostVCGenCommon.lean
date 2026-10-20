/-
**`vcgen` over `EnvGC`/`EnvGTC`, the ISA-neutral half**: the `@[simp]` `ok`/`step` lemmas of `EnvGC` and `EnvGTC`, the
step facts `step_loadFactsTC`/`step_storeFactsTC`/`step_rmwFactsTC`,
`claimSlotsC_armv8_rel`, and the `SharedEnv.FenceMono` instances
(`fenceMono_le_envGC`/`_envGTC`).

The x64 copies in `EnvG/X64RmwGhostVCGen.lean` (`envGC_*X`, `envGTCI_*X`,
`step_*FactsTCX`) are aliases of these, with their original statements.

This file imports no ISA syntax.
-/
import Kraken.Promising.SLR.EnvG.RmwGhostTakeCore
import Kraken.Promising.SLR.EnvG.TakeVCGenCommon
import Kraken.Promising.SLR.EnvG.TakeFacts

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## `ok` and `step` of `EnvGC` -/

@[simp] theorem envGC_ok_load_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGC I A tid pl).State) (k : LoadKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) : (EnvGC I A tid pl).ok (.load k xcl addr n) σ := trivial

@[simp] theorem envGC_ok_fence_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGC I A tid pl).State) (k : FenceKind) :
    (EnvGC I A tid pl).ok (.fence k) σ := trivial

@[simp] theorem envGC_ok_store_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGC I A tid pl).State) (k : StoreKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGC I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGC_ok_rmw_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGC I A tid pl).State) (k : RmwKind)
    (addr : BitVec 64) (n : Nat) (op : Val → Option Val) :
    (EnvGC I A tid pl).ok (.rmw k addr n op) σ = RmwOkC A tid pl σ k ⟨addr, n⟩ op := rfl

@[simp] theorem envGC_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGC I A tid pl).State) (k : LoadKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGC I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOut A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGC_step_store (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGC I A tid pl).State) (k : StoreKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (EnvGC I A tid pl).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envGC_step_rmw (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGC I A tid pl).State) (k : RmwKind)
    (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val) :
    (EnvGC I A tid pl).step (.rmw k addr n op) σ old σ' = RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old := rfl

@[simp] theorem envGC_step_fence (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGC I A tid pl).State) (k : FenceKind)
    (u : Unit) : (EnvGC I A tid pl).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-! ## `ok` and `step` of `EnvGTC` -/

@[simp] theorem envGTC_ok_load_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTC I A tid pl).State) (k : LoadKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) : (EnvGTC I A tid pl).ok (.load k xcl addr n) σ := trivial

@[simp] theorem envGTC_ok_fence_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTC I A tid pl).State)
    (k : FenceKind) : (EnvGTC I A tid pl).ok (.fence k) σ := trivial

@[simp] theorem envGTC_ok_store_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTC I A tid pl).State)
    (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGTC I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGTC_ok_rmw_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTC I A tid pl).State) (k : RmwKind)
    (addr : BitVec 64) (n : Nat) (op : Val → Option Val) :
    (EnvGTC I A tid pl).ok (.rmw k addr n op) σ = RmwOkC A tid pl σ k ⟨addr, n⟩ op := rfl

@[simp] theorem envGTC_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTC I A tid pl).State)
    (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGTC I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGTC_step_store (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTC I A tid pl).State)
    (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (EnvGTC I A tid pl).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envGTC_step_rmw (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTC I A tid pl).State) (k : RmwKind)
    (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val) :
    (EnvGTC I A tid pl).step (.rmw k addr n op) σ old σ' = RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old := rfl

@[simp] theorem envGTC_step_fence (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTC I A tid pl).State)
    (k : FenceKind) (u : Unit) : (EnvGTC I A tid pl).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-! ## Step facts of `EnvGTC` -/

/-- **What a load of `EnvGTC` exposes** (`EnvGT`'s, `loadOutT_facts`). -/
theorem step_loadFactsTC {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} (h : (EnvGTC I A tid pl).step (.load k xcl addr n) σ v σ') :
    LoadFactsT A tid σ σ' k ⟨addr, n⟩ v :=
  loadOutT_facts h

/-- **What a store of `EnvGTC` exposes** (`EnvG`'s, `storeOut_facts`). -/
theorem step_storeFactsTC {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (h : (EnvGTC I A tid pl).step (.store k xcl addr n v) σ b σ') : StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

/-- **What an RMW of `EnvGTC` exposes** (`EnvGC`'s, `rmwOutC_facts`). -/
theorem step_rmwFactsTC {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} (h : (EnvGTC I A tid pl).step (.rmw k addr n op) σ old σ') :
    RmwFactsC A tid pl σ σ' k ⟨addr, n⟩ op old :=
  rmwOutC_facts h

/-- On armv8 a release-only RMW (`swpl`, `ldaddl`) claims nothing. -/
@[simp] theorem claimSlotsC_armv8_rel (vs : Views) (g : Ghost) (l : Loc) (tr : Time) :
    claimSlotsC Arch.armv8 .rel vs g l tr = [] :=
  claimSlotsC_of_not claimOk_rel_false

/-! ## Fences -/

/-- Every `EnvGC` fence is permitted and stays in `FenceLe σ` (its fences
are `EnvG`'s). -/
theorem fenceInv_fenceLeC (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvGC I A tid pl).FenceInv (FenceLe σ) :=
  fenceInv_fenceLe A tid pl σ

/-- Every `EnvGTC` fence is permitted and stays in `FenceLe σ`. -/
theorem fenceInv_fenceLeTC (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvGTC I A tid pl).FenceInv (FenceLe σ) :=
  fenceInv_fenceLe A tid pl σ

instance (A : Arch) (tid : Nat) (pl : Plan) : (EnvGC I A tid pl).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLeC A tid pl⟩

instance (A : Arch) (tid : Nat) (pl : Plan) : (EnvGTC I A tid pl).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLeTC A tid pl⟩

@[simp] theorem fenceMono_le_envGC (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMono.le (env := EnvGC I A tid pl)) = FenceLe := rfl

@[simp] theorem fenceMono_le_envGTC (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMono.le (env := EnvGTC I A tid pl)) = FenceLe := rfl

end Kraken.Promising.SLR.EnvG
