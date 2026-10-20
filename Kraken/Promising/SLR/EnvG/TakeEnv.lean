/-
**Part 3: the environment with taking loads**. ISA-neutral. Additive: `EnvG`
(`EnvG/Env.lean`) is unchanged.

`EnvGT I A tid pl` is `EnvG I A tid pl` except that its load step is
`LoadOutT` (`EnvG/TakeFacts.lean`): a non-forwarded acquire load takes every
exposed slot of the message it reads for the acquire ids the thread holds.
Its state, permissions (`ok`), and store, RMW and fence steps are `EnvG`'s,
definitionally (`envGT_ok`, `envGT_step_store` etc.), so every store/RMW/fence
lemma about `EnvG` applies verbatim.

- `step_loadFactsT`: every load outcome satisfies `LoadFactsT`;
  `step_storeFactsT`, `step_rmwFactsT`, `step_fenceFactsT`: as for `EnvG`.
- `envG_step_load_of_envGT`: a load outcome of `EnvGT` with nothing to take
  is one of `EnvG`.

Phase-1 limits: single-access trees; releases are stores; only
non-forwarded acquire loads take (no fence-node take).
-/
import Kraken.Promising.SLR.EnvG.TakeFacts

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **The whole-thread SLR environment with taking loads** of thread `tid`
under the plan `pl`. -/
def _root_.Kraken.Promising.SLR.EnvGT (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := (EnvG I A tid pl).ok a σ
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

theorem envGT_ok (A : Arch) (tid : Nat) (pl : Plan) (a : SharedAccess) (σ : State I) :
    (EnvGT I A tid pl).ok a σ = (EnvG I A tid pl).ok a σ := rfl

@[simp] theorem envGT_ok_load (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : LoadKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) : (EnvGT I A tid pl).ok (.load k xcl addr n) σ := trivial

@[simp] theorem envGT_ok_fence (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : FenceKind) :
    (EnvGT I A tid pl).ok (.fence k) σ := trivial

theorem envGT_step_store {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} :
    (EnvGT I A tid pl).step (.store k xcl addr n v) σ b σ' = (EnvG I A tid pl).step (.store k xcl addr n v) σ b σ' :=
  rfl

theorem envGT_step_rmw {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} :
    (EnvGT I A tid pl).step (.rmw k addr n op) σ old σ' = (EnvG I A tid pl).step (.rmw k addr n op) σ old σ' := rfl

theorem envGT_step_fence {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : FenceKind} {u : Unit} :
    (EnvGT I A tid pl).step (.fence k) σ u σ' = (EnvG I A tid pl).step (.fence k) σ u σ' := rfl

/-- **What a load exposes** (with the take). -/
theorem step_loadFactsT {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} (h : (EnvGT I A tid pl).step (.load k xcl addr n) σ v σ') :
    LoadFactsT A tid σ σ' k ⟨addr, n⟩ v :=
  loadOutT_facts h

theorem step_storeFactsT {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} (h : (EnvGT I A tid pl).step (.store k xcl addr n v) σ b σ') :
    StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

theorem step_rmwFactsT {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} (h : (EnvGT I A tid pl).step (.rmw k addr n op) σ old σ') :
    RmwFacts A tid pl σ σ' k ⟨addr, n⟩ op old :=
  rmwOut_facts h

theorem step_fenceFactsT {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : FenceKind} {u : Unit}
    (h : (EnvGT I A tid pl).step (.fence k) σ u σ') : FenceFacts σ σ' k :=
  h

/-- A load outcome of `EnvGT` with nothing to take is one of `EnvG`. -/
theorem envG_step_load_of_envGT {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val}
    (hn : ∀ ga tr, TakeCond A k σ.vs ⟨addr, n⟩ tr → takeAll ⟨addr, n⟩ tr σ.r ga = ⟨σ.r, ga, []⟩)
    (h : (EnvGT I A tid pl).step (.load k xcl addr n) σ v σ') : (EnvG I A tid pl).step (.load k xcl addr n) σ v σ' :=
  loadOut_of_loadOutT hn h

end Kraken.Promising.SLR.EnvG
