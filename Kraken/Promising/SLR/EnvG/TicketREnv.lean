/-
**Item 1, part 1: the ticket environment with
a release-kind ticket RMW** `EnvGTDR`. ISA-neutral. Additive: `EnvGTD`
(`EnvG/TicketEnv.lean`) is unchanged.

`EnvGTDR I A tid pl D` is `EnvGTD I A tid pl D` with one change in the RMW
permission (`RmwOkTDR`): the ticket RMW on `D.x` may be of **any kind**
(`ldaddal`, x64 `lock xadd`), provided the plan never makes a write to `D.x`
a release (`∀ v, pl.rel D.x v = false`: `next` stays pure,
so the RMW never forwards what it claims). Everything else (`ok` of loads,
stores and fences, every `step`) is `EnvGTD`'s, verbatim, so the `EnvGTD`
facts and the ISA-neutral VCs of `EnvG/TicketLockVC.lean` for loads and
stores apply to `EnvGTDR` definitionally.

- `RmwOkTDR`, `RmwOkTD.toR` (a non-release ticket RMW of a plan with pure
  `D.x` is permitted here too);
- `EnvGTDR`, its `simp` lemmas and facts (`step_*FactsTDR`);
- `FenceMono` and the `envGTDR_step_*'` simp set for `vcgen`
  (namespace `TicketLock`, as `EnvG/TicketEnv.lean`).
-/
import Kraken.Promising.SLR.EnvG.TicketEnv

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **An RMW's permission in the ticket environment with release-kind
RMWs**: `RmwOk`, on the ticket counter, a ticket operation, the plan never
releases at the counter, and the thread has not accessed the counter
(`coh D.x = 0`). `RmwOkTD` without `¬ effRelRmw A k`. -/
def RmwOkTDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) : Prop :=
  RmwOk A tid pl σ k l op ∧ l = D.x ∧ TicketOp D.N op ∧ (∀ v, pl.rel D.x v = false) ∧ σ.vs.getCoh D.x = 0

/-- A permitted ticket RMW of `EnvGTD` is permitted in `EnvGTDR` when the
plan never releases at the counter. -/
theorem RmwOkTD.toR {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {σ : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} (h : RmwOkTD A tid pl D σ k l op) (hrel : ∀ v, pl.rel D.x v = false) :
    RmwOkTDR A tid pl D σ k l op :=
  ⟨h.1, h.2.1, h.2.2.1, hrel, h.2.2.2.2⟩

/-- **The ticket environment with release-kind ticket RMWs** of thread
`tid` under the plan `pl`, for the dispenser `D` (`EnvGTD` with `RmwOkTDR`). -/
def _root_.Kraken.Promising.SLR.EnvGTDR (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) :
    SharedEnv where
  State := State I
  ok a σ := match a with
    | .load _ _ addr n => (⟨addr, n⟩ : Loc) ≠ D.x
    | .fence _ => True
    | .store k xcl addr n v => StoreOk A tid pl σ k xcl ⟨addr, n⟩ v ∧ (⟨addr, n⟩ : Loc) ≠ D.x
    | .rmw k addr n op => RmwOkTDR A tid pl D σ k ⟨addr, n⟩ op
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOutTD A tid pl D σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

section Simp

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {σ σ' : State I}

@[simp] theorem envGTDR_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} :
    (EnvGTDR I A tid pl D).ok (.load k xcl addr n) σ ↔ (⟨addr, n⟩ : Loc) ≠ D.x := Iff.rfl

@[simp] theorem envGTDR_ok_fence {k : FenceKind} : (EnvGTDR I A tid pl D).ok (.fence k) σ := trivial

@[simp] theorem envGTDR_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} :
    (EnvGTDR I A tid pl D).ok (.store k xcl addr n v) σ ↔
      StoreOk A tid pl σ k xcl ⟨addr, n⟩ v ∧ (⟨addr, n⟩ : Loc) ≠ D.x := Iff.rfl

@[simp] theorem envGTDR_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} :
    (EnvGTDR I A tid pl D).ok (.rmw k addr n op) σ ↔ RmwOkTDR A tid pl D σ k ⟨addr, n⟩ op := Iff.rfl

theorem envGTDR_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} :
    (EnvGTDR I A tid pl D).step (.load k xcl addr n) σ v σ' = LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

theorem envGTDR_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} :
    (EnvGTDR I A tid pl D).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

theorem envGTDR_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} :
    (EnvGTDR I A tid pl D).step (.rmw k addr n op) σ old σ' = RmwOutTD A tid pl D σ σ' k ⟨addr, n⟩ op old := rfl

theorem envGTDR_step_fence {k : FenceKind} {u : Unit} :
    (EnvGTDR I A tid pl D).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-- `EnvGTDR` and `EnvGTD` have the same steps. -/
theorem envGTDR_step_eq {a : SharedAccess} {ret : a.Ret} :
    (EnvGTDR I A tid pl D).step a σ ret σ' = (EnvGTD I A tid pl D).step a σ ret σ' := by
  cases a <;> rfl

/-! ## Facts -/

/-- **What a load exposes** (with the take). -/
theorem step_loadFactsTDR {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val}
    (h : (EnvGTDR I A tid pl D).step (.load k xcl addr n) σ v σ') : LoadFactsT A tid σ σ' k ⟨addr, n⟩ v :=
  loadOutT_facts h

/-- **What a store exposes.** -/
theorem step_storeFactsTDR {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (h : (EnvGTDR I A tid pl D).step (.store k xcl addr n v) σ b σ') : StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

/-- **What an RMW exposes**: the RMW's facts before the hand-out, the bound,
the token. -/
theorem step_rmwFactsTDR {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    (h : (EnvGTDR I A tid pl D).step (.rmw k addr n op) σ old σ') :
    RmwFactsTD A tid pl D σ σ' k ⟨addr, n⟩ op old :=
  step_rmwFactsTD (I := I) h

/-- **What a fence exposes.** -/
theorem step_fenceFactsTDR {k : FenceKind} {u : Unit} (h : (EnvGTDR I A tid pl D).step (.fence k) σ u σ') :
    FenceFacts σ σ' k :=
  h

end Simp

/-! ## `EnvGTDR`: fences and `simp` for `vcgen` -/

namespace TicketLock

instance (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) : (EnvGTDR I A tid pl D).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLe A tid pl⟩

@[simp] theorem fenceMono_le_envGTDR (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) :
    (SharedEnv.FenceMono.le (env := EnvGTDR I A tid pl D)) = FenceLe := rfl

@[simp] theorem envGTDR_step_load' (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser)
    (σ σ' : (EnvGTDR I A tid pl D).State) (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGTDR I A tid pl D).step (.load k xcl addr n) σ v σ' = LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGTDR_step_store' (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser)
    (σ σ' : (EnvGTDR I A tid pl D).State) (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val)
    (b : Bool) :
    (EnvGTDR I A tid pl D).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envGTDR_step_rmw' (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser)
    (σ σ' : (EnvGTDR I A tid pl D).State) (k : RmwKind) (addr : BitVec 64) (n : Nat) (op : Val → Option Val)
    (old : Val) :
    (EnvGTDR I A tid pl D).step (.rmw k addr n op) σ old σ' = RmwOutTD A tid pl D σ σ' k ⟨addr, n⟩ op old := rfl

end TicketLock

end Kraken.Promising.SLR.EnvG
