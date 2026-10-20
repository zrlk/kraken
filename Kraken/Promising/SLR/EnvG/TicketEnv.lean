/-
**Layer L, part 2: the ticket environment** `EnvGTD`.
ISA-neutral. Additive: `EnvGT` (`EnvG/TakeEnv.lean`) is unchanged.

`EnvGTD I A tid pl D` is `EnvGT I A tid pl` (loads take) for a program with
the ticket dispenser `D` (`SLR/LoadClaim.lean`) whose only access to the
ticket counter `D.x` is one `ldadda`-like RMW per thread:

- loads: not of `D.x`;
- stores: `StoreOk`, not to `D.x`;
- RMWs: `RmwOk`, on `D.x` only, of a never-failing operation that adds one
  to every value below `D.N` (`TicketOp`), not of release kind, and only
  while the env's `coh D.x` is `0` (the thread has not touched `D.x` yet:
  one ticket per thread);
- the RMW step (`RmwOutTD`) is `RmwOut` followed by the **hand-out**: the
  value read is below `D.N` and the thread's resource gains the token
  `tok D.o (D.tk old)` (`Dispenser.handGhost` moves it out of the
  dispenser slot; the link, `EnvG/TicketLink.lean`, proves the bound from
  the counting extension `TX D`, `SLR/TicketX.lean`).

Facts: `step_loadFactsTD` (`LoadFactsT`), `step_storeFactsTD`,
`step_fenceFactsTD` as for `EnvGT`; `step_rmwFactsTD` (`RmwFactsTD`:
`RmwFacts` of the RMW before the hand-out, the bound, the token).
-/
import Kraken.Promising.SLR.EnvG.TakeEnv
import Kraken.Promising.SLR.TicketX
import Kraken.Promising.SLR.EnvG.VCGenCommon

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **The ticket operation**: never fails, and adds one to every value below
`N` (no wraparound there). -/
def TicketOp (N : Nat) (op : Val → Option Val) : Prop :=
  (∀ old, op old ≠ none) ∧ ∀ old new, old.toNat < N → op old = some new → new.toNat = old.toNat + 1

/-- **An RMW's permission in the ticket environment**: `RmwOk`, on the
ticket counter, a ticket operation, not a release, and the thread has not
accessed the counter (`coh D.x = 0`). -/
def RmwOkTD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) : Prop :=
  RmwOk A tid pl σ k l op ∧ l = D.x ∧ TicketOp D.N op ∧ ¬ effRelRmw A k ∧ σ.vs.getCoh D.x = 0

/-- **An RMW outcome in the ticket environment**: an `RmwOut` outcome `σ₁`
whose value read is below `D.N`, then the hand-out of `tk old`. -/
def RmwOutTD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ σ' : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (old : Val) : Prop :=
  ∃ σ₁, RmwOut A tid pl σ σ₁ k l op old ∧ old.toNat < D.N ∧ σ' = { σ₁ with r := σ₁.r.op (tok D.o (D.tk old.toNat)) }

/-- **What an RMW exposes in the ticket environment.** -/
def RmwFactsTD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ σ' : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (old : Val) : Prop :=
  ∃ σ₁, RmwFacts A tid pl σ σ₁ k l op old ∧ old.toNat < D.N ∧
    σ' = { σ₁ with r := σ₁.r.op (tok D.o (D.tk old.toNat)) }

/-- **The ticket environment** of thread `tid` under the plan `pl`, for the
dispenser `D`. -/
def _root_.Kraken.Promising.SLR.EnvGTD (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) : SharedEnv where
  State := State I
  ok a σ := match a with
    | .load _ _ addr n => (⟨addr, n⟩ : Loc) ≠ D.x
    | .fence _ => True
    | .store k xcl addr n v => StoreOk A tid pl σ k xcl ⟨addr, n⟩ v ∧ (⟨addr, n⟩ : Loc) ≠ D.x
    | .rmw k addr n op => RmwOkTD A tid pl D σ k ⟨addr, n⟩ op
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOutTD A tid pl D σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

section Simp

variable {A : Arch} {tid : Nat} {pl : Plan} {D : Dispenser} {σ σ' : State I}

@[simp] theorem envGTD_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} :
    (EnvGTD I A tid pl D).ok (.load k xcl addr n) σ ↔ (⟨addr, n⟩ : Loc) ≠ D.x := Iff.rfl

@[simp] theorem envGTD_ok_fence {k : FenceKind} : (EnvGTD I A tid pl D).ok (.fence k) σ := trivial

@[simp] theorem envGTD_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} :
    (EnvGTD I A tid pl D).ok (.store k xcl addr n v) σ ↔
      StoreOk A tid pl σ k xcl ⟨addr, n⟩ v ∧ (⟨addr, n⟩ : Loc) ≠ D.x := Iff.rfl

@[simp] theorem envGTD_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} :
    (EnvGTD I A tid pl D).ok (.rmw k addr n op) σ ↔ RmwOkTD A tid pl D σ k ⟨addr, n⟩ op := Iff.rfl

theorem envGTD_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} :
    (EnvGTD I A tid pl D).step (.load k xcl addr n) σ v σ' = LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

theorem envGTD_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} :
    (EnvGTD I A tid pl D).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

theorem envGTD_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} :
    (EnvGTD I A tid pl D).step (.rmw k addr n op) σ old σ' = RmwOutTD A tid pl D σ σ' k ⟨addr, n⟩ op old := rfl

theorem envGTD_step_fence {k : FenceKind} {u : Unit} :
    (EnvGTD I A tid pl D).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-! ## Facts -/

/-- **What a load exposes** (with the take). -/
theorem step_loadFactsTD {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val}
    (h : (EnvGTD I A tid pl D).step (.load k xcl addr n) σ v σ') : LoadFactsT A tid σ σ' k ⟨addr, n⟩ v :=
  loadOutT_facts h

/-- **What a store exposes.** -/
theorem step_storeFactsTD {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (h : (EnvGTD I A tid pl D).step (.store k xcl addr n v) σ b σ') : StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

/-- **What an RMW exposes**: the RMW's facts before the hand-out, the bound,
the token. -/
theorem step_rmwFactsTD {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    (h : (EnvGTD I A tid pl D).step (.rmw k addr n op) σ old σ') : RmwFactsTD A tid pl D σ σ' k ⟨addr, n⟩ op old := by
  obtain ⟨σ₁, h1, h2, h3⟩ := h
  exact ⟨σ₁, rmwOut_facts h1, h2, h3⟩

/-- **What a fence exposes.** -/
theorem step_fenceFactsTD {k : FenceKind} {u : Unit} (h : (EnvGTD I A tid pl D).step (.fence k) σ u σ') :
    FenceFacts σ σ' k :=
  h

end Simp

/-! ## `EnvGTD`: fences and `simp` for `vcgen`

Moved from `EnvG/TicketLockVC.lean` (as `EnvG/TakeVCGenCommon.lean`
for `EnvGT`); the names stay in `TicketLock`. -/

namespace TicketLock

instance (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) : (EnvGTD I A tid pl D).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLe A tid pl⟩

@[simp] theorem fenceMono_le_envGTD (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) :
    (SharedEnv.FenceMono.le (env := EnvGTD I A tid pl D)) = FenceLe := rfl

@[simp] theorem envGTD_step_load' (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ σ' : (EnvGTD I A tid pl D).State)
    (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGTD I A tid pl D).step (.load k xcl addr n) σ v σ' = LoadOutT A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGTD_step_store' (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser)
    (σ σ' : (EnvGTD I A tid pl D).State) (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (EnvGTD I A tid pl D).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envGTD_step_rmw' (A : Arch) (tid : Nat) (pl : Plan) (D : Dispenser) (σ σ' : (EnvGTD I A tid pl D).State)
    (k : RmwKind) (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val) :
    (EnvGTD I A tid pl D).step (.rmw k addr n op) σ old σ' = RmwOutTD A tid pl D σ σ' k ⟨addr, n⟩ op old := rfl

end TicketLock

end Kraken.Promising.SLR.EnvG
