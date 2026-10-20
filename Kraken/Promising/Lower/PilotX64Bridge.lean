/-
**The value-restricted x64 environments and
the open bridge `EnvGValsBridgeX`.** x64; program
independent.

The x64 counterpart of the stack-frame pilot's `Lower/Pilot2Bridge.lean`
(AArch64). `valsEnv` and its simp lemmas are a copy
of the stack-frame pilot's (that file imports AArch64 and cannot be co-imported).

## Why x64 needs more than AArch64

`pop` loads the link of the node it read from `top` (`movq (%rax), %rcx`).
With the call stack in `dmem` that load is shared only if its address is off
`dmem`, which needs a value fact about `top` (the stack-frame pilot's finding). On x64 the
Theorem 1′ chain has two more consumers of the same fact:

1. **The layout.** The x64 link runs in `EnvGCAdjX … S = EnvGCAdj.within S`
   with `Split S dmem` (no byte of `S` mapped). The verbatim x64 Treiber
   proofs use `S = sAll` (every 8-byte location), and `Split sAll d` holds
   only for an empty `d`. With a stack, `S` must avoid the stack, so the
   `within` permission of the pointer load, `(y0, 8) ∈ S`, needs `y0`'s
   value. (No finite or infinite `S` avoids this: a `y0` straddling the
   stack's edge is unmapped as an 8-byte access and covers mapped bytes.)
2. **The purity pass.** `final_of_relPureSafelyQX_tsoF'` takes per-thread
   all-release specifications in `(relPureQ Arch.tso ⊥).within S`, with the
   same `within S` permission at the same load. AArch64's purity
   specifications (`RelPureSpec`) have no layout and are unaffected.

So the x64 bridge restricts the purity judgments' answers too.

## What

- `valsEnv E G`, `EnvGCAdjXV`, `QX64CAdjV`: the stack-frame pilot's value-restricted
  ownership environment and invariant, at x64's `EnvGCAdjX … S`.
- `relInvX S G` (in `SLR/EnvG/X64EnvRefine.lean`, aliased here): the
  purity environment with `inv S G`'s permissions (every access a location
  of `S`, every write in `G`) and answers in `G`; one
  judgment in it is both a purity specification under the value invariant
  and (`Safely.relInvX_inv`) a `ThreadSpec` of `inv S G`, whose
  `inv_reachable` (`InvLinkX64`) discharges the bridge's `hvals`.
  `RelPureSpecQX.HoldsV` is `RelPureSpecQX.Holds` with that judgment.
- `Safely.refine` (in `SLR/EnvG/X64EnvRefine.lean`, aliased here): a
  judgment transfers along an environment refinement (more permissions
  needed, fewer outcomes); `Effects.AllEnv.refine`.
- **`EnvGValsBridgeX S G`** (open) and its instance `envGValsBridgeX_true` at
  `G = ⊤`.
-/
import Kraken.Promising.SLR.EnvG.X64AdjLink
import Kraken.Promising.SLR.EnvG.X64EnvRefine
import Kraken.Promising.SLR.EnvG.RelPureEnvX64F
import Kraken.Promising.SLR.EnvG.X64VCGen
import Kraken.Promising.InvLinkX64

namespace Kraken.Promising.Lower.PilotX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64
open Kraken.Promising.X64.EnvG

/-! ## Environment refinement -/

/-! `Effects.AllEnv.refine`, `instrStepEnv_refine` and `Safely.refine` are in
`SLR/EnvG/X64EnvRefine.lean` (namespace `X64.EnvG`); the names here are aliases. -/
export Kraken.Promising.X64.EnvG (Effects.AllEnv.refine instrStepEnv_refine Safely.refine)

/-! ## The value-restricted ownership environment -/

/-- The value condition of an access's answer: a load's value satisfies `G`
at its location; other answers are unconstrained (the stack-frame pilot's `LoadVal`). -/
def LoadVal (G : Loc → Val → Prop) : (a : SharedAccess) → a.Ret → Prop
  | .load _ _ addr n, v => G ⟨addr, n⟩ v
  | _, _ => True

/-- **`E` with value-restricted load answers** (the stack-frame pilot's `valsEnv`): the same
permissions, and only the outcomes whose load values satisfy `G`. -/
def valsEnv (E : SharedEnv) (G : Loc → Val → Prop) : SharedEnv where
  State := E.State
  ok := E.ok
  step a σ r σ' := E.step a σ r σ' ∧ LoadVal G a r

section Simp

variable (E : SharedEnv) (G : Loc → Val → Prop) (σ σ' : (valsEnv E G).State)

@[simp] theorem valsEnv_ok (a : SharedAccess) : (valsEnv E G).ok a σ = E.ok a σ := rfl

@[simp] theorem valsEnv_step_load (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (valsEnv E G).step (.load k xcl addr n) σ v σ' = (E.step (.load k xcl addr n) σ v σ' ∧ G ⟨addr, n⟩ v) := rfl

@[simp] theorem valsEnv_step_store (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (valsEnv E G).step (.store k xcl addr n v) σ b σ' = (E.step (.store k xcl addr n v) σ b σ' ∧ True) := rfl

@[simp] theorem valsEnv_step_rmw (k : RmwKind) (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val) :
    (valsEnv E G).step (.rmw k addr n op) σ old σ' = (E.step (.rmw k addr n op) σ old σ' ∧ True) := rfl

@[simp] theorem valsEnv_step_fence (k : FenceKind) (u : Unit) :
    (valsEnv E G).step (.fence k) σ u σ' = (E.step (.fence k) σ u σ' ∧ True) := rfl

end Simp

/-- Fences are `E`'s. -/
instance (E : SharedEnv) [E.FenceMonoX] (G : Loc → Val → Prop) : (valsEnv E G).FenceMonoX where
  le := SharedEnv.FenceMonoX.le (env := E)
  refl := SharedEnv.FenceMonoX.refl (env := E)
  fenceInv σ k g hg :=
    ⟨(SharedEnv.FenceMonoX.fenceInv (env := E) σ k g hg).1,
      fun g' hs => (SharedEnv.FenceMonoX.fenceInv (env := E) σ k g hg).2 g' hs.1⟩

@[simp] theorem fenceMonoX_le_valsEnv (E : SharedEnv) [E.FenceMonoX] (G : Loc → Val → Prop) :
    (SharedEnv.FenceMonoX.le (env := valsEnv E G)) = SharedEnv.FenceMonoX.le (env := E) := rfl

/-- `valsEnv E G` refines `E` (same permissions, fewer outcomes). -/
theorem Safely.vals {E : SharedEnv} {G : Loc → Val → Prop} {e : Kraken.Executable Directive}
    {post : MachineState × E.State → Prop} {x : MachineState} {g : E.State}
    (h : Safely (e.instrStepEnv E) post (x, g)) : Safely (e.instrStepEnv (valsEnv E G)) post (x, g) :=
  (Safely.refine (E₁ := E) (E₂ := valsEnv E G) id (fun _ _ h => h) (fun _ _ _ g₂ h => ⟨g₂, rfl, h.1⟩) h).mono
    fun _ ⟨_, h1, h2⟩ => by subst h1; exact h2

/-- `valsEnv E ⊤` has `E`'s outcomes. -/
theorem Safely.of_vals_top {E : SharedEnv} {e : Kraken.Executable Directive}
    {post : MachineState × E.State → Prop} {x : MachineState} {g : E.State}
    (h : Safely (e.instrStepEnv (valsEnv E fun _ _ => True)) post (x, g)) : Safely (e.instrStepEnv E) post (x, g) :=
  (Safely.refine (E₁ := valsEnv E fun _ _ => True) (E₂ := E) id (fun _ _ h => h)
    (fun a _ _ g₂ h => ⟨g₂, rfl, h, by cases a <;> trivial⟩) h).mono
    fun _ ⟨_, h1, h2⟩ => by subst h1; exact h2

/-- **`EnvGCAdjX` with value-restricted load answers.** -/
abbrev EnvGCAdjXV (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (G : Loc → Val → Prop) : SharedEnv :=
  valsEnv (EnvGCAdjX A tid pl S) G

/-- `QX64CAdj` with the `Safely` judgment of `EnvGCAdjXV`. -/
def QX64CAdjV (A : Arch) (tid : Nat) (pl : Plan) (S : SharedEnv.Layout) (G : Loc → Val → Prop)
    (e : Kraken.Executable Directive) (endPc : Int64) (post : MachineState × EStateX → Prop) (st : State)
    (σ : EStateX) : Prop :=
  st.exe = e ∧ st.decls = {} ∧ st.endPc = endPc ∧ Split S st.st.1.dmem ∧
    Safely (e.instrStepEnv (EnvGCAdjXV A tid pl S G)) post (st.st, σ)

/-! ## The value-restricted purity environment -/

/-! `relInvX`, its simp lemmas, `Safely.relInvX_inv`, `Safely.relInvX_top` and
`RelPureSpecQX.HoldsV` are in `SLR/EnvG/X64EnvRefine.lean` (namespace
`X64.EnvG`); the `PilotX` names here are aliases. -/
export Kraken.Promising.X64.EnvG (relInvX relInvX_ok relInvX_step_load relInvX_step_store relInvX_step_rmw
  Safely.relInvX_inv Safely.relInvX_top)

/-! ## The open bridge -/

/-- **The EnvG ↔ value-invariant bridge, x64 (open).** the stack-frame pilot's
`EnvGValsBridge` at x64: `CmpxPublic.final_of_relPureSafelyQX_tsoF'`
(`EnvG/RelPureEnvX64F.lean`, the x64 counterpart of
`final_of_relPureSafelyF`) with

- the per-thread `NPSafeF` premise, which `npSafeF_of_safelyEnvGFCAdjX`
  gives from a judgment in `EnvGCAdjX`, replaced by that rule's premises with
  the judgment in `EnvGCAdjXV Arch.tso tid pl S G`;
- the purity specifications' judgments (`RelPureSpecQX.Holds`, in
  `(relPureQ Arch.tso ⊥).within sp.S`) replaced by judgments in
  `relInvX sp.S G` (`RelPureSpecQX.HoldsV`);
- `hvals`: every configuration reachable from the start keeps `MemInv G`.

Differences from the stack-frame pilot's AArch64 statement: `Arch.tso` only (the x64
assembly is TSO's); no `NTFree` premise (on x64 the chain derives it from the
purity specifications); `∀ ts, ts ∉ g₀.pend` (the x64 assembly's form); the
layout `S` and `Le16 S` (the x64 link's `within S`); the purity judgments
value-restricted (see the module docstring, item 2).

**Why it is stated for the whole program**: as the stack-frame pilot's. `NPSafeF` and the
purity link quantify over environment extensions and certification runs that
may hold any value the plan's release predicates allow; only along actual
executions from the start does `hvals` restrict the answers to `G`.

**Why it is believed true** (sketch, as the stack-frame pilot's): relativise `NPSafeF`,
`theorem1FChain` and the purity link `promisePure_of_relWrites` to
configurations satisfying `MemInv G c.mem`; at such a configuration every
load answer and every RMW's old value the links build is a message of
`c.mem` or an initial value, hence in `G`, so the `EnvGCAdjX`/purity outcome
is an `EnvGCAdjXV`/`relInvX` outcome; `relInvX`'s permissions include
`relPureQ`'s and `within S`'s. At `G = ⊤` the statement is the existing chain
(`envGValsBridgeX_true`). -/
def EnvGValsBridgeX (S : SharedEnv.Layout) (G : Loc → Val → Prop) : Prop :=
  Le16 S →
  ∀ (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val)) (rF : Nat → Res) (g₀ : Ghost)
    (B : Config isa → Res → Ghost → Prop) (Φ : Config isa → Prop) (pl : Nat → Plan)
    (e : Nat → Kraken.Executable Directive) (endPc : Nat → Int64) (post : Nat → MachineState × EStateX → Prop),
    Erase rF g₀ (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g₀.pend) →
    ∀ (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False), (∀ tid s, states[tid]? = some s → (sp tid).HoldsV G s) →
    -- the value invariant of every reachable memory
    (∀ c, Reachable Arch.tso fuel (Config.init states initMem) c → MemInv G c.mem) →
    -- per thread: `npSafeF_of_safelyEnvGFCAdjX`'s premises, the judgment in `EnvGCAdjXV`
    (∀ tid, tid < states.length →
      Kraken.Executable.ValidLayout (e tid) ∧ (pl tid).Valid ∧ Phase1TreeFX (e tid) ∧
      (∀ y, post tid y → y.1.2 = endPc tid) ∧
      (∀ x R, x.1.2 = endPc tid → ¬ (e tid).instrStepEnv (EnvGCAdjXV Arch.tso tid (pl tid) S G) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post tid (t.st.st, σ) → t.prom = [] →
        EnvRel tid (pl tid) σ c t r g cl → cl → B c r g) ∧
      ∃ s, states[tid]? = some s ∧
        QX64CAdjV Arch.tso tid (pl tid) S G (e tid) (endPc tid) (post tid) s
          (σInitX (Config.init states initMem) (rF tid) g₀)) →
    ∀ c, Reachable Arch.tso fuel (Config.init states initMem) c → c.final = true →
    (∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) →
    Φ c

/-- **Satisfiability check: at `G = ⊤` the bridge holds**; it is
`final_of_relPureSafelyQX_tsoF'` with `npSafeF_of_safelyEnvGFCAdjX`
(`hvals` is trivial, `EnvGCAdjXV … ⊤` has `EnvGCAdjX`'s outcomes and
`relInvX S ⊤` judgments are purity judgments). -/
theorem envGValsBridgeX_true (S : SharedEnv.Layout) : EnvGValsBridgeX S fun _ _ => True := by
  intro hS fuel states initMem rF g₀ B Φ pl e endPc post hE hpend sp h0 _ hthr c hc hf hfin
  refine CmpxPublic.final_of_relPureSafelyQX_tsoF' hE hpend sp
    (fun tid s hs => ?_) ?_ hc hf hfin
  · obtain ⟨he, hend, hds, hsp, hsafe⟩ := h0 tid s hs
    exact ⟨he, hend, hds, hsp, Safely.relInvX_top hsafe⟩
  intro tid htid n m
  obtain ⟨hv, hpl, hshape, hpost, hstuck, hB, s, hs, he, hds, hend, hsp, hsafe⟩ := hthr tid htid
  haveI := hv
  exact npSafeF_of_safelyEnvGFCAdjX (e := e tid) (post := post tid) hpl hS hshape hpost
    (fun x R hx hR => hstuck x _ hx (instrStepEnv_refine (E₁ := EnvGCAdjX Arch.tso tid (pl tid) S)
      (E₂ := EnvGCAdjXV Arch.tso tid (pl tid) S fun _ _ => True) id (fun _ _ h => h)
      (fun _ _ _ g₂ h => ⟨g₂, rfl, h.1⟩) hR)) hB n m
    (invGFCAdjX_init hs (List.eq_nil_iff_forall_not_mem.mpr hpend) ⟨he, hds, hend, hsp, Safely.of_vals_top hsafe⟩)

end Kraken.Promising.Lower.PilotX
