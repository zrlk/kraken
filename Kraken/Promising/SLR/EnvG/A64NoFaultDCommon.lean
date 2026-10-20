/-
**No fault at the runner's declarations: the ISA-neutral part**. ISA-neutral
(imports neither `Syntax`).

The AArch64 route (`EnvG/A64NoFaultD.lean`) needs the ISA-neutral half of
the no-fault-at-declarations proofs' `EnvG/X64NoFaultD.lean`, which that file
keeps beside x64 code (it
imports `X64DeclsLink`, so an AArch64 file cannot import it). The statements
here are the no-fault-at-declarations proofs', restated for `EvTree.reresolve`
(the AArch64 declarations proofs' name for
`underDecls`) under unique names; each names its twin in its docstring.
`Decls.AgreesAt` itself lives in the x64 file `X64VecDecls`.

| here | twin |
|---|---|
| `Decls.AgreesAtA`, `EvTree.access_of_agreesAtA` | `X64VecDecls.Decls.AgreesAt`, `EvTree.access_of_agreesAt` |
| `Decls.AgreesOnA` | `X64NoFaultD.Decls.AgreesOn` |
| `EvTree.RootInSA`, `EvTree.RootOnlyDA` | `EvTree.RootInS`, `EvTree.RootOnlyD` |
| `accessFree_mapA`, `rootOnlyDA_map`, `rootOnlyDA_of_singleAccessS(2)` | `accessFree_mapD`, `rootOnlyD_map`, `rootOnlyD_of_singleAccessS(2)` |
| `noFault_reresolve_accessFree`, `noFault_reresolve_rootD` | `noFault_underDecls_accessFreeD`, `noFault_underDecls_rootD` |

New here (no x64 twin), for the address run of `A64NoFaultD`:

- **`SharedEnv.inv S ⊤`** (`invTop S`, the invariant environment with the
  trivial invariant): every access must be exactly a location of `S`, any
  value may be read, a non-exclusive store succeeds. A run in it constrains
  the machine state only (addresses), never the shared values.
- `EvTree.AllLeavesA P t`: every leaf reached under `invTop`'s outcomes (any
  value; store success unless exclusive) satisfies `P`; `allLeavesJA`, the
  live judgment of `invTop S` whose `W` it is; `rootInJA`, the live judgment
  of `invTop S` whose `W` is `RootInSA S`.
- `TreeJLive.guardA J P`: the live judgment of `E` "`AllLeavesA P t → J.W t`",
  for an environment whose non-exclusive stores succeed (`StoreSuccA E`):
  the product of a run in `E` and a run in `invTop S`.

The twins are now defined from (definitions) or proved by (lemmas)
their originals, which moved to the ISA-neutral `EnvG/NoFaultDCommon.lean`
together with `noFault_reresolve_accessFree` (same name). Each keeps its
name, type and reducibility; their docstrings say "Defined from".
`noFault_reresolve_rootD` is an instance of
`NoFaultDCommon.noFault_reresolve_rootSameD`.
-/
import Kraken.Promising.SLR.EnvG.A64DeclsCommon
import Kraken.Promising.SLR.EnvG.NoFaultDCommon
import Kraken.SharedEnvInv

namespace Kraken.Promising

/-- **`ds` resolves an `n`-byte access at `a` to its own footprint.**
Defined from `Decls.AgreesAt` (`NoFaultDCommon`). -/
def Decls.AgreesAtA (ds : Decls) (a : BitVec 64) (n : Nat) : Prop := ds.AgreesAt a n

/-- **`ds` resolves every location of `S` to itself.**
Defined from `Decls.AgreesOn` (`NoFaultDCommon`). -/
def Decls.AgreesOnA (ds : Decls) (S : SharedEnv.Layout) : Prop := ds.AgreesOn S

/-- Defined from `EvTree.access_of_agreesAt` (`NoFaultDCommon`). -/
theorem EvTree.access_of_agreesAtA {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} (h : ds.AgreesAtA a n)
    (k : Loc → EvTree σ) : EvTree.access ds a n k = EvTree.access {} a n k :=
  EvTree.access_of_agreesAt h k

namespace EvTree

/-- **The root accesses are `S`-locations**: every access reached through
`choose` and fences only. Defined from `EvTree.RootInS` (`NoFaultDCommon`). -/
def RootInSA (S : SharedEnv.Layout) {σ : Type} (t : EvTree σ) : Prop := t.RootInS S

/-- **Single access**: no access after an access.
Defined from `EvTree.RootOnlyD` (`NoFaultDCommon`). -/
def RootOnlyDA {σ : Type} (t : EvTree σ) : Prop := t.RootOnlyD

/-- **Every leaf reached under `SharedEnv.inv S ⊤`'s outcomes satisfies
`P`**: any value at a load or an RMW, success at a non-exclusive store
(either answer at an exclusive one). -/
def AllLeavesA {σ : Type} (P : σ → Prop) : EvTree σ → Prop
  | .done s => P s
  | .fault _ => True
  | .choose _ k => ∀ i, AllLeavesA P (k i)
  | .fence _ ret => AllLeavesA P (ret ())
  | .load _ _ _ ret => ∀ v, AllLeavesA P (ret v)
  | .store _ xcl _ _ ret => ∀ b, (b = true ∨ xcl = true) → AllLeavesA P (ret b)
  | .rmw _ _ _ _ ret => ∀ v, AllLeavesA P (ret v)

end EvTree

end Kraken.Promising

namespace Kraken.SharedEnv

/-- **The trivial invariant environment on `S`**: `inv S ⊤`. -/
abbrev invTop (S : Layout) : SharedEnv := inv S fun _ _ => True

/-- **Every non-exclusive store of `E` succeeds** (every `EnvG` variant:
`StoreOut`'s `b = true`). -/
def StoreSuccA (E : SharedEnv) : Prop :=
  ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : BitVec 128} {g : E.State} {b : Bool}
    {g' : E.State}, E.step (.store k xcl addr n v) g b g' → b = true ∨ xcl = true

end Kraken.SharedEnv

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {σ : Type}

/-! ## Shapes -/

/-- Defined from `accessFree_mapD` (`NoFaultDCommon`). -/
theorem accessFree_mapA {τ : Type} (f : σ → τ) : ∀ t : EvTree σ, AccessFree t → AccessFree (t.map f) :=
  accessFree_mapD f

/-- Defined from `rootOnlyD_map` (`NoFaultDCommon`). -/
theorem rootOnlyDA_map {τ : Type} (f : σ → τ) : ∀ t : EvTree σ, t.RootOnlyDA → (t.map f).RootOnlyDA :=
  rootOnlyD_map f

/-- Defined from `rootOnlyD_of_singleAccessS` (`NoFaultDCommon`). -/
theorem rootOnlyDA_of_singleAccessS {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} :
    ∀ t : EvTree σ, SingleAccessS Lok Sok Rok D t → t.RootOnlyDA :=
  rootOnlyD_of_singleAccessS

/-- Defined from `rootOnlyD_of_singleAccessS2` (`NoFaultDCommon`). -/
theorem rootOnlyDA_of_singleAccessS2 {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} :
    ∀ t : EvTree σ, SingleAccessS2 Lok Sok Rok D t → t.RootOnlyDA :=
  rootOnlyD_of_singleAccessS2

theorem rootOnlyDA_of_phase1Shape {A : Arch} {t : EvTree σ} (h : Phase1Shape A t) : t.RootOnlyDA :=
  rootOnlyDA_of_singleAccessS _ h.2

theorem rootOnlyDA_of_phase1ShapeR {A : Arch} {t : EvTree σ} (h : Phase1ShapeR A t) : t.RootOnlyDA :=
  rootOnlyDA_of_singleAccessS2 _ h.2

theorem rootOnlyDA_of_phase1ShapeF {t : EvTree σ} (h : Phase1ShapeF t) : t.RootOnlyDA :=
  rootOnlyDA_of_singleAccessS2 _ h.2

/-! ## No fault under `reresolve` -/

/-- **A fault-free single-access tree whose root accesses are `S`-locations
stays fault-free re-resolved against declarations agreeing on `S`.**
Instance of `NoFaultDCommon.noFault_reresolve_rootSameD` (as is
`X64NoFaultD.noFault_underDecls_rootD`). -/
theorem noFault_reresolve_rootD {ds : Decls} {S : SharedEnv.Layout} (hag : ds.AgreesOnA S) :
    ∀ t : EvTree σ, t.RootInSA S → t.RootOnlyDA → t.NoFault → (t.reresolve ds).NoFault :=
  fun t hi ho h => noFault_reresolve_rootSameD hag t hi (rootSameD_of_rootOnlyD t ho) h

/-! ## The judgments of the address run -/

/-- **"Root accesses in `S`"**, the live judgment of `invTop S`. -/
def rootInJA (S : SharedEnv.Layout) : TreeJLive (SharedEnv.invTop S) σ where
  W t _ := t.RootInSA S
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose h := fun i => h i
  load h₁ _ := h₁
  store h₁ _ := h₁.1
  rmw h₁ _ := h₁.1
  fence _ h₂ := h₂ () trivial

/-- **"Every leaf in `P`"**, the live judgment of `invTop S`. -/
def allLeavesJA (S : SharedEnv.Layout) (P : σ → Prop) : TreeJLive (SharedEnv.invTop S) σ where
  W t _ := t.AllLeavesA P
  Post s _ := P s
  done h := h
  fault := trivial
  choose h := fun i => h i
  load _ h₂ := fun v => h₂ v () trivial
  store _ h₂ := fun b hb => h₂ b () hb
  rmw _ h₂ := fun v => h₂ v () trivial
  fence _ h₂ := h₂ () trivial

/-- **A live judgment of `E` guarded by the address run**: `W t g` is
"`AllLeavesA P t → J.W t g`", `Post s g` is "`P s → J.Post s g`". For an
environment whose non-exclusive stores succeed, the laws are `J`'s. -/
def TreeJLive.guardA {E : SharedEnv} (hss : E.StoreSuccA) (J : TreeJLive E σ)
    (P : σ → Prop) : TreeJLive E σ where
  W t g := t.AllLeavesA P → J.W t g
  Post s g := P s → J.Post s g
  done h hP := J.done (h hP)
  fault _ := J.fault
  choose h hA := J.choose fun i => h i (hA i)
  load h₁ h₂ hA := J.load h₁ fun v g' hs => h₂ v g' hs (hA v)
  store h₁ h₂ hA := J.store h₁ fun b g' hs => h₂ b g' hs (hA b (hss hs))
  rmw h₁ h₂ hA := J.rmw h₁ fun v g' hs => h₂ v g' hs (hA v)
  fence h₁ h₂ hA := J.fence h₁ fun g' hs => h₂ g' hs hA

end Kraken.Promising.SLR.EnvG

set_option hygiene false in
/-- `decls_agrees_on_a` proves a concrete `Decls.AgreesOnA ds S` (a literal
layout and declarations, symbol addresses rewritten to numerals first): one
`rfl` per location of `S` (`X64NoFaultD`'s `decls_agrees_on`). -/
macro "decls_agrees_on_a" : tactic => `(tactic| (
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' (rcases hp with rfl | hp)
  all_goals rfl))

#print axioms Kraken.Promising.SLR.EnvG.noFault_reresolve_rootD
