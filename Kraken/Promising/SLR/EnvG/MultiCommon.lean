/-
Whole-thread environment (`EnvG`), phase 2, shared helpers. ISA-neutral (no `Syntax` import), so both the AArch64 and the x64
phase-2 links use the same lemmas.

- **The phase-2 tree shapes are closed under `EvTree.map`**:
  `multiAccessS_map`, `noRelWrite_map`, `phase2Shape_map`, moved verbatim
  from `MultiA64.lean` (names kept, namespace `Kraken.Promising.AArch64.EnvG`
  as before; the phase-1 shapes are in `EnvG/TreeMap.lean`).
- **The phase-2 no-fault rule from fault-free trees**
  `noFaultRule_ofEnvG2_struct`, moved verbatim from `MultiNoFault.lean`.

The x64 copies in `MultiX64.lean` (`X64.EnvG.multiAccessS_map`, …,
`noFaultRule_ofEnvG2_structX`) are statement-preserving aliases of these.
-/
import Kraken.Promising.SLR.EnvG.MultiRule
import Kraken.Promising.SLR.EnvG.Answers
import Kraken.Promising.SLR.EnvG.TreeMap

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- **The phase-2 no-fault rule from fault-free trees** (`noFaultRule_ofEnvG_struct`
for `ThreadRuleRX.ofEnvG2`): unconditional in the thread's promises. -/
theorem noFaultRule_ofEnvG2_struct {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps2 A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRule (ThreadRuleRX.ofEnvG2 H hB) :=
  NoFaultRule.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvG.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Tree shapes along `EvTree.map` -/

theorem multiAccessS_map {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} {σ τ : Type}
    (f : σ → τ) (t : EvTree σ) (h : MultiAccessS Lok Sok Rok D t) : MultiAccessS Lok Sok Rok D (t.map f) := by
  induction t with
  | done _ => exact h
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load _ _ _ _ ih => exact ⟨h.1, fun v => ih v (h.2 v)⟩
  | store _ _ _ _ _ _ => exact ⟨h.1, fun b => (accessFree_map f _).mpr (h.2 b)⟩
  | rmw _ _ _ _ _ _ => exact ⟨h.1, fun v => (accessFree_map f _).mpr (h.2 v)⟩

theorem noRelWrite_map {A : Arch} {σ τ : Type} (f : σ → τ) (t : EvTree σ) (h : NoRelWrite A t) :
    NoRelWrite A (t.map f) := by
  induction t with
  | done _ => trivial
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load _ _ _ _ ih => exact fun v => ih v (h v)
  | store _ _ _ _ _ ih => exact ⟨h.1, fun b => ih b (h.2 b)⟩
  | rmw _ _ _ _ _ ih => exact ⟨h.1, fun v => ih v (h.2 v)⟩

theorem phase2Shape_map {A : Arch} {σ τ : Type} (f : σ → τ) {t : EvTree σ} (h : Phase2Shape A t) :
    Phase2Shape A (t.map f) :=
  ⟨multiAccessS_map f t h.1, noRelWrite_map f t h.2⟩

end Kraken.Promising.AArch64.EnvG
