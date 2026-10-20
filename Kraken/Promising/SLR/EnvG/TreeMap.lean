/-
Whole-thread environment (`EnvG`), shared helpers:
**the phase-1 tree shapes are closed under `EvTree.map`**. ISA-neutral (no
`Syntax` import), so both the AArch64 and the x64 links use the same lemmas.

Moved verbatim from `SafelyBridge.lean` (`accessFree_map`, `detAccess_map`,
`singleAccessS_map`, `phase1Shape_map`) and `A64LinkR.lean`
(`singleAccessS2_map`, `phase1ShapeR_map`). They keep their names, which
live in the namespace `Kraken.Promising.AArch64.EnvG` for historical
reasons; the x64 copies in `X64Link.lean` (namespace
`Kraken.Promising.X64.EnvG`) are statement-preserving aliases of these.
The phase-2 shapes are in `EnvG/MultiCommon.lean`.
-/
import Kraken.Promising.SLR.EnvG.Phase1

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Tree shapes along `EvTree.map` -/

theorem accessFree_map {σ τ : Type} (f : σ → τ) (t : EvTree σ) : AccessFree (t.map f) ↔ AccessFree t := by
  induction t with
  | done _ => exact Iff.rfl
  | fault _ => exact Iff.rfl
  | choose _ _ ih => exact forall_congr' fun i => ih i
  | fence _ _ ih => exact ih ()
  | load _ _ _ _ _ => exact Iff.rfl
  | store _ _ _ _ _ _ => exact Iff.rfl
  | rmw _ _ _ _ _ _ => exact Iff.rfl

theorem detAccess_map {σ τ : Type} (f : σ → τ) (t : EvTree σ) (h : DetAccess t) : DetAccess (t.map f) := by
  induction t with
  | choose _ _ _ => exact fun i => (accessFree_map f _).mpr (h i)
  | fence _ _ ih => exact ih () h
  | _ => trivial

theorem singleAccessS_map {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} {σ τ : Type}
    (f : σ → τ) (t : EvTree σ) (h : SingleAccessS Lok Sok Rok D t) : SingleAccessS Lok Sok Rok D (t.map f) := by
  induction t with
  | done _ => exact h
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load _ _ _ _ _ => exact ⟨h.1, fun v => (accessFree_map f _).mpr (h.2 v)⟩
  | store _ _ _ _ _ _ => exact ⟨h.1, fun b => (accessFree_map f _).mpr (h.2 b)⟩
  | rmw _ _ _ _ _ _ => exact ⟨h.1, fun v => (accessFree_map f _).mpr (h.2 v)⟩

theorem phase1Shape_map {A : Arch} {σ τ : Type} (f : σ → τ) {t : EvTree σ} (h : Phase1Shape A t) :
    Phase1Shape A (t.map f) :=
  ⟨detAccess_map f t h.1, singleAccessS_map f t h.2⟩

theorem singleAccessS2_map {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Loc → (Val → Option Val) → Prop}
    {D : Prop} {σ τ : Type} (f : σ → τ) (t : EvTree σ) (h : SingleAccessS2 Lok Sok Rok D t) :
    SingleAccessS2 Lok Sok Rok D (t.map f) := by
  induction t with
  | done _ => exact h
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load _ _ _ _ _ => exact ⟨h.1, fun v => (accessFree_map f _).mpr (h.2 v)⟩
  | store _ _ _ _ _ _ => exact ⟨h.1, fun b => (accessFree_map f _).mpr (h.2 b)⟩
  | rmw _ _ _ _ _ _ => exact ⟨h.1, fun v => (accessFree_map f _).mpr (h.2 v)⟩

theorem phase1ShapeR_map {A : Arch} {σ τ : Type} (f : σ → τ) {t : EvTree σ} (h : Phase1ShapeR A t) :
    Phase1ShapeR A (t.map f) :=
  ⟨detAccess_map f t h.1, singleAccessS2_map f t h.2⟩

end Kraken.Promising.AArch64.EnvG
