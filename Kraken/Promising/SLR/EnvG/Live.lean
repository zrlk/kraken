/-
EnvG, live trees (ISA-neutral part): **live trees** and the tree judgment whose
`rmw` law answers only for `noRet = false`.

`SharedAccess.rmw` carries no `noRet`, so `EnvSpike.TreeJ`'s `rmw` law must
hold for both values of the flag; for `noRet = true` the read of the RMW is
plain and a claiming RMW (a `swpa`/`casa` lock acquire) cannot meet the
floor bound of `ReachRules`. The additive fix:

- `EvTree.RmwLive`: no `rmw` node of the tree has `noRet = true`. A static
  per-thread property (`A64Live.lean`: `Program.rmwLive`; `X64Live.lean`:
  always).
- `TreeJLive E σ`: a copy of `EnvSpike.TreeJ` whose `rmw` law concludes only
  `W (.rmw k false …)`. A judgment of this kind is sound on live trees:
  `TreeJLive.toTreeJ` is an `EnvSpike.TreeJ` whose `W` is
  "`RmwLive` implies `J.W`" (the `noRet = true` case of the `rmw` law is
  vacuous there), so every per-ISA simulation of `TreeJ`
  (`EnvSpikeA64.exec_treeJ_of_instrStepEnv`) carries over unchanged.

Phase 1: the judgments here are used on single-access instruction trees (one
access per instruction); nothing in this file depends
on it, but that is the only use made of them so far.
-/
import Kraken.Promising.SLR.EnvSpike

namespace Kraken.Promising

/-- **Live trees**: no `rmw` node has `noRet = true` (every RMW's read is
returned, hence may be an acquire and is ordered by `fence .ld`). Decided
statically per program: `Program.rmwLive` (AArch64), always on x64. -/
def EvTree.RmwLive {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).RmwLive
  | .load _ _ _ ret => ∀ v, (ret v).RmwLive
  | .store _ _ _ _ ret => ∀ b, (ret b).RmwLive
  | .rmw _ noRet _ _ ret => noRet = false ∧ ∀ v, (ret v).RmwLive
  | .fence _ ret => ∀ u, (ret u).RmwLive

/-- Liveness ignores the leaves (`EvTree.map` changes only them). -/
theorem EvTree.rmwLive_map {σ τ : Type} (f : σ → τ) :
    ∀ t : EvTree σ, (t.map f).RmwLive ↔ t.RmwLive
  | .done _ => Iff.rfl
  | .fault _ => Iff.rfl
  | .choose _ k => forall_congr' fun i => rmwLive_map f (k i)
  | .load _ _ _ ret => forall_congr' fun v => rmwLive_map f (ret v)
  | .store _ _ _ _ ret => forall_congr' fun b => rmwLive_map f (ret b)
  | .rmw _ _ _ _ ret => and_congr_right fun _ => forall_congr' fun v => rmwLive_map f (ret v)
  | .fence _ ret => forall_congr' fun u => rmwLive_map f (ret u)

end Kraken.Promising

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvSpike (TreeJ)

/-- **`TreeJ.live`**: `EnvSpike.TreeJ` with the `rmw` law restricted to
`noRet = false`. Every other law is
`TreeJ`'s. Sound on live trees (`TreeJLive.toTreeJ`); a `TreeJ` is a
`TreeJLive` (`EnvSpike.TreeJ.toLive`). -/
structure TreeJLive (E : SharedEnv) (σ : Type) where
  W : EvTree σ → E.State → Prop
  Post : σ → E.State → Prop
  done : ∀ {s g}, Post s g → W (.done s) g
  fault : ∀ {m g}, W (.fault m) g
  choose : ∀ {n : Nat} {k : Fin n → EvTree σ} {g}, (∀ i, W (k i) g) → W (.choose n k) g
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {ret : Val → EvTree σ} {g},
    E.ok (.load k xcl addr n) g → (∀ v g', E.step (.load k xcl addr n) g v g' → W (ret v) g') →
      W (.load k xcl ⟨addr, n⟩ ret) g
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {ret : Bool → EvTree σ} {g},
    E.ok (.store k xcl addr n v) g → (∀ b g', E.step (.store k xcl addr n v) g b g' → W (ret b) g') →
      W (.store k xcl ⟨addr, n⟩ v ret) g
  /-- The live `rmw` law: only `noRet = false`. -/
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val}
    {ret : Val → EvTree σ} {g},
    E.ok (.rmw k addr n op) g → (∀ old g', E.step (.rmw k addr n op) g old g' → W (ret old) g') →
      W (.rmw k false ⟨addr, n⟩ op ret) g
  fence : ∀ {k : FenceKind} {ret : Unit → EvTree σ} {g},
    E.ok (.fence k) g → (∀ g', E.step (.fence k) g () g' → W (ret ()) g') → W (.fence k ret) g

namespace TreeJLive

variable {E : SharedEnv}

/-- A live tree judgment read through `EvTree.map f` (as `TreeJ.comap`). -/
def comap {σ τ : Type} (J : TreeJLive E τ) (f : σ → τ) : TreeJLive E σ where
  W t g := J.W (t.map f) g
  Post s g := J.Post (f s) g
  done h := J.done h
  fault := J.fault
  choose h := J.choose h
  load h₁ h₂ := J.load h₁ h₂
  store h₁ h₂ := J.store h₁ h₂
  rmw h₁ h₂ := J.rmw h₁ h₂
  fence h₁ h₂ := J.fence h₁ h₂

/-- **A live judgment is a `TreeJ` on live trees**: `W t g := t.RmwLive →
J.W t g`. The `rmw` law of `TreeJ` (any `noRet`) holds because a live
`rmw` node has `noRet = false`. So the prototype's per-ISA simulations apply
to `J.toTreeJ` verbatim. -/
def toTreeJ {σ : Type} (J : TreeJLive E σ) : TreeJ E σ where
  W t g := t.RmwLive → J.W t g
  Post := J.Post
  done h _ := J.done h
  fault _ := J.fault
  choose h hl := J.choose fun i => h i (hl i)
  load h₁ h₂ hl := J.load h₁ fun v g' hs => h₂ v g' hs (hl v)
  store h₁ h₂ hl := J.store h₁ fun b g' hs => h₂ b g' hs (hl b)
  rmw h₁ h₂ hl := by
    obtain ⟨hnr, hl⟩ := hl
    subst hnr
    exact J.rmw h₁ fun old g' hs => h₂ old g' hs (hl old)
  fence h₁ h₂ hl := J.fence h₁ fun g' hs => h₂ g' hs (hl ())

theorem toTreeJ_W {σ : Type} (J : TreeJLive E σ) {t : EvTree σ} {g : E.State} :
    J.toTreeJ.W t g ↔ (t.RmwLive → J.W t g) := Iff.rfl

theorem toTreeJ_Post {σ : Type} (J : TreeJLive E σ) : J.toTreeJ.Post = J.Post := rfl

end TreeJLive

/-- Forgetting: every `TreeJ` is a `TreeJLive` (its `rmw` law at
`noRet = false`). -/
def _root_.Kraken.Promising.SLR.EnvSpike.TreeJ.toLive {E : SharedEnv} {σ : Type} (J : TreeJ E σ) :
    TreeJLive E σ where
  W := J.W
  Post := J.Post
  done := J.done
  fault := J.fault
  choose := J.choose
  load := J.load
  store := J.store
  rmw := J.rmw
  fence := J.fence

end Kraken.Promising.SLR.EnvG
