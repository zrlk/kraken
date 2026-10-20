/-
Whole-thread environment (`EnvG`), phase 3: the **tree-level link
for trees with several writes**, over an abstract environment. ISA-neutral.

Phase 2 (`MultiTreeLink.lean`) links trees with a prefix of loads and then at
most one access (`MultiAccessS`). This file admits, after the load prefix,
**a sequence of stores** (`MultiWriteS`): on every path, any number of loads
(and fences), then either one RMW and nothing else, or any number of stores
with no load or RMW between or after them (`WritesOnly`). That covers
AArch64 `STP` (two stores), and the x64 vector stores split into pieces.

The per-node transport `NodeSimW` is `NodeSimM` with one more field,
`store_post`: a store from the post relation (after a first write) lands in
the post relation again. A load never follows a write: after a write the
next access is anchored at the intermediate configuration, where the
clean-erasure knowledge a load adds (`LoadOut`'s `ClAt` at the load's
anchor) is not the one `ThreadRuleRX.wp` adds (at the instruction's start).

- `WritesOnly Sok`, `MultiWriteS Lok Sok Rok D`, `.mono`,
  `MultiAccessS.toW` (phase-2 trees are phase-3 trees);
- `NodeSimW`, `TreeJLive.eraseWPRDW`, `treeJ_eraseWPRDW`: link theorem 1
  (abstract) for such trees.

Additive: the phase-1/2 names are unchanged.
-/
import Kraken.Promising.SLR.EnvG.MultiTreeLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## Trees with a load prefix and a store suffix -/

/-- **Stores only** (and fences): every store needs `Sok l v`; no load, no
RMW. -/
def WritesOnly (Sok : Loc → Val → Prop) {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, WritesOnly Sok (k i)
  | .fence _ ret => WritesOnly Sok (ret ())
  | .load .. => False
  | .store _ _ l v ret => Sok l v ∧ ∀ b, WritesOnly Sok (ret b)
  | .rmw .. => False

/-- An access-free tree writes only. -/
theorem AccessFree.writesOnly {Sok : Loc → Val → Prop} {σ : Type} :
    ∀ {tree : EvTree σ}, AccessFree tree → WritesOnly Sok tree
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => AccessFree.writesOnly (tree := k i) (h i)
  | .fence _ ret, h => AccessFree.writesOnly (tree := ret ()) h
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .rmw .., h => h.elim

theorem WritesOnly.mono {Sok Sok' : Loc → Val → Prop} (hS : ∀ l v, Sok l v → Sok' l v) {σ : Type} :
    ∀ {tree : EvTree σ}, WritesOnly Sok tree → WritesOnly Sok' tree
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => WritesOnly.mono hS (tree := k i) (h i)
  | .fence _ ret, h => WritesOnly.mono hS (tree := ret ()) h
  | .load .., h => h.elim
  | .store .., h => ⟨hS _ _ h.1, fun b => WritesOnly.mono hS (h.2 b)⟩
  | .rmw .., h => h.elim

/-- **A prefix of loads, then one RMW or a sequence of stores**: every load
needs `Lok`; a store of `v` to `l` needs `Sok l v` and may be followed by
more stores (`WritesOnly`); an RMW of kind `k` needs `Rok k` and ends the
accesses; a leaf reached with no write needs `D`. -/
def MultiWriteS (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Prop) (D : Prop) {σ : Type} :
    EvTree σ → Prop
  | .done _ => D
  | .fault _ => True
  | .choose _ k => ∀ i, MultiWriteS Lok Sok Rok D (k i)
  | .fence _ ret => MultiWriteS Lok Sok Rok D (ret ())
  | .load _ _ _ ret => Lok ∧ ∀ v, MultiWriteS Lok Sok Rok D (ret v)
  | .store _ _ l v ret => Sok l v ∧ ∀ b, WritesOnly Sok (ret b)
  | .rmw k _ _ _ ret => Rok k ∧ ∀ v, AccessFree (ret v)

theorem MultiWriteS.mono {Lok Lok' : Prop} {Sok Sok' : Loc → Val → Prop} {Rok Rok' : RmwKind → Prop}
    {D D' : Prop} (hL : Lok → Lok') (hS : ∀ l v, Sok l v → Sok' l v) (hR : ∀ k, Rok k → Rok' k) (hD : D → D')
    {σ : Type} : ∀ {tree : EvTree σ}, MultiWriteS Lok Sok Rok D tree → MultiWriteS Lok' Sok' Rok' D' tree
  | .done _, h => hD h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => MultiWriteS.mono hL hS hR hD (tree := k i) (h i)
  | .fence _ ret, h => MultiWriteS.mono hL hS hR hD (tree := ret ()) h
  | .load _ _ _ ret, h => ⟨hL h.1, fun v => MultiWriteS.mono hL hS hR hD (tree := ret v) (h.2 v)⟩
  | .store .., h => ⟨hS _ _ h.1, fun b => WritesOnly.mono hS (h.2 b)⟩
  | .rmw .., h => ⟨hR _ h.1, h.2⟩

/-- Phase-2 trees (a load prefix, at most one access) are phase-3 trees. -/
theorem MultiAccessS.toW {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} {σ : Type} :
    ∀ {tree : EvTree σ}, MultiAccessS Lok Sok Rok D tree → MultiWriteS Lok Sok Rok D tree
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => MultiAccessS.toW (tree := k i) (h i)
  | .fence _ ret, h => MultiAccessS.toW (tree := ret ()) h
  | .load _ _ _ ret, h => ⟨h.1, fun v => MultiAccessS.toW (tree := ret v) (h.2 v)⟩
  | .store .., h => ⟨h.1, fun b => (h.2 b).writesOnly⟩
  | .rmw .., h => h

/-! ## The per-node transport -/

/-- **Per-node transport for trees with a store suffix**: `NodeSimM` plus a
store from the post relation (after a first write) back into it. -/
structure NodeSimW (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I)
    (t : Thread I) (E : SharedEnv) (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Prop) (D : Prop)
    (Pre Post : E.State → Res → Ghost → Ctx → Prop) : Prop extends
    NodeSimM A tid iv rF T c t E Lok Sok Rok D Pre Post where
  store_post : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {s r g cx},
    Sok ⟨addr, n⟩ v → Post s r g cx → E.ok (.store k xcl addr n v) s →
    (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl ⟨addr, n⟩ v
        (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
      ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
      cx'.Overtaken ∨ ∃ r' g' s', E.step (.store k xcl addr n v) s true s' ∧ ErAt rF T c t tid r' g' cx' ∧
        RStep c.mem.last r g r' g' cx' ∧ Post s' r' g' cx') ∧
    (xcl = true → ∃ s', E.step (.store k xcl addr n v) s false s' ∧ Post s' r g (xclFailCtx cx ⟨addr, n⟩))

section Link

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {E : SharedEnv} {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop}
  {Pre Post : E.State → Res → Ghost → Ctx → Prop}

/-- **`EraseWPRD` is a live tree judgment** of any environment with a
`NodeSimW`: `W tree s` says that `EvTree.EraseWPRD` holds from every actual
state related to `s` by `Pre` if the tree is `MultiWriteS`, and by `Post` if
it writes only. -/
def TreeJLive.eraseWPRDW (hs : NodeSimW A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    (Q : σ → E.State → Prop) : TreeJLive E σ where
  W tree s :=
    (∀ r g cx, Pre s r g cx → MultiWriteS Lok Sok Rok D tree →
      tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx) ∧
    (∀ r g cx, Post s r g cx → WritesOnly Sok tree → tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx)
  Post := Q
  done h := ⟨fun _ _ _ hp hd => ⟨_, h, hs.pre_post hd hp⟩, fun _ _ _ hp _ => ⟨_, h, hp⟩⟩
  fault := ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
  choose h := ⟨fun r g cx hp ha i => (h i).1 r g cx hp (ha i), fun r g cx hp ha i => (h i).2 r g cx hp (ha i)⟩
  fence hok h := by
    refine ⟨fun r g cx hp ha => ?_, fun r g cx hp ha => ?_⟩
    · obtain ⟨s', hst, hp'⟩ := hs.fence_pre hp hok
      exact (h s' hst).1 r g _ hp' ha
    · obtain ⟨s', hst, hp'⟩ := hs.fence_post hp hok
      exact (h s' hst).2 r g _ hp' ha
  load hok h := by
    refine ⟨fun r g cx hp ha x hx => ?_, fun _ _ _ _ ha => ha.elim⟩
    obtain ⟨s', hst, hp'⟩ := hs.load ha.1 hp hok x hx
    exact (h _ s' hst).1 r g _ hp' (ha.2 _)
  store hok h := by
    refine ⟨fun r g cx hp ha => ⟨fun cx' hc E hi hm => ?_, fun hx => ?_⟩,
      fun r g cx hp ha => ⟨fun cx' hc E hi hm => ?_, fun hx => ?_⟩⟩
    · rcases (hs.store ha.1 hp hok).1 cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h true s' hst).2 r' g' cx' hp' (ha.2 true)⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.store ha.1 hp hok).2 hx
      exact (h false s' hst).2 r g _ hp' (ha.2 false)
    · rcases (hs.store_post ha.1 hp hok).1 cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h true s' hst).2 r' g' cx' hp' (ha.2 true)⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.store_post ha.1 hp hok).2 hx
      exact (h false s' hst).2 r g _ hp' (ha.2 false)
  rmw := by
    intro k addr n op ret s hok h
    refine ⟨fun r g cx hp ha x hx => ⟨fun hop => ?_, fun new hop cx' hc E hi hm => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.rmw ha.1 hp hok x hx).1 hop
      exact (h _ s' hst).2 r g _ hp' (ha.2 _).writesOnly
    · rcases (hs.rmw ha.1 hp hok x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h _ s' hst).2 r' g' _ hp' (ha.2 _).writesOnly⟩

/-- **Link theorem 1, abstract form, for trees with a store suffix.** -/
theorem treeJ_eraseWPRDW (hs : NodeSimW A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    {Q : σ → E.State → Prop} {tree : EvTree σ} {s : E.State} (hW : (TreeJLive.eraseWPRDW hs Q).W tree s)
    {r : Res} {g : Ghost} {cx : Ctx} (hp : Pre s r g cx) (ha : MultiWriteS Lok Sok Rok D tree) :
    tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx :=
  hW.1 r g cx hp ha

end Link

end Kraken.Promising.SLR.EnvG
