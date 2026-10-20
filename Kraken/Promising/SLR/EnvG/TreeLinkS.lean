/-
Whole-thread environment (`EnvG`): the **tree-level link with
per-node side conditions**, over an abstract environment. ISA-neutral.

`TreeLink.lean`'s `NodeSim` asks every node transport to work for every
access of the given shape. Some transports only hold for the accesses an
instruction can actually perform in the given start state: an in-flight
prepaid release (`EnvG/NodeRel.lean`, `InflightMode`) makes every write
other than the release's fulfilment a dead branch only if the instruction's
single access *is* that release store. The existing `InflightWritesDead`
(`EnvG/Link.lean`) states this tree-independently and is therefore not
provable; this file is its tree-indexed replacement (additive: the existing
`NodeSim`/`treeJ_eraseWPRD` are unchanged).

- `SingleAccessS Lok Sok Rok D`: `SingleAccess` whose load nodes need `Lok`,
  store nodes of `(l, v)` need `Sok l v`, RMW nodes of kind `k` need
  `Rok k`, and leaves reached before the access need `D`.
- `NodeSimS`: `NodeSim` whose fields take those side conditions.
- `TreeJLive.eraseWPRDS`, `treeJ_eraseWPRDS`: link theorem 1 (abstract) for
  such trees; `NodeSim.toS` and `SingleAccess.toS` recover the old form.
-/
import Kraken.Promising.SLR.EnvG.TreeLink

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## Single-access trees with side conditions -/

/-- **At most one access on every path, with side conditions**: a load needs
`Lok`, a store of `v` to `l` needs `Sok l v`, an RMW of kind `k` needs
`Rok k`, and a leaf reached with no access needs `D`. -/
def SingleAccessS (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Prop) (D : Prop) {σ : Type} :
    EvTree σ → Prop
  | .done _ => D
  | .fault _ => True
  | .choose _ k => ∀ i, SingleAccessS Lok Sok Rok D (k i)
  | .fence _ ret => SingleAccessS Lok Sok Rok D (ret ())
  | .load _ _ _ ret => Lok ∧ ∀ v, AccessFree (ret v)
  | .store _ _ l v ret => Sok l v ∧ ∀ b, AccessFree (ret b)
  | .rmw k _ _ _ ret => Rok k ∧ ∀ v, AccessFree (ret v)

/-- A single-access tree satisfies the trivial side conditions. -/
theorem SingleAccess.toS {σ : Type} {tree : EvTree σ} (h : SingleAccess tree) :
    SingleAccessS True (fun _ _ => True) (fun _ => True) True tree := by
  induction tree with
  | done _ => trivial
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load => exact ⟨trivial, h⟩
  | store => exact ⟨trivial, h⟩
  | rmw => exact ⟨trivial, h⟩

theorem SingleAccessS.singleAccess {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop}
    {σ : Type} {tree : EvTree σ} (h : SingleAccessS Lok Sok Rok D tree) : SingleAccess tree := by
  induction tree with
  | done _ => trivial
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load => exact h.2
  | store => exact h.2
  | rmw => exact h.2

/-! ## The per-node transport with side conditions -/

/-- **Per-node transport with side conditions** (`NodeSim` whose fields take
the node's side condition of `SingleAccessS`). -/
structure NodeSimS (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I)
    (t : Thread I) (E : SharedEnv) (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Prop) (D : Prop)
    (Pre Post : E.State → Res → Ghost → Ctx → Prop) : Prop where
  pre_post : ∀ {s r g cx}, D → Pre s r g cx → Post s r g cx
  fence_pre : ∀ {k : FenceKind} {s r g cx}, Pre s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Pre s' r g (fenceStep cx k)
  fence_post : ∀ {k : FenceKind} {s r g cx}, Post s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Post s' r g (fenceStep cx k)
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {s r g cx}, Lok →
    Pre s r g cx → E.ok (.load k xcl addr n) s →
    ∀ x ∈ readSuccs A iv cx k xcl ⟨addr, n⟩, ∃ s', E.step (.load k xcl addr n) s x.2.1 s' ∧ Post s' r g x.2.2
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {s r g cx}, Sok ⟨addr, n⟩ v →
    Pre s r g cx → E.ok (.store k xcl addr n v) s →
    (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl ⟨addr, n⟩ v
        (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
      ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
      cx'.Overtaken ∨ ∃ r' g' s', E.step (.store k xcl addr n v) s true s' ∧ ErAt rF T c t tid r' g' cx' ∧
        RStep c.mem.last r g r' g' cx' ∧ Post s' r' g' cx') ∧
    (xcl = true → ∃ s', E.step (.store k xcl addr n v) s false s' ∧ Post s' r g (xclFailCtx cx ⟨addr, n⟩))
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {s r g cx}, Rok k →
    Pre s r g cx → E.ok (.rmw k addr n op) s →
    ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false ⟨addr, n⟩ false,
      (op x.2.1 = none → ∃ s', E.step (.rmw k addr n op) s x.2.1 s' ∧ Post s' r g (fenceOptCtx A x.2.2)) ∧
      ∀ new, op x.2.1 = some new →
        ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true ⟨addr, n⟩ new (some x.1)
            (x.2.2.loadViews.getLastD 0),
          ErAt rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
          cx'.Overtaken ∨ ∃ r' g' s', E.step (.rmw k addr n op) s x.2.1 s' ∧ ErAt rF T c t tid r' g' cx' ∧
            RStep c.mem.last r g r' g' (rmwAfter A k false ⟨addr, n⟩ cx') ∧
            Post s' r' g' (rmwAfter A k false ⟨addr, n⟩ cx')

section Link

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {E : SharedEnv} {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop}
  {Pre Post : E.State → Res → Ghost → Ctx → Prop}

/-- Every `NodeSim` is a `NodeSimS` for any side conditions. -/
theorem NodeSim.toS (hs : NodeSim A tid iv rF T c t E Pre Post) :
    NodeSimS A tid iv rF T c t E Lok Sok Rok D Pre Post where
  pre_post _ h := hs.pre_post h
  fence_pre := hs.fence_pre
  fence_post := hs.fence_post
  load _ := hs.load
  store _ := hs.store
  rmw _ := hs.rmw

/-- **`EraseWPRD` is a live tree judgment** of any environment with a
per-node transport with side conditions (`NodeSimS`), as
`TreeJLive.eraseWPRD`: `W tree s` says that `EvTree.EraseWPRD` holds from
every actual state related to `s` by `Pre` if the tree satisfies
`SingleAccessS`, and by `Post` if it is access-free. -/
def TreeJLive.eraseWPRDS (hs : NodeSimS A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    (Q : σ → E.State → Prop) : TreeJLive E σ where
  W tree s :=
    (∀ r g cx, Pre s r g cx → SingleAccessS Lok Sok Rok D tree →
      tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx) ∧
    (∀ r g cx, Post s r g cx → AccessFree tree → tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx)
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
    exact (h _ s' hst).2 r g _ hp' (ha.2 _)
  store hok h := by
    refine ⟨fun r g cx hp ha => ⟨fun cx' hc E hi hm => ?_, fun hx => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · rcases (hs.store ha.1 hp hok).1 cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h true s' hst).2 r' g' cx' hp' (ha.2 true)⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.store ha.1 hp hok).2 hx
      exact (h false s' hst).2 r g _ hp' (ha.2 false)
  rmw := by
    intro k addr n op ret s hok h
    refine ⟨fun r g cx hp ha x hx => ⟨fun hop => ?_, fun new hop cx' hc E hi hm => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.rmw ha.1 hp hok x hx).1 hop
      exact (h _ s' hst).2 r g _ hp' (ha.2 _)
    · rcases (hs.rmw ha.1 hp hok x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h _ s' hst).2 r' g' _ hp' (ha.2 _)⟩

/-- **Link theorem 1, abstract form, with side conditions.** -/
theorem treeJ_eraseWPRDS (hs : NodeSimS A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    {Q : σ → E.State → Prop} {tree : EvTree σ} {s : E.State} (hW : (TreeJLive.eraseWPRDS hs Q).W tree s)
    {r : Res} {g : Ghost} {cx : Ctx} (hp : Pre s r g cx) (ha : SingleAccessS Lok Sok Rok D tree) :
    tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx :=
  hW.1 r g cx hp ha

end Link

/-! ## Side conditions that see an RMW's location and operation

`SingleAccessS2`/`NodeSimS2`/`TreeJLive.eraseWPRDS2` are `SingleAccessS`/
`NodeSimS`/`TreeJLive.eraseWPRDS` with the RMW side condition taking the
node's kind, location and operation (`Rok k l op`): an RMW that fulfils an
in-flight prepaid release must write the in-flight location and must not fail
(`EnvG/LinkR.lean`). Additive; the old forms are the special case
`Rok k _ _ := Rok k` (`SingleAccessS.toS2`, `NodeSimS2.ofS`). -/

/-- **At most one access on every path, with side conditions** (RMW side
condition on kind, location and operation). -/
def SingleAccessS2 (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Loc → (Val → Option Val) → Prop)
    (D : Prop) {σ : Type} : EvTree σ → Prop
  | .done _ => D
  | .fault _ => True
  | .choose _ k => ∀ i, SingleAccessS2 Lok Sok Rok D (k i)
  | .fence _ ret => SingleAccessS2 Lok Sok Rok D (ret ())
  | .load _ _ _ ret => Lok ∧ ∀ v, AccessFree (ret v)
  | .store _ _ l v ret => Sok l v ∧ ∀ b, AccessFree (ret b)
  | .rmw k _ l op ret => Rok k l op ∧ ∀ v, AccessFree (ret v)

theorem SingleAccessS.toS2 {Lok : Prop} {Sok : Loc → Val → Prop} {Rok : RmwKind → Prop} {D : Prop} {σ : Type} :
    ∀ {tree : EvTree σ}, SingleAccessS Lok Sok Rok D tree → SingleAccessS2 Lok Sok (fun k _ _ => Rok k) D tree
  | .done _, h => h
  | .fault _, h => h
  | .choose _ k, h => fun i => SingleAccessS.toS2 (tree := k i) (h i)
  | .fence _ ret, h => SingleAccessS.toS2 (tree := ret ()) h
  | .load .., h => h
  | .store .., h => h
  | .rmw .., h => h

theorem SingleAccessS2.singleAccess {Lok : Prop} {Sok : Loc → Val → Prop}
    {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} {σ : Type} :
    ∀ {tree : EvTree σ}, SingleAccessS2 Lok Sok Rok D tree → SingleAccess tree
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => SingleAccessS2.singleAccess (tree := k i) (h i)
  | .fence _ ret, h => SingleAccessS2.singleAccess (tree := ret ()) h
  | .load .., h => h.2
  | .store .., h => h.2
  | .rmw .., h => h.2

/-- `SingleAccessS2` is monotone in its side conditions. -/
theorem SingleAccessS2.mono {Lok Lok' : Prop} {Sok Sok' : Loc → Val → Prop}
    {Rok Rok' : RmwKind → Loc → (Val → Option Val) → Prop} {D D' : Prop} (hL : Lok → Lok')
    (hS : ∀ l v, Sok l v → Sok' l v) (hR : ∀ k l op, Rok k l op → Rok' k l op) (hD : D → D') {σ : Type} :
    ∀ {tree : EvTree σ}, SingleAccessS2 Lok Sok Rok D tree → SingleAccessS2 Lok' Sok' Rok' D' tree
  | .done _, h => hD h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => SingleAccessS2.mono hL hS hR hD (tree := k i) (h i)
  | .fence _ ret, h => SingleAccessS2.mono hL hS hR hD (tree := ret ()) h
  | .load .., h => ⟨hL h.1, h.2⟩
  | .store .., h => ⟨hS _ _ h.1, h.2⟩
  | .rmw .., h => ⟨hR _ _ _ h.1, h.2⟩

/-- **Per-node transport with side conditions on an RMW's kind, location and
operation** (`NodeSimS` with `Rok k l op`). -/
structure NodeSimS2 (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I)
    (t : Thread I) (E : SharedEnv) (Lok : Prop) (Sok : Loc → Val → Prop)
    (Rok : RmwKind → Loc → (Val → Option Val) → Prop) (D : Prop)
    (Pre Post : E.State → Res → Ghost → Ctx → Prop) : Prop where
  pre_post : ∀ {s r g cx}, D → Pre s r g cx → Post s r g cx
  fence_pre : ∀ {k : FenceKind} {s r g cx}, Pre s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Pre s' r g (fenceStep cx k)
  fence_post : ∀ {k : FenceKind} {s r g cx}, Post s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Post s' r g (fenceStep cx k)
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {s r g cx}, Lok →
    Pre s r g cx → E.ok (.load k xcl addr n) s →
    ∀ x ∈ readSuccs A iv cx k xcl ⟨addr, n⟩, ∃ s', E.step (.load k xcl addr n) s x.2.1 s' ∧ Post s' r g x.2.2
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {s r g cx}, Sok ⟨addr, n⟩ v →
    Pre s r g cx → E.ok (.store k xcl addr n v) s →
    (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl ⟨addr, n⟩ v
        (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
      ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
      cx'.Overtaken ∨ ∃ r' g' s', E.step (.store k xcl addr n v) s true s' ∧ ErAt rF T c t tid r' g' cx' ∧
        RStep c.mem.last r g r' g' cx' ∧ Post s' r' g' cx') ∧
    (xcl = true → ∃ s', E.step (.store k xcl addr n v) s false s' ∧ Post s' r g (xclFailCtx cx ⟨addr, n⟩))
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {s r g cx}, Rok k ⟨addr, n⟩ op →
    Pre s r g cx → E.ok (.rmw k addr n op) s →
    ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false ⟨addr, n⟩ false,
      (op x.2.1 = none → ∃ s', E.step (.rmw k addr n op) s x.2.1 s' ∧ Post s' r g (fenceOptCtx A x.2.2)) ∧
      ∀ new, op x.2.1 = some new →
        ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true ⟨addr, n⟩ new (some x.1)
            (x.2.2.loadViews.getLastD 0),
          ErAt rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
          cx'.Overtaken ∨ ∃ r' g' s', E.step (.rmw k addr n op) s x.2.1 s' ∧ ErAt rF T c t tid r' g' cx' ∧
            RStep c.mem.last r g r' g' (rmwAfter A k false ⟨addr, n⟩ cx') ∧
            Post s' r' g' (rmwAfter A k false ⟨addr, n⟩ cx')

section Link2

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {E : SharedEnv} {Lok : Prop} {Sok : Loc → Val → Prop}
  {Rok : RmwKind → Loc → (Val → Option Val) → Prop} {D : Prop} {Pre Post : E.State → Res → Ghost → Ctx → Prop}

/-- Every `NodeSimS` is a `NodeSimS2` whose RMW side condition ignores the
location and operation. -/
theorem NodeSimS2.ofS {Rok₁ : RmwKind → Prop} (hs : NodeSimS A tid iv rF T c t E Lok Sok Rok₁ D Pre Post) :
    NodeSimS2 A tid iv rF T c t E Lok Sok (fun k _ _ => Rok₁ k) D Pre Post where
  pre_post := hs.pre_post
  fence_pre := hs.fence_pre
  fence_post := hs.fence_post
  load := hs.load
  store := hs.store
  rmw := hs.rmw

/-- **`EraseWPRD` is a live tree judgment** of any environment with a
`NodeSimS2` (as `TreeJLive.eraseWPRDS`). -/
def TreeJLive.eraseWPRDS2 (hs : NodeSimS2 A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    (Q : σ → E.State → Prop) : TreeJLive E σ where
  W tree s :=
    (∀ r g cx, Pre s r g cx → SingleAccessS2 Lok Sok Rok D tree →
      tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx) ∧
    (∀ r g cx, Post s r g cx → AccessFree tree → tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx)
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
    exact (h _ s' hst).2 r g _ hp' (ha.2 _)
  store hok h := by
    refine ⟨fun r g cx hp ha => ⟨fun cx' hc E hi hm => ?_, fun hx => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · rcases (hs.store ha.1 hp hok).1 cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h true s' hst).2 r' g' cx' hp' (ha.2 true)⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.store ha.1 hp hok).2 hx
      exact (h false s' hst).2 r g _ hp' (ha.2 false)
  rmw := by
    intro k addr n op ret s hok h
    refine ⟨fun r g cx hp ha x hx => ⟨fun hop => ?_, fun new hop cx' hc E hi hm => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.rmw ha.1 hp hok x hx).1 hop
      exact (h _ s' hst).2 r g _ hp' (ha.2 _)
    · rcases (hs.rmw ha.1 hp hok x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h _ s' hst).2 r' g' _ hp' (ha.2 _)⟩

/-- **Link theorem 1, abstract form, with RMW side conditions on location
and operation.** -/
theorem treeJ_eraseWPRDS2 (hs : NodeSimS2 A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    {Q : σ → E.State → Prop} {tree : EvTree σ} {s : E.State} (hW : (TreeJLive.eraseWPRDS2 hs Q).W tree s)
    {r : Res} {g : Ghost} {cx : Ctx} (hp : Pre s r g cx) (ha : SingleAccessS2 Lok Sok Rok D tree) :
    tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx :=
  hW.1 r g cx hp ha

end Link2

end Kraken.Promising.SLR.EnvG
