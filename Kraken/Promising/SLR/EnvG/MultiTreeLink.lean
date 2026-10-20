/-
Whole-thread environment (`EnvG`), phase 2 (the multi-access link prototype): the
**tree-level link for trees with a load prefix**, over an abstract
environment. ISA-neutral.

Phase 1 links only trees with at most one access per path
(`SingleAccessS`, `TreeLinkS.lean`). This file admits a *prefix of loads*:
on every path, any number of loads (and fences), then at most one access of
any kind (`MultiAccessS`). That shape covers the multi-load instructions
(AArch64 `LDP`/`LDPSW`, `LDXP`/`LDAXP` of two locations; the non-atomic x64
vector loads, split into 8-byte pieces) and the load-then-write ones (x64
unlocked `inc`/`add`/`xadd`/`cmpxchg` on memory, `pop`/`push` with a shared
memory operand).

The per-node transport `NodeSimM` is `NodeSimS` (`TreeLinkS.lean`) whose load
field returns to `Pre` instead of `Post`: a load never changes the resource or
the ghost state, so the relation before the next access can be the relation
before the first one (re-established at the load's outcome). Leaves reached
without a write need `D` (`pre_post`), as in `SingleAccessS`.

- `MultiAccessS Lok Sok Rok D`;
- `NodeSimM`, `TreeJLive.eraseWPRDM`, `treeJ_eraseWPRDM`: link theorem 1
  (abstract) for such trees.

Additive: the phase-1 names are unchanged.
-/
import Kraken.Promising.SLR.EnvG.TreeLinkS

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## Trees with a load prefix -/

/-- **A prefix of loads, then at most one access, with side conditions**:
every load needs `Lok` and may be followed by anything of the same shape; a
store of `v` to `l` needs `Sok l v`, an RMW of kind `k` needs `Rok k`, and
both end the accesses of their path; a leaf reached with no write needs
`D`. -/
def MultiAccessS (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Prop) (D : Prop) {σ : Type} :
    EvTree σ → Prop
  | .done _ => D
  | .fault _ => True
  | .choose _ k => ∀ i, MultiAccessS Lok Sok Rok D (k i)
  | .fence _ ret => MultiAccessS Lok Sok Rok D (ret ())
  | .load _ _ _ ret => Lok ∧ ∀ v, MultiAccessS Lok Sok Rok D (ret v)
  | .store _ _ l v ret => Sok l v ∧ ∀ b, AccessFree (ret b)
  | .rmw k _ _ _ ret => Rok k ∧ ∀ v, AccessFree (ret v)

/-- `MultiAccessS` is monotone in its side conditions. -/
theorem MultiAccessS.mono {Lok Lok' : Prop} {Sok Sok' : Loc → Val → Prop} {Rok Rok' : RmwKind → Prop}
    {D D' : Prop} (hL : Lok → Lok') (hS : ∀ l v, Sok l v → Sok' l v) (hR : ∀ k, Rok k → Rok' k) (hD : D → D')
    {σ : Type} : ∀ {tree : EvTree σ}, MultiAccessS Lok Sok Rok D tree → MultiAccessS Lok' Sok' Rok' D' tree
  | .done _, h => hD h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => MultiAccessS.mono hL hS hR hD (tree := k i) (h i)
  | .fence _ ret, h => MultiAccessS.mono hL hS hR hD (tree := ret ()) h
  | .load _ _ _ ret, h => ⟨hL h.1, fun v => MultiAccessS.mono hL hS hR hD (tree := ret v) (h.2 v)⟩
  | .store .., h => ⟨hS _ _ h.1, h.2⟩
  | .rmw .., h => ⟨hR _ h.1, h.2⟩

/-! ## The per-node transport -/

/-- **Per-node transport for trees with a load prefix**: `NodeSimS` whose
load field re-establishes `Pre` (a load keeps the resource and the ghost
state). -/
structure NodeSimM (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I)
    (t : Thread I) (E : SharedEnv) (Lok : Prop) (Sok : Loc → Val → Prop) (Rok : RmwKind → Prop) (D : Prop)
    (Pre Post : E.State → Res → Ghost → Ctx → Prop) : Prop where
  pre_post : ∀ {s r g cx}, D → Pre s r g cx → Post s r g cx
  fence_pre : ∀ {k : FenceKind} {s r g cx}, Pre s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Pre s' r g (fenceStep cx k)
  fence_post : ∀ {k : FenceKind} {s r g cx}, Post s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Post s' r g (fenceStep cx k)
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {s r g cx}, Lok →
    Pre s r g cx → E.ok (.load k xcl addr n) s →
    ∀ x ∈ readSuccs A iv cx k xcl ⟨addr, n⟩, ∃ s', E.step (.load k xcl addr n) s x.2.1 s' ∧ Pre s' r g x.2.2
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

/-- A `NodeSimM` whose `Pre` implies `Post` is a `NodeSimS` for the same
relations. -/
theorem NodeSimM.toS (hs : NodeSimM A tid iv rF T c t E Lok Sok Rok D Pre Post)
    (hpp : ∀ {s r g cx}, Pre s r g cx → Post s r g cx) :
    NodeSimS A tid iv rF T c t E Lok Sok Rok D Pre Post where
  pre_post hd h := hs.pre_post hd h
  fence_pre := hs.fence_pre
  fence_post := hs.fence_post
  load hl hp hok x hx := by
    obtain ⟨s', hst, hp'⟩ := hs.load hl hp hok x hx
    exact ⟨s', hst, hpp hp'⟩
  store := hs.store
  rmw := hs.rmw

/-- **`EraseWPRD` is a live tree judgment** of any environment with a
`NodeSimM`: `W tree s` says that `EvTree.EraseWPRD` holds from every actual
state related to `s` by `Pre` if the tree has a load prefix
(`MultiAccessS`), and by `Post` if it is access-free. -/
def TreeJLive.eraseWPRDM (hs : NodeSimM A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    (Q : σ → E.State → Prop) : TreeJLive E σ where
  W tree s :=
    (∀ r g cx, Pre s r g cx → MultiAccessS Lok Sok Rok D tree →
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
    exact (h _ s' hst).1 r g _ hp' (ha.2 _)
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

/-- **Link theorem 1, abstract form, for trees with a load prefix.** -/
theorem treeJ_eraseWPRDM (hs : NodeSimM A tid iv rF T c t E Lok Sok Rok D Pre Post) {σ : Type}
    {Q : σ → E.State → Prop} {tree : EvTree σ} {s : E.State} (hW : (TreeJLive.eraseWPRDM hs Q).W tree s)
    {r : Res} {g : Ghost} {cx : Ctx} (hp : Pre s r g cx) (ha : MultiAccessS Lok Sok Rok D tree) :
    tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx :=
  hW.1 r g cx hp ha

end Link

end Kraken.Promising.SLR.EnvG
