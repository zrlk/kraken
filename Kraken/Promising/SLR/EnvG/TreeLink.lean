/-
Whole-thread environment (`EnvG`): the **tree-level link**, over an abstract
environment.

ISA-neutral and independent of `EnvG`'s state: the environment `E` is any
`SharedEnv`, related to the actual instruction by two relations,

- `Pre s r g cx`: before the instruction's (single) access, the environment
  state `s` and the actual resource, ghost state and context `(r, g, cx)`;
- `Post s r g cx`: after it.

`NodeSim` is the per-node transport, one field per event shape: from the
environment's `ok`, every actual outcome of the node is answered by an
environment `step` re-establishing the relation, and at a write the erasure
obligations of `EvTree.EraseWPRD` (`ErAt`, `RStep`) hold, or the write
overtook an own promise (`Ctx.Overtaken`, the dead branch). The concrete
instance (`EnvG`'s state, `NodeRel`, the `Sim` transports) is in
`SLR/EnvG/Link.lean`.

- `SingleAccess` / `AccessFree`: on every path at most one load, store or RMW
  (fences are free: they leave the instruction-local fields of the context at
  their defaults).
- `TreeJLive.eraseWPRD`: `EvTree.EraseWPRD` (from `Pre`, at single-access
  trees; from `Post`, at access-free trees) is a `TreeJLive` judgment, the
  postcondition read through `Post`.
- `treeJ_eraseWPRD`: **link theorem 1** in its abstract form.
- `TreeJLiveNF`, `TreeJLiveNF.noFault`, `treeJ_noFaultRun`: the no-fault
  track (a judgment with no `fault` law, `NodeSimNF` with total answers).
-/
import Kraken.Promising.SLR.EnvG.Live
import Kraken.Promising.SLR.Sim.NoFault

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## Single-access trees -/

/-- No load, store or RMW on any path (fences allowed). -/
def AccessFree {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, AccessFree (k i)
  | .fence _ ret => AccessFree (ret ())
  | .load .. => False
  | .store .. => False
  | .rmw .. => False

/-- **At most one access on every path** (the environment
resets the instruction-local context fields at every access, which is exact
when the instruction has one load, store or RMW; fences do not count). -/
def SingleAccess {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, SingleAccess (k i)
  | .fence _ ret => SingleAccess (ret ())
  | .load _ _ _ ret => ∀ v, AccessFree (ret v)
  | .store _ _ _ _ ret => ∀ b, AccessFree (ret b)
  | .rmw _ _ _ _ ret => ∀ v, AccessFree (ret v)

theorem AccessFree.singleAccess {σ : Type} {tree : EvTree σ} (h : AccessFree tree) : SingleAccess tree := by
  induction tree with
  | done _ => trivial
  | fault _ => trivial
  | choose _ _ ih => exact fun i => ih i (h i)
  | fence _ _ ih => exact ih () h
  | load => exact h.elim
  | store => exact h.elim
  | rmw => exact h.elim

/-! ## The per-node transport -/

/-- **Per-node transport** between an environment `E` and the actual
instruction (thread `tid`, state `t` in `c`, instruction views `iv`,
frame `rF`, erasure set `T`), through `Pre` (before the access) and `Post`
(after it). Each field takes the environment's `ok` for the access and
returns, for every actual outcome the corresponding `EvTree.EraseWPRD` node
quantifies over, an environment `step` to a related state. -/
structure NodeSim (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I)
    (t : Thread I) (E : SharedEnv) (Pre Post : E.State → Res → Ghost → Ctx → Prop) : Prop where
  /-- A tree with no access ends where it started. -/
  pre_post : ∀ {s r g cx}, Pre s r g cx → Post s r g cx
  fence_pre : ∀ {k : FenceKind} {s r g cx}, Pre s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Pre s' r g (fenceStep cx k)
  fence_post : ∀ {k : FenceKind} {s r g cx}, Post s r g cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Post s' r g (fenceStep cx k)
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {s r g cx},
    Pre s r g cx → E.ok (.load k xcl addr n) s →
    ∀ x ∈ readSuccs A iv cx k xcl ⟨addr, n⟩, ∃ s', E.step (.load k xcl addr n) s x.2.1 s' ∧ Post s' r g x.2.2
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {s r g cx},
    Pre s r g cx → E.ok (.store k xcl addr n v) s →
    (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl ⟨addr, n⟩ v
        (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
      ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
      cx'.Overtaken ∨ ∃ r' g' s', E.step (.store k xcl addr n v) s true s' ∧ ErAt rF T c t tid r' g' cx' ∧
        RStep c.mem.last r g r' g' cx' ∧ Post s' r' g' cx') ∧
    (xcl = true → ∃ s', E.step (.store k xcl addr n v) s false s' ∧ Post s' r g (xclFailCtx cx ⟨addr, n⟩))
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {s r g cx},
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

/-! ## Link theorem 1 (abstract form) -/

section Link

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {E : SharedEnv} {Pre Post : E.State → Res → Ghost → Ctx → Prop}

/-- The postcondition `EvTree.EraseWPRD` is read with: the judgment's
postcondition at some environment state related by `Post`. -/
def PostOf {σ : Type} (Q : σ → E.State → Prop) (Post : E.State → Res → Ghost → Ctx → Prop) :
    σ → Res → Ghost → Ctx → Prop :=
  fun st r g cx => ∃ s, Q st s ∧ Post s r g cx

/-- **`EraseWPRD` is a live tree judgment** of any environment with a
per-node transport (`NodeSim`): `W tree s` says that `EvTree.EraseWPRD`
holds from every actual state related to `s` by `Pre` if the tree is
single-access, and by `Post` if it is access-free. -/
def TreeJLive.eraseWPRD (hs : NodeSim A tid iv rF T c t E Pre Post) {σ : Type} (Q : σ → E.State → Prop) :
    TreeJLive E σ where
  W tree s :=
    (∀ r g cx, Pre s r g cx → SingleAccess tree → tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx) ∧
    (∀ r g cx, Post s r g cx → AccessFree tree → tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx)
  Post := Q
  done h := ⟨fun _ _ _ hp _ => ⟨_, h, hs.pre_post hp⟩, fun _ _ _ hp _ => ⟨_, h, hp⟩⟩
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
    obtain ⟨s', hst, hp'⟩ := hs.load hp hok x hx
    exact (h _ s' hst).2 r g _ hp' (ha _)
  store hok h := by
    refine ⟨fun r g cx hp ha => ⟨fun cx' hc E hi hm => ?_, fun hx => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · rcases (hs.store hp hok).1 cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h true s' hst).2 r' g' cx' hp' (ha true)⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.store hp hok).2 hx
      exact (h false s' hst).2 r g _ hp' (ha false)
  rmw := by
    intro k addr n op ret s hok h
    refine ⟨fun r g cx hp ha x hx => ⟨fun hop => ?_, fun new hop cx' hc E hi hm => ?_⟩, fun _ _ _ _ ha => ha.elim⟩
    · obtain ⟨s', hst, hp'⟩ := (hs.rmw hp hok x hx).1 hop
      exact (h _ s' hst).2 r g _ hp' (ha _)
    · rcases (hs.rmw hp hok x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', s', hst, E', hR, hp'⟩
      · exact .inl ho
      · exact .inr ⟨r', g', E', hR, (h _ s' hst).2 r' g' _ hp' (ha _)⟩

/-- **Link theorem 1, abstract form.** Any `TreeJLive` judgment the
environment's run gives the tree (`exec_treeJLive_of_instrStepEnv`, at the
judgment `TreeJLive.eraseWPRD hs Q`) yields the instruction's erasure WP with
dead branches from every actual state related to the environment state by
`Pre`, for a single-access tree; the postcondition is the judgment's,
at an environment state related by `Post`. -/
theorem treeJ_eraseWPRD (hs : NodeSim A tid iv rF T c t E Pre Post) {σ : Type} {Q : σ → E.State → Prop}
    {tree : EvTree σ} {s : E.State} (hW : (TreeJLive.eraseWPRD hs Q).W tree s) {r : Res} {g : Ghost} {cx : Ctx}
    (hp : Pre s r g cx) (ha : SingleAccess tree) :
    tree.EraseWPRD A tid iv rF T c t (PostOf Q Post) r g cx :=
  hW.1 r g cx hp ha

end Link

/-! ## The no-fault track

`TreeJLive` has a `fault` law (`W (.fault m)` always), as `EvTree.EraseWPRD`
treats a fault as `True`. A judgment in which the environment treats a fault
as `False` has no `fault` law (`TreeJLiveNF`); it transfers from an `AllEnv`
judgment exactly when `AllEnv` is `False` at the effects that produce a
`.fault` leaf. The per-node transport must then answer **every** actual
outcome (`NodeSimNF`: `runTree` visits all of them, overtaken writes
included), and needs no erasure. -/

/-- A live tree judgment with no `fault` law: the environment treats a fault
as `False`. -/
structure TreeJLiveNF (E : SharedEnv) (σ : Type) where
  W : EvTree σ → E.State → Prop
  Post : σ → E.State → Prop
  done : ∀ {s g}, Post s g → W (.done s) g
  choose : ∀ {n : Nat} {k : Fin n → EvTree σ} {g}, (∀ i, W (k i) g) → W (.choose n k) g
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {ret : Val → EvTree σ} {g},
    E.ok (.load k xcl addr n) g → (∀ v g', E.step (.load k xcl addr n) g v g' → W (ret v) g') →
      W (.load k xcl ⟨addr, n⟩ ret) g
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {ret : Bool → EvTree σ} {g},
    E.ok (.store k xcl addr n v) g → (∀ b g', E.step (.store k xcl addr n v) g b g' → W (ret b) g') →
      W (.store k xcl ⟨addr, n⟩ v ret) g
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val}
    {ret : Val → EvTree σ} {g},
    E.ok (.rmw k addr n op) g → (∀ old g', E.step (.rmw k addr n op) g old g' → W (ret old) g') →
      W (.rmw k false ⟨addr, n⟩ op ret) g
  fence : ∀ {k : FenceKind} {ret : Unit → EvTree σ} {g},
    E.ok (.fence k) g → (∀ g', E.step (.fence k) g () g' → W (ret ()) g') → W (.fence k ret) g

/-- **Total per-node transport** (no-fault track): context relations only,
and every actual outcome of a node is answered by an environment step. -/
structure NodeSimNF (A : Arch) (tid : Nat) (iv : InstrViews) (E : SharedEnv) (Pre Post : E.State → Ctx → Prop) :
    Prop where
  pre_post : ∀ {s cx}, Pre s cx → Post s cx
  fence_pre : ∀ {k : FenceKind} {s cx}, Pre s cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Pre s' (fenceStep cx k)
  fence_post : ∀ {k : FenceKind} {s cx}, Post s cx → E.ok (.fence k) s →
    ∃ s', E.step (.fence k) s () s' ∧ Post s' (fenceStep cx k)
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {s cx}, Pre s cx → E.ok (.load k xcl addr n) s →
    ∀ x ∈ readSuccs A iv cx k xcl ⟨addr, n⟩, ∃ s', E.step (.load k xcl addr n) s x.2.1 s' ∧ Post s' x.2.2
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {s cx}, Pre s cx →
    E.ok (.store k xcl addr n v) s →
    (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl ⟨addr, n⟩ v
        (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
      ∃ s', E.step (.store k xcl addr n v) s true s' ∧ Post s' cx') ∧
    (xcl = true → ∃ s', E.step (.store k xcl addr n v) s false s' ∧ Post s' (xclFailCtx cx ⟨addr, n⟩))
  rmw : ∀ {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {s cx}, Pre s cx →
    E.ok (.rmw k addr n op) s →
    ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false ⟨addr, n⟩ false,
      (op x.2.1 = none → ∃ s', E.step (.rmw k addr n op) s x.2.1 s' ∧ Post s' (fenceOptCtx A x.2.2)) ∧
      ∀ new, op x.2.1 = some new →
        ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true ⟨addr, n⟩ new (some x.1)
            (x.2.2.loadViews.getLastD 0),
          ∃ s', E.step (.rmw k addr n op) s x.2.1 s' ∧ Post s' (rmwAfter A k false ⟨addr, n⟩ cx')

section NoFault

variable {A : Arch} {tid : Nat} {iv : InstrViews} {E : SharedEnv} {Pre Post : E.State → Ctx → Prop}

/-- **No faulting run is a no-fault live judgment** of any environment with a
total per-node transport. -/
def TreeJLiveNF.noFault (hs : NodeSimNF A tid iv E Pre Post) (σ : Type) : TreeJLiveNF E σ where
  W tree s :=
    (∀ cx, Pre s cx → SingleAccess tree → tree.NoFaultRun A tid iv cx) ∧
    (∀ cx, Post s cx → AccessFree tree → tree.NoFaultRun A tid iv cx)
  Post _ _ := True
  done _ := ⟨fun _ _ _ m hm => by simp [runTree] at hm, fun _ _ _ m hm => by simp [runTree] at hm⟩
  choose h := by
    refine ⟨fun cx hp ha m hm => ?_, fun cx hp ha m hm => ?_⟩ <;>
    · simp only [runTree, List.mem_flatMap] at hm
      obtain ⟨i, -, hi⟩ := hm
      first | exact (h i).1 cx hp (ha i) m hi | exact (h i).2 cx hp (ha i) m hi
  fence hok h := by
    refine ⟨fun cx hp ha m hm => ?_, fun cx hp ha m hm => ?_⟩
    · obtain ⟨s', hst, hp'⟩ := hs.fence_pre hp hok
      exact (h s' hst).1 _ hp' ha m hm
    · obtain ⟨s', hst, hp'⟩ := hs.fence_post hp hok
      exact (h s' hst).2 _ hp' ha m hm
  load hok h := by
    refine ⟨fun cx hp ha m hm => ?_, fun _ _ ha => ha.elim⟩
    simp only [runTree, List.mem_flatMap] at hm
    obtain ⟨x, hx, hm⟩ := hm
    obtain ⟨s', hst, hp'⟩ := hs.load hp hok x hx
    exact (h _ s' hst).2 _ hp' (ha _) m hm
  store hok h := by
    refine ⟨fun cx hp ha m hm => ?_, fun _ _ ha => ha.elim⟩
    simp only [runTree, List.mem_append] at hm
    rcases hm with hm | hm
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at hm
      obtain ⟨-, c', hc, hm⟩ := hm
      obtain ⟨s', hst, hp'⟩ := (hs.store hp hok).1 c' hc
      exact (h true s' hst).2 _ hp' (ha true) m hm
    · rw [List.mem_ite_nil_right] at hm
      obtain ⟨s', hst, hp'⟩ := (hs.store hp hok).2 hm.1
      exact (h false s' hst).2 _ hp' (ha false) m hm.2
  rmw := by
    intro k addr n op ret s hok h
    refine ⟨fun cx hp ha m hm => ?_, fun _ _ ha => ha.elim⟩
    simp only [runTree] at hm
    change (.error m : Except String _) ∈ (readSuccs A iv (fenceOptCtx A cx) (A.rmwKind k).loadKind false
      ⟨addr, n⟩ false).flatMap _ at hm
    rw [List.mem_flatMap] at hm
    obtain ⟨x, hx, hm⟩ := hm
    obtain ⟨tr, old, c3⟩ := x
    simp only at hm
    split at hm
    · next hop =>
      obtain ⟨s', hst, hp'⟩ := (hs.rmw hp hok _ hx).1 hop
      exact (h _ s' hst).2 _ hp' (ha _) m hm
    · next new hop =>
      rw [List.mem_flatMap] at hm
      obtain ⟨c4, hc4, hm⟩ := hm
      obtain ⟨s', hst, hp'⟩ := (hs.rmw hp hok _ hx).2 new hop c4 hc4
      exact (h _ s' hst).2 _ hp' (ha _) m hm

/-- **No-fault link, abstract form**: a no-fault live judgment of the tree
(`TreeJLiveNF.noFault`) gives no faulting run from every context related by
`Pre`, for a single-access tree. -/
theorem treeJ_noFaultRun (hs : NodeSimNF A tid iv E Pre Post) {σ : Type} {tree : EvTree σ} {s : E.State}
    (hW : (TreeJLiveNF.noFault hs σ).W tree s) {cx : Ctx} (hp : Pre s cx) (ha : SingleAccess tree) :
    tree.NoFaultRun A tid iv cx :=
  hW.1 cx hp ha

end NoFault

end Kraken.Promising.SLR.EnvG
