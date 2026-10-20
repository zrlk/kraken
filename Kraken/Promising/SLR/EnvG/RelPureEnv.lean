/-
**The purity environment** `SharedEnv.relPure A rel`, ISA-neutral part.

`final_of_relWrites` (`SLR/PromisePureGeneral.lean`) asks, at every reachable
thread state, that the next instruction's tree satisfy
`EvTree.RelWrites A (fun l v => Pred.Pure (rel l) v)`: every **non-release**
write (a store whose effective kind `A.storeKind k` is not `.rel`, an RMW
write whose `A.storeKind (A.rmwKind k).storeKind` is not `.rel`) writes a
value pure for its location's release predicate. This file turns that into an
environment, so that a program discharges it by one `vcgen` call per thread:

- `SharedEnv.relPureQ A Q`: state `Unit`; `ok` is `Q` at every non-release
  store or RMW write (exactly `EvTree.RelWrites`' condition, per access);
  loads, release writes and fences are always permitted; every outcome is
  possible (`step` is `True`: reads return anything, stores may fail).
  `SharedEnv.relPure A rel` is the instance `Q l v = Pred.Pure (rel l) v`.
  `Skips` (fences change nothing), so the plain `env_lift_spec` `vcgen` rule
  applies. The x64 TSO stores are releases (`Arch.tso.plainStore = .rel`):
  under `Arch.tso` `ok` asks nothing of a plain store, exactly as `RelWrites`.
- `EnvSpike.TreeJ.relWrites`: the tree judgment "`RelWrites A Q` and every
  leaf satisfies `Post`", whose laws are `relPureQ`'s `ok`/`step` (so every
  per-ISA simulation of `TreeJ` carries an environment step to it).
- `relWrites_reach`: a per-thread predicate `J tid` that every instruction
  keeps, and under which every instruction's tree is `RelWrites`, gives the
  `Jinv`/`hJ`/`hcell` of `final_of_relWrites` (`Jinv st := ∃ tid, J tid st`);
  `final_of_relWritesJ` packages it. No memory invariant is involved.

The AArch64 link (thread specifications from `Safely` judgments in
`relPure`, `exec_treeJ_of_instrStepEnv`) is `EnvG/RelPureEnvA64.lean`.
-/
import Kraken.Promising.SLR.PromisePureGeneral
import Kraken.Promising.SLR.EnvSpike

namespace Kraken.SharedEnv

open Kraken.Promising Kraken.Promising.SLR

/-- **The purity environment, at a value condition `Q`.** Every non-release
store or RMW write (effective kind under `A` not `.rel`) must write a value
satisfying `Q` at its location (an RMW's `op` is checked at every old value);
loads, release writes and fences are always permitted, and every outcome is
possible. The state is trivial. -/
def relPureQ (A : Arch) (Q : Loc → Val → Prop) : SharedEnv where
  State := Unit
  ok a _ := match a with
    | .load .. => True
    | .store k _ addr n v => A.storeKind k ≠ .rel → Q ⟨addr, n⟩ v
    | .rmw k addr n op => A.storeKind (A.rmwKind k).storeKind ≠ .rel →
        ∀ old new, op old = some new → Q ⟨addr, n⟩ new
    | .fence _ => True
  step _ _ _ _ := True

/-- **The purity environment**: non-release writes write values pure for
their location's release predicate `rel l` (the condition of
`final_of_relWrites` for the initial ghost `g₀`, at `rel = g₀.rel`). -/
abbrev relPure (A : Arch) (rel : Loc → Pred) : SharedEnv :=
  relPureQ A fun l v => Pred.Pure (rel l) v

variable {A : Arch} {Q : Loc → Val → Prop}

theorem relPureQ_fencesSkip (A : Arch) (Q : Loc → Val → Prop) : (relPureQ A Q).FencesSkip :=
  fun _ _ => ⟨trivial, fun _ _ => rfl⟩

instance (A : Arch) (Q : Loc → Val → Prop) : (relPureQ A Q).Skips := ⟨relPureQ_fencesSkip A Q⟩

instance (A : Arch) (rel : Loc → Pred) : (relPure A rel).Skips := ⟨relPureQ_fencesSkip _ _⟩

@[simp] theorem relPureQ_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {g : (relPureQ A Q).State} : (relPureQ A Q).ok (.load k xcl addr n) g ↔ True := Iff.rfl

@[simp] theorem relPureQ_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : BitVec 128}
    {g : (relPureQ A Q).State} :
    (relPureQ A Q).ok (.store k xcl addr n v) g ↔ (A.storeKind k ≠ .rel → Q ⟨addr, n⟩ v) := Iff.rfl

@[simp] theorem relPureQ_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g : (relPureQ A Q).State} :
    (relPureQ A Q).ok (.rmw k addr n op) g ↔
      (A.storeKind (A.rmwKind k).storeKind ≠ .rel → ∀ old new, op old = some new → Q ⟨addr, n⟩ new) :=
  Iff.rfl

@[simp] theorem relPureQ_ok_fence {k : FenceKind} {g : (relPureQ A Q).State} :
    (relPureQ A Q).ok (.fence k) g ↔ True := Iff.rfl

@[simp] theorem relPureQ_step {a : SharedAccess} {g g' : (relPureQ A Q).State} {r : a.Ret} :
    (relPureQ A Q).step a g r g' ↔ True := Iff.rfl

/-! The same at `relPure` (whose state type `simp` sees unreduced). -/

variable {rel : Loc → Pred}

@[simp] theorem relPure_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {g : (relPure A rel).State} : (relPure A rel).ok (.load k xcl addr n) g ↔ True := Iff.rfl

@[simp] theorem relPure_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : BitVec 128}
    {g : (relPure A rel).State} :
    (relPure A rel).ok (.store k xcl addr n v) g ↔ (A.storeKind k ≠ .rel → Pred.Pure (rel ⟨addr, n⟩) v) :=
  Iff.rfl

@[simp] theorem relPure_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g : (relPure A rel).State} :
    (relPure A rel).ok (.rmw k addr n op) g ↔
      (A.storeKind (A.rmwKind k).storeKind ≠ .rel →
        ∀ old new, op old = some new → Pred.Pure (rel ⟨addr, n⟩) new) := Iff.rfl

@[simp] theorem relPure_ok_fence {k : FenceKind} {g : (relPure A rel).State} :
    (relPure A rel).ok (.fence k) g ↔ True := Iff.rfl

@[simp] theorem relPure_step {a : SharedAccess} {g g' : (relPure A rel).State} {r : a.Ret} :
    (relPure A rel).step a g r g' ↔ True := Iff.rfl

end Kraken.SharedEnv

namespace Kraken.Promising.SLR.EnvSpike

open Kraken Kraken.Promising

/-- **`RelWrites` as a tree judgment of `relPureQ`**: the tree's non-release
writes satisfy `Q`, and every leaf satisfies `Post`. -/
def TreeJ.relWrites (A : Arch) (Q : Loc → Val → Prop) {σ : Type} (Post : σ → Prop) :
    TreeJ (SharedEnv.relPureQ A Q) σ where
  W t _ := t.RelWrites A Q ∧ t.All Post
  Post s _ := Post s
  done h := ⟨trivial, h⟩
  fault := ⟨trivial, trivial⟩
  choose h := ⟨fun i => (h i).1, fun i => (h i).2⟩
  load _ h := ⟨fun v => (h v () trivial).1, fun v => (h v () trivial).2⟩
  store hok h := ⟨⟨hok, fun b => (h b () trivial).1⟩, fun b => (h b () trivial).2⟩
  rmw hok h := ⟨⟨hok, fun v => (h v () trivial).1⟩, fun v => (h v () trivial).2⟩
  fence _ h := ⟨fun ⟨⟩ => (h () trivial).1, fun ⟨⟩ => (h () trivial).2⟩

end Kraken.Promising.SLR.EnvSpike

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## From a per-thread step property to `final_of_relWrites`' hypotheses -/

/-- **Per-thread purity at every reachable configuration.** If every
instruction of thread `tid` from a state satisfying `J tid` has a tree whose
non-release writes satisfy `Q` and whose leaves satisfy `J tid` (`hstep`),
and every initial thread state satisfies its `J` (`h0`), then every thread of
every reachable configuration satisfies its `J` (promises included: a promise
step leaves the ISA state unchanged; `configInv_reachable` with the trivial
memory invariant). -/
theorem relWrites_reach [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {Q : Loc → Val → Prop} (J : Nat → I.State → Prop)
    (hstep : ∀ tid st tree, J tid st → I.exec st = some tree → tree.RelWrites A Q ∧ tree.All (J tid))
    (h0 : ∀ tid s, states[tid]? = some s → J tid s)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) :
    ∀ tid t, c.threads[tid]? = some t → J tid t.st := by
  have hP : StepPreserves (I := I) A (fun _ _ => True) J := fun tid _ _ _ _ hJ _ hs ho =>
    ⟨stepOne_leaf A hs ho fun tree hex => (hstep tid _ tree hJ hex).2, fun _ => trivial, fun _ _ => trivial⟩
  refine (configInv_reachable hP ⟨⟨fun _ => trivial, fun _ _ => trivial⟩, fun tid t ht => ?_⟩ hc).2
  obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
  exact h0 tid s hs

/-- **`final_of_relWrites` from a per-thread step property** (`relWrites_reach`):
`Jinv st := ∃ tid, J tid st`, its reachability and the cell condition all
come from `hstep` and `h0`. -/
theorem final_of_relWritesJ [I.LawfulState] (A : Arch) (fuel : Nat) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (J : Nat → I.State → Prop)
    (hstep : ∀ tid st tree, J tid st → I.exec st = some tree →
      tree.RelWrites A (fun l v => Pred.Pure (g₀.rel l) v) ∧ tree.All (J tid))
    (h0 : ∀ tid s, states[tid]? = some s → J tid s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWrites A fuel hH hE hpend (fun st => ∃ tid, J tid st)
    (fun _ hc' tid t ht => ⟨tid, relWrites_reach J hstep h0 hc' tid t ht⟩)
    (fun st tree ⟨tid, hJ⟩ hex => (hstep tid st tree hJ hex).1) hsafe hc hf hfin

end Kraken.Promising.SLR
