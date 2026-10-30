/-
**The stack map's clauses of `Components` at any configuration of the kernel
model** (AArch64, any number of threads): from `Kernel.OwnDom` (each
thread's private memory is its initial stack and the ranges it holds, the
held ranges in the pool, pairwise disjoint, the initial stacks off the pool)
and the shared messages in the layout (`MemIn`), a thread's stack range
(`Kernel.stackRangeOf`: the range it holds that its `sp` is on) is in the
pool, off every other thread's, mapped in its own private memory and in no
other thread's, and off every shared message. With no marked place, the
marked and unmarked clauses are trivial.

- `StackOk`: `Components`' `stack_pool`, `stack_disj`, `stack_owned`,
  `stack_private`, `stack_marked`, `stack_unmarked` for a witness.
- `stackOk`: `StackOk` from `OwnDom` and `MemIn` for a witness without marked
  places.
-/
import Spike.Lib.A64OwnedCopy
import Scc.Sem.Correct

namespace Spike.Lib.WakeStack

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.Consumer1 (MemIn memIn_msgs sub_contains shared_not_pool)

/-- **The stack map's clauses of `Components`** for the witness `w` at the
target configuration `t`. -/
structure StackOk (M : ExtMachine) (Λ : Scc.Sem.Layout) (w : Witness M) (t : M.Cfg) : Prop where
  stack_pool : ∀ j rg, M.stackRange t j = some rg → rg.Sub Λ.stackPool
  stack_disj : ∀ j j' rg rg', j ≠ j' → M.stackRange t j = some rg → M.stackRange t j' = some rg' →
    rg.Disjoint rg'
  stack_owned : ∀ j rg, M.stackRange t j = some rg → ∀ j' tt', t.1.threads[j']? = some tt' →
    ∀ a, a % 8 = 0 → rg.contains a → rg.contains (a + 7) →
    ((M.privLoad tt'.st (BitVec.ofNat 64 a)).isSome ↔ j' = j)
  stack_private : ∀ j rg, M.stackRange t j = some rg → ∀ m ∈ t.1.mem.msgs.toList,
    ¬ rg.contains m.loc.addr.toNat
  stack_marked : ∀ j pl, w.marked j pl → ∃ tt rg v, t.1.threads[j]? = some tt ∧
    M.stackRange t j = some rg ∧ placeVal M tt.st pl = some v ∧ rg.contains v
  stack_unmarked : ∀ i d x k wp pl j, w.env i d x k = some wp → pl ∈ wp.places → w.thr i = some j →
    ¬ w.marked j pl

/-- A thread's stack range is a range it holds. -/
private theorem held_of_range {c : Config isaLSE2 × KState} {j : Nat} {rg : Range}
    (h : stackRangeOf abi c j = some rg) : (j, rg) ∈ c.2.held := by
  unfold stackRangeOf at h
  split at h
  · cases h
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    have hm := List.mem_of_find?_eq_some hx
    have hp := List.find?_some hx
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [← hp.1]
    exact hm

/-- Two held entries of distinct threads are disjoint. -/
private theorem disj_of_held {held : List (Nat × Range)} (hd : held.Pairwise fun h h' => h.2.Disjoint h'.2)
    {x y : Nat × Range} (hx : x ∈ held) (hy : y ∈ held) (hne : x ≠ y) : x.2.Disjoint y.2 := by
  induction held with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact absurd rfl hne
    · exact hd.1 _ hy'
    · have := hd.1 _ hx'
      unfold Range.Disjoint at this ⊢; omega
    · exact ih hd.2 hx' hy'

/-- **The stack map's clauses from `OwnDom`**: every thread's private
memory its initial stack and its held ranges (`hD`), the pool the layout's
(`hpool`), the shared messages in the layout (`hmi`), no marked place. -/
theorem stackOk {n : Nat} {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {E : Nat → BitVec 64 → Prop}
    {P : State → Prop} {t : (machine (kernel n)).Cfg} (hD : OwnDom abi E P t) (hpool : t.2.pool = Λ.stackPool)
    (hmi : MemIn Λ t.1.mem) {w : Witness (machine (kernel n))} (hw : ∀ j pl, ¬ w.marked j pl) :
    StackOk (machine (kernel n)) Λ w t := by
  have hsub : ∀ j rg, stackRangeOf abi t j = some rg → rg.Sub Λ.stackPool := fun j rg h => by
    rw [← hpool]; exact (hD.held_ok _ (held_of_range h)).2.1
  refine ⟨hsub, ?_, ?_, ?_, fun j pl h => absurd h (hw j pl), fun _ _ _ _ _ pl j _ _ _ => hw j pl⟩
  · intro j j' rg rg' hne h h'
    exact disj_of_held hD.held_disj (held_of_range h) (held_of_range h') (by intro he; cases he; exact hne rfl)
  · intro j rg h j' tt' htt a h8 h1 h2
    have hm := held_of_range h
    obtain ⟨hpos, -, hfit⟩ := hD.held_ok _ hm
    simp only at hpos hfit
    refine Iff.trans (Spike.Lib.A64Consumer.privLoad_isSome_iff (tt'.st : State) (BitVec.ofNat 64 a)) ?_
    constructor
    · intro hall
      have h0 := hall 0 (by decide)
      rw [BitVec.add_zero] at h0
      have hrg : rg.contains (BitVec.ofNat 64 a).toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Range.contains at h1 h2; omega)]; exact h1
      rcases (hD.dom j' tt' htt _).mp h0 with hE | ⟨r', hr', hc⟩
      · exact absurd (hpool ▸ sub_contains (hsub j rg h) hrg) (hD.pool_E j' _ hE)
      · refine Classical.byContradiction fun hne => ?_
        have hd := disj_of_held hD.held_disj hr' hm (by intro he; cases he; exact hne rfl)
        simp only at hd
        unfold Range.Disjoint at hd; unfold Range.contains at hc hrg; omega
    · rintro rfl i hi
      refine (hD.dom _ tt' htt _).mpr (.inr ⟨rg, hm, ?_⟩)
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Range.contains at h1 h2; omega)]
      unfold Range.contains at h1 h2 ⊢; omega
  · intro j rg h m hm hc
    exact shared_not_pool hwf (memIn_msgs hmi m hm).addr (sub_contains (hsub j rg h) hc)

/-- info: 'Spike.Lib.WakeStack.stackOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeStack.stackOk

end Spike.Lib.WakeStack
