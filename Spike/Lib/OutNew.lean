/-
**Rows where box allocations are admitted, split at the box's rows**: an
`Out` row under a memory side with `newOk` is the box's initialising store
(its premises at the pair, `NewStM`), the counter's add at a box, or the
same row under the memory side with no box rows (`newOk := False`). So a
consumer that lands the box's store from its premises (whatever row the
node gives) and refutes the counter's add elsewhere keeps its rows for
memory sides with no box rows.

- `NewStM p lbl ms s c`: `Out.newStore`'s premises at `(s, c)` under `ms`
  (`CtrRowsN.NewSt` at `ms`'s own fields).
- `Out.unnew`: an `Out` row is `NewStM`, the counter's add at a box (its
  instruction and the counter's premises), or the row with no box rows.
-/
import Spike.Lib.CtrRowsN

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- **The box's initialising store at `(s, c)` under `ms`**: `Out.newStore`'s
premises (`CtrRowsN.NewSt`) at `ms`'s arena, mapped words, allocation
fragment and box allowance. -/
abbrev NewStM (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (s : I.State) (c : Ctl) :
    Prop :=
  CtrRowsN.NewSt p lbl ms.heap ms.ctr ms.units ms.off ms.cells ms.mp ms.xa ms.newOk s c

/-- The box's initialising store is off a return (its pair is at `new`). -/
theorem NewStM.not_ret {ms : MemSide I} {s : I.State} {c : Ctl} (h : NewStM p lbl ms s c) :
    ∀ a, c.term ≠ .ret a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, -, -, -, ht, -⟩ := h
  intro a ha; rw [ha] at ht; cases ht

/-- **An `Out` row, split at the box's rows**: the box's initialising store
(`NewStM`); the counter's add at a box (the read-modify-write of the counter
word adding the object's units, the counter the runtime's, every new value
one runtime memory may hold there); or the same row with no box rows. -/
theorem Out.unnew {ms : MemSide I} {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c) :
    NewStM p lbl ms s c ∨
      (∃ (k : Kraken.RmwKind) (op : Val → Option Val) (g : Val → I.State) (n : Nat) (τ : Ty),
        I.exec s = some (.rmw k false ⟨BitVec.ofNat 64 ms.ctr, 8⟩ op fun v => .done (g v)) ∧
        ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
        (∀ old, op old = some ((old.setWidth 64 + BitVec.ofNat 64 (ms.units n τ)).setWidth 128)) ∧
        ∀ old, ms.G ⟨BitVec.ofNat 64 ms.ctr, 8⟩ old →
          (∀ w, (⟨BitVec.ofNat 64 ms.ctr, 8⟩, w) ∈ ms.own s → old = w) →
          (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
          ms.G ⟨BitVec.ofNat 64 ms.ctr, 8⟩ ((old.setWidth 64 + BitVec.ofNat 64 (ms.units n τ)).setWidth 128)) ∨
      Out p lbl { ms with newOk := False } X s c := by
  cases h with
  | silent s' c' he hr hx => exact .inr (.inr (.silent s' c' he hr hx))
  | choice P t he hs hx => exact .inr (.inr (.choice P t he hs hx))
  | load kl A g x a e ty w he ht hev hv hx htag => exact .inr (.inr (.load kl A g x a e ty w he ht hev hv hx htag))
  | store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag =>
    exact .inr (.inr (.store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag))
  | rtStore kr L V s' c' he hrt hm hG hr hx => exact .inr (.inr (.rtStore kr L V s' c' he hrt hm hG hr hx))
  | rtLoad kl L g c' he hrt hm hr hx => exact .inr (.inr (.rtLoad kl L g c' he hrt hm hr hx))
  | rtRmw k L op g c' he hrt hm hr hx => exact .inr (.inr (.rtRmw k L op g c' he hrt hm hr hx))
  | sys K call hK ha hd hok hx => exact .inr (.inr (.sys K call hK ha hd hok hx))
  | holdLoad kl A g x sa u v e he hx hA hh hX => exact .inr (.inr (.holdLoad kl A g x sa u v e he hx hA hh hX))
  | xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .inr (.inr (.xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX))
  | ctrRmw k op g x τ e n he hrt hm hs hh hop hX =>
    rcases hs with hb | ⟨-, hb⟩
    · exact .inr (.inr (.ctrRmw k op g x τ e n he hrt hm (.inl hb) hh hop hX))
    · exact .inr (.inl ⟨k, op, g, n, τ, he, hrt, hop, fun old hG ho hc hl => (hX old hG ho hc hl).1⟩)
  | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    exact .inr (.inr (.alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX))
  | newStore kr A V s' x a t e w wold old hN he hm ht hev hu hv hh hold hA hc hX =>
    exact .inl ⟨kr, A, V, s', x, a, t, e, w, wold, old, hN, he, hm, ht, hev, hu, hv, hh, hold, hA, hc, hX⟩
  | emit K buf n Pw Qw hK ha hd h0 hb hr hq => exact .inr (.inr (.emit K buf n Pw Qw hK ha hd h0 hb hr hq))
  | fence k s' c' he hr hx => exact .inr (.inr (.fence k s' c' he hr hx))

/-- info: 'Spike.Lib.Out.unnew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Out.unnew

/-- **An `Out` row off a system call has an instruction** (any memory side,
box rows or not). -/
theorem Out.exec_isSome {ms : MemSide I} {X : Frag I} {s : I.State} {c : Ctl} {K : Scc.Sem.Kernel.Abi I}
    (hK : ms.K = some K) (hns : K.atSys s = false) (h : Out p lbl ms X s c) : (I.exec s).isSome := by
  cases h with
  | sys K' _ hK' hs => rw [hK] at hK'; cases hK'; rw [hns] at hs; cases hs
  | emit K' _ _ _ _ hK' hae => rw [hK] at hK'; cases hK'; rw [hns] at hae; cases hae
  | silent _ _ he | choice _ _ he _ | load _ _ _ _ _ _ _ _ he | store _ _ _ _ _ _ _ _ _ _ _ _ he
  | rtStore _ _ _ _ _ he | rtLoad _ _ _ _ he | rtRmw _ _ _ _ _ he | holdLoad _ _ _ _ _ _ _ _ he
  | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he | ctrRmw _ _ _ _ _ _ _ he | alloc _ _ _ _ _ _ _ _ _ _ _ _ he
  | fence _ _ _ he | newStore _ _ _ _ _ _ _ _ _ _ _ _ he =>
    rw [he]; rfl

end Spike.Lib
