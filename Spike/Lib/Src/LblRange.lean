/-
**A placed label's words are not private** (`heapWord_none`): every label
the placement `lbl` places lies, with its size `lsize`, inside the heap or
`.data` (`LblRange`, the memory relation's `lbl_range`); a frame loading no
word of either (`WordsNone`) loads none of the label's words below its size.
The lane store's address-unmapped facts at the exchange's load and store.

- `LblRange`: every placed label's range inside the heap or `.data`;
- `lblRange_of_memRel`: from the memory relation;
- `heapWord_none`: the label's word `k < lsize l` unmapped in `dmem`.

ISA-free.
-/
import Spike.Lib.DmemPriv

namespace Spike.Lib.LowerNode

open Scc.Sem
open Spike.Lib.DmemPriv (WordsNone WordIn)

variable {Λ : Layout}

/-- **Every placed label's range inside the heap or `.data`**: the label `l`
placed at `b` with `8 * lsize l` bytes (`lrange`). -/
def LblRange (Λ : Layout) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) : Prop :=
  ∀ l b, lbl l = some b → (lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data

/-- **`LblRange` from the memory relation** (`MemRel.lbl_range`). -/
theorem lblRange_of_memRel {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Kraken.Promising.Memory} {sm : WeakMem.Memory} {pairs : List Nat}
    (h : MemRel Λ lbl lsize ts tm sm pairs) : LblRange Λ lbl lsize :=
  fun l b hl => (h.lbl_range l b hl).2

/-- **A placed label's word below its size is unmapped** in a memory loading
no word of the heap or `.data`: the word `k < lsize l` of the label `l`
placed at `b`, at the address `a` (`a = b + 8 * k`). -/
theorem heapWord_none {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    (hr : LblRange Λ lbl lsize) {d : _root_.Mem 64} (hwn : WordsNone Λ d) {l : WeakMem.AllocLabel} {b k : Nat}
    (hl : lbl l = some b) (hk : k < lsize l) {a : BitVec 64} (ha : a.toNat = b + 8 * k) :
    Mem.loadInt d a 8 = none := by
  refine hwn a ?_
  rw [ha]
  rcases hr l b hl with h | h
  · left
    unfold Range.Sub lrange at h
    unfold WordIn Range.contains
    simp only at h
    omega
  · right
    unfold Range.Sub lrange at h
    unfold WordIn Range.contains
    simp only at h
    omega

/--
info: 'Spike.Lib.LowerNode.heapWord_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms heapWord_none

/--
info: 'Spike.Lib.LowerNode.lblRange_of_memRel' does not depend on any axioms
-/
#guard_msgs in
#print axioms lblRange_of_memRel

end Spike.Lib.LowerNode
