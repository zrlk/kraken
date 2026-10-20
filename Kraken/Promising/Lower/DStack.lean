/-
**A thread-private stack in `dmem` beside env-level
proofs about shared memory, route (I).** ISA-neutral
(imports neither ISA's `Syntax`).

Kraken routes an access by mappedness: `Mem.loadInt s.dmem a n = some _`
serves it from the thread's private memory (no event), `= none` makes it a
shared event (`AArch64/Semantics.lean` `MachineData.load` and friends, the x64
twins, `Promising/{AArch64,X64}.lean` `toEv`). The env rules therefore carry
the side condition `Mem.loadInt s.dmem a n = none` (`hv` in
`AArch64/EnvWPRules.lean`, the `*_shared_spec` conjunct in `EnvVCGen.lean`,
`hdm` in `Lower/Events*.lean`). For an address computed from a value the
environment returned (pop's `ldr x4, [x2, #8]`), nothing relates the address to
`dom dmem`, so proofs so far assumed an empty `dmem`
(`∀ a, Mem.loadInt s.dmem a 8 = none`). A call stack in `dmem` (x64 `call`/
`ret` always use one) breaks that assumption.

**The invariant**: an address
predicate `H` (the heap, i.e. every shared cell a pointer may name) disjoint
from the thread's private memory, `HeapOff H dmem`. Then every access at an
`H` address is the shared event (`HeapOff.loadInt_none`). `dom dmem` never
grows: the semantics only stores into bytes that are already mapped, so
`HeapOff` is kept by every private store (`HeapOff.storeInt`). The usual way
to set it up is static: `dmem` maps only the stack region (`StackDom S`) and
the heap avoids it (`HeapSep H S`), `HeapOff.of_stackDom`. When the
environment confines accesses to a layout `L` (`SharedEnv.inv L G`, `within
L`), take `H := SharedLayout.Covers L`: the access's `env.ok` already gives
its membership (`HeapOff.loadInt_none_of_mem`). `InvLinkX64.Split L d` (the x64
EnvG link's invariant) is this `HeapOff` by definition
(`Lower/DStackX64.lean`).

The other direction, for stack slots: `StackFull lo n dmem` (the bytes
`[lo, lo + n)` are mapped) makes an in-range access private
(`StackFull.loadInt_isSome`). Every store keeps it.

The combined mapped-or-shared rules (x64 `mov`/`push`/`pop`/`ret`/`call`,
`EnvVCGen.lean`) leave a disjunction "served by `dmem`" or "a shared step".
`shared_of_heapOff_load`/`shared_of_heapOff_store` pick the shared side for an
`H` address; `private_of_mapped_load`/`private_of_mapped_store` pick the private
side for a mapped slot.
-/
import Kraken.Mem
import Kraken.Promising.MergedMem
import Kraken.SharedEnvInv

namespace Kraken.DStack

open Std Kraken.Promising

/-! ## The predicates -/

/-- **The heap is off the private memory**: no address satisfying `H` is
mapped in `d`. -/
def HeapOff (H : BitVec 64 → Prop) (d : Mem 64) : Prop := ∀ k, H k → d.get? k = none

/-- **`d` maps only stack addresses**: every mapped byte satisfies `S`. -/
def StackDom (S : BitVec 64 → Prop) (d : Mem 64) : Prop := ∀ k, (d.get? k).isSome → S k

/-- **Heap and stack are disjoint.** Static, from the layout. -/
def HeapSep (H S : BitVec 64 → Prop) : Prop := ∀ k, H k → ¬ S k

/-- One heap for every thread's stack: `H` avoids each `Stacks tid`. -/
def HeapSepAll (H : BitVec 64 → Prop) (Stacks : Nat → BitVec 64 → Prop) : Prop :=
  ∀ tid, HeapSep H (Stacks tid)

/-- The `n` bytes from `lo`: `k ∈ [lo, lo + n)` (modulo `2⁶⁴`). -/
def InRange (lo : BitVec 64) (n : Nat) (k : BitVec 64) : Prop := (k - lo).toNat < n

/-- **The stack region is mapped**: every byte of `[lo, lo + n)` is in `d`. -/
def StackFull (lo : BitVec 64) (n : Nat) (d : Mem 64) : Prop := ∀ k, InRange lo n k → (d.get? k).isSome

/-! ## Basic facts -/

/-- An empty private memory keeps every heap off. -/
theorem HeapOff.empty (H : BitVec 64 → Prop) : HeapOff H ∅ := fun _ _ => by
  simp [ExtHashMap.get?_eq_getElem?]

/-- A smaller heap is still off. -/
theorem HeapOff.mono {H H' : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) (hH : ∀ k, H' k → H k) :
    HeapOff H' d := fun k hk => h k (hH k hk)

/-- **From the layout**: a private memory that maps only stack bytes keeps a
heap disjoint from the stack off. -/
theorem HeapOff.of_stackDom {H S : BitVec 64 → Prop} {d : Mem 64} (hS : StackDom S d) (hH : HeapSep H S) :
    HeapOff H d := fun k hk => by
  cases hg : d.get? k with
  | none => rfl
  | some _ => exact absurd (hS k (by rw [hg]; rfl)) (hH k hk)

/-- Thread `tid`'s instance of a heap shared by all threads. -/
theorem HeapSepAll.heapOff {H : BitVec 64 → Prop} {Stacks : Nat → BitVec 64 → Prop} (h : HeapSepAll H Stacks)
    {tid : Nat} {d : Mem 64} (hS : StackDom (Stacks tid) d) : HeapOff H d :=
  .of_stackDom hS (h tid)

theorem StackDom.mono {S S' : BitVec 64 → Prop} {d : Mem 64} (h : StackDom S d) (hS : ∀ k, S k → S' k) :
    StackDom S' d := fun k hk => hS k (h k hk)

/-! ## The shared rule: an access at a heap address is unmapped -/

/-- **A heap address is not loaded from the private memory**, at any width:
its first byte is unmapped. -/
theorem HeapOff.loadBytes_none {H : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) {a : BitVec 64}
    (ha : H a) {n : Nat} (hn : 0 < n) : d.loadBytes a n = none := by
  cases hb : d.loadBytes a n with
  | none => rfl
  | some _ =>
    have := Mem.get?_isSome_of_loadBytes (m := d) (a := a) (n := n) (by rw [hb]; rfl) 0 hn
    rw [BitVec.add_zero, h a ha] at this
    cases this

/-- **The shared-access side condition** `Mem.loadInt d a n = none` of every
env rule, for an address in the heap. -/
theorem HeapOff.loadInt_none {H : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) {a : BitVec 64}
    (ha : H a) {n : Nat} (hn : 0 < n) : Mem.loadInt d a n = none := by
  unfold Mem.loadInt
  rw [h.loadBytes_none ha hn]
  rfl

/-- A mapped address is not in the heap. -/
theorem HeapOff.not_of_isSome {H : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) {a : BitVec 64} {n : Nat}
    (hs : (Mem.loadInt d a n).isSome = true) (hn : 0 < n) : ¬ H a := fun ha => by
  rw [h.loadInt_none ha hn] at hs
  cases hs

/-- A location of the layout `L` covers its first byte. -/
theorem covers_self {L : SharedEnv.Layout} {a : BitVec 64} {n : Nat} (hm : (a, n) ∈ L) (hn : 0 < n) :
    SharedLayout.Covers L a :=
  ⟨a, n, hm, by rw [BitVec.sub_self]; simpa using hn⟩

/-- **With `H` the bytes of a layout**: a location of the layout is unmapped.
In a layout-confined environment (`SharedEnv.inv L G`, `within L`) the
access's own `env.ok` gives `(a, n) ∈ L`. -/
theorem HeapOff.loadInt_none_of_mem {L : SharedEnv.Layout} {d : Mem 64} (h : HeapOff (SharedLayout.Covers L) d)
    {a : BitVec 64} {n : Nat} (hm : (a, n) ∈ L) (hn : 0 < n) : Mem.loadInt d a n = none :=
  h.loadInt_none (covers_self hm hn) hn

/-- `HeapOff` from finitely many byte lookups, for a layout heap. -/
theorem HeapOff.of_layout {L : SharedEnv.Layout} {d : Mem 64}
    (h : ∀ a n, (a, n) ∈ L → ∀ i < n, d.get? (a + BitVec.ofNat 64 i) = none) :
    HeapOff (SharedLayout.Covers L) d := by
  rintro k ⟨a, n, hm, hlt⟩
  have := h a n hm _ hlt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this

/-- **`SharedEnv.inv`: a permitted load is at an unmapped location.** -/
theorem HeapOff.inv_load {L : SharedEnv.Layout} {G : Promising.Loc → Promising.Val → Prop} {d : Mem 64}
    (h : HeapOff (SharedLayout.Covers L) d) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat}
    {g : (SharedEnv.inv L G).State} (hok : (SharedEnv.inv L G).ok (.load k xcl a n) g) (hn : 0 < n) :
    Mem.loadInt d a n = none :=
  h.loadInt_none_of_mem hok hn

/-- **`SharedEnv.inv`: a permitted store is at an unmapped location.** -/
theorem HeapOff.inv_store {L : SharedEnv.Layout} {G : Promising.Loc → Promising.Val → Prop} {d : Mem 64}
    (h : HeapOff (SharedLayout.Covers L) d) {k : StoreKind} {xcl : Bool} {a : BitVec 64} {n : Nat}
    {v : BitVec 128} {g : (SharedEnv.inv L G).State} (hok : (SharedEnv.inv L G).ok (.store k xcl a n v) g)
    (hn : 0 < n) : Mem.loadInt d a n = none :=
  h.loadInt_none_of_mem hok.1 hn

/-- **`SharedEnv.inv`: a permitted `rmw` is at an unmapped location.** -/
theorem HeapOff.inv_rmw {L : SharedEnv.Layout} {G : Promising.Loc → Promising.Val → Prop} {d : Mem 64}
    (h : HeapOff (SharedLayout.Covers L) d) {k : RmwKind} {a : BitVec 64} {n : Nat}
    {op : BitVec 128 → Option (BitVec 128)} {g : (SharedEnv.inv L G).State}
    (hok : (SharedEnv.inv L G).ok (.rmw k a n op) g) (hn : 0 < n) : Mem.loadInt d a n = none :=
  h.loadInt_none_of_mem hok.1 hn

/-! ## The source's half: pointers in shared cells name heap nodes -/

/-- **The source-typing obligation** (heap cells come from a GC'd heap, a
published cell's pointer words name heap cells, and stacks are not heap). Every value `v` that the value invariant `G`
allows in a pointer cell `L l` is null or the base of a heap node (`Node`).
Kraken does not prove this: the lowering's source side supplies it (as the
value invariant of `SharedEnv.inv L' G`, a `MemVals` specification, or a
ghost fact of the environment), and the env proofs consume it at accesses
through loaded pointers (`PtrsInHeap.loadInt_none`). -/
def PtrsInHeap (L : Promising.Loc → Prop) (G : Promising.Loc → Promising.Val → Prop) (Node : BitVec 64 → Prop) :
    Prop :=
  ∀ l v, L l → G l v → v.setWidth 64 = 0 ∨ Node (v.setWidth 64)

/-- **An access through a loaded pointer is shared**: `v`, read from a
pointer cell, is non-null, so it names a node; the field at `off` is a heap
address (a layout fact, `hF`), hence unmapped. -/
theorem PtrsInHeap.loadInt_none {L : Promising.Loc → Prop} {G : Promising.Loc → Promising.Val → Prop}
    {Node H : BitVec 64 → Prop} (hP : PtrsInHeap L G Node) {off : BitVec 64} (hF : ∀ p, Node p → H (p + off))
    {d : Mem 64} (hd : HeapOff H d) {l : Promising.Loc} {v : Promising.Val} (hl : L l) (hg : G l v)
    (hnz : v.setWidth 64 ≠ 0) {n : Nat} (hn : 0 < n) : Mem.loadInt d (v.setWidth 64 + off) n = none :=
  hd.loadInt_none (hF _ ((hP l v hl hg).resolve_left hnz)) hn

/-! ## Preservation: private stores keep the domain -/

/-- A store's bytes are mapped afterwards; any other byte is as before. -/
private theorem get?_storeBytes_isSome {d : Mem 64} {a k : BitVec 64} {bs : List UInt8}
    (hk : ((d.storeBytes a bs).get? k).isSome) : (∃ i < bs.length, k = a + BitVec.ofNat 64 i) ∨ (d.get? k).isSome := by
  rw [Mem.get?_storeBytes] at hk
  by_cases hm : k ∈ bs.At a
  · exact .inl ((mem_At_iff _ _ _).mp hm)
  · rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.getElem?_eq_none hm] at hk
    exact .inr (by simpa using hk)

/-- **A store into mapped bytes maps nothing new.** -/
theorem dom_storeBytes {d : Mem 64} {a : BitVec 64} {bs : List UInt8} (hd : (d.loadBytes a bs.length).isSome)
    {k : BitVec 64} (hk : ((d.storeBytes a bs).get? k).isSome) : (d.get? k).isSome := by
  rcases get?_storeBytes_isSome hk with ⟨i, hi, rfl⟩ | h
  · exact Mem.get?_isSome_of_loadBytes hd i hi
  · exact h

/-- `dom_storeBytes` for `storeInt`, from the semantics' own guard
(`Mem.loadInt d a n = some _`). -/
theorem dom_storeInt {d : Mem 64} {a : BitVec 64} {n : Nat} (hd : (Mem.loadInt d a n).isSome = true) (v : Int)
    {k : BitVec 64} (hk : ((d.storeInt a n v).get? k).isSome) : (d.get? k).isSome := by
  have hb : (d.loadBytes a (Int.toBytes n v).length).isSome := by
    rw [Int.toBytes_length]
    unfold Mem.loadInt at hd
    cases hb : d.loadBytes a n <;> simp_all
  exact dom_storeBytes hb hk

/-- **A private store keeps the heap off.** -/
theorem HeapOff.storeInt {H : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) {a : BitVec 64} {n : Nat}
    (hd : (Mem.loadInt d a n).isSome = true) (v : Int) : HeapOff H (d.storeInt a n v) := fun k hk => by
  cases hg : (d.storeInt a n v).get? k with
  | none => rfl
  | some _ =>
    have := dom_storeInt hd v (k := k) (by rw [hg]; rfl)
    rw [h k hk] at this
    cases this

/-- A private store of raw bytes (x64 vector pieces) keeps the heap off. -/
theorem HeapOff.storeBytes {H : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) {a : BitVec 64}
    {bs : List UInt8} (hd : (d.loadBytes a bs.length).isSome) : HeapOff H (d.storeBytes a bs) := fun k hk => by
  cases hg : (d.storeBytes a bs).get? k with
  | none => rfl
  | some _ =>
    have := dom_storeBytes hd (k := k) (by rw [hg]; rfl)
    rw [h k hk] at this
    cases this

/-- A private store keeps the stack domain. -/
theorem StackDom.storeInt {S : BitVec 64 → Prop} {d : Mem 64} (h : StackDom S d) {a : BitVec 64} {n : Nat}
    (hd : (Mem.loadInt d a n).isSome = true) (v : Int) : StackDom S (d.storeInt a n v) :=
  fun k hk => h k (dom_storeInt hd v hk)

/-- **Every store keeps the stack region mapped.** -/
theorem StackFull.storeInt {lo : BitVec 64} {n : Nat} {d : Mem 64} (h : StackFull lo n d) (a : BitVec 64) (m : Nat)
    (v : Int) : StackFull lo n (d.storeInt a m v) := fun k hk => by
  unfold Mem.storeInt
  rw [Mem.get?_storeBytes]
  have := h k hk
  cases hb : ((Int.toBytes m v).At a).get? k <;> simp_all

/-- **An in-range slot is private**: `m` bytes at `a` inside `[lo, lo + n)`
load from the private memory. -/
theorem StackFull.loadInt_isSome {lo : BitVec 64} {n : Nat} {d : Mem 64} (h : StackFull lo n d) {a : BitVec 64}
    {m : Nat} (hr : (a - lo).toNat + m ≤ n) : (Mem.loadInt d a m).isSome = true := by
  simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff, List.forall_mem_map,
    List.mem_range]
  intro i hi
  apply h
  unfold InRange
  rw [show a + BitVec.ofNat 64 i - lo = (a - lo) + BitVec.ofNat 64 i by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  have h1 := (a - lo).isLt
  by_cases hm : i < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hm]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega)

/-! ## Invariants of every run

The semantics of both ISAs writes the private memory only through
`Mem.storeInt d a n v` under the guard `Mem.loadInt d a n = some _`, and the
environment hands `dmem` back unchanged. So a property of `dmem` that such
stores keep (`StoreClosed`) holds along every run
(`Lower/DStackA64.lean`/`Lower/DStackX64.lean`,
`instrStepEnv_dmem`/`safely_dmem`/`eventually_dmem`). `HeapOff H`,
`StackDom S`, `StackFull lo n` and `DomEq d₀` ("the domain is `d₀`'s":
**`dom dmem` is constant**) are such properties. -/

/-- **A property of the private memory kept by every private store.** -/
def StoreClosed (I : Mem 64 → Prop) : Prop :=
  ∀ d a n v, I d → (Mem.loadInt d a n).isSome = true → I (d.storeInt a n v)

/-- `d` has exactly `d₀`'s domain. -/
def DomEq (d₀ d : Mem 64) : Prop := ∀ k, (d.get? k).isSome = (d₀.get? k).isSome

theorem StoreClosed.store {I : Mem 64 → Prop} (hI : StoreClosed I) {d : Mem 64} (hd : I d) {a : BitVec 64}
    {n : Nat} {x : Int} (hm : Mem.loadInt d a n = some x) (v : Int) : I (d.storeInt a n v) :=
  hI d a n v hd (by rw [hm]; rfl)

/-- A private store keeps every mapped access mapped. -/
theorem isSome_loadInt_storeInt {d : Mem 64} {b : BitVec 64} {m : Nat} (hb : (Mem.loadInt d b m).isSome = true)
    (a : BitVec 64) (n : Nat) (v : Int) : (Mem.loadInt (d.storeInt a n v) b m).isSome = true := by
  have hb' : (d.loadBytes b m).isSome := by
    unfold Mem.loadInt at hb
    cases h : d.loadBytes b m <;> simp_all
  have := Mem.loadBytes_isSome_storeBytes (bs := Int.toBytes n v) a hb'
  unfold Mem.loadInt Mem.storeInt
  cases h : (d.storeBytes a (Int.toBytes n v)).loadBytes b m <;> simp_all

/-- **Two private stores** (a pair's halves, both mapped). -/
theorem StoreClosed.store₂ {I : Mem 64 → Prop} (hI : StoreClosed I) {d : Mem 64} (hd : I d) {a b : BitVec 64}
    {n : Nat} {x y : Int} (ha : Mem.loadInt d a n = some x) (hb : Mem.loadInt d b n = some y) (u v : Int) :
    I ((d.storeInt a n u).storeInt b n v) :=
  hI _ b n v (hI.store hd ha u) (isSome_loadInt_storeInt (by rw [hb]; rfl) a n u)

theorem StoreClosed.and {I J : Mem 64 → Prop} (hI : StoreClosed I) (hJ : StoreClosed J) :
    StoreClosed fun d => I d ∧ J d :=
  fun d a n v h hs => ⟨hI d a n v h.1 hs, hJ d a n v h.2 hs⟩

theorem heapOff_storeClosed (H : BitVec 64 → Prop) : StoreClosed (HeapOff H) :=
  fun _ _ _ v h hs => h.storeInt hs v

theorem stackDom_storeClosed (S : BitVec 64 → Prop) : StoreClosed (StackDom S) :=
  fun _ _ _ v h hs => h.storeInt hs v

theorem stackFull_storeClosed (lo : BitVec 64) (n : Nat) : StoreClosed (StackFull lo n) :=
  fun _ a m v h _ => h.storeInt a m v

/-- **The domain is constant**: a private store keeps `DomEq d₀`. -/
theorem domEq_storeClosed (d₀ : Mem 64) : StoreClosed (DomEq d₀) := fun d a n v h hs k => by
  rw [← h k]
  cases hg : (d.storeInt a n v).get? k with
  | none =>
    cases hd : d.get? k with
    | none => rfl
    | some _ =>
      have : ((d.storeInt a n v).get? k).isSome := by
        unfold Mem.storeInt; rw [Mem.get?_storeBytes, hd]; cases ((Int.toBytes n v).At a).get? k <;> rfl
      rw [hg] at this; cases this
  | some _ => exact (dom_storeInt hs v (k := k) (by rw [hg]; rfl)).symm

theorem DomEq.refl (d : Mem 64) : DomEq d d := fun _ => rfl

/-! ## Eliminators for the combined mapped-or-shared rules -/

/-- **A combined load at a heap address is the shared step.** -/
theorem shared_of_heapOff_load {H : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) {a : BitVec 64}
    (ha : H a) {n : Nat} (hn : 0 < n) {R : Int → Prop} {Q : Prop}
    (hc : (∃ v, Mem.loadInt d a n = some v ∧ R v) ∨ (Mem.loadInt d a n = none ∧ Q)) : Q := by
  rcases hc with ⟨v, hv, -⟩ | ⟨-, hq⟩
  · rw [h.loadInt_none ha hn] at hv
    cases hv
  · exact hq

/-- **A combined store at a heap address is the shared step.** -/
theorem shared_of_heapOff_store {H : BitVec 64 → Prop} {d : Mem 64} (h : HeapOff H d) {a : BitVec 64}
    (ha : H a) {n : Nat} (hn : 0 < n) {R Q : Prop}
    (hc : ((Mem.loadInt d a n).isSome = true ∧ R) ∨ (Mem.loadInt d a n = none ∧ Q)) : Q := by
  rcases hc with ⟨hs, -⟩ | ⟨-, hq⟩
  · rw [h.loadInt_none ha hn] at hs
    cases hs
  · exact hq

/-- **A combined load at a mapped slot is served by the private memory.** -/
theorem private_of_mapped_load {d : Mem 64} {a : BitVec 64} {n : Nat} (hs : (Mem.loadInt d a n).isSome = true)
    {R : Int → Prop} {Q : Prop} (hc : (∃ v, Mem.loadInt d a n = some v ∧ R v) ∨ (Mem.loadInt d a n = none ∧ Q)) :
    ∃ v, Mem.loadInt d a n = some v ∧ R v := by
  rcases hc with h | ⟨hn, -⟩
  · exact h
  · rw [hn] at hs
    cases hs

/-- **A combined store at a mapped slot is served by the private memory.** -/
theorem private_of_mapped_store {d : Mem 64} {a : BitVec 64} {n : Nat} (hs : (Mem.loadInt d a n).isSome = true)
    {R Q : Prop} (hc : ((Mem.loadInt d a n).isSome = true ∧ R) ∨ (Mem.loadInt d a n = none ∧ Q)) : R := by
  rcases hc with ⟨-, h⟩ | ⟨hn, -⟩
  · exact h
  · rw [hn] at hs
    cases hs

end Kraken.DStack
