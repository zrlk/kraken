/-
**A lane store's element word is a heap word** (AArch64; the twin of
`Spike/Lib/LowerX64/HeapWOf.lean`): at an output passing `placeOKAt`, with
every placed label inside the allocator's arena (`LblArena`) and the frame
condition's states loading no heap or `.data` word (`WordsNone`), the word
`k < lsize l` of a placed label `l` is mapped for reading and writing in the
loaded kernel state, owned at no state (the runtime's counters lie in `data`
or `pinned`, disjoint from the heap), a word of the label, not the arena's
counter, and unmapped in the frame condition's private memory (`HeapW`).

- `HeapW`: the element's word at a lane store (the x86-64 `LowerX64.HeapW`'s
  conjuncts at AArch64's `K0` and owned words);
- `mapped_K0_of_heap`: a word in the heap is mapped in `K0`;
- `ne_rtWord_of_heap`, `not_own_of_heap`: a heap word is no runtime word,
  hence owned at no state (`PhRec.own`);
- `heapW_of`: `HeapW` at the runtime's owned words and `arOf`;
- `heapW_ofReach`: the same at every placement reachable by allocations
  from one placing no label.
-/
import Spike.Lib.A64ConsumerAWr
import Spike.Lib.A64PhRec
import Spike.Lib.Rt.A64ArenaOfPlaceOK
import Spike.Lib.LblArena

namespace Spike.Lib.LowerA64

open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Spike.Lib.A64Consumer (K0 Own Lbl Lsize)
open Spike.Lib.A64.Rt (RuntimeLayout arOf CtrZ)
open Spike.Lib.DmemPriv (WordsNone)
open Scc.Cert.PlaceOK.A64 (placeOKAt)

/-- **The element's word at a lane store** `A`: mapped for reading and
writing in the loaded kernel state, owned at no state, a word of a placed
label (an arena write `ArenaW` allows), not the arena's counter, and
unmapped in the private memory of the frame condition's states. -/
def HeapW (Λ : Scc.Sem.Layout) (own : Own) (ar : Spike.Lib.Arena) (lbl : Lbl) (lsize : Lsize)
    (F : MachineData → Prop) (A : BitVec 64) : Prop :=
  Kernel.mapped (K0 Λ) false ⟨A, 8⟩ = true ∧ Kernel.mapped (K0 Λ) true ⟨A, 8⟩ = true ∧
    (∀ (s : State) w, (⟨A, 8⟩, w) ∉ own s) ∧ (∃ l b, lbl l = some b ∧ (lrange lsize l b).contains A.toNat) ∧
    (⟨A, 8⟩ : Loc) ≠ ar.ctrLoc ∧ ∀ m, F m → Mem.loadInt m.dmem A 8 = none

/-- **A word in the heap is mapped in `K0`**, for reading and writing. -/
theorem mapped_K0_of_heap {Λ : Scc.Sem.Layout} {w : Bool} {a : BitVec 64} (h : ∀ i < 8, Λ.heap.contains (a.toNat + i)) :
    Kernel.mapped (K0 Λ) w ⟨a, 8⟩ = true := by
  unfold Kernel.mapped
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi
  exact ⟨Λ.heap, by simp [Kernel.mappedRegions, K0], h i hi⟩

/-- **A heap word is no runtime word**: the runtime's words lie in `data`
or `pinned` (`words_mapped`), both disjoint from the heap. -/
theorem ne_rtWord_of_heap (L : RuntimeLayout) (hdh : L.Λ.data.Disjoint L.Λ.heap)
    (hhp : L.Λ.heap.Disjoint L.Λ.pinned) {A : BitVec 64} (hA : ∀ i < 8, L.Λ.heap.contains (A.toNat + i))
    {a : BitVec 64} (ha : a ∈ L.rtWords) : A ≠ a := by
  rintro rfl
  have h0 := hA 0 (by omega)
  unfold Range.Disjoint at hdh hhp
  unfold Range.contains at h0
  rcases (L.words_mapped A ha).2.2 0 (by omega) with h | h <;> unfold Range.contains at h <;> omega

/-- **A heap word is owned at no state** (`PhRec.own`: the runtime's
counters). -/
theorem not_own_of_heap (L : RuntimeLayout) (hdh : L.Λ.data.Disjoint L.Λ.heap)
    (hhp : L.Λ.heap.Disjoint L.Λ.pinned) {A : BitVec 64} (hA : ∀ i < 8, L.Λ.heap.contains (A.toNat + i)) :
    ∀ (s : State) w, (⟨A, 8⟩, w) ∉ Spike.Lib.A64.PhRec.own L s := by
  intro s w hm
  have hne := fun {a} (ha : a ∈ L.rtWords) => ne_rtWord_of_heap L hdh hhp hA ha
  unfold Spike.Lib.A64.PhRec.own Spike.Lib.A64.PhRec.ownOf at hm
  simp only [List.mem_cons, Prod.mk.injEq, Loc.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩
  · exact hne L.pn_mem h
  · exact hne L.lock_mem h
  · exact hne L.freeN_mem h
  · exact hne L.next_mem h

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}

/-- **A lane store's element word is a heap word** (`HeapW`) at the
runtime's owned words (`PhRec.own` at `RuntimeLayout.ofPlaceOK`, `own2`'s at
`i = imms2Of p`) and the allocator's arena `arOf`: the word `A = b + 8 · k`
of the label `l` placed at `b`, `k < lsize l`, every placed label inside the
arena (`hla`), the counter's item a zeroed word (`hc`) and the frame
condition's states loading no heap or `.data` word (`hwn`). -/
theorem heapW_of (hpl : placeOKAt cfg Λ o = true) (hc : CtrZ o)
    {i : CoreTerm.Expr → String → Nat → Option Nat} {lbl : Lbl} {lsize : Lsize} {F : MachineData → Prop}
    (hla : LblArena (arOf Λ) lbl lsize) (hwn : ∀ m, F m → WordsNone Λ m.dmem)
    {l : WeakMem.AllocLabel} {b k : Nat} (hl : lbl l = some b) (hk : k < lsize l)
    {A : BitVec 64} (hA : A.toNat = b + 8 * k) :
    HeapW Λ (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK hpl i)) (arOf Λ) lbl lsize F A := by
  have hs := Spike.Lib.A64.Rt.arOf_sub hpl
  have hH := hla.heap hs hl hk hA
  have hW := hla.word hl hk hA
  have hd := (Scc.Cert.PlaceOK.A64.wf_of_placeOKAt hpl).disjoint
  refine ⟨mapped_K0_of_heap hH, mapped_K0_of_heap hH,
    not_own_of_heap (RuntimeLayout.ofPlaceOK hpl i) hd.2.2.2.1 hd.2.2.2.2.2.2.2.2.1 hH,
    ⟨l, b, hl, ?_⟩, Spike.Lib.A64ConsumerA.loc_ne_ctrLoc (Spike.Lib.A64.Rt.arOf_ok hpl hc) (by omega) (by omega),
    fun m hm => Spike.Lib.LowerNode.heapWord_none (hla.lblRange hs) (hwn m hm) hl hk hA⟩
  unfold lrange Range.contains
  simp only
  omega

/--
info: 'Spike.Lib.LowerA64.heapW_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms heapW_of

/-- **`heapW_of` at every placement reachable by allocations** (the lane
stores' `hHW`): from a start placing no label (`hL0`, e.g. `lay2`'s
`static := none`), every reachable placement `lbl`, `lsize` keeps its labels
inside the allocator's arena `arOf` (`LblArena.reach`), so each word
`A = b + 8 · k`, `k < lsize l`, of a placed label `l` is a heap word. -/
theorem heapW_ofReach (hpl : placeOKAt cfg Λ o = true) (hc : CtrZ o)
    {i : CoreTerm.Expr → String → Nat → Option Nat} {F : MachineData → Prop}
    (hwn : ∀ m, F m → WordsNone Λ m.dmem) {L0 : Lbl} {ls0 : Lsize} (hL0 : ∀ l, L0 l = none)
    {lbl : Lbl} {lsize : Lsize} (hR : Spike.Lib.AllocReach.Reach (arOf Λ) L0 ls0 lbl lsize) :
    ∀ l b k (A : BitVec 64), lbl l = some b → k < lsize l → A.toNat = b + 8 * k →
      HeapW Λ (Spike.Lib.A64.PhRec.own (RuntimeLayout.ofPlaceOK hpl i)) (arOf Λ) lbl lsize F A := by
  have h0 : LblArena (arOf Λ) L0 ls0 := fun l b h => by rw [hL0 l] at h; cases h
  exact fun l b k A hl hk hA => heapW_of hpl hc (h0.reach hR) hwn hl hk hA

/--
info: 'Spike.Lib.LowerA64.heapW_ofReach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms heapW_ofReach

end Spike.Lib.LowerA64
