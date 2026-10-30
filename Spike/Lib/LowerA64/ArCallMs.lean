/-
**The allocator's memory-side premises at the arena of a placed output**
(AArch64): at the rows' memory side `msOfAX … (arOf Λ) …` over a layout `Λ`
passing `placeOKAt`, the call's memory-side fields `CallMsOK` (at no placed
label, a header with no trace words), and `allocW2At_of`'s word premises
`hmem`, `hno`, `hlt`, `h64`, from the placement check alone.

The counter `heapUseOf Λ` is a word of `.data` (`ctr_item_of_placeOKAt`),
below the heap (`dataBelow_of_placeOKAt`); a header `heap + 16 · o` of a
call fitting the cells is a word of the heap (`heapSize_of_placeOKAt`).
Both are mapped in `K0` and shared; the runtime's words are neither
(`hctr_of_placeOKAt`, `ne_rtWord_of_heap`).

- `arOf_units_pos`, `arOf_off_eq`: the arena's units of a call with
  accesses are positive, its offset one header word;
- `ctr_bytes_arOf`, `hdr_bytes_arOf`: the counter's bytes in `.data`, a
  fitting header's in the heap;
- `callMsOK_arOf`: `CallMsOK` at `msOfAX … (arOf Λ) … (fun _ => none)`, the
  value invariant `G` free at the counter and at the heap's words;
- `gOf_ctr_arOf`, `gOf_heap_arOf`: `PhRec.GOf`'s two premises;
- `hmem_arOf`, `hno_arOf`, `hlt_arOf`, `h64_arOf`: `allocW2At_of`'s word
  premises.
-/
import Spike.Lib.LowerA64.AllocW2AtOf
import Spike.Lib.LowerA64.HeapW
import Spike.Lib.A64WordsNone
import Spike.Lib.A64StartOfPlaceOK

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Spike.Lib (Arena)
open Spike.Lib.A64Consumer (K0 Lbl Lsize)
open Spike.Lib.A64ConsumerS (OwnS InvS)
open Spike.Lib.A64ConsumerA (msOfAX msOfA)
open Spike.Lib.A64.Alloc (Call mOf)
open Spike.Lib.A64.Rt (RuntimeLayout arOf CtrZ)
open Spike.Lib.DmemPriv (WordsNone)
open Scc.Cert.PlaceOK (allocCells heapUseOf)
open Scc.Cert.PlaceOK.A64 (placeOKAt)

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}

/-! ## The arena's units and offset -/

/-- **A call with accesses takes at least one unit** of the arena. -/
theorem arOf_units_pos {n : Nat} {τ : Ty} (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us) :
    1 ≤ (arOf Λ).units n τ := by
  obtain ⟨us, hus⟩ := hacc
  simp only [arOf, Arena.ofWords, hus]
  split <;> omega

/-- **The arena's offset of a call with accesses is one header word** (no
trace words). -/
theorem arOf_off_eq {n : Nat} {τ : Ty} (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us) :
    (arOf Λ).off n τ = 8 := by
  obtain ⟨us, hus⟩ := hacc
  simp only [arOf, Arena.ofWords, hus, Nat.mul_zero]

/-! ## The counter's and the headers' bytes -/

/-- **The counter's eight bytes lie in `.data`**, its address below `2 ^ 32`. -/
theorem ctr_bytes_arOf (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    (BitVec.ofNat 64 (arOf Λ).ctr).toNat = heapUseOf Λ ∧
      ∀ i < 8, Λ.data.contains ((BitVec.ofNat 64 (arOf Λ).ctr).toNat + i) := by
  obtain ⟨h1, h2, -⟩ := Spike.Lib.A64.Rt.ctr_item_of_placeOKAt h hc
  have hb := Spike.Lib.A64.Rt.data_below_of_placeOKAt h
  have e : (BitVec.ofNat 64 (arOf Λ).ctr).toNat = heapUseOf Λ := by
    show (BitVec.ofNat 64 (heapUseOf Λ)).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨e, fun i hi => ?_⟩
  rw [e]; unfold Range.contains; omega

/-- **A fitting header's eight bytes lie in the heap**: at a memory side
with the arena's base, a call with no trace-word offset (`hnm`) and at
least one unit, its header for an old count `o` within the cells. -/
theorem hdr_bytes_arOf (h : placeOKAt cfg Λ o = true) {ms : MemSide isaLSE2} (hheap : ms.heap = Λ.heap.lo)
    {q : Call} (hnm : q.n * (mOf q.h).toNat = 0) (hu1 : 1 ≤ (arOf Λ).units q.n q.τ) {o' : Nat}
    (ho : o' + (arOf Λ).units q.n q.τ ≤ (arOf Λ).cells) :
    (BitVec.ofNat 64 (q.hdrAt ms o')).toNat = q.hdrAt ms o' ∧
      ∀ i < 8, Λ.heap.contains ((BitVec.ofNat 64 (q.hdrAt ms o')).toNat + i) := by
  have hs := Scc.Cert.PlaceOK.A64.heapSize_of_placeOKAt h
  have hb := Spike.Lib.A64.Rt.heap_below_of_placeOKAt h
  have hcl : (arOf Λ).cells = allocCells := rfl
  have hA : allocCells = 4194304 := rfl
  have e1 : q.hdrAt ms o' = Λ.heap.lo + 16 * o' := by
    simp only [Call.hdrAt, hheap, hnm, Nat.mul_zero, Nat.add_zero]
  have e : (BitVec.ofNat 64 (q.hdrAt ms o')).toNat = q.hdrAt ms o' := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨e, fun i hi => ?_⟩
  rw [e, e1]; unfold Range.contains; omega

/-! ## `CallMsOK` at the arena -/

variable {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS} {I : InvS}
  {ls : Lsize} {fs : List TermRun.Frame}

/-- **`CallMsOK` at `msOfA` over the arena `arOf Λ`** at no placed label (the
`ab = none` case of `callMsOK_arOf`). -/
theorem callMsOK_arOfA (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) (E : Entry)
    (hGc : ∀ v, G ⟨BitVec.ofNat 64 (arOf Λ).ctr, 8⟩ v)
    (hGh : ∀ a : BitVec 64, (∀ i < 8, Λ.heap.contains (a.toNat + i)) → ∀ v, G ⟨a, 8⟩ v)
    {q : Call} (hacc : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us) (hm : (mOf q.h).toNat = 0) :
    CallMsOK (msOfA Λ μ rd G own (arOf Λ) I (fun _ => none) ls fs)
      (_root_.Executable.labels
        (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label q := by
  obtain ⟨ec, hcb⟩ := ctr_bytes_arOf h hc
  have hu1 : 1 ≤ (arOf Λ).units q.n q.τ := arOf_units_pos hacc
  have hnm : q.n * (mOf q.h).toNat = 0 := by rw [hm, Nat.mul_zero]
  have hrt : ∀ a : Nat, (msOfA Λ μ rd G own (arOf Λ) I (fun _ => none) ls fs).rt a := by
    rintro a ⟨l, b, hl, -⟩; cases hl
  refine ⟨Spike.Lib.A64.Rt.arOf_ctrLab h E, Spike.Lib.A64.Rt.arOf_heapLab h E,
    Scc.Cert.PlaceOK.A64.heapRoom_of_placeOKAt h, rfl, ?_, ?_, hrt _, ?_, fun _ _ _ => hGc _, ?_⟩
  · obtain ⟨us, hus⟩ := hacc
    show (arOf Λ).units q.n q.τ < 2 ^ 63
    simp only [arOf, Arena.ofWords, hus]
    split <;> omega
  · show (arOf Λ).off q.n q.τ = _
    rw [arOf_off_eq hacc, hnm]
  · refine ⟨Spike.Lib.A64Consumer.mapped_K0_of_mem fun i hi => .inl (hcb i hi), fun _ i hi => ?_⟩
    exact .inl (hcb i (by simpa [Kernel.locBytes] using hi))
  · intro o' _ ho
    obtain ⟨-, hhb⟩ := hdr_bytes_arOf h (ms := msOfA Λ μ rd G own (arOf Λ) I (fun _ => none) ls fs) rfl hnm hu1 ho
    exact ⟨hrt _, ⟨mapped_K0_of_heap hhb, fun _ i hi => .inr (.inl (hhb i (by simpa [Kernel.locBytes] using hi)))⟩,
      hGh _ hhb _⟩

/-- **`CallMsOK` at the rows' memory side over the arena `arOf Λ`** at no
placed label, at either write abort phase `ab`: the counter's and the
arena's labels and room from the placement check (`arOf_ctrLab`,
`arOf_heapLab`, `heapRoom_of_placeOKAt`), the units saturating below
`2 ^ 63`, the offset one header word (`hm`: no trace words in the header),
the counter in `.data` and a fitting header in the heap, mapped and
shared, the value invariant free there (`hGc`, `hGh`). -/
theorem callMsOK_arOf (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) (E : Entry) (ab : Option (State → Prop))
    (hGc : ∀ v, G ⟨BitVec.ofNat 64 (arOf Λ).ctr, 8⟩ v)
    (hGh : ∀ a : BitVec 64, (∀ i < 8, Λ.heap.contains (a.toNat + i)) → ∀ v, G ⟨a, 8⟩ v)
    {q : Call} (hacc : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us) (hm : (mOf q.h).toNat = 0) :
    CallMsOK (msOfAX Λ μ p rd G own (arOf Λ) I ab (fun _ => none) ls fs)
      (_root_.Executable.labels
        (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label q := by
  have H := callMsOK_arOfA (μ := μ) (rd := rd) (own := own) (I := I) (ls := ls) (fs := fs) h hc E hGc hGh hacc hm
  cases ab <;> exact ⟨H.ctr, H.heap, H.room, H.cells, H.units, H.off, H.rt, H.mp, H.grow, H.hdr⟩

/-! ## The value invariant `GOf` -/

/-- **`GOf` is free at the counter** (the counter is no runtime word,
`hctr_of_placeOKAt`, so not the limit word). -/
theorem gOf_ctr_arOf (h : placeOKAt cfg Λ o = true) (i : Expr → String → Nat → Option Nat) (m0 : Memory) :
    ∀ v, Spike.Lib.A64.PhRec.GOf (RuntimeLayout.ofPlaceOK h i) m0
      ⟨BitVec.ofNat 64 (arOf (RuntimeLayout.ofPlaceOK h i).Λ).ctr, 8⟩ v := by
  refine Spike.Lib.A64.PhRec.gOf_ne fun he => ?_
  exact RuntimeLayout.hctr_of_placeOKAt h i _ ((RuntimeLayout.ofPlaceOK h i).fld_mem (i := 1) (by decide))
    (congrArg (fun a => (⟨a, 8⟩ : Loc)) he.symm)

/-- **`GOf` is free at the heap's words** (a heap word is no runtime word,
`ne_rtWord_of_heap`, so not the limit word). -/
theorem gOf_heap_arOf (h : placeOKAt cfg Λ o = true) (i : Expr → String → Nat → Option Nat) (m0 : Memory) :
    ∀ a : BitVec 64, (∀ k < 8, (RuntimeLayout.ofPlaceOK h i).Λ.heap.contains (a.toNat + k)) →
      ∀ v, Spike.Lib.A64.PhRec.GOf (RuntimeLayout.ofPlaceOK h i) m0 ⟨a, 8⟩ v := by
  intro a ha
  have hd := (Scc.Cert.PlaceOK.A64.wf_of_placeOKAt h).disjoint
  exact Spike.Lib.A64.PhRec.gOf_ne (ne_rtWord_of_heap _ hd.2.2.2.1 hd.2.2.2.2.2.2.2.2.1 ha
    ((RuntimeLayout.ofPlaceOK h i).fld_mem (i := 1) (by decide)))

/-! ## `allocW2At_of`'s word premises -/

/-- **A call's header address at a memory side over `arOf Λ`** is a heap
word when it fits: `q.OK` gives the offset `8 · (n · m) + 8`, the arena's is
`8` (`arOf_off_eq`), so the header has no trace-word offset. -/
theorem hdr_bytes_ofOK (h : placeOKAt cfg Λ o = true) {ms : MemSide isaLSE2} {lab : Label → Int64}
    (hheap : ms.heap = Λ.heap.lo) (hoff : ms.off = (arOf Λ).off) {q : Call} (hq : q.OK ms lab) {o' : Nat}
    (ho : o' + (arOf Λ).units q.n q.τ ≤ (arOf Λ).cells) :
    (BitVec.ofNat 64 (q.hdrAt ms o')).toNat = q.hdrAt ms o' ∧
      ∀ i < 8, Λ.heap.contains ((BitVec.ofNat 64 (q.hdrAt ms o')).toNat + i) := by
  have h1 := hq.off
  rw [hoff, arOf_off_eq hq.accs] at h1
  exact hdr_bytes_arOf h hheap (by omega) (arOf_units_pos hq.accs) ho

/-- **`hmem` at a memory side over `arOf Λ`** from a frame loading no heap
or `.data` word (`hmem_of_wordsNone`). -/
theorem hmem_arOf (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) {F : MachineData → Prop}
    (hwn : ∀ m, F m → WordsNone Λ m.dmem) {ms : MemSide isaLSE2} {lab : Label → Int64}
    (hheap : ms.heap = Λ.heap.lo) (hcl : ms.cells = allocCells) (hct : ms.ctr = heapUseOf Λ)
    (hun : ms.units = (arOf Λ).units) (hoff : ms.off = (arOf Λ).off) :
    ∀ q : Call, q.OK ms lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none := by
  have hs := Scc.Cert.PlaceOK.A64.heapSize_of_placeOKAt h
  obtain ⟨h1, h2, -⟩ := Spike.Lib.A64.Rt.ctr_item_of_placeOKAt h hc
  refine Spike.Lib.A64.Alloc.hmem_of_wordsNone (Scc.Cert.PlaceOK.A64.wf_of_placeOKAt h) hwn (by omega)
    (by rw [hheap, hcl]; omega) (.inr ?_) fun q hq => ?_
  · rw [hct]; unfold Spike.Lib.DmemPriv.WordIn Range.contains; omega
  · rw [hoff, hun, arOf_off_eq hq.accs]; have := arOf_units_pos (Λ := Λ) (n := q.n) hq.accs; omega

/-- **`hno`: neither the counter nor a fitting header is an owned word**
(`PhRec.ownOf`'s words are runtime words: off the counter,
`hctr_of_placeOKAt`, and off the heap, `ne_rtWord_of_heap`). -/
theorem hno_arOf (h : placeOKAt cfg Λ o = true) (i : Expr → String → Nat → Option Nat) {ms : MemSide isaLSE2}
    {lab : Label → Int64} (hheap : ms.heap = Λ.heap.lo) (hoff : ms.off = (arOf Λ).off) :
    ∀ q : Call, q.OK ms lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (arOf Λ).ctr ∨ ∃ o, o + (arOf Λ).units q.n q.τ ≤ (arOf Λ).cells ∧
        a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ Spike.Lib.A64.PhRec.ownOf (RuntimeLayout.ofPlaceOK h i) j := by
  intro q hq a ha j w hm
  have hne : ∀ b ∈ (RuntimeLayout.ofPlaceOK h i).rtWords, a ≠ b := by
    rcases ha with rfl | ⟨o', ho, ha⟩
    · intro b hb he
      exact RuntimeLayout.hctr_of_placeOKAt h i b hb (by rw [← he]; rfl)
    · obtain ⟨e, hhb⟩ := hdr_bytes_ofOK h hheap hoff hq ho
      have hd := (Scc.Cert.PlaceOK.A64.wf_of_placeOKAt h).disjoint
      intro b hb
      refine ne_rtWord_of_heap _ hd.2.2.2.1 hd.2.2.2.2.2.2.2.2.1 (fun k hk => ?_) hb
      have := hhb k hk; rw [e, ← ha] at this; exact this
  let L := RuntimeLayout.ofPlaceOK h i
  unfold Spike.Lib.A64.PhRec.ownOf at hm
  simp only [List.mem_cons, Prod.mk.injEq, Loc.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩
  · exact hne _ L.pn_mem e
  · exact hne _ L.lock_mem e
  · exact hne _ L.freeN_mem e
  · exact hne _ L.next_mem e

/-- **`hlt`: the counter's word lies below the arena** (`.data` below the
heap). -/
theorem hlt_arOf (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) : (arOf Λ).ctr + 8 ≤ (arOf Λ).heap := by
  obtain ⟨-, h2, -⟩ := Spike.Lib.A64.Rt.ctr_item_of_placeOKAt h hc
  have := Scc.Cert.PlaceOK.A64.dataBelow_of_placeOKAt h
  show heapUseOf Λ + 8 ≤ Λ.heap.lo
  omega

/-- **`h64`: the counter is an address.** -/
theorem h64_arOf (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) : (arOf Λ).ctr < 2 ^ 64 := by
  obtain ⟨-, h2, -⟩ := Spike.Lib.A64.Rt.ctr_item_of_placeOKAt h hc
  have := Spike.Lib.A64.Rt.data_below_of_placeOKAt h
  show heapUseOf Λ < 2 ^ 64
  omega

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.callMsOK_arOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callMsOK_arOf

/-- info: 'Spike.Lib.LowerA64.gOf_ctr_arOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.gOf_ctr_arOf

/-- info: 'Spike.Lib.LowerA64.gOf_heap_arOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.gOf_heap_arOf

/-- info: 'Spike.Lib.LowerA64.hmem_arOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hmem_arOf

/-- info: 'Spike.Lib.LowerA64.hno_arOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hno_arOf

/-- info: 'Spike.Lib.LowerA64.hlt_arOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hlt_arOf

/-- info: 'Spike.Lib.LowerA64.h64_arOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.h64_arOf
