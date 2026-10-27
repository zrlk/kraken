/-
**The allocator's arena from the placement check** (AArch64): an output
passing `placeOKAt` at a layout `Λ` gives the arena `arOf Λ` (the heap
arena's base `Λ.heap.lo`, `allocCells` cells, the counter at `heapUseOf Λ`,
no trace words in a header) and every premise the allocation-capable
consumer asks of it (`correctKA`'s `hok`, `hsub`, `hal`, `hz0`, `hc0`), with
no layout constant.

- `arOf`: the arena.
- `CtrZ`: the output's `.bss`/`.data` give `scc_rt_heap_use` an all-zero
  item of at least a word (a fact of the emitted sections, not of the
  layout; the runtime's `.bss` has it).
- From A1/A2/A8 (`placeOKAt`):
  - `ctr_data_of_placeOKAt`: the counter lies in `.data` (A2's `imageOk` places the
    symbol's item there), and no image word meets it (`ctr_noImage_of_placeOKAt`);
  - `arOf_ok`: `Arena.OK` (the counter off the arena: `.data` and the heap are
    disjoint, A1);
  - `arOf_sub`, `arOf_al`, `arOf_lt`: the arena in the heap region (A8's
    `heapSizeOk`), 16-aligned (A1), below `2 ^ 64`;
  - `arOf_init`: no initial word of the canonical load in the arena or at the
    counter (`ArenaInit.arenaInitOk`): the image is in `.data` off the counter,
    the `.rodata` words in `.rodata`, clear of the regions (A2's `rodataFits`);
  - `arOf_z0`, `arOf_c0`: so the arena and the counter start at `0`;
  - `arOf_heapLab`, `arOf_ctrLab`: `scc_rt_heap` and `scc_rt_heap_use` label the arena's
    base and counter in the loaded thread (A8's `heapOk`).
- Each holds at `{ Λ with static := s, imms := i }` as well (`placeOKAt_static`).
-/
import Spike.Lib.Arena
import Spike.Lib.ArenaInit
import Spike.Lib.LowerA64.ArenaOfPlaceOK
import Scc.Cert.Rt.RtInitA64

namespace Spike.Lib.A64.Rt

open Kraken.Promising
open Scc.Sem (Range wordLoc Entry)
open Scc.Cert.PlaceOK (allocCells heapUseOf heapUseSym)
open Scc.Cert.PlaceOK.A64 (placeOKAt)
open Scc.Cert.Link (symItems allZero itemLen imageOk symRanges mem_symRanges special)
open Spike.Lib (Arena)

/-- **The allocator's arena of the layout `Λ`**: at the heap arena's base,
of `allocCells` 16-byte cells, the counter at `scc_rt_heap_use`'s address,
no trace words in a header. -/
def arOf (Λ : Scc.Sem.Layout) : Arena := Arena.ofWords Λ.heap.lo allocCells (heapUseOf Λ) (fun _ => 0)

/-- **The counter's item is a zeroed word** in the output's `.bss`/`.data`:
`scc_rt_heap_use` labels an all-zero item of at least 8 bytes. -/
def CtrZ (o : Scc.Cert.PlaceOK.A64.Out) : Prop :=
  ∃ its, (heapUseSym, its) ∈ symItems (o.secs.bss ++ o.secs.data) ∧ allZero its = true ∧ 8 ≤ itemLen its

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}

/-- The counter's symbol is not one of the regions' own. -/
theorem special_heapUse : special heapUseSym = false := by decide

/-- **The counter's item lies in `.data`, no image word meeting it** (A2's
`imageOk`). -/
theorem ctr_item_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    Λ.data.lo ≤ heapUseOf Λ ∧ heapUseOf Λ + 8 ≤ Λ.data.lo + Λ.data.size ∧
      ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 := by
  obtain ⟨its, hx, hz, h8⟩ := hc
  have himg := Scc.Cert.PlaceOK.A64.imageIn_of_placeOKAt h
  simp only [Scc.Cert.Link.A64.imageIn, imageOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at himg
  obtain ⟨⟨hres, hok⟩, -⟩ := himg
  have := hres _ hx
  simp only [special_heapUse, Bool.false_or, Option.isSome_iff_exists] at this
  obtain ⟨a, ha⟩ := this
  have hu : heapUseOf Λ = a := by simp [heapUseOf, ha]
  obtain ⟨⟨hs, hlo⟩, hhi⟩ := hok _ (mem_symRanges.mpr ⟨hx, special_heapUse, ha⟩)
  simp only [Scc.Cert.Link.symOk, hz, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hs
  dsimp only at hlo hhi hs
  rw [hu]
  refine ⟨hlo, by omega, fun p hp => ?_⟩
  have := hs p hp
  omega

/-- **The counter lies in `.data`.** -/
theorem ctr_data_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) : Λ.data.contains (heapUseOf Λ) := by
  obtain ⟨h1, h2, -⟩ := ctr_item_of_placeOKAt h hc
  exact ⟨h1, by omega⟩

/-- **No image word meets the counter's word.** -/
theorem ctr_noImage_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 :=
  (ctr_item_of_placeOKAt h hc).2.2

/-- The `.data` region and the heap are disjoint (A1). -/
theorem data_heap_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.data.Disjoint Λ.heap :=
  (Scc.Cert.PlaceOK.A64.wf_of_placeOKAt h).disjoint.2.2.2.1

/-- `.data` ends below `2 ^ 32` (A1). -/
theorem data_below_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.data.lo + Λ.data.size ≤ 2 ^ 32 :=
  Scc.Cert.PlaceOK.A64.below32_of_placeOKAt h _ (by simp [Scc.Sem.Layout.regions])

/-- The heap ends below `2 ^ 32` (A1). -/
theorem heap_below_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.heap.lo + Λ.heap.size ≤ 2 ^ 32 :=
  Scc.Cert.PlaceOK.A64.below32_of_placeOKAt h _ (by simp [Scc.Sem.Layout.regions])

/-- **The counter is off the arena.** -/
theorem ctr_out_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    ¬ (Λ.heap.lo ≤ heapUseOf Λ ∧ heapUseOf Λ < Λ.heap.lo + 16 * allocCells) := by
  have hd := ctr_data_of_placeOKAt h hc
  have hj := data_heap_of_placeOKAt h
  have hs := Scc.Cert.PlaceOK.A64.heapSize_of_placeOKAt h
  simp only [Range.contains, Range.Disjoint] at hd hj
  omega

/-- **`hok`: the arena's facts.** -/
theorem arOf_ok (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) : (arOf Λ).OK :=
  Arena.ofWords_ok (ctr_out_of_placeOKAt h hc) (by decide)
    (by have := ctr_data_of_placeOKAt h hc; have := data_below_of_placeOKAt h
        simp only [Range.contains] at *; omega)
    fun _ _ _ => Nat.zero_le _

/-- **`hsub`: the arena lies in the heap region** (A8's `heapSizeOk`). -/
theorem arOf_sub (h : placeOKAt cfg Λ o = true) : (Range.mk (arOf Λ).heap (16 * (arOf Λ).cells)).Sub Λ.heap :=
  ⟨Nat.le_refl _, by have := Scc.Cert.PlaceOK.A64.heapSize_of_placeOKAt h; simp only [arOf, Arena.ofWords]; omega⟩

/-- **`hal`: the arena is 16-aligned** (A1). -/
theorem arOf_al (h : placeOKAt cfg Λ o = true) : (arOf Λ).heap % 16 = 0 :=
  (Scc.Cert.PlaceOK.A64.wf_of_placeOKAt h).aligned _ (by simp [Scc.Sem.Layout.regions])

/-- **The arena lies below `2 ^ 64`.** -/
theorem arOf_lt (h : placeOKAt cfg Λ o = true) : (arOf Λ).heap + 16 * (arOf Λ).cells ≤ 2 ^ 64 :=
  Nat.le_of_lt (Scc.Cert.PlaceOK.A64.arena_end_lt_of_placeOKAt h)

/-- A word of an image at `base` starts in the image's bytes. -/
theorem mem_words {base : Nat} {img : List UInt8} {p : Nat × Nat} (hp : p ∈ Kraken.DataImage.words base img) :
    base ≤ p.1 ∧ p.1 < base + img.length := by
  obtain ⟨⟨j, hj, he⟩, -⟩ := Kraken.DataImage.wordsN_mem _ _ _ p hp
  omega

/-- **A `.rodata` word starts in `.rodata`'s image**, which then is
non-empty and fits `Λ.rodata` (A2's `rodataFits`). -/
theorem rodataWord_of_placeOKAt (h : placeOKAt cfg Λ o = true) {p : Nat × Nat}
    (hp : p ∈ Scc.Sem.rodataWords Λ o.secs.rodata (Scc.Cert.Link.A64.quadCode Λ o.prog)) :
    Λ.rodata.lo ≤ p.1 ∧ p.1 < Λ.rodata.lo + Λ.rodata.size ∧
      ∀ r ∈ Λ.regions, r.lo + r.size ≤ Λ.rodata.lo ∨ Λ.rodata.lo + Λ.rodata.size ≤ r.lo := by
  have hl := Scc.Cert.PlaceOK.A64.loadOk_of_placeOKAt h
  simp only [Scc.Cert.Link.A64.loadOk, Bool.and_eq_true] at hl
  have hf := hl.1.1.1.1.1.1.1
  simp only [Scc.Sem.rodataFits, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff,
    List.all_eq_true] at hf
  obtain ⟨⟨-, hend⟩, hne⟩ := hf
  unfold Scc.Sem.rodataWords at hp
  have hw := mem_words hp
  have hlen := Kraken.DataImage.image_length
    (Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((Scc.Cert.Link.A64.quadCode Λ o.prog l).getD 0))
      Λ.rodata.lo o.secs.rodata) Λ.rodata.lo o.secs.rodata
  rcases hne with he | ⟨-, hr⟩
  · rw [he] at hp
    simp [Kraken.DataImage.image, Kraken.DataImage.words, Kraken.DataImage.wordsN] at hp
  · refine ⟨hw.1, by omega, fun r hr' => ?_⟩
    have := hr r hr'
    simpa using this

/-- An address below `2 ^ 64` read back from its 64-bit word. -/
theorem toNat_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt ha

/-- **No initial word of the canonical load in the arena or at the
counter**: the image is in `.data` (A1), off the counter (A2's `imageOk`);
the `.rodata` words in `.rodata`, clear of the regions (A2's `rodataFits`). -/
theorem arOf_init (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    Spike.Lib.ArenaInit.arenaInitOk (Scc.Cert.Rt.A64.initOf Λ o.prog o.secs) (arOf Λ).heap (arOf Λ).cells
      (arOf Λ).ctr = true := by
  have hwf := Scc.Cert.PlaceOK.A64.wf_of_placeOKAt h
  have hd := ctr_data_of_placeOKAt h hc
  have hdb := data_below_of_placeOKAt h
  have hhb := heap_below_of_placeOKAt h
  have hj := data_heap_of_placeOKAt h
  have hs := Scc.Cert.PlaceOK.A64.heapSize_of_placeOKAt h
  have hni := ctr_noImage_of_placeOKAt h hc
  simp only [Range.contains, Range.Disjoint] at hd hj
  simp only [Spike.Lib.ArenaInit.arenaInitOk, List.all_eq_true]
  intro e he
  simp only [arOf, Arena.ofWords]
  -- the entry's address `a`, off the heap and the counter
  suffices hx : ∃ a, e.1 = ⟨BitVec.ofNat 64 a, 8⟩ ∧ a < 2 ^ 32 ∧
      ¬ (Λ.heap.lo ≤ a ∧ a < Λ.heap.lo + Λ.heap.size) ∧ a ≠ heapUseOf Λ by
    obtain ⟨a, hea, ha32, hah, hac⟩ := hx
    have hat : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_of_lt (by omega)
    rw [hea]
    simp only [hat, wordLoc, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨by omega, fun heq => hac ?_⟩
    have h2 := congrArg (fun l : Loc => l.addr.toNat) heq
    simp only [hat, toNat_ofNat_of_lt (show heapUseOf Λ < 2 ^ 64 by omega)] at h2
    exact h2
  simp only [Scc.Cert.Rt.A64.initOf, List.mem_append, Scc.Sem.A64.imageMem, Scc.Sem.A64.wordsMem,
    List.mem_map] at he
  rcases he with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · obtain ⟨⟨hp1, hp2⟩, -, -⟩ := hwf.image p hp
    have := hni p hp
    exact ⟨p.1, rfl, by omega, by omega, by omega⟩
  · obtain ⟨hr1, hr2, hr⟩ := rodataWord_of_placeOKAt h hp
    have hrb := Scc.Cert.PlaceOK.A64.below32_of_placeOKAt h Λ.rodata (List.mem_cons_self ..)
    have hh := hr Λ.heap (by simp [Scc.Sem.Layout.regions])
    have hdd := hr Λ.data (by simp [Scc.Sem.Layout.regions])
    exact ⟨p.1, rfl, by omega, by omega, by omega⟩

/-- **`hz0`: the arena starts zero** in a memory with the canonical load's
initial words. -/
theorem arOf_z0 (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.A64.initOf Λ o.prog o.secs) {a : Nat}
    (ha : (Spike.Lib.AllocRow.freeR (arOf Λ).heap (arOf Λ).cells 0).contains a) : m.initVal (wordLoc a) = 0 :=
  Spike.Lib.ArenaInit.initVal_arena (by rw [hm]; exact arOf_init h hc) (arOf_lt h) ha

/-- **`hc0`: the counter starts at `0`** in a memory with the canonical
load's initial words. -/
theorem arOf_c0 (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.A64.initOf Λ o.prog o.secs) : m.initVal (wordLoc (arOf Λ).ctr) = 0 :=
  Spike.Lib.ArenaInit.initVal_ctr (by rw [hm]; exact arOf_init h hc)

/-- **`scc_rt_heap` labels the arena's base** in the loaded thread (A8). -/
theorem arOf_heapLab (h : placeOKAt cfg Λ o = true) (E : Entry) :
    ((_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label
        Scc.Cert.Link.heapSym).toBitVec.toNat = (arOf Λ).heap :=
  Scc.Cert.PlaceOK.A64.heapLab_toNat_of_placeOKAt h E

/-- **`scc_rt_heap_use` labels the arena's counter** in the loaded thread (A8). -/
theorem arOf_ctrLab (h : placeOKAt cfg Λ o = true) (E : Entry) :
    ((_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label
        heapUseSym).toBitVec = BitVec.ofNat 64 (arOf Λ).ctr :=
  Scc.Cert.PlaceOK.A64.heapUseLab_of_placeOKAt h E

/-- info: 'Spike.Lib.A64.Rt.ctr_data_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctr_data_of_placeOKAt

/-- info: 'Spike.Lib.A64.Rt.arOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_ok

/-- info: 'Spike.Lib.A64.Rt.arOf_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_sub

/-- info: 'Spike.Lib.A64.Rt.arOf_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_al

/-- info: 'Spike.Lib.A64.Rt.arOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_lt

/-- info: 'Spike.Lib.A64.Rt.arOf_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_init

/-- info: 'Spike.Lib.A64.Rt.arOf_z0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_z0

/-- info: 'Spike.Lib.A64.Rt.arOf_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_c0

/-- info: 'Spike.Lib.A64.Rt.arOf_heapLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_heapLab

/-- info: 'Spike.Lib.A64.Rt.arOf_ctrLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_ctrLab

end Spike.Lib.A64.Rt
