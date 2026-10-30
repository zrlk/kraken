/-
**The allocator's arena at `PlaceW`** (AArch64): `Rt.arOf`'s facts
(`Spike/Lib/Rt/A64ArenaOfPlaceOK.lean`) at an output with wake's placement
facts (`PlaceW`, A1/A2/A8), their proofs the originals' with the
`*_of_placeW` extraction lemmas; the A2/A8 extractions it reads
(`imageIn`, `heapOk`, `heapSize`, `heapLab_toNat`, `heapUseLab`) are
twinned here. The arena's end below `2 ^ 64` is from A1's `below32`
(in place of `arena_end_lt_of_placeOKAt`).

- `ctr_item_of_placeW`, `ctr_data_of_placeW`, `ctr_noImage_of_placeW`,
  `ctr_out_of_placeW`, `data_heap_of_placeW`, `data_below_of_placeW`,
  `heap_below_of_placeW`, `rodataWord_of_placeW`;
- `arOf_ok`, `arOf_sub`, `arOf_al`, `arOf_lt`, `arOf_init`, `arOf_z0`,
  `arOf_c0`, `arOf_heapLab`, `arOf_ctrLab` (namespace `Rt.ArenaW`).
-/
import Spike.Lib.Arena
import Spike.Lib.ArenaInit
import Spike.Lib.LowerA64.ArenaOfPlaceOK
import Scc.Cert.Rt.RtInitA64
import Spike.Lib.Rt.A64ArenaOfPlaceOK
import Spike.Lib.PlaceW

namespace Spike.Lib.A64.Rt.ArenaW

open Kraken.Promising
open Scc.Sem (Range wordLoc Entry)
open Scc.Cert.PlaceOK (allocCells heapUseOf heapUseSym)
open Scc.Cert.Link (symItems allZero itemLen imageOk symRanges mem_symRanges special)
open Spike.Lib (Arena PlaceW)
open Spike.Lib.A64.Rt (arOf CtrZ special_heapUse mem_words toNat_ofNat_of_lt)

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}

/-! ## A2/A8 extraction at `PlaceW` -/

/-- **A2**: the image checks. -/
theorem PlaceW.imageIn_of_placeW (h : PlaceW cfg Λ o) : Scc.Cert.Link.A64.imageIn o.prog o.secs Λ = true := by
  have := h.a2; simp only [Scc.Cert.PlaceOK.A64.a2, Bool.and_eq_true] at this; exact this.2

/-- **A8**: the heap checks. -/
theorem PlaceW.heapOk_of_placeW (h : PlaceW cfg Λ o) : Scc.Cert.PlaceOK.A64.heapOk o Λ = true := by
  have h8 := h.a8; simp only [Scc.Cert.PlaceOK.A64.a8, Bool.and_eq_true] at h8; exact h8.2

/-- **A8**: the arena fits the heap region. -/
theorem PlaceW.heapSize_of_placeW (h : PlaceW cfg Λ o) : 16 * allocCells ≤ Λ.heap.size := by
  have hh := PlaceW.heapOk_of_placeW h
  simp only [Scc.Cert.PlaceOK.A64.heapOk, Bool.and_eq_true] at hh
  exact Scc.Cert.PlaceOK.heapSize_of_heapSizeOk hh.1.2

/-- **A8**: `scc_rt_heap`'s label as a number is the heap arena's base. -/
theorem PlaceW.heapLab_toNat_of_placeW (h : PlaceW cfg Λ o) (E : Entry) :
    ((_root_.Executable.labels (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label
      Scc.Cert.Link.heapSym).toBitVec.toNat = Λ.heap.lo := by
  have hh := PlaceW.heapOk_of_placeW h
  simp only [Scc.Cert.PlaceOK.A64.heapOk, Bool.and_eq_true, decide_eq_true_eq] at hh
  rw [Scc.Cert.Rt.A64.label_threadAt_of_symLab
    (Scc.Cert.Link.A64.symsAround_of_loadOk (PlaceW.loadOk_of_placeW h)) hh.1.1.1]
  have hb := PlaceW.below32_of_placeW h Λ.heap (by simp [Scc.Sem.Layout.regions])
  have e : (Int64.ofNat Λ.heap.lo).toBitVec = BitVec.ofNat 64 Λ.heap.lo := by simp
  rw [e, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- **A8**: `scc_rt_heap_use`'s label is the counter's address. -/
theorem PlaceW.heapUseLab_of_placeW (h : PlaceW cfg Λ o) (E : Entry) :
    ((_root_.Executable.labels (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label
      heapUseSym).toBitVec = BitVec.ofNat 64 (heapUseOf Λ) := by
  have hh := PlaceW.heapOk_of_placeW h
  simp only [Scc.Cert.PlaceOK.A64.heapOk, Bool.and_eq_true, decide_eq_true_eq] at hh
  rw [Scc.Cert.Rt.A64.label_threadAt_of_symLab
    (Scc.Cert.Link.A64.symsAround_of_loadOk (PlaceW.loadOk_of_placeW h)) hh.1.1.2]
  simp

/-- **The counter's item lies in `.data`, no image word meeting it** (A2's
`imageOk`). -/
theorem ctr_item_of_placeW (h : PlaceW cfg Λ o) (hc : CtrZ o) :
    Λ.data.lo ≤ heapUseOf Λ ∧ heapUseOf Λ + 8 ≤ Λ.data.lo + Λ.data.size ∧
      ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 := by
  obtain ⟨its, hx, hz, h8⟩ := hc
  have himg := PlaceW.imageIn_of_placeW h
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
theorem ctr_data_of_placeW (h : PlaceW cfg Λ o) (hc : CtrZ o) : Λ.data.contains (heapUseOf Λ) := by
  obtain ⟨h1, h2, -⟩ := ctr_item_of_placeW h hc
  exact ⟨h1, by omega⟩

/-- **No image word meets the counter's word.** -/
theorem ctr_noImage_of_placeW (h : PlaceW cfg Λ o) (hc : CtrZ o) :
    ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 :=
  (ctr_item_of_placeW h hc).2.2

/-- The `.data` region and the heap are disjoint (A1). -/
theorem data_heap_of_placeW (h : PlaceW cfg Λ o) : Λ.data.Disjoint Λ.heap :=
  (PlaceW.wf_of_placeW h).disjoint.2.2.2.1

/-- `.data` ends below `2 ^ 32` (A1). -/
theorem data_below_of_placeW (h : PlaceW cfg Λ o) : Λ.data.lo + Λ.data.size ≤ 2 ^ 32 :=
  PlaceW.below32_of_placeW h _ (by simp [Scc.Sem.Layout.regions])

/-- The heap ends below `2 ^ 32` (A1). -/
theorem heap_below_of_placeW (h : PlaceW cfg Λ o) : Λ.heap.lo + Λ.heap.size ≤ 2 ^ 32 :=
  PlaceW.below32_of_placeW h _ (by simp [Scc.Sem.Layout.regions])

/-- **The counter is off the arena.** -/
theorem ctr_out_of_placeW (h : PlaceW cfg Λ o) (hc : CtrZ o) :
    ¬ (Λ.heap.lo ≤ heapUseOf Λ ∧ heapUseOf Λ < Λ.heap.lo + 16 * allocCells) := by
  have hd := ctr_data_of_placeW h hc
  have hj := data_heap_of_placeW h
  have hs := PlaceW.heapSize_of_placeW h
  simp only [Range.contains, Range.Disjoint] at hd hj
  omega

/-- **`hok`: the arena's facts.** -/
theorem arOf_ok (h : PlaceW cfg Λ o) (hc : CtrZ o) : (arOf Λ).OK :=
  Arena.ofWords_ok (ctr_out_of_placeW h hc) (by decide)
    (by have := ctr_data_of_placeW h hc; have := data_below_of_placeW h
        simp only [Range.contains] at *; omega)
    fun _ _ _ => Nat.zero_le _

/-- **`hsub`: the arena lies in the heap region** (A8's `heapSizeOk`). -/
theorem arOf_sub (h : PlaceW cfg Λ o) : (Range.mk (arOf Λ).heap (16 * (arOf Λ).cells)).Sub Λ.heap :=
  ⟨Nat.le_refl _, by have := PlaceW.heapSize_of_placeW h; simp only [arOf, Arena.ofWords]; omega⟩

/-- **`hal`: the arena is 16-aligned** (A1). -/
theorem arOf_al (h : PlaceW cfg Λ o) : (arOf Λ).heap % 16 = 0 :=
  (PlaceW.wf_of_placeW h).aligned _ (by simp [Scc.Sem.Layout.regions])

/-- **The arena lies below `2 ^ 64`.** -/
theorem arOf_lt (h : PlaceW cfg Λ o) : (arOf Λ).heap + 16 * (arOf Λ).cells ≤ 2 ^ 64 :=
  by have := PlaceW.heapSize_of_placeW h; have := heap_below_of_placeW h; simp only [arOf, Arena.ofWords]; omega

/-- **A `.rodata` word starts in `.rodata`'s image**, which then is
non-empty and fits `Λ.rodata` (A2's `rodataFits`). -/
theorem rodataWord_of_placeW (h : PlaceW cfg Λ o) {p : Nat × Nat}
    (hp : p ∈ Scc.Sem.rodataWords Λ o.secs.rodata (Scc.Cert.Link.A64.quadCode Λ o.prog)) :
    Λ.rodata.lo ≤ p.1 ∧ p.1 < Λ.rodata.lo + Λ.rodata.size ∧
      ∀ r ∈ Λ.regions, r.lo + r.size ≤ Λ.rodata.lo ∨ Λ.rodata.lo + Λ.rodata.size ≤ r.lo := by
  have hl := PlaceW.loadOk_of_placeW h
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

/-- **No initial word of the canonical load in the arena or at the
counter**: the image is in `.data` (A1), off the counter (A2's `imageOk`);
the `.rodata` words in `.rodata`, clear of the regions (A2's `rodataFits`). -/
theorem arOf_init (h : PlaceW cfg Λ o) (hc : CtrZ o) :
    Spike.Lib.ArenaInit.arenaInitOk (Scc.Cert.Rt.A64.initOf Λ o.prog o.secs) (arOf Λ).heap (arOf Λ).cells
      (arOf Λ).ctr = true := by
  have hwf := PlaceW.wf_of_placeW h
  have hd := ctr_data_of_placeW h hc
  have hdb := data_below_of_placeW h
  have hhb := heap_below_of_placeW h
  have hj := data_heap_of_placeW h
  have hs := PlaceW.heapSize_of_placeW h
  have hni := ctr_noImage_of_placeW h hc
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
  · obtain ⟨hr1, hr2, hr⟩ := rodataWord_of_placeW h hp
    have hrb := PlaceW.below32_of_placeW h Λ.rodata (List.mem_cons_self ..)
    have hh := hr Λ.heap (by simp [Scc.Sem.Layout.regions])
    have hdd := hr Λ.data (by simp [Scc.Sem.Layout.regions])
    exact ⟨p.1, rfl, by omega, by omega, by omega⟩

/-- **`hz0`: the arena starts zero** in a memory with the canonical load's
initial words. -/
theorem arOf_z0 (h : PlaceW cfg Λ o) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.A64.initOf Λ o.prog o.secs) {a : Nat}
    (ha : (Spike.Lib.AllocRow.freeR (arOf Λ).heap (arOf Λ).cells 0).contains a) : m.initVal (wordLoc a) = 0 :=
  Spike.Lib.ArenaInit.initVal_arena (by rw [hm]; exact arOf_init h hc) (arOf_lt h) ha

/-- **`hc0`: the counter starts at `0`** in a memory with the canonical
load's initial words. -/
theorem arOf_c0 (h : PlaceW cfg Λ o) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.A64.initOf Λ o.prog o.secs) : m.initVal (wordLoc (arOf Λ).ctr) = 0 :=
  Spike.Lib.ArenaInit.initVal_ctr (by rw [hm]; exact arOf_init h hc)

/-- **`scc_rt_heap` labels the arena's base** in the loaded thread (A8). -/
theorem arOf_heapLab (h : PlaceW cfg Λ o) (E : Entry) :
    ((_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label
        Scc.Cert.Link.heapSym).toBitVec.toNat = (arOf Λ).heap :=
  PlaceW.heapLab_toNat_of_placeW h E

/-- **`scc_rt_heap_use` labels the arena's counter** in the loaded thread (A8). -/
theorem arOf_ctrLab (h : PlaceW cfg Λ o) (E : Entry) :
    ((_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label
        heapUseSym).toBitVec = BitVec.ofNat 64 (arOf Λ).ctr :=
  PlaceW.heapUseLab_of_placeW h E

/-- info: 'Spike.Lib.A64.Rt.ArenaW.ctr_data_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctr_data_of_placeW

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_ok

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_sub

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_al

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_lt

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_init

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_z0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_z0

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_c0

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_heapLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_heapLab

/-- info: 'Spike.Lib.A64.Rt.ArenaW.arOf_ctrLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arOf_ctrLab

end Spike.Lib.A64.Rt.ArenaW
