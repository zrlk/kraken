/-
**The allocator's arena from `PlaceWX`** (x86-64; the twin of
`Spike/Lib/Rt/A64ArenaOfPlaceW.lean`): `Spike/Lib/Rt/X64ArenaOfPlaceOK.lean`'s
arena premises (`arOf_ok`, `arOf_sub`, `arOf_al`, `arOf_lt`, `arOf_init`,
`arOf_z0`, `arOf_c0`, `arOf_heapLab`, `arOf_ctrLab`) at an output passing
wake's placement facts `PlaceWX` (A1, A2, A8), where `placeOKAt` is false
for wake. The proofs are `X64ArenaOfPlaceOK`'s, with the A1/A2/A8 facts
from `PlaceWX` (`Spike/Lib/X64PlaceW.lean`) and the A8 extractions below.

- `PlaceWX.heapSize_of_placeWX`, `PlaceWX.heapLab_toNat_of_placeWX`,
  `PlaceWX.heapUseLab_of_placeWX`: A8's heap facts.
- `ctr_item_of_placeW`, `ctr_data_of_placeW`, `ctr_noImage_of_placeW`,
  `data_below_of_placeW`, `heap_below_of_placeW`: the counter in `.data`,
  off the image; the regions below `2 ^ 32`.
- `arOf_*`: the arena's premises.

Where x86-64 differs from AArch64: A64 also states
`PlaceW.imageIn_of_placeW` and `PlaceW.heapOk_of_placeW` here; on x86-64
`PlaceWX.imageIn_of_placeWX` and `PlaceWX.heapOk_of_placeWX` are already in
`X64PlaceW`. The arena's `.rodata` words' bound is
`X64ArenaOfPlaceOK.rodataWords_addr`'s (private there, restated), in place
of A64's `rodataWord_of_placeW`.
Namespace `Spike.Lib.X64.Rt.ArenaW`, theorem names A64's.
-/
import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Spike.Lib.X64PlaceW

namespace Spike.Lib.X64.Rt.ArenaW

open Kraken.Promising
open Scc.Sem (Range wordLoc loadSyms rodataWords rodataFits Entry)
open Scc.Sem.X64 (threadAt wordsMem imageMem)
open Scc.Cert.PlaceOK (heapUseSym heapUseOf allocCells)
open Scc.Cert.PlaceOK.X64 (heapOk)
open Scc.Cert.Link (symItems allZero itemLen)
open Spike.Lib (Arena PlaceWX)
open Spike.Lib.X64.Rt (arOf CtrZ)

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}

/-! ## A8 extraction at `PlaceWX` -/

/-- **A8**: the arena fits the heap region. -/
theorem PlaceWX.heapSize_of_placeWX (h : PlaceWX cfg Λ o) : 16 * allocCells ≤ Λ.heap.size := by
  have hh := PlaceWX.heapOk_of_placeWX h
  simp only [heapOk, Bool.and_eq_true] at hh
  exact Scc.Cert.PlaceOK.heapSize_of_heapSizeOk hh.1.2

/-- **A8**: `scc_rt_heap`'s label as a number is the heap arena's base. -/
theorem PlaceWX.heapLab_toNat_of_placeWX (h : PlaceWX cfg Λ o) (E : Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      Scc.Cert.Link.heapSym).toBitVec.toNat = Λ.heap.lo := by
  have hh := PlaceWX.heapOk_of_placeWX h
  simp only [heapOk, Bool.and_eq_true, decide_eq_true_eq] at hh
  rw [Scc.Cert.Rt.X64.label_threadAt_of_symLab
    (Scc.Cert.Link.X64.symsAround_of_loadOk (PlaceWX.loadOk_of_placeWX h)) hh.1.1.1]
  have hb := PlaceWX.below32_of_placeWX h Λ.heap (by simp [Scc.Sem.Layout.regions])
  have e : (Int64.ofNat Λ.heap.lo).toBitVec = BitVec.ofNat 64 Λ.heap.lo := by simp
  rw [e, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- **A8**: `scc_rt_heap_use`'s label is the counter's address. -/
theorem PlaceWX.heapUseLab_of_placeWX (h : PlaceWX cfg Λ o) (E : Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      heapUseSym).toBitVec = BitVec.ofNat 64 (heapUseOf Λ) := by
  have hh := PlaceWX.heapOk_of_placeWX h
  simp only [heapOk, Bool.and_eq_true, decide_eq_true_eq] at hh
  rw [Scc.Cert.Rt.X64.label_threadAt_of_symLab
    (Scc.Cert.Link.X64.symsAround_of_loadOk (PlaceWX.loadOk_of_placeWX h)) hh.1.1.2]
  simp

/-! ## The arena -/

/-- The counter's item at the counter in `.data`, every image word off it
(A2's `imageOk`). -/
private theorem ctr_item (h : PlaceWX cfg Λ o) (hc : CtrZ o) :
    (Λ.data.lo ≤ heapUseOf Λ ∧ heapUseOf Λ + 8 ≤ Λ.data.lo + Λ.data.size) ∧
      ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 := by
  obtain ⟨its, hm, hz, h8⟩ := hc
  have hi := PlaceWX.imageIn_of_placeWX h
  unfold Scc.Cert.Link.X64.imageIn at hi
  have hs : Scc.Cert.Link.special heapUseSym = false := by decide
  simp only [Scc.Cert.Link.imageOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hi
  obtain ⟨⟨hres, hok⟩, -⟩ := hi
  have hsome := hres _ hm
  simp only [hs, Bool.false_or] at hsome
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  have hu : heapUseOf Λ = a := by simp [heapUseOf, ha]
  have hr := hok _ (Scc.Cert.Link.mem_symRanges.mpr ⟨hm, hs, ha⟩)
  simp only [Scc.Cert.Link.symOk, hz, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hr
  rw [hu]
  refine ⟨⟨hr.1.2, by omega⟩, fun p hp => ?_⟩
  rcases hr.1.1 p hp with h1 | h1
  · exact .inl h1
  · exact .inr (by omega)

/-- **The counter's word in `.data`, every image word off it** (A2; the
A64 twin's `ctr_item_of_placeW`). -/
theorem ctr_item_of_placeW (h : PlaceWX cfg Λ o) (hc : CtrZ o) :
    Λ.data.lo ≤ heapUseOf Λ ∧ heapUseOf Λ + 8 ≤ Λ.data.lo + Λ.data.size ∧
      ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 :=
  ⟨(ctr_item h hc).1.1, (ctr_item h hc).1.2, (ctr_item h hc).2⟩

/-- **The counter is in `.data`** (A2). -/
theorem ctr_data_of_placeW (h : PlaceWX cfg Λ o) (hc : CtrZ o) : Λ.data.contains (heapUseOf Λ) := by
  have := (ctr_item h hc).1
  exact ⟨this.1, by omega⟩

/-- **No image word meets the counter's word** (A2). -/
theorem ctr_noImage_of_placeW (h : PlaceWX cfg Λ o) (hc : CtrZ o) :
    ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 :=
  (ctr_item h hc).2

/-- The `.data` region below `2 ^ 32` (A1). -/
private theorem data_lt (h : PlaceWX cfg Λ o) : Λ.data.lo + Λ.data.size ≤ 2 ^ 32 :=
  PlaceWX.below32_of_placeWX h Λ.data (by simp [Scc.Sem.Layout.regions])

/-- The heap region below `2 ^ 32` (A1). -/
private theorem heap_lt (h : PlaceWX cfg Λ o) : Λ.heap.lo + Λ.heap.size ≤ 2 ^ 32 :=
  PlaceWX.below32_of_placeWX h Λ.heap (by simp [Scc.Sem.Layout.regions])

/-- `.data` ends below `2 ^ 32` (A1). -/
theorem data_below_of_placeW (h : PlaceWX cfg Λ o) : Λ.data.lo + Λ.data.size ≤ 2 ^ 32 :=
  data_lt h

/-- The heap ends below `2 ^ 32` (A1). -/
theorem heap_below_of_placeW (h : PlaceWX cfg Λ o) : Λ.heap.lo + Λ.heap.size ≤ 2 ^ 32 :=
  heap_lt h

/-- The `.data` region and the heap are disjoint (A1). -/
theorem data_heap_of_placeW (h : PlaceWX cfg Λ o) : Λ.data.Disjoint Λ.heap :=
  (PlaceWX.wf_of_placeWX h).disjoint.2.2.2.1

/-- **The counter is off the arena.** -/
theorem ctr_out_of_placeW (h : PlaceWX cfg Λ o) (hc : CtrZ o) :
    ¬ (Λ.heap.lo ≤ heapUseOf Λ ∧ heapUseOf Λ < Λ.heap.lo + 16 * allocCells) := by
  have hd := ctr_data_of_placeW h hc
  have hj := data_heap_of_placeW h
  have hs := PlaceWX.heapSize_of_placeWX h
  simp only [Range.contains, Range.Disjoint] at hd hj
  omega

/-- **The arena's facts** (`hok`). -/
theorem arOf_ok (h : PlaceWX cfg Λ o) (hc : CtrZ o) : (arOf Λ).OK := by
  have hd := ctr_data_of_placeW h hc
  have hdh := (PlaceWX.wf_of_placeWX h).disjoint.2.2.2.1
  have hsz := PlaceWX.heapSize_of_placeWX h
  have hdl := data_lt h
  simp only [Range.contains, Range.Disjoint] at hd hdh
  exact Arena.ofWords_ok (by omega) (by decide) (by omega) fun _ _ _ => Nat.zero_le _

/-- **The arena lies in the heap region** (`hsub`, A8). -/
theorem arOf_sub (h : PlaceWX cfg Λ o) : (Range.mk (arOf Λ).heap (16 * (arOf Λ).cells)).Sub Λ.heap :=
  ⟨Nat.le_refl _, by have := PlaceWX.heapSize_of_placeWX h; simp only [arOf, Arena.ofWords]; omega⟩

/-- **The arena is 16-aligned** (`hal`, A1). -/
theorem arOf_al (h : PlaceWX cfg Λ o) : (arOf Λ).heap % 16 = 0 :=
  (PlaceWX.wf_of_placeWX h).aligned Λ.heap (by simp [Scc.Sem.Layout.regions])

/-- **The arena lies below `2 ^ 64`**. -/
theorem arOf_lt (h : PlaceWX cfg Λ o) : (arOf Λ).heap + 16 * (arOf Λ).cells ≤ 2 ^ 64 :=
  by have := PlaceWX.heapSize_of_placeWX h; have := heap_below_of_placeW h; simp only [arOf, Arena.ofWords]; omega

/-- `arenaInitOk` of 8-byte words, each below `2 ^ 64`, off the arena and
not at the counter. -/
private theorem arenaInitOk_wordsMem {ws : List (Nat × Nat)} {heap cells ctr : Nat} (hctr : ctr < 2 ^ 64)
    (hw : ∀ p ∈ ws, p.1 < 2 ^ 64 ∧ ¬ (heap ≤ p.1 ∧ p.1 < heap + 16 * cells) ∧ p.1 ≠ ctr) :
    Spike.Lib.ArenaInit.arenaInitOk (wordsMem ws) heap cells ctr = true := by
  simp only [Spike.Lib.ArenaInit.arenaInitOk, wordsMem, List.all_map, List.all_eq_true]
  intro p hp
  obtain ⟨hlt, hout, hne⟩ := hw p hp
  have e : (BitVec.ofNat 64 p.1).toNat = p.1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  simp only [Function.comp, e, wordLoc, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, bne_iff_ne, ne_eq, Loc.mk.injEq, and_true]
  refine ⟨by omega, fun he => hne ?_⟩
  have := congrArg BitVec.toNat he
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hctr] at this

/-- A `.rodata` word lies in the bytes of the `.rodata` image. -/
private theorem rodataWords_addr {Λ : Scc.Sem.Layout} {items : List Kraken.DataImage.Item}
    {code : String → Option Nat} {p : Nat × Nat} (hp : p ∈ rodataWords Λ items code) :
    Λ.rodata.lo ≤ p.1 ∧ p.1 < Kraken.DataImage.endAddr Λ.rodata.lo items := by
  simp only [rodataWords, Kraken.DataImage.words] at hp
  obtain ⟨⟨j, hj, he⟩, -⟩ := Kraken.DataImage.wordsN_mem _ _ _ p hp
  rw [← Kraken.DataImage.image_length (Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((code l).getD 0))
    Λ.rodata.lo items) Λ.rodata.lo items]
  omega

/-- **No initial word of the canonical load in the arena or at the counter**
(A1, A2). -/
theorem arOf_init (h : PlaceWX cfg Λ o) (hc : CtrZ o) :
    Spike.Lib.ArenaInit.arenaInitOk (Scc.Cert.Rt.X64.initOf Λ o.prog o.secs) (arOf Λ).heap (arOf Λ).cells
      (arOf Λ).ctr = true := by
  have hwf := PlaceWX.wf_of_placeWX h
  have hd := ctr_data_of_placeW h hc
  have hni := ctr_noImage_of_placeW h hc
  have hdh := hwf.disjoint.2.2.2.1
  have hsz := PlaceWX.heapSize_of_placeWX h
  have hdl := data_lt h
  have hhl := heap_lt h
  have hro := PlaceWX.below32_of_placeWX h Λ.rodata (List.mem_cons_self ..)
  have hfit : rodataFits Λ o.secs.rodata = true := by
    have := PlaceWX.loadOk_of_placeWX h
    simp only [Scc.Cert.Link.X64.loadOk, Bool.and_eq_true] at this
    exact this.1.1.1.1.1.1.2
  simp only [Range.contains, Range.Disjoint] at hd hdh
  have hctr : heapUseOf Λ < 2 ^ 64 := by omega
  simp only [Scc.Cert.Rt.X64.initOf, Spike.Lib.ArenaInit.arenaInitOk, List.all_append, Bool.and_eq_true]
  simp only [arOf, Arena.ofWords]
  refine ⟨arenaInitOk_wordsMem hctr fun p hp => ?_, arenaInitOk_wordsMem hctr fun p hp => ?_⟩
  · have hi := hwf.image p hp
    simp only [Range.contains] at hi
    have := hni p hp
    refine ⟨by omega, by omega, by omega⟩
  · obtain ⟨hlo, hhi⟩ := rodataWords_addr hp
    simp only [rodataFits, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hfit
    rcases hfit.2 with he | ⟨-, hr⟩
    · rw [List.isEmpty_iff.mp he] at hhi
      simp [Kraken.DataImage.endAddr, Kraken.DataImage.addrAt] at hhi
      omega
    · have hh := hr Λ.heap (by simp [Scc.Sem.Layout.regions])
      have hdd := hr Λ.data (by simp [Scc.Sem.Layout.regions])
      have hend := hfit.1.2
      refine ⟨by omega, by omega, by omega⟩

/-- **The arena starts zero** (`hz0`) in a memory with the canonical load's
initial words. -/
theorem arOf_z0 (h : PlaceWX cfg Λ o) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.X64.initOf Λ o.prog o.secs) {a : Nat}
    (ha : (Spike.Lib.AllocRow.freeR (arOf Λ).heap (arOf Λ).cells 0).contains a) : m.initVal (wordLoc a) = 0 :=
  Spike.Lib.ArenaInit.initVal_arena (by rw [hm]; exact arOf_init h hc) (arOf_lt h) ha

/-- **The counter starts at `0`** (`hc0`) in a memory with the canonical
load's initial words. -/
theorem arOf_c0 (h : PlaceWX cfg Λ o) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.X64.initOf Λ o.prog o.secs) : m.initVal (wordLoc (arOf Λ).ctr) = 0 :=
  Spike.Lib.ArenaInit.initVal_ctr (by rw [hm]; exact arOf_init h hc)

/-- **`scc_rt_heap` labels the arena's base** in the loaded thread (A8). -/
theorem arOf_heapLab (h : PlaceWX cfg Λ o) (E : Scc.Sem.Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      Scc.Cert.Link.heapSym).toBitVec.toNat = (arOf Λ).heap :=
  PlaceWX.heapLab_toNat_of_placeWX h E

/-- **`scc_rt_heap_use` labels the arena's counter** in the loaded thread
(A8). -/
theorem arOf_ctrLab (h : PlaceWX cfg Λ o) (E : Scc.Sem.Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      heapUseSym).toBitVec = BitVec.ofNat 64 (arOf Λ).ctr :=
  PlaceWX.heapUseLab_of_placeWX h E

end Spike.Lib.X64.Rt.ArenaW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX

/-- info: 'Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapLab_toNat_of_placeWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapLab_toNat_of_placeWX

/-- info: 'Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapUseLab_of_placeWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapUseLab_of_placeWX

/-- info: 'Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.ctr_data_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.ctr_data_of_placeW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.ctr_noImage_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.ctr_noImage_of_placeW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.data_heap_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.data_heap_of_placeW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.ctr_out_of_placeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.ctr_out_of_placeW

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_ok

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_sub

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_al

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_lt

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_init

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_z0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_z0

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_c0

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_heapLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_heapLab

/-- info: 'Spike.Lib.X64.Rt.ArenaW.arOf_ctrLab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.ArenaW.arOf_ctrLab

