/-
**The allocator's arena from the placement check on x86-64**: an x86-64
output passing `Scc.Cert.PlaceOK.X64.placeOKAt` at a layout `Λ` gives the
arena premises of the allocation-capable consumer (`correctKA`'s `hok`,
`hsub`, `hal`, `hz0`, `hc0`) at the arena `arOf Λ`, with no layout constant:

- **`arOf Λ`**: `Arena.ofWords Λ.heap.lo allocCells (heapUseOf Λ) (fun _ => 0)`,
  the heap region's base (A8's `scc_rt_heap`), the allocator's cells (A7's
  literal, `allocCells_eq_lit`), the counter at `scc_rt_heap_use`'s address.
- **`CtrZ o`**: a fact of the emitted sections, not of the layout: the
  counter's item in `.bss`/`.data` is all zero and at least a word. With it
  A2's `imageOk` places the counter in `.data` (`ctr_data_of_placeOKAt`) and
  keeps every image word off it (`ctr_noImage_of_placeOKAt`); no new
  `placeOK` conjunct is needed.
- `arOf_ok`, `arOf_sub`, `arOf_al`, `arOf_lt`: `Arena.OK` (the counter in
  `.data`, disjoint from the heap by A1), in the heap region (A8's
  `heapSizeOk`), 16-aligned (A1), below `2 ^ 64`.
- `arOf_init`, `arOf_z0`, `arOf_c0`: no initial word of the canonical load
  (`Rt.X64.initOf`: the image, in `.data`; the `.rodata` words, in
  `Λ.rodata`, clear of the regions by A2's `rodataFits`) in the arena or at
  the counter, so both start zero.
- `arOf_heapLab`, `arOf_ctrLab`: the arena's base and counter at their labels
  in the loaded thread (A8).

The x86-64 twin of `Spike/Lib/Rt/A64ArenaOfPlaceOK.lean`.
-/
import Scc.Cert.PlaceOKX64
import Spike.Lib.Arena
import Spike.Lib.ArenaInit
import Spike.Lib.LowerX64.ArenaOfPlaceOK

namespace Spike.Lib.X64.Rt

open Kraken.Promising
open Scc.Sem (Range wordLoc loadSyms rodataWords rodataFits)
open Scc.Sem.X64 (threadAt wordsMem imageMem)
open Scc.Cert.PlaceOK (heapUseSym heapUseOf allocCells)
open Scc.Cert.PlaceOK.X64
open Scc.Cert.Link (symItems allZero itemLen)
open Spike.Lib (Arena)

/-- **The allocator's arena of a layout**: at the heap region's base, of
`allocCells` cells, the counter at `scc_rt_heap_use`'s address, no trace
words in a header. -/
def arOf (Λ : Scc.Sem.Layout) : Arena := Arena.ofWords Λ.heap.lo allocCells (heapUseOf Λ) (fun _ => 0)

/-- **The counter's item is a zero word** in the output's `.bss`/`.data`
(today's emitter: `scc_rt_heap_use: .zero 8`). -/
def CtrZ (o : Scc.Cert.PlaceOK.X64.Out) : Prop :=
  ∃ its, (heapUseSym, its) ∈ symItems (o.secs.bss ++ o.secs.data) ∧ allZero its = true ∧ 8 ≤ itemLen its

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}

/-- The counter's item at the counter in `.data`, every image word off it
(A2's `imageOk`). -/
private theorem ctr_item (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    (Λ.data.lo ≤ heapUseOf Λ ∧ heapUseOf Λ + 8 ≤ Λ.data.lo + Λ.data.size) ∧
      ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 := by
  obtain ⟨its, hm, hz, h8⟩ := hc
  have hi := imageIn_of_placeOKAt h
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
A64 twin's `ctr_item_of_placeOKAt`). -/
theorem ctr_item_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    Λ.data.lo ≤ heapUseOf Λ ∧ heapUseOf Λ + 8 ≤ Λ.data.lo + Λ.data.size ∧
      ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 :=
  ⟨(ctr_item h hc).1.1, (ctr_item h hc).1.2, (ctr_item h hc).2⟩

/-- **The counter is in `.data`** (A2). -/
theorem ctr_data_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) : Λ.data.contains (heapUseOf Λ) := by
  have := (ctr_item h hc).1
  exact ⟨this.1, by omega⟩

/-- **No image word meets the counter's word** (A2). -/
theorem ctr_noImage_of_placeOKAt (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    ∀ p ∈ Λ.image, p.1 + 8 ≤ heapUseOf Λ ∨ heapUseOf Λ + 8 ≤ p.1 :=
  (ctr_item h hc).2

/-- The `.data` region below `2 ^ 32` (A1). -/
private theorem data_lt (h : placeOKAt cfg Λ o = true) : Λ.data.lo + Λ.data.size ≤ 2 ^ 32 :=
  below32_of_placeOKAt h Λ.data (by simp [Scc.Sem.Layout.regions])

/-- The heap region below `2 ^ 32` (A1). -/
private theorem heap_lt (h : placeOKAt cfg Λ o = true) : Λ.heap.lo + Λ.heap.size ≤ 2 ^ 32 :=
  below32_of_placeOKAt h Λ.heap (by simp [Scc.Sem.Layout.regions])

/-- `.data` ends below `2 ^ 32` (A1). -/
theorem data_below_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.data.lo + Λ.data.size ≤ 2 ^ 32 :=
  data_lt h

/-- The heap ends below `2 ^ 32` (A1). -/
theorem heap_below_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.heap.lo + Λ.heap.size ≤ 2 ^ 32 :=
  heap_lt h

/-- **The arena's facts** (`hok`). -/
theorem arOf_ok (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) : (arOf Λ).OK := by
  have hd := ctr_data_of_placeOKAt h hc
  have hdh := (wf_of_placeOKAt h).disjoint.2.2.2.1
  have hsz := heapSize_of_placeOKAt h
  have hdl := data_lt h
  simp only [Range.contains, Range.Disjoint] at hd hdh
  exact Arena.ofWords_ok (by omega) (by decide) (by omega) fun _ _ _ => Nat.zero_le _

/-- **The arena lies in the heap region** (`hsub`, A8). -/
theorem arOf_sub (h : placeOKAt cfg Λ o = true) : (Range.mk (arOf Λ).heap (16 * (arOf Λ).cells)).Sub Λ.heap :=
  ⟨Nat.le_refl _, by have := heapSize_of_placeOKAt h; simp only [arOf, Arena.ofWords]; omega⟩

/-- **The arena is 16-aligned** (`hal`, A1). -/
theorem arOf_al (h : placeOKAt cfg Λ o = true) : (arOf Λ).heap % 16 = 0 :=
  (wf_of_placeOKAt h).aligned Λ.heap (by simp [Scc.Sem.Layout.regions])

/-- **The arena lies below `2 ^ 64`**. -/
theorem arOf_lt (h : placeOKAt cfg Λ o = true) : (arOf Λ).heap + 16 * (arOf Λ).cells ≤ 2 ^ 64 :=
  Nat.le_of_lt (arena_end_lt_of_placeOKAt h)

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
theorem arOf_init (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) :
    Spike.Lib.ArenaInit.arenaInitOk (Scc.Cert.Rt.X64.initOf Λ o.prog o.secs) (arOf Λ).heap (arOf Λ).cells
      (arOf Λ).ctr = true := by
  have hwf := wf_of_placeOKAt h
  have hd := ctr_data_of_placeOKAt h hc
  have hni := ctr_noImage_of_placeOKAt h hc
  have hdh := hwf.disjoint.2.2.2.1
  have hsz := heapSize_of_placeOKAt h
  have hdl := data_lt h
  have hhl := heap_lt h
  have hro := below32_of_placeOKAt h Λ.rodata (List.mem_cons_self ..)
  have hfit : rodataFits Λ o.secs.rodata = true := by
    have := loadOk_of_placeOKAt h
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
theorem arOf_z0 (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.X64.initOf Λ o.prog o.secs) {a : Nat}
    (ha : (Spike.Lib.AllocRow.freeR (arOf Λ).heap (arOf Λ).cells 0).contains a) : m.initVal (wordLoc a) = 0 :=
  Spike.Lib.ArenaInit.initVal_arena (by rw [hm]; exact arOf_init h hc) (arOf_lt h) ha

/-- **The counter starts at `0`** (`hc0`) in a memory with the canonical
load's initial words. -/
theorem arOf_c0 (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) {m : Memory}
    (hm : m.init = Scc.Cert.Rt.X64.initOf Λ o.prog o.secs) : m.initVal (wordLoc (arOf Λ).ctr) = 0 :=
  Spike.Lib.ArenaInit.initVal_ctr (by rw [hm]; exact arOf_init h hc)

/-- **`scc_rt_heap` labels the arena's base** in the loaded thread (A8). -/
theorem arOf_heapLab (h : placeOKAt cfg Λ o = true) (E : Scc.Sem.Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      Scc.Cert.Link.heapSym).toBitVec.toNat = (arOf Λ).heap :=
  heapLab_toNat_of_placeOKAt h E

/-- **`scc_rt_heap_use` labels the arena's counter** in the loaded thread
(A8). -/
theorem arOf_ctrLab (h : placeOKAt cfg Λ o = true) (E : Scc.Sem.Entry) :
    ((_root_.Executable.labels (threadAt E Λ.code.lo o.prog (loadSyms Λ o.secs.rodata)).exe).label
      heapUseSym).toBitVec = BitVec.ofNat 64 (arOf Λ).ctr :=
  heapUseLab_of_placeOKAt h E

end Spike.Lib.X64.Rt
