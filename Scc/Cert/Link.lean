import Scc.Sem.Target

/-!
# A static link of an emitted text, by evaluation in the kernel

The layout `Λ` (`Scc.Sem.Layout`) a static link gives an emitted text,
computed from its data sections as the loader reads them
(`Scc.Sem.dataSections`, a literal for a given text) by list and `Nat` code
alone, so that `decide +kernel` can check what is claimed of it: its
well-formedness (`wfB`, sound for `Layout.WF`) and its agreement with a
layout written out as numbers.

`link B secs code` is the test model's static link (`Scc.Sem.Test.layoutOf`,
`Scc/Sem/Test/RunA64.lean`) over data items instead of lines:

- the code at `B.codeLo`, `B.codeSize` bytes;
- `.rodata` from `B.roLo`, its size rounded up to 16 (the loader builds its
  image and resolves its labels from it; the test model also lists them as
  symbols, which `Layout.WF` does not allow: they are outside the data
  regions, and the loader places them the same either way, `loadSyms`);
- `.bss` then `.data` from `B.dataLo` (scc writes every `.bss` section
  before the `.data` ones, so this is their order in the text), laid out as a
  linker would: alignment, labels, `.zero`, `.byte`, `.quad` (numbers, or
  labels `code` resolves);
- the heap arena (`scc_rt_heap`), the stack pool (`scc_rt_stacks`) and the
  pinned region (`scc_rt_pinned`) in their own regions at `B.heapLo`,
  `B.poolLo` and `B.pinnedLo`, sized by the `.zero` after their label;
- the non-zero 8-byte words of the data bytes as the image, in address
  order; the labelled `exit_group` of each abort routine as its abort label.

`Scc/Test/LinkTest.lean` checks it against the test model on emitted texts.
-/

namespace Scc.Cert.Link

open Scc.Sem Kraken.DataImage

/-- The bases of a static link. -/
structure Bases where
  codeLo : Nat
  codeSize : Nat
  roLo : Nat
  dataLo : Nat
  heapLo : Nat
  poolLo : Nat
  pinnedLo : Nat
  deriving Repr, DecidableEq

/-- The bases of the test model's static link (`Scc/Sem/Test/RunA64.lean`):
code at `0x400000` (1 MiB), `.rodata` at `0x500000`, the other data
sections at `0x600000`, the heap arena at `0x1000000`, the pinned region at
`0x8000000`, the stack pool at `0x10000000`. -/
def canonical : Bases where
  codeLo := 0x400000
  codeSize := 0x100000
  roLo := 0x500000
  dataLo := 0x600000
  heapLo := 0x1000000
  poolLo := 0x10000000
  pinnedLo := 0x8000000

/-- The symbols of the three regions of their own. -/
def heapSym : String := "scc_rt_heap"
def poolSym : String := "scc_rt_stacks"
def pinnedSym : String := "scc_rt_pinned"

/-- The labelled `exit_group` of the runtime's abort routine of each kind
(`scc_rt_abort_<kind>_exit`). -/
def abortName : AbortKind → String
  | .overflow => "scc_rt_abort_overflow_exit"
  | .heap => "scc_rt_abort_heap_exit"
  | .stack => "scc_rt_abort_stack_exit"
  | .threads => "scc_rt_abort_threads_exit"
  | .writeErr => "scc_rt_abort_write_exit"

/-- Round `n` up to a multiple of `k`. -/
def alignUp (n k : Nat) : Nat := if k = 0 then n else (n + k - 1) / k * k

/-- Add byte `b` at address `a` to an image of 8-byte words `(address,
value)` in address order. -/
def addByte : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], a, b => [(a / 8 * 8, b * 2 ^ (8 * (a % 8)))]
  | (w, v) :: ws, a, b =>
    if a / 8 * 8 < w then (a / 8 * 8, b * 2 ^ (8 * (a % 8))) :: (w, v) :: ws
    else if a / 8 * 8 = w then (w, v + b * 2 ^ (8 * (a % 8))) :: ws
    else (w, v) :: addByte ws a b

/-- Add bytes `bs` from address `a`. -/
def addBytes (img : List (Nat × Nat)) (a : Nat) : List Nat → List (Nat × Nat)
  | [] => img
  | b :: bs => addBytes (addByte img a b) (a + 1) bs

/-- The 8 bytes of a 64-bit value, least significant first. -/
def bytes8 (v : Nat) : List Nat := (List.range 8).map fun j => v / 2 ^ (8 * j) % 256

/-- The state of the walk over `.bss` and `.data`. -/
structure Walk where
  cur : Nat
  /-- The region the next `.zero` fills: the heap (0), the pool (1) or the
  pinned region (2). -/
  special : Option Nat := none
  /-- The symbols, last first. -/
  syms : List (String × Nat) := []
  img : List (Nat × Nat) := []
  heap : Range := ⟨0, 0⟩
  pool : Range := ⟨0, 0⟩
  pinned : Range := ⟨0, 0⟩

/-- One data item in the walk; `code` resolves `.quad` labels. -/
def step (B : Bases) (code : String → Option Nat) (w : Walk) : Item → Walk
  | .label l =>
    if l = heapSym then { w with special := some 0, syms := (l, B.heapLo) :: w.syms }
    else if l = poolSym then { w with special := some 1, syms := (l, B.poolLo) :: w.syms }
    else if l = pinnedSym then { w with special := some 2, syms := (l, B.pinnedLo) :: w.syms }
    else { w with special := none, syms := (l, w.cur) :: w.syms }
  | .align n => { w with cur := alignUp w.cur n }
  | .zero n =>
    match w.special with
    | some 0 => { w with heap := ⟨B.heapLo, n⟩, special := none }
    | some 1 => { w with pool := ⟨B.poolLo, n⟩, special := none }
    | some _ => { w with pinned := ⟨B.pinnedLo, n⟩, special := none }
    | none => { w with cur := w.cur + n }
  | .bytes bs => { w with cur := w.cur + bs.length, img := addBytes w.img w.cur (bs.map UInt8.toNat) }
  | .quad v => { w with cur := w.cur + 8, img := addBytes w.img w.cur (bytes8 (v % 2 ^ 64).toNat) }
  | .quadLabel l => { w with cur := w.cur + 8, img := addBytes w.img w.cur (bytes8 ((code l).getD 0 % 2 ^ 64)) }

/-- The walk over items from `w`. -/
def walk (B : Bases) (code : String → Option Nat) (w : Walk) (items : List Item) : Walk :=
  items.foldl (step B code) w

/-- **The static link of a text with data sections `secs`**, its `.quad`
labels resolved by `code`. -/
def link (B : Bases) (secs : DataSecs) (code : String → Option Nat) : Layout :=
  let w := walk B code { cur := B.dataLo } (secs.bss ++ secs.data)
  { code := ⟨B.codeLo, B.codeSize⟩
    rodata := ⟨B.roLo, alignUp (endAddr B.roLo secs.rodata - B.roLo) 16⟩
    data := ⟨B.dataLo, alignUp (w.cur - B.dataLo) 16⟩
    heap := w.heap
    stackPool := w.pool
    pinned := w.pinned
    -- TODO: if `static` ever places labels, the runtime's words need a real `RtFree` check (today none is placed).
    static _ := none
    image := w.img.filter (·.2 ≠ 0)
    symbols := w.syms.reverse
    abortLbl := abortName }

/-- Every `.quad` label of `.bss` and `.data` resolves. -/
def quadsOk (secs : DataSecs) (code : String → Option Nat) : Bool :=
  (quadLabels (secs.bss ++ secs.data)).all fun l => (code l).isSome

/-! ## Well-formedness, decided -/

/-- Every abort kind. -/
def kinds : List AbortKind := [.overflow, .heap, .stack, .threads, .writeErr]

theorem mem_kinds (k : AbortKind) : k ∈ kinds := by cases k <;> simp [kinds]

/-- `Range.InSpace`, decided. -/
def inSpaceB (r : Range) : Bool := decide (0 < r.lo) && decide (r.lo + r.size ≤ 2 ^ 64)

/-- `Range.Disjoint`, decided. -/
def disjB (r s : Range) : Bool := decide (r.lo + r.size ≤ s.lo) || decide (s.lo + s.size ≤ r.lo)

/-- `Range.contains`, decided. -/
def containsB (r : Range) (a : Nat) : Bool := decide (r.lo ≤ a) && decide (a < r.lo + r.size)

/-- Distinct names, by pairwise comparison. -/
def nodupB : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- **`Layout.WF`, decided.** -/
def wfB (Λ : Layout) : Bool :=
  Λ.regions.all inSpaceB &&
  Λ.regions.all (fun r => decide (r.lo % 16 = 0)) &&
  disjB Λ.code Λ.data && disjB Λ.code Λ.heap && disjB Λ.code Λ.stackPool &&
  disjB Λ.data Λ.heap && disjB Λ.data Λ.stackPool && disjB Λ.heap Λ.stackPool &&
  disjB Λ.code Λ.pinned && disjB Λ.data Λ.pinned && disjB Λ.heap Λ.pinned &&
  disjB Λ.stackPool Λ.pinned &&
  kinds.all (fun k => kinds.all fun k' => !(Λ.abortLbl k == Λ.abortLbl k') || decide (k = k')) &&
  Λ.image.all (fun p => containsB Λ.data p.1 && decide (p.1 % 8 = 0) && decide (p.2 < 2 ^ 64)) &&
  Λ.symbols.all (fun p => containsB Λ.data p.2 || containsB Λ.heap p.2 ||
    containsB Λ.stackPool p.2 || containsB Λ.pinned p.2) &&
  Λ.symbols.all (fun p => decide (p.2 < Λ.code.lo) || decide (Λ.code.lo + Λ.code.size ≤ p.2)) &&
  nodupB (Λ.symbols.map Prod.fst) &&
  Λ.regions.all (fun r => decide (0 < r.lo))

theorem nodupB_nodup : ∀ {xs : List String}, nodupB xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, nodupB_nodup h.2⟩
    have := List.contains_iff_mem.mpr hx
    simp_all

theorem inSpaceB_iff {r : Range} : inSpaceB r = true ↔ r.InSpace := by
  simp [inSpaceB, Range.InSpace]

theorem disjB_iff {r s : Range} : disjB r s = true ↔ r.Disjoint s := by
  simp [disjB, Range.Disjoint]

theorem containsB_iff {r : Range} {a : Nat} : containsB r a = true ↔ r.contains a := by
  simp [containsB, Range.contains]

/-- **`wfB` is sound.** -/
theorem wfB_sound {Λ : Layout} (h : wfB Λ = true) : Λ.WF := by
  simp only [wfB, Bool.and_eq_true, List.all_eq_true, disjB_iff, inSpaceB_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, hal⟩, d1⟩, d2⟩, d3⟩, d4⟩, d5⟩, d6⟩, d7⟩, d8⟩, d9⟩, d10⟩, hab⟩, him⟩, hsy⟩,
    hab'⟩, hnd⟩, hpos⟩ := h
  refine ⟨hsp, hal, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩, fun k k' hk => ?_, fun p hp => ?_,
    fun p hp => ?_, fun p hp => by simpa using hab' p hp, nodupB_nodup hnd, hpos⟩
  · have := hab k (mem_kinds k) k' (mem_kinds k')
    simp_all
  · have := him p hp
    simp only [containsB_iff] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := hsy p hp
    simp only [Bool.or_eq_true, containsB_iff] at this
    unfold Layout.dataRegion
    rcases this with ((h | h) | h) | h <;> simp [h]

end Scc.Cert.Link
