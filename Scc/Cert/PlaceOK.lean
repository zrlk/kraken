import Scc.Cert.Link

/-!
# `PlaceOK`: the per-program placement check, ISA-generic core

The release theorem is to be a corollary of a compiler theorem
`lower_correct cfg p hA hP` whose only per-program hypothesis about the
emitted code is `hP : PlaceOK cfg (lowerAll cfg p) = true`, decided by the
kernel. This module fixes the form of `PlaceOK` shared by the two ISAs; the
ISA modules (`Scc/Cert/PlaceOKA64.lean`, its x86-64 twin) give the output's
types, the tables and the nine components.

* **The output** `Out P D`: scc's output at the AST level, what
  `scc --code`/`--blocks` write today: the program `prog` (of the ISA's type
  `P`: AArch64's directive list, x86-64's sized cells), the data sections
  `secs`, the label offsets the assembler reported (`labelOffs`, x86-64
  only) and the placement data `place` (of the ISA's type `D`).
* **The tables** are computed from the output (`tablesOf`, the ISA's), not
  emitted: the static link `Λ` first (`Tables.Λ`, `linkTables`).
* **The components** `Checks`: eleven `Bool`s A1–A9, A11 and A12 over the
  output and its tables (A12 `true` unless the ISA sets it); `Checks.ok`
  their conjunction, which is `PlaceOK`. Each component is used only through
  its projection (`Checks.a1_of_ok` … `a9_of_ok`, `a11_of_ok`, `a12_of_ok`)
  and
  the ISA's extraction lemma from it to a `Prop`.
* **A1, the static link**, is ISA-generic: `Link.wfB` of `Λ`, sound by
  `Link.wfB_sound` (`wf_of_a1`).

`PlaceOK` never takes the source program or a machine state: its inputs are
the configuration, the output and tables computed from the output.
-/

namespace Scc.Cert.PlaceOK

open Scc.Sem

/-- **The configuration** of the lowering and the link: the static link's
bases, and the stack need's budget and thread entries (`needOk`'s). -/
structure Config where
  bases : Link.Bases := Link.canonical
  needBudget : Nat := 12288
  entries : List String := ["scc_rt_main"]

/-- The configuration of the test model (`Link.canonical`). -/
def Config.canonical : Config := {}

/-- **scc's output** at the AST level: the program (`P`: the ISA's
instruction list), the data sections, the assembler's label offsets
(x86-64; empty on AArch64), and the placement data (`D`, the ISA's). -/
structure Out (P D : Type) where
  prog : P
  secs : DataSecs
  labelOffs : List (String × Nat) := []
  place : D

/-- **The ISA-generic part of the tables**: the static link of the output. -/
structure Tables where
  Λ : Layout

/-- The ISA-generic tables of an output whose code labels resolve by `code`:
the static link at the configuration's bases. -/
def linkTables (cfg : Config) (secs : DataSecs) (code : String → Option Nat) : Tables :=
  ⟨Link.link cfg.bases secs code⟩

/-- **The eleven components** of `PlaceOK` over an output type `O` and its
tables `T`, each a `Bool`:

* A1 the static link well-formed; A2 the loader's agreement; A3 the code at
  its place; A4 the instruction fragment and the stack need;
* A5 the static offsets of every node; A6 the phases, dead targets and
  returns of every node; A7 the marks at their pcs; A8 the runtime's data
  words; A9 the placement data against the program; A11 the runtime's fixed
  code; A12 the code of every user function (`true` by default: an ISA
  without that check). -/
structure Checks (O T : Type) where
  a1 : O → T → Bool
  a2 : O → T → Bool
  a3 : O → T → Bool
  a4 : O → T → Bool
  a5 : O → T → Bool
  a6 : O → T → Bool
  a7 : O → T → Bool
  a8 : O → T → Bool
  a9 : O → T → Bool
  a11 : O → T → Bool
  a12 : O → T → Bool := fun _ _ => true

/-- **`PlaceOK`**: the eleven components at the output and its tables. -/
def Checks.ok {O T : Type} (C : Checks O T) (tablesOf : O → T) (o : O) : Bool :=
  let t := tablesOf o
  C.a1 o t && C.a2 o t && C.a3 o t && C.a4 o t && C.a5 o t && C.a6 o t && C.a7 o t && C.a8 o t && C.a9 o t &&
    C.a11 o t && C.a12 o t

section Proj

variable {O T : Type} {C : Checks O T} {tablesOf : O → T} {o : O}

private theorem parts (h : C.ok tablesOf o = true) :
    C.a1 o (tablesOf o) = true ∧ C.a2 o (tablesOf o) = true ∧ C.a3 o (tablesOf o) = true ∧
    C.a4 o (tablesOf o) = true ∧ C.a5 o (tablesOf o) = true ∧ C.a6 o (tablesOf o) = true ∧
    C.a7 o (tablesOf o) = true ∧ C.a8 o (tablesOf o) = true ∧ C.a9 o (tablesOf o) = true ∧
    C.a11 o (tablesOf o) = true ∧ C.a12 o (tablesOf o) = true := by
  simp only [Checks.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12⟩

theorem Checks.a1_of_ok (h : C.ok tablesOf o = true) : C.a1 o (tablesOf o) = true := (parts h).1
theorem Checks.a2_of_ok (h : C.ok tablesOf o = true) : C.a2 o (tablesOf o) = true := (parts h).2.1
theorem Checks.a3_of_ok (h : C.ok tablesOf o = true) : C.a3 o (tablesOf o) = true := (parts h).2.2.1
theorem Checks.a4_of_ok (h : C.ok tablesOf o = true) : C.a4 o (tablesOf o) = true := (parts h).2.2.2.1
theorem Checks.a5_of_ok (h : C.ok tablesOf o = true) : C.a5 o (tablesOf o) = true := (parts h).2.2.2.2.1
theorem Checks.a6_of_ok (h : C.ok tablesOf o = true) : C.a6 o (tablesOf o) = true :=
  (parts h).2.2.2.2.2.1
theorem Checks.a7_of_ok (h : C.ok tablesOf o = true) : C.a7 o (tablesOf o) = true :=
  (parts h).2.2.2.2.2.2.1
theorem Checks.a8_of_ok (h : C.ok tablesOf o = true) : C.a8 o (tablesOf o) = true :=
  (parts h).2.2.2.2.2.2.2.1
theorem Checks.a9_of_ok (h : C.ok tablesOf o = true) : C.a9 o (tablesOf o) = true :=
  (parts h).2.2.2.2.2.2.2.2.1
theorem Checks.a11_of_ok (h : C.ok tablesOf o = true) : C.a11 o (tablesOf o) = true :=
  (parts h).2.2.2.2.2.2.2.2.2.1
theorem Checks.a12_of_ok (h : C.ok tablesOf o = true) : C.a12 o (tablesOf o) = true :=
  (parts h).2.2.2.2.2.2.2.2.2.2

/-- **`PlaceOK` from its components**, each decided on its own (a
certificate may decide its components in separate declarations or files,
and combine them here without another decision). -/
theorem Checks.ok_of (h1 : C.a1 o (tablesOf o) = true) (h2 : C.a2 o (tablesOf o) = true)
    (h3 : C.a3 o (tablesOf o) = true) (h4 : C.a4 o (tablesOf o) = true) (h5 : C.a5 o (tablesOf o) = true)
    (h6 : C.a6 o (tablesOf o) = true) (h7 : C.a7 o (tablesOf o) = true) (h8 : C.a8 o (tablesOf o) = true)
    (h9 : C.a9 o (tablesOf o) = true) (h11 : C.a11 o (tablesOf o) = true) (h12 : C.a12 o (tablesOf o) = true) :
    C.ok tablesOf o = true := by
  simp only [Checks.ok, h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12, Bool.and_self]

end Proj

/-- **The first failing component** of `PlaceOK` (its number `N` of AN), by
evaluation, for diagnostics only (`Scc/Test/placediag.sh`): nothing is
proved from it, and a certificate that states a failure decides it again
(`Scc.Cert.Gen.Placement.fails`). -/
def Checks.firstFail {O T : Type} (C : Checks O T) (tablesOf : O → T) (o : O) : Option Nat :=
  let t := tablesOf o
  ([(1, C.a1 o t), (2, C.a2 o t), (3, C.a3 o t), (4, C.a4 o t), (5, C.a5 o t), (6, C.a6 o t),
    (7, C.a7 o t), (8, C.a8 o t), (9, C.a9 o t), (11, C.a11 o t), (12, C.a12 o t)].find? (!·.2)).map (·.1)

/-! ## A1: the static link -/

/-- **A1**: the static link is well-formed (`Link.wfB`): its regions in the
address space, 16-aligned and pairwise disjoint, its image words in `data`
and 8-aligned, its symbols in a data region above the code with distinct
names, its abort labels distinct per kind. -/
def a1 (t : Tables) : Bool := Link.wfB t.Λ

/-- **A1's extraction lemma**: the static link is `Layout.WF`. -/
theorem wf_of_a1 {t : Tables} (h : a1 t = true) : t.Λ.WF := Link.wfB_sound h

/-- `Layout.WF` reads no immediate table: it holds of the link with the
lowering's immediates (`Layout.imms`) when it holds of the link. -/
theorem wf_withImms {Λ : Layout} (h : Λ.WF) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    ({ Λ with imms := i } : Layout).WF :=
  ⟨h.inSpace, h.aligned, h.disjoint, h.abortInj, h.image, h.symIn, h.symAbove, h.symNodup, h.pos⟩

/-! ## A1: the layout's ties to the output

These facts tie a layout to the output and bound it, independently of the
entry state, so that A1 holds of a layout the link did not compute (one
read off an executable) as well as of `Link.link`'s. -/

/-- The size of the `.zero` right after the label `l` in `items` (`none`
if `l` is not followed by a `.zero`). -/
def zeroAfter : List Kraken.DataImage.Item → String → Option Nat
  | .label l' :: .zero n :: rest, l => if l' = l then some n else zeroAfter (.zero n :: rest) l
  | _ :: rest, l => zeroAfter rest l
  | [], _ => none

/-- **The regions of their own tied to the output**: the heap arena, the
stack pool and the pinned region each at its symbol (`Link.heapSym` …), of
the size of the `.zero` after that symbol in `.bss` and `.data`. -/
def regionsTied (secs : DataSecs) (Λ : Layout) : Bool :=
  [(Link.heapSym, Λ.heap), (Link.poolSym, Λ.stackPool), (Link.pinnedSym, Λ.pinned)].all fun (x, r) =>
    decide (Λ.symbols.lookup x = some r.lo) && decide (zeroAfter (secs.bss ++ secs.data) x = some r.size)

/-- **The layout below `2 ^ 32`**: `.rodata` and every region end at or
below `2 ^ 32`. -/
def below32 (Λ : Layout) : Bool :=
  (Λ.rodata :: Λ.regions).all fun r => decide (r.lo + r.size ≤ 2 ^ 32)

/-- **The standard abort labels**: each abort kind's label is the
runtime's (`Link.abortName`), as the static link names them; a layout read
off an executable must name them so too. -/
def abortStd (Λ : Layout) : Bool :=
  Link.kinds.all fun k => Λ.abortLbl k == Link.abortName k

/-- **A1's layout facts**: `.rodata` clear of the stack pool, the regions
of their own tied to the output (`regionsTied`), the layout below `2 ^ 32`
(`below32`), the standard abort labels (`abortStd`). -/
def layoutOk (secs : DataSecs) (Λ : Layout) : Bool :=
  Link.disjB Λ.rodata Λ.stackPool && regionsTied secs Λ && below32 Λ && abortStd Λ

/-- **The allocator's arena in 16-byte cells**: the limit `scc_rt_alloc`
compares its counter with, the constant of the runtime's fixed code that A7
checks (`allocIn`: AArch64 `movz x10, #64, lsl #16`, x86-64
`movq $4194304, %rcx`; tied to that code by `PlaceOK.A64.allocCells_eq_lit` and
`PlaceOK.X64.allocCells_eq_lit`). -/
def allocCells : Nat := 4194304

/-- The allocator's counter (`scc_rt_heap_use`, in cells). -/
def heapUseSym : String := "scc_rt_heap_use"

/-- The allocator's counter's address in the link's symbols (0 if not
listed). -/
def heapUseOf (Λ : Layout) : Nat := (Λ.symbols.lookup heapUseSym).getD 0

/-- **The heap arena holds the allocator's cells** (A8): `16 * allocCells`
bytes from the arena's base lie in `Λ.heap`, so an allocation the
allocator accepts stays in the arena. -/
def heapSizeOk (Λ : Layout) : Bool := decide (16 * allocCells ≤ Λ.heap.size)

theorem heapSize_of_heapSizeOk {Λ : Layout} (h : heapSizeOk Λ = true) : 16 * allocCells ≤ Λ.heap.size :=
  of_decide_eq_true h

/-- **The static data below the heap**: `.data` ends at or below the heap's
start, so the counter word (in `.data`) is below every word the allocator
stores (its header at `heap + 16 o + 8·n·m`). -/
def dataBelowHeap (Λ : Layout) : Bool := decide (Λ.data.lo + Λ.data.size ≤ Λ.heap.lo)

theorem dataBelow_of_dataBelowHeap {Λ : Layout} (h : dataBelowHeap Λ = true) :
    Λ.data.lo + Λ.data.size ≤ Λ.heap.lo :=
  of_decide_eq_true h

section LayoutOk

variable {secs : DataSecs} {Λ : Layout}

theorem rodata_stackPool_of_layoutOk (h : layoutOk secs Λ = true) : Λ.rodata.Disjoint Λ.stackPool := by
  simp only [layoutOk, Bool.and_eq_true] at h; exact Link.disjB_iff.mp h.1.1.1

theorem regionsTied_of_layoutOk (h : layoutOk secs Λ = true) : regionsTied secs Λ = true := by
  simp only [layoutOk, Bool.and_eq_true] at h; exact h.1.1.2

theorem below32_of_layoutOk (h : layoutOk secs Λ = true) :
    ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32 := by
  simp only [layoutOk, below32, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h; exact h.1.2

/-- **The abort labels are the runtime's** (`abortStd`): the static link's
`abortLbl` (`Link.abortName`), whatever layout passed the check. -/
theorem abortLbl_of_layoutOk (h : layoutOk secs Λ = true) : Λ.abortLbl = Link.abortName := by
  simp only [layoutOk, abortStd, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact funext fun k => h.2 k (Link.mem_kinds k)

/-- **Below `2 ^ 32`, clear of the Linux entry stack**: the facts the
entry state `Entry.linux` was checked for before A1 became independent of
it. -/
theorem clear_of_below32 (h : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    Entry.linux.clear Λ = true := by
  simp only [Entry.clear, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
  refine ⟨by decide, fun r hr => Or.inl ?_⟩
  have := h r hr
  have hlo : Entry.linux.stack.lo = 2 ^ 47 - 4096 - 65536 := rfl
  omega

end LayoutOk

theorem layoutOk_withImms (secs : DataSecs) (Λ : Layout) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    layoutOk secs { Λ with imms := i } = layoutOk secs Λ := rfl

end Scc.Cert.PlaceOK
