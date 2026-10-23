/-
**Sized x64 code layout for a thread.**

`mkState` lays a parsed program out one byte per instruction. A binary lays it
out at the instruction lengths the assembler chose, which is what a return
address pushed by `call` or a label stored in data (`.quad L`) records. This
file gives the same thread state with the cell sizes taken from a table, one
length per non-label directive in text order, supplied from outside (say, a
certificate read off the object file's listing):

- `sizedCells prog table`: the cells of `prog` with labels at size 0 and every
  other directive at the next table entry (`none` if the lengths disagree);
  `sizedCells_unit`: the all-ones table gives `mkState`'s cells;
- `mkStateCells` / `mkStateSized`: `mkState` with those cells; on the
  executable, end address, start state and declarations `mkStateCells` with
  the unit cells is `mkState` (`mkStateCells_unit_*`);
- `SizeCheck base cells labelOffs`: a decidable consistency check of the table
  (positive instruction sizes, empty labels, no wrap, `nopalign` targets
  aligned, and each listed label at the listed byte offset). The table is
  not checked against an encoder: `validLayout_of_sizeCheck` gives
  `ValidLayout`, and `label_of_sizeCheck` the label's address, so the
  `codeAt`/`CellAt` lemmas (`Kraken/CodeAt.lean`,
  `Lower/CodeSegX64.lean`) apply unchanged; `mkStateCells_endPc` is their end
  address hypothesis when there are no symbols.

The step relation is untouched: `Executable.step` already advances by the
cell's size and `call` pushes the pc plus the cell's size.
-/
import Kraken.Promising.X64
import Kraken.CodeAt

namespace Kraken.Promising.X64

open Kraken

/-- One byte per instruction, none per label: the cell size `mkState` uses. -/
def unitSize : Directive → Nat
  | .label _ => 0
  | _ => 1

/-- The cells of a program at the lengths of a table: a label takes no bytes
and no table entry, every other directive takes the next entry. `none` when
the table is shorter or longer than the program's non-label directives. -/
def sizedCells : Program → List Nat → Option (List (Directive × Nat))
  | [], [] => some []
  | [], _ :: _ => none
  | .label l :: ds, t => (sizedCells ds t).map ((.label l, 0) :: ·)
  | d :: ds, t =>
    match t with
    | [] => none
    | z :: t => (sizedCells ds t).map ((d, z) :: ·)

/-- The all-ones table of a program: one entry of `1` per non-label directive. -/
def unitTable (prog : Program) : List Nat :=
  prog.filterMap fun d => match d with | .label _ => none | _ => some 1

/-- The all-ones table lays a program out as `mkState` does. -/
theorem sizedCells_unit : ∀ prog : Program,
    sizedCells prog (unitTable prog) = some (prog.map fun d => (d, unitSize d))
  | [] => rfl
  | d :: ds => by
    have ih := sizedCells_unit ds
    simp only [unitTable, unitSize] at ih
    cases d <;> simp [unitTable, unitSize, sizedCells, ih]

/-- `sizedCells` keeps the directives in order. -/
theorem sizedCells_fst : ∀ {prog : Program} {t : List Nat} {cells : List (Directive × Nat)},
    sizedCells prog t = some cells → cells.map (·.1) = prog
  | [], [], cells, h => by simp [sizedCells] at h; subst h; rfl
  | [], _ :: _, _, h => by simp [sizedCells] at h
  | .label l :: ds, t, cells, h => by
    simp only [sizedCells, Option.map_eq_some_iff] at h
    obtain ⟨cs, hcs, rfl⟩ := h
    simp [sizedCells_fst hcs]
  | .instr i :: ds, [], _, h => by simp [sizedCells] at h
  | .instr i :: ds, z :: t, cells, h => by
    simp only [sizedCells, Option.map_eq_some_iff] at h
    obtain ⟨cs, hcs, rfl⟩ := h
    simp [sizedCells_fst hcs]
  | .byteArray a :: ds, [], _, h => by simp [sizedCells] at h
  | .byteArray a :: ds, z :: t, cells, h => by
    simp only [sizedCells, Option.map_eq_some_iff] at h
    obtain ⟨cs, hcs, rfl⟩ := h
    simp [sizedCells_fst hcs]

/-- The index among the non-label cells of the instruction at `pc`, walking
the cells from address `a` with index `i`; for `showPc`. -/
def instrIndexAt (pc : Int64) : Int64 → Nat → List (Directive × Nat) → Option Nat
  | _, _, [] => none
  | a, i, (.label _, _) :: cs => instrIndexAt pc a i cs
  | a, i, (_, z) :: cs => if a == pc then some i else instrIndexAt pc (a + .ofNat z) (i + 1) cs

/-- `mkState` with given code cells: laid out at `0x100000 * (tid + 1)`,
halting after the last cell, symbolic data locations named by `syms` placed
after the code as in `mkState`. `showPc` finds the instruction by address. -/
def mkStateCells (tid : Nat) (codeCells : List (Directive × Nat)) (regs : Reg64s)
    (syms : List (String × BitVec 64) := []) (dmem : DataMem := ∅) (texts : List String := [])
    (decls : Decls := {}) : State :=
  let base : Int64 := Int64.ofNat (0x100000 * (tid + 1))
  let codeLen := (codeCells.map (·.2)).sum
  let pad (n : Nat) : Directive × Nat := (.byteArray (.mk #[]), n)
  let (cells, _) := syms.foldl (init := (codeCells, base.toBitVec.toNat + codeLen)) fun (cells, cur) (x, a) =>
    (cells ++ [pad (a.toNat - cur), (.label x, 0)], a.toNat)
  let exe : _root_.Executable := (base, cells)
  let instrs := (codeCells.filter fun c => match c.1 with | .label _ => false | _ => true).map (·.1)
  { exe, endPc := base + Int64.ofNat codeLen, st := ({ regs, dmem }, base), decls,
    showPc := fun pc =>
      match instrIndexAt pc base 0 codeCells with
      | some i =>
        match texts[i]?, instrs[i]? with
        | some t, _ => t | none, some d => toString (repr d) | none, none => s!"pc={pc}"
      | none => s!"pc={pc}" }

/-- A thread state for a parsed program at the instruction lengths of
`table` (see `sizedCells`); `none` when the table does not fit the program. -/
def mkStateSized (tid : Nat) (prog : Program) (table : List Nat) (regs : Reg64s)
    (syms : List (String × BitVec 64) := []) (dmem : DataMem := ∅) (texts : List String := [])
    (decls : Decls := {}) : Option State :=
  (sizedCells prog table).map fun cells => mkStateCells tid cells regs syms dmem texts decls

section unit
variable (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64))
  (dmem : DataMem) (texts : List String) (decls : Decls)

/-- With the unit cells, `mkStateCells` lays out the same executable as `mkState`. -/
theorem mkStateCells_unit_exe :
    (mkStateCells tid (prog.map fun d => (d, unitSize d)) regs syms dmem texts decls).exe
      = (mkState tid prog regs syms dmem texts decls).exe := rfl

/-- With the unit cells, `mkStateCells` has `mkState`'s end address. -/
theorem mkStateCells_unit_endPc :
    (mkStateCells tid (prog.map fun d => (d, unitSize d)) regs syms dmem texts decls).endPc
      = (mkState tid prog regs syms dmem texts decls).endPc := rfl

/-- With the unit cells, `mkStateCells` has `mkState`'s start state. -/
theorem mkStateCells_unit_st :
    (mkStateCells tid (prog.map fun d => (d, unitSize d)) regs syms dmem texts decls).st
      = (mkState tid prog regs syms dmem texts decls).st := rfl

/-- With the unit cells, `mkStateCells` has `mkState`'s declarations. -/
theorem mkStateCells_unit_decls :
    (mkStateCells tid (prog.map fun d => (d, unitSize d)) regs syms dmem texts decls).decls
      = (mkState tid prog regs syms dmem texts decls).decls := rfl

/-- The all-ones table gives `mkState`'s layout: `mkStateSized` succeeds, with
`mkState`'s executable, end address and start state. -/
theorem mkStateSized_unit :
    ∃ s, mkStateSized tid prog (unitTable prog) regs syms dmem texts decls = some s ∧
      s.exe = (mkState tid prog regs syms dmem texts decls).exe ∧
      s.endPc = (mkState tid prog regs syms dmem texts decls).endPc ∧
      s.st = (mkState tid prog regs syms dmem texts decls).st :=
  ⟨mkStateCells tid (prog.map fun d => (d, unitSize d)) regs syms dmem texts decls,
    by rw [mkStateSized, sizedCells_unit]; rfl, rfl, rfl, rfl⟩

end unit

section nosyms
variable (tid : Nat) (cells : List (Directive × Nat)) (regs : Reg64s) (dmem : DataMem)
  (texts : List String) (decls : Decls)

/-- Without symbols, the executable is the cells at the thread's base. -/
theorem mkStateCells_exe :
    (mkStateCells tid cells regs [] dmem texts decls).exe
      = (Int64.ofNat (0x100000 * (tid + 1)), cells) := rfl

/-- The start state: the registers and memory at the thread's base. -/
theorem mkStateCells_st (syms : List (String × BitVec 64)) :
    (mkStateCells tid cells regs syms dmem texts decls).st
      = ({ regs, dmem }, Int64.ofNat (0x100000 * (tid + 1))) := rfl

/-- Without symbols, the end address is the end of the text (the `hend` of
`cellAt_of_codeAt`). -/
theorem mkStateCells_endPc :
    (mkStateCells tid cells regs [] dmem texts decls).endPc
      = (mkStateCells tid cells regs [] dmem texts decls).exe.1
        + .ofNat ((mkStateCells tid cells regs [] dmem texts decls).exe.2.map (·.2)).sum := rfl

end nosyms

/-! ### Checking a table -/

/-- Whether a cell's size is consistent, `a` being the address after it: a
label is empty, every other directive occupies at least one byte, and a
`nopalign n` ends at a multiple of `n`. -/
def cellSizeOk (a : Int64) (c : Directive × Nat) : Bool :=
  match c.1 with
  | .label _ => c.2 == 0
  | .instr (.regular _ _ (.nopalign n _)) => 0 < c.2 && (n == 0 || a.toBitVec.toNat % n == 0)
  | _ => 0 < c.2

/-- The first index of a label in a cell list. -/
def labelIdx (L : Label) : List (Directive × Nat) → Option Nat
  | [] => none
  | c :: cs => if c.1 = .label L then some 0 else (labelIdx L cs).map (· + 1)

theorem labelIdx_spec {L : Label} : ∀ {cs : List (Directive × Nat)} {n : Nat},
    labelIdx L cs = some n →
      n < cs.length ∧ cs[n]?.map (·.1) = some (.label L) ∧ ∀ dz ∈ cs.take n, dz.1 ≠ .label L
  | [], _, h => by simp [labelIdx] at h
  | c :: cs, n, h => by
    unfold labelIdx at h
    by_cases hc : c.1 = .label L
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [hc]
    · simp only [hc, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := labelIdx_spec hm
      refine ⟨by simp; omega, by simpa using h2, ?_⟩
      intro dz hdz
      rw [List.take_succ_cons, List.mem_cons] at hdz
      rcases hdz with rfl | hdz
      · exact hc
      · exact h3 dz hdz

/-- **The consistency check of a size table**, on the cells it lays out at
`base`: no wrap past `2 ^ 64`, every cell's size consistent (`cellSizeOk`),
and every `(L, off)` of `labelOffs` (the label offsets of the object file)
a label of the cells whose first occurrence is `off` bytes from `base`. -/
def SizeCheck (base : Int64) (cells : List (Directive × Nat)) (labelOffs : List (Label × Nat)) : Bool :=
  decide ((cells.map (·.2)).sum < 2 ^ 64) &&
  (List.range cells.length).all (fun i => match cells[i]? with
    | some c => cellSizeOk (Kraken.Executable.addrOf (base, cells) (i + 1)) c
    | none => true) &&
  labelOffs.all fun (L, off) => match labelIdx L cells with
    | some n => Kraken.Executable.sizeBefore (base, cells) n == off
    | none => false

private theorem sizeCheck_cell {base : Int64} {cells : List (Directive × Nat)} {offs : List (Label × Nat)}
    (h : SizeCheck base cells offs = true) {i : Nat} {c : Directive × Nat} (hc : cells[i]? = some c) :
    cellSizeOk (Kraken.Executable.addrOf (base, cells) (i + 1)) c = true := by
  simp only [SizeCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hi : i < cells.length := by
    rcases Nat.lt_or_ge i cells.length with hi | hi
    · exact hi
    · rw [List.getElem?_eq_none hi] at hc; cases hc
  have := h.1.2 i hi
  rwa [hc] at this

/-- **A checked table is a valid layout.** -/
theorem validLayout_of_sizeCheck {base : Int64} {cells : List (Directive × Nat)}
    {offs : List (Label × Nat)} (h : SizeCheck base cells offs = true) :
    Kraken.Executable.ValidLayout (base, cells) where
  label_size i l z hi := by
    have := sizeCheck_cell h hi
    simpa [cellSizeOk] using this
  instr_size i d z hi hd := by
    have := sizeCheck_cell h hi
    rcases d with ins | l | a
    · unfold cellSizeOk at this
      split at this
      · simp_all
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
      · simpa using this
    · exact absurd rfl (hd l)
    · simpa [cellSizeOk] using this
  no_wrap := by
    simp only [SizeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  align_addr i aw w n pad z hi hn := by
    have := sizeCheck_cell h hi
    simp only [cellSizeOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this.2 with h0 | h0
    · omega
    · exact h0

/-- **A checked label offset is the label's address**, in the cells followed
by anything (say, the symbol pads of `mkStateCells`). -/
theorem label_of_sizeCheck {base : Int64} {cells : List (Directive × Nat)}
    {offs : List (Label × Nat)} (h : SizeCheck base cells offs = true) {L : Label} {off : Nat}
    (hL : (L, off) ∈ offs) (rest : List (Directive × Nat)) :
    (_root_.Executable.labels (base, cells ++ rest)).label L = base + .ofNat off := by
  have hoff := h
  simp only [SizeCheck, Bool.and_eq_true, List.all_eq_true] at hoff
  have hl := hoff.2 _ hL
  split at hl
  case h_2 => cases hl
  rename_i n hn
  obtain ⟨hlt, hget, hfirst⟩ := labelIdx_spec hn
  obtain ⟨c, hc⟩ : ∃ c, cells[n]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [hc] at hget
  simp only [Option.map_some, Option.some.injEq] at hget
  obtain ⟨d, z⟩ := c
  simp only at hget
  subst hget
  have hz : z = 0 := by simpa [cellSizeOk] using sizeCheck_cell h hc
  subst hz
  have := Kraken.Executable.label_addrOf (base, cells ++ rest) L n
    (by simp [List.getElem?_append_left hlt, hc])
    (by
      intro dz hdz
      rw [List.take_append_of_le_length (by omega)] at hdz
      exact hfirst dz hdz)
  rw [this]
  simp only [beq_iff_eq] at hl
  rw [← hl]
  unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
  simp [List.take_append_of_le_length (Nat.le_of_lt hlt)]

/-- `label_of_sizeCheck` on the cells alone. -/
theorem label_of_sizeCheck' {base : Int64} {cells : List (Directive × Nat)}
    {offs : List (Label × Nat)} (h : SizeCheck base cells offs = true) {L : Label} {off : Nat}
    (hL : (L, off) ∈ offs) :
    (_root_.Executable.labels (base, cells)).label L = base + .ofNat off := by
  have := label_of_sizeCheck h hL []
  rwa [List.append_nil] at this

end Kraken.Promising.X64
