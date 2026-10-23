/-
**Cells of a laid-out x64 program with data symbols** (`CellAt`).

`cellAt_of_codeAt` asks the end address to be the end of the whole cell
list (`hend`), which fails when `syms ≠ []`: `mkState` / `mkStateCells` /
`mkStateData` place a padding cell and a label cell per data symbol after the
code, and the end address is the end of the code. Here the end bound is over
the code prefix only:

- `cellAt_of_codeAt_instr`: an instruction `codeAt` finds at the pc is a
  `CellAt`, given a valid layout, the cells split as code `cs` followed by
  cells none of which is an instruction, and the end address at the end of
  `cs`;
- `cellAt_segment_instr`: the same for every instruction of a label-free run;
- `mkStateCells_split`, `mkState_split`: the cells of `mkStateCells` /
  `mkState` are the code cells followed by the symbol cells (padding and
  labels), for any `syms`, and the end address is the end of the code
  (`mkStateCells_endPc_code`, `mkState_endPc_code`);
- `cellAt_mkStateCells`, `cellAt_mkStateData`, `cellAt_mkState`: the three
  together, for the thread states of those constructors with any `syms`.
-/
import Kraken.Promising.Lower.CodeSegX64
import Kraken.Promising.X64Data
import Kraken.CodeAtPrefix

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- **An instruction `codeAt` finds at the pc is a `CellAt`**, when the end
address is the end of the code prefix `cs` of the cells. -/
theorem cellAt_of_codeAt_instr {st : State} {i : Instr} {sz : Nat} {rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe) {cs ds : List (Directive × Nat)}
    (hsplit : st.exe.2 = cs ++ ds) (hds : ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i)
    (hend : st.endPc = st.exe.1 + .ofNat (cs.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe st.st.2 = (.instr i, sz) :: rest) : CellAt st (.instr i) sz := by
  refine ⟨hv, ?_, rest, h⟩
  rw [hend]
  exact beq_false_of_ne (Kraken.Executable.codeAt_ne_prefix_end st.exe hsplit hds h)

/-- **A label-free run of cells at `pc`**, the end address at the end of the
code prefix: instruction cell `j` of `cs'` is the cell at `pc` plus the sizes
of the cells before it, in any machine data `m`. -/
theorem cellAt_segment_instr {st : State} {pc : Int64} {cs' rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe) {cs ds : List (Directive × Nat)}
    (hsplit : st.exe.2 = cs ++ ds) (hds : ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i)
    (hend : st.endPc = st.exe.1 + .ofNat (cs.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe pc = cs' ++ rest)
    (hcs : ∀ c ∈ cs', c.1.isLabel = false) {j : Nat} {i : Instr} {sz : Nat} (hd : cs'[j]? = some (.instr i, sz))
    (m : MachineData) :
    CellAt { st with st := (m, pc + .ofNat ((cs'.take j).map (·.2)).sum) } (.instr i) sz := by
  have hj : j < cs'.length := by
    rcases Nat.lt_or_ge j cs'.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hd; cases hd
  have hseg := Kraken.Executable.codeAt_segment st.exe h hcs j hj
  rw [List.drop_eq_getElem_cons hj, List.cons_append,
    show cs'[j] = (.instr i, sz) by rw [List.getElem?_eq_getElem hj] at hd; exact Option.some.inj hd] at hseg
  exact cellAt_of_codeAt_instr (st := { st with st := (m, pc + .ofNat ((cs'.take j).map (·.2)).sum) })
    hv hsplit hds hend hseg

/-! ## The constructors' cells -/

/-- The symbol cells `mkStateCells` appends: padding then a label, per
symbol. -/
private theorem fold_split : ∀ (syms : List (String × BitVec 64)) (cs : List (Directive × Nat)) (cur : Nat),
    ∃ ds, (syms.foldl (init := (cs, cur)) fun (p : List (Directive × Nat) × Nat) (xa : String × BitVec 64) =>
        (p.1 ++ [((.byteArray (.mk #[]) : Directive), xa.2.toNat - p.2), (.label xa.1, 0)], xa.2.toNat)).1
      = cs ++ ds ∧ ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i
  | [], cs, _ => ⟨[], by simp⟩
  | (x, a) :: syms, cs, cur => by
    obtain ⟨ds, h1, h2⟩ := fold_split syms (cs ++ [((.byteArray (.mk #[]) : Directive), a.toNat - cur),
      (.label x, 0)]) a.toNat
    refine ⟨[((.byteArray (.mk #[]) : Directive), a.toNat - cur), (.label x, 0)] ++ ds, ?_, ?_⟩
    · simpa using h1
    · intro c hc i
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl) | hc
      · simp
      · simp
      · exact h2 c hc i

/-- **`mkStateCells`' cells**: the code cells followed by symbol cells, none
an instruction, for any `syms`. -/
theorem mkStateCells_split (tid : Nat) (cells : List (Directive × Nat)) (regs : Reg64s)
    (syms : List (String × BitVec 64)) (dmem : DataMem) (texts : List String) (decls : Decls) :
    ∃ ds, (mkStateCells tid cells regs syms dmem texts decls).exe.2 = cells ++ ds ∧
      ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i :=
  fold_split syms cells _

/-- `mkStateCells`' executable starts at the thread's base. -/
theorem mkStateCells_exe_base (tid : Nat) (cells : List (Directive × Nat)) (regs : Reg64s)
    (syms : List (String × BitVec 64)) (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkStateCells tid cells regs syms dmem texts decls).exe.1 = threadBase tid := rfl

/-- **`mkStateCells`' end address is the end of the code**, for any `syms`. -/
theorem mkStateCells_endPc_code (tid : Nat) (cells : List (Directive × Nat)) (regs : Reg64s)
    (syms : List (String × BitVec 64)) (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkStateCells tid cells regs syms dmem texts decls).endPc
      = (mkStateCells tid cells regs syms dmem texts decls).exe.1 + .ofNat (cells.map (·.2)).sum := rfl

/-- **An instruction at the pc of a `mkStateCells` state is a `CellAt`**, for
any `syms`, given a valid layout of the whole cell list. -/
theorem cellAt_mkStateCells {tid : Nat} {cells : List (Directive × Nat)} {regs : Reg64s}
    {syms : List (String × BitVec 64)} {dmem : DataMem} {texts : List String} {decls : Decls}
    {st : State} (hst : st = mkStateCells tid cells regs syms dmem texts decls)
    (m : MachineData) (pc : Int64)
    (hv : Kraken.Executable.ValidLayout st.exe) {i : Instr} {sz : Nat} {rest : List (Directive × Nat)}
    (h : Kraken.Executable.codeAt st.exe pc = (.instr i, sz) :: rest) :
    CellAt { st with st := (m, pc) } (.instr i) sz := by
  subst hst
  obtain ⟨ds, h1, h2⟩ := mkStateCells_split tid cells regs syms dmem texts decls
  exact cellAt_of_codeAt_instr (st := { mkStateCells tid cells regs syms dmem texts decls with st := (m, pc) })
    hv h1 h2 (mkStateCells_endPc_code tid cells regs syms dmem texts decls) h

/-- `cellAt_mkStateCells` for `mkStateData`. -/
theorem cellAt_mkStateData {tid : Nat} {cells : List (Directive × Nat)} {regs : Reg64s} {dataBase : Nat}
    {items : List DataImage.Item} {syms : List (String × BitVec 64)} {dmem : DataMem} {texts : List String}
    {decls : Decls} {st : State} (hst : st = mkStateData tid cells regs dataBase items syms dmem texts decls)
    (m : MachineData) (pc : Int64)
    (hv : Kraken.Executable.ValidLayout st.exe) {i : Instr} {sz : Nat} {rest : List (Directive × Nat)}
    (h : Kraken.Executable.codeAt st.exe pc = (.instr i, sz) :: rest) :
    CellAt { st with st := (m, pc) } (.instr i) sz :=
  cellAt_mkStateCells (hst.trans (mkStateData_eq ..)) m pc hv h

/-- **`mkState`'s cells**: the one-byte code cells followed by symbol cells,
none an instruction, for any `syms`. -/
theorem mkState_split (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64))
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    ∃ ds, (mkState tid prog regs syms dmem texts decls).exe.2 = prog.map (fun d => (d, unitSize d)) ++ ds ∧
      ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i := by
  rw [← mkStateCells_unit_exe tid prog regs syms dmem texts decls]
  exact mkStateCells_split ..

/-- **`mkState`'s end address is the end of the code**, for any `syms`. -/
theorem mkState_endPc_code (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64))
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkState tid prog regs syms dmem texts decls).endPc
      = (mkState tid prog regs syms dmem texts decls).exe.1
        + .ofNat ((prog.map (fun d => (d, unitSize d))).map (·.2)).sum := by
  rw [← mkStateCells_unit_exe tid prog regs syms dmem texts decls,
    ← mkStateCells_unit_endPc tid prog regs syms dmem texts decls]
  rfl

/-- **An instruction at the pc of a `mkState` state is a `CellAt`**, for any
`syms`, given a valid layout. -/
theorem cellAt_mkState {tid : Nat} {prog : Program} {regs : Reg64s} {syms : List (String × BitVec 64)}
    {dmem : DataMem} {texts : List String} {decls : Decls}
    {st : State} (hst : st = mkState tid prog regs syms dmem texts decls)
    (m : MachineData) (pc : Int64)
    (hv : Kraken.Executable.ValidLayout st.exe) {i : Instr} {sz : Nat} {rest : List (Directive × Nat)}
    (h : Kraken.Executable.codeAt st.exe pc = (.instr i, sz) :: rest) :
    CellAt { st with st := (m, pc) } (.instr i) sz := by
  subst hst
  obtain ⟨ds, h1, h2⟩ := mkState_split tid prog regs syms dmem texts decls
  exact cellAt_of_codeAt_instr (st := { mkState tid prog regs syms dmem texts decls with st := (m, pc) })
    hv h1 h2 (mkState_endPc_code tid prog regs syms dmem texts decls) h

end Kraken.Promising.Lower.X64
