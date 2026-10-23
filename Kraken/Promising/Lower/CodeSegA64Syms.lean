/-
**Cells of a laid-out AArch64 program with data symbols** (`CellAt`).

`Promising.AArch64.mkState` has no data symbols. `mkStateSyms` is `mkState`
with symbolic data locations named by `syms` (name, address) placed after the
code as labels behind padding, as x64's `mkState` does; the end address stays
at the end of the code. With `syms = []` it lays out the executable of
`mkState` (`mkStateSyms_nil_exe`).

- `cellAt_of_codeAt_instr`, `cellAt_segment4_instr`: `cellAt_of_codeAt` /
  `cellAt_segment4` with the end address at the end of a code prefix `cs` of
  the cells, the cells after it none an instruction;
- `mkStateSyms_split`, `mkStateSyms_endPc_code`: the cells of `mkStateSyms`
  are the code cells followed by the symbol cells, the end address the end of
  the code;
- `cellAt_mkStateSyms`: the two together;
- `validLayout_of_cellsOk`: a decidable check of `ValidLayout` for a concrete
  cell list (padding of size 0, i.e. a symbol at the end of the code or two
  symbols at one address, fails it).

The index computation is `Kraken/AArch64/WP/CodeAtPrefix.lean`.
-/
import Kraken.Promising.Lower.CodeSegA64
import Kraken.AArch64.WP.CodeAtPrefix

namespace Kraken.Promising.AArch64

/-- `mkState` with symbolic data locations named by `syms` (name, address)
placed after the code: a padding cell up to the address then a label, per
symbol, in order (as x64's `mkState`). Each directive is its `fakeSize`;
the end address is the end of the code. -/
def mkStateSyms (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64) := [])
    (dmem : DataMem := ∅) (texts : List String := []) (decls : Decls := {}) : State :=
  let base : Int64 := Int64.ofNat (0x100000 * (tid + 1))
  let codeCells : List (Directive × Nat) := prog.map fun d => (d, d.fakeSize)
  let codeLen := (codeCells.map (·.2)).sum
  let pad (n : Nat) : Directive × Nat := (.byteArray (.mk #[]), n)
  let (cells, _) := syms.foldl (init := (codeCells, base.toBitVec.toNat + codeLen)) fun (cells, cur) (x, a) =>
    (cells ++ [pad (a.toNat - cur), (.label x, 0)], a.toNat)
  let exe : _root_.Executable := (base, cells)
  let instrs := prog.filter fun d => match d with | .label _ => false | _ => true
  { exe, endPc := base + Int64.ofNat codeLen, st := ({ regs, dmem }, base), decls,
    showPc := fun pc =>
      let i := ((pc - base).toBitVec.toNat) / 4
      match texts[i]?, instrs[i]? with
      | some t, _ => t | none, some d => toString (repr d) | none, none => s!"pc={pc}" }

/-- The symbol cells `mkStateSyms` appends: padding then a label, per symbol. -/
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

/-- **`mkStateSyms`' cells**: the code cells, each directive its `fakeSize`,
followed by symbol cells none of which is an instruction. -/
theorem mkStateSyms_split (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64))
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    ∃ ds, (mkStateSyms tid prog regs syms dmem texts decls).exe.2 = prog.map (fun d => (d, d.fakeSize)) ++ ds ∧
      ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i :=
  fold_split syms _ _

/-- `mkStateSyms`' executable starts at `0x100000 * (tid + 1)`. -/
theorem mkStateSyms_exe_base (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64))
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkStateSyms tid prog regs syms dmem texts decls).exe.1 = Int64.ofNat (0x100000 * (tid + 1)) := rfl

/-- `mkStateSyms` starts at the start of its text. -/
theorem mkStateSyms_pc (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64))
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkStateSyms tid prog regs syms dmem texts decls).st.2
      = (mkStateSyms tid prog regs syms dmem texts decls).exe.1 := rfl

/-- **`mkStateSyms`' end address is the end of the code**, for any `syms`. -/
theorem mkStateSyms_endPc_code (tid : Nat) (prog : Program) (regs : Reg64s) (syms : List (String × BitVec 64))
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkStateSyms tid prog regs syms dmem texts decls).endPc
      = (mkStateSyms tid prog regs syms dmem texts decls).exe.1
        + .ofNat ((prog.map (fun d => (d, d.fakeSize))).map (·.2)).sum := rfl

/-- With no symbols, `mkStateSyms` lays out `mkState`'s executable. -/
theorem mkStateSyms_nil_exe (tid : Nat) (prog : Program) (regs : Reg64s) (dmem : DataMem)
    (texts : List String) (decls : Decls) :
    (mkStateSyms tid prog regs [] dmem texts decls).exe = (mkState tid prog regs dmem texts decls).exe := by
  rw [mkState_exe]; rfl

end Kraken.Promising.AArch64

namespace Kraken.Executable

/-- A cell's size as `ValidLayout` asks: 0 for a label, 4 for an instruction,
positive for data. -/
def cellOk : Directive × Nat → Bool
  | (.label _, z) => z == 0
  | (.instr _, z) => z == 4
  | (.byteArray _, z) => 0 < z

/-- **A decidable check of `ValidLayout`**: every cell is `cellOk` and the
cells fit the address space. -/
theorem validLayout_of_cellsOk (e : Kraken.Executable Directive) (hc : e.2.all cellOk = true)
    (hw : (e.2.map (·.2)).sum < 2 ^ 64) : ValidLayout e where
  label_size i l z h := by
    have := List.all_eq_true.mp hc _ (List.mem_of_getElem? h)
    simpa [cellOk] using this
  instr_size i ins z h := by
    have := List.all_eq_true.mp hc _ (List.mem_of_getElem? h)
    simpa [cellOk] using this
  data_size i a z h := by
    have := List.all_eq_true.mp hc _ (List.mem_of_getElem? h)
    simpa [cellOk] using this
  no_wrap := hw

end Kraken.Executable

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

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

/-- **A label-free run of instructions at `pc`**, the end address at the end
of the code prefix: instruction `j` of `is` is the 4-byte cell at
`pc + 4j`, in any machine data `m`. -/
theorem cellAt_segment4_instr {st : State} {pc : Int64} {is : List Instr} {rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe) {cs ds : List (Directive × Nat)}
    (hsplit : st.exe.2 = cs ++ ds) (hds : ∀ c ∈ ds, ∀ i, c.1 ≠ .instr i)
    (hend : st.endPc = st.exe.1 + .ofNat (cs.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe pc = (is.map Directive.instr).map (·, 4) ++ rest)
    {j : Nat} {i : Instr} (hi : is[j]? = some i)
    (m : MachineData) : CellAt { st with st := (m, pc + .ofNat (4 * j)) } (.instr i) 4 := by
  have hj : j < is.length := by
    rcases Nat.lt_or_ge j is.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hi; cases hi
  have hl : ∀ d ∈ is.map Directive.instr, d.isLabel = false := by
    intro d hd
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hd
    rfl
  have hj' : j < (is.map Directive.instr).length := by simpa using hj
  have hseg := Kraken.Executable.codeAt_segment4 st.exe h hl j hj'
  rw [List.drop_eq_getElem_cons hj', List.map_cons, List.cons_append, List.getElem_map,
    show is[j] = i by rw [List.getElem?_eq_getElem hj] at hi; exact Option.some.inj hi] at hseg
  exact cellAt_of_codeAt_instr (st := { st with st := (m, pc + .ofNat (4 * j)) }) hv hsplit hds hend hseg

/-- **An instruction at the pc of a `mkStateSyms` state is a `CellAt`**, for
any `syms`, given a valid layout of the whole cell list. -/
theorem cellAt_mkStateSyms {tid : Nat} {prog : Program} {regs : Reg64s} {syms : List (String × BitVec 64)}
    {dmem : DataMem} {texts : List String} {decls : Decls}
    {st : State} (hst : st = mkStateSyms tid prog regs syms dmem texts decls)
    (m : MachineData) (pc : Int64)
    (hv : Kraken.Executable.ValidLayout st.exe) {i : Instr} {sz : Nat} {rest : List (Directive × Nat)}
    (h : Kraken.Executable.codeAt st.exe pc = (.instr i, sz) :: rest) :
    CellAt { st with st := (m, pc) } (.instr i) sz := by
  subst hst
  obtain ⟨ds, h1, h2⟩ := mkStateSyms_split tid prog regs syms dmem texts decls
  exact cellAt_of_codeAt_instr (st := { mkStateSyms tid prog regs syms dmem texts decls with st := (m, pc) })
    hv h1 h2 (mkStateSyms_endPc_code tid prog regs syms dmem texts decls) h

end Kraken.Promising.Lower.A64
