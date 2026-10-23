/-
A stack-map table in data, reached from the code through a data symbol, at
binary instruction lengths. The program

    leaq scc_stackmap(%rip), %rdi
    movq 8(%rdi), %rsi
    call f
  ret_site:
    movq $1, %rax
  f:
    ret

at lengths `[7, 4, 5, 7, 1]` with the `.rodata` section of
`SizedLayoutData.lean` at `0x200000` in its private memory (`mkStateData`)
and its labels as the thread's data symbols (`syms = dataSyms dataBase
items`, so that `leaq scc_stackmap(%rip)` resolves). The three steps are:
`leaq` puts the table's address in `rdi`, the load reads the table's
`.quad ret_site` word into `rsi`, and `call f` pushes the same address
(`rsi_eq_retAddr`). With symbols the end address is the end of the code
only, so the `CellAt`s come from `cellAt_mkStateData`
(`Lower/CodeSegX64Syms.lean`), not `cellAt_of_codeAt`.
-/
import Kraken.X64.Parser
import Kraken.Promising.Lower.CodeSegX64Syms

namespace Kraken.X64.Examples.SizedLayoutSyms

open Kraken.X64.Parser
open Kraken Kraken.DataImage Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

/-- The program: take the table's address, load its second word, call `f`. -/
def prog : Program := parse("
  leaq scc_stackmap(%rip), %rdi
  movq 8(%rdi), %rsi
  call f
ret_site:
  movq $1, %rax
f:
  ret
")

/-- The instruction lengths, in text order. -/
def table : List Nat := [7, 4, 5, 7, 1]

/-- The cells at those lengths. -/
def cells : List (Directive × Nat) :=
  match prog with
  | [a, b, c, l, m, f, r] => [(a, 7), (b, 4), (c, 5), (l, 0), (m, 7), (f, 0), (r, 1)]
  | _ => []

theorem sizedCells_prog : sizedCells prog table = some cells := rfl

/-- The `.rodata` section. -/
def items : List Item :=
  [.align 8, .label "scc_stackmap", .quad 1, .quadLabel "ret_site", .quad 0]

/-- Where the section is placed. -/
abbrev dataBase : Nat := 0x200000

/-- The data symbols. -/
abbrev syms : List (String × BitVec 64) := dataSyms dataBase items

#guard_msgs in
#guard syms == [("scc_stackmap", 0x200000#64)]

/-- Thread 0's base address. -/
abbrev base : Int64 := Int64.ofNat 0x100000

/-- The cells of the thread's executable: the code, the padding up to the
section, and the symbol's label. -/
def exeCells : List (Directive × Nat) :=
  cells ++ [(.byteArray (.mk #[]), 0x200000 - (0x100000 + 24)), (.label "scc_stackmap", 0)]

/-- The label offsets: the code labels as the object file's symbol table gives
them, and the data symbol. -/
def labelOffs : List (Label × Nat) := [("ret_site", 16), ("f", 23), ("scc_stackmap", 0x100000)]

theorem sizeCheck_exe : SizeCheck base exeCells labelOffs = true := by decide

theorem sizeCheck_code : SizeCheck base cells [("ret_site", 16), ("f", 23)] = true := by decide

-- A symbol at the end of the code (an empty padding cell) fails the check.
#guard_msgs in
#guard !SizeCheck base (cells ++ [(.byteArray (.mk #[]), 0), (.label "scc_stackmap", 0)]) []

variable (regs : Reg64s) (dmem : DataMem)

/-- Thread 0 at the binary's lengths, with the table in its memory and its
labels as data symbols. -/
abbrev st0 : State := mkStateData 0 cells regs dataBase items syms dmem

theorem st0_exe : (st0 regs dmem).exe = (base, exeCells) := rfl

theorem validLayout_st0 : Kraken.Executable.ValidLayout (st0 regs dmem).exe := by
  rw [st0_exe]; exact validLayout_of_sizeCheck sizeCheck_exe

theorem scc_stackmap_addr : labelAddr (st0 regs dmem) "scc_stackmap" = base + .ofNat 0x100000 := by
  rw [labelAddr, st0_exe]; exact label_of_sizeCheck' sizeCheck_exe (by decide)

/-- `codeAt` at the base: the three instructions before `ret_site`, then the
rest of the cells. -/
theorem codeAt_base : Kraken.Executable.codeAt (st0 regs dmem).exe base = cells.take 3 ++ exeCells.drop 3 := by
  rw [st0_exe, show base = (base, exeCells).1 from rfl, Kraken.Executable.codeAt_start]; rfl

/-- **Instruction `j` of the run at the base is a `CellAt`**, in any machine
data, although the end address is short of the symbol cells. -/
theorem cellAt_run (m : MachineData) {j : Nat} {i : Instr} {sz : Nat}
    (hd : (cells.take 3)[j]? = some (.instr i, sz)) :
    CellAt { st0 regs dmem with st := (m, base + .ofNat (((cells.take 3).take j).map (·.2)).sum) }
      (.instr i) sz := by
  obtain ⟨ds, h1, h2⟩ := mkStateCells_split 0 cells regs syms (imageMem 0 cells dmem dataBase items) [] {}
  exact cellAt_segment_instr (st := st0 regs dmem) (validLayout_st0 regs dmem) h1 h2
    (mkStateCells_endPc_code 0 cells regs syms (imageMem 0 cells dmem dataBase items) [] {})
    (codeAt_base regs dmem) (by decide) hd m

/-- The `leaq` operand. -/
abbrev leaM : AddrExpr :=
  { base := some .rip, idx := none, disp := .sub (.label "scc_stackmap") .after_current_instruction }

/-- The load operand. -/
abbrev ldM : AddrExpr := { base := some (.reg .rdi), idx := none, disp := .int64 8 }

/-- **The effective address of `L(%rip)`** is the address of `L`, at any cell. -/
theorem eaddr_rip_label (st : State) (sz : Nat) (L : Label) :
    eaddr st sz { base := some .rip, idx := none, disp := .sub (.label L) .after_current_instruction }
      = (labelAddr st L).toBitVec := by
  simp only [eaddr, AddrExpr.interp, ConstExpr.interp, BitVec.setWidth_eq]
  have h (x y : BitVec 64) : BitVec.ofInt 64 (x.toInt + 0 + y.toInt) = x + y := by
    rw [Int.add_zero, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  refine (h _ _).trans ?_
  rw [Int64.toBitVec_sub, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The machine data after the `leaq`. -/
abbrev m1 : MachineData := { (st0 regs dmem).st.1 with regs := regs.set (.low .rdi .W64) 0x200000#64 }

/-- **`leaq scc_stackmap(%rip), %rdi`**: no event; `rdi` is the table's
address. -/
theorem step_lea : isa.exec (st0 regs dmem) = some (.done (after (st0 regs dmem) 7 (m1 regs dmem))) := by
  have hc : CellAt (st0 regs dmem) (op64 (.lea (.low .rdi .W64) leaM)) 7 := cellAt_run regs dmem _ (j := 0) rfl
  rw [exec_lea hc, eaddr_rip_label, scc_stackmap_addr]
  rfl

/-- The state after the `leaq`. -/
abbrev st1 : State := after (st0 regs dmem) 7 (m1 regs dmem)

/-- The value of the table's second word: the address of `ret_site`. -/
abbrev retSite : BitVec 64 := (threadBase 0 + .ofNat 16).toBitVec

/-- The machine data after the load. -/
abbrev m2 : MachineData := { (m1 regs dmem) with regs := (m1 regs dmem).regs.set (.low .rsi .W64) (retSite) }

/-- **`movq 8(%rdi), %rsi`**: the table is in private memory, so no event;
`rsi` is the table's `.quad ret_site` word. -/
theorem step_load : isa.exec (st1 regs dmem) = some (.done (after (st1 regs dmem) 4 (m2 regs dmem))) := by
  have hc : CellAt (st1 regs dmem) (op64 (.mov (.reg (.low .rsi .W64)) (.mem ldM))) 4 :=
    cellAt_run regs dmem _ (j := 1) rfl
  have hw := load_quadLabel_sized (tid := 0) (dmem := dmem) (dataBase := dataBase) (items := items)
    sizeCheck_code (L := "ret_site") (off := 16) (by decide) rfl (by decide) (n := 3) rfl
  obtain ⟨j, hj, hv⟩ := Option.map_eq_some_iff.mp hw
  have ha : eaddr (st1 regs dmem) 4 ldM = BitVec.ofNat 64 (addrAt dataBase items 3) := by
    rw [eaddr_reg_disp]; rfl
  rw [exec_load_mapped hc ha hj, hv]

/-- The state after the load: at the `call`. -/
abbrev st2 : State := after (st1 regs dmem) 4 (m2 regs dmem)

/-- The `call f` is the cell at `st2`. -/
theorem cellAt_call :
    CellAt (st2 regs dmem) (op64 (.call (.rel (.sub (.label "f") .after_current_instruction)))) 5 :=
  cellAt_run regs dmem _ (j := 2) rfl

/-- **The loaded word is the address `call f` pushes**: two no-event steps
from the start reach the `call` with `rsi` holding the table's word, which is
the `call`'s return address, the address of `ret_site`. -/
theorem rsi_eq_retAddr :
    isa.exec (st0 regs dmem) = some (.done (st1 regs dmem)) ∧
      isa.exec (st1 regs dmem) = some (.done (st2 regs dmem)) ∧
      (st2 regs dmem).st.1.regs.get64 .rsi = retAddr (st2 regs dmem) 5 ∧
      retAddr (st2 regs dmem) 5 = (labelAddr (st0 regs dmem) "ret_site").toBitVec := by
  refine ⟨step_lea regs dmem, step_load regs dmem, rfl, ?_⟩
  rw [labelAddr, st0_exe, label_of_sizeCheck' sizeCheck_exe (L := "ret_site") (off := 16) (by decide)]
  rfl

/-- **`call f`** then pushes `rsi`'s value: with the stack slot mapped, the
step jumps to `f` having stored `retAddr st2 5`. -/
theorem step_call {j : Int}
    (hdm : Mem.loadInt (st2 regs dmem).st.1.dmem (rspOf (st2 regs dmem).st.1 - 8#64) 8 = some j) :
    isa.exec (st2 regs dmem) = some (.done (jumpTo (st2 regs dmem) (callPost (st2 regs dmem) 5)
      (labelAddr (st2 regs dmem) "f"))) :=
  exec_call_label (cellAt_call regs dmem) hdm

end Kraken.X64.Examples.SizedLayoutSyms
