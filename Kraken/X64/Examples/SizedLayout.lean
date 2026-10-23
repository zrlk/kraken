/-
A call at binary instruction lengths. `call f` is 5 bytes, `movq $1, %rax`
7 and `ret` 1 (`e8 rel32`, `48 c7 c0 imm32`, `c3`). Laid out at those
lengths (`mkStateCells`, from the table `[5, 7, 1]` by `sizedCells`), the
address `call` pushes is the address of `ret_site`, which is also the value
the assembler stores for `.quad ret_site`: both are the thread's base plus 5.
Under `mkState`'s one byte per instruction the label sits at base plus 1
instead, as `ret_site_unit` shows.
-/
import Kraken.X64.Parser
import Kraken.Promising.Lower.CodeSegX64
import Kraken.Promising.X64Sized

namespace Kraken.X64.Examples.SizedLayout

open Kraken.X64.Parser
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

/-- The program: call `f`, which returns to `ret_site`. -/
def prog : Program := parse("
  call f
ret_site:
  movq $1, %rax
f:
  ret
")

/-- The instruction lengths, in text order. -/
def table : List Nat := [5, 7, 1]

/-- The cells at those lengths. -/
def cells : List (Directive × Nat) :=
  match prog with
  | [c, l, m, f, r] => [(c, 5), (l, 0), (m, 7), (f, 0), (r, 1)]
  | _ => []

theorem sizedCells_prog : sizedCells prog table = some cells := rfl

-- A table with the wrong number of entries lays out nothing.
#guard_msgs in
#guard (sizedCells prog [5, 7]).isNone && (sizedCells prog [5, 7, 1, 1]).isNone

/-- Thread 0's base address. -/
abbrev base : Int64 := Int64.ofNat 0x100000

/-- The label offsets as the object file's symbol table gives them. -/
def labelOffs : List (Label × Nat) := [("ret_site", 5), ("f", 12)]

theorem sizeCheck_prog : SizeCheck base cells labelOffs = true := by decide

-- The table passes the check, and a wrong label offset fails it.
#guard_msgs in
#guard SizeCheck base cells labelOffs && !SizeCheck base cells [("ret_site", 1)]

variable (regs : Reg64s) (dmem : DataMem)

/-- Thread 0 at the binary's lengths. -/
abbrev st : State := mkStateCells 0 cells regs [] dmem

theorem ret_site_addr : labelAddr (st regs dmem) "ret_site" = base + 5 :=
  label_of_sizeCheck' sizeCheck_prog (by decide)

/-- The first cell is the `call`, at 5 bytes. -/
theorem cellAt_call :
    CellAt (st regs dmem) (op64 (.call (.rel (.sub (.label "f") .after_current_instruction)))) 5 :=
  cellAt_of_codeAt (validLayout_of_sizeCheck sizeCheck_prog) (mkStateCells_endPc ..)
    (by rw [mkStateCells_st, mkStateCells_exe, Kraken.Executable.codeAt_start]; rfl)

/-- **`call f` pushes the address of `ret_site`**: with the stack slot
mapped, the step jumps to `f` having stored `retAddr st 5`, and that is the
address of `ret_site` (the value of `.quad ret_site`). -/
theorem call_pushes_ret_site {j : Int}
    (hdm : Mem.loadInt (st regs dmem).st.1.dmem (rspOf (st regs dmem).st.1 - 8#64) 8 = some j) :
    isa.exec (st regs dmem) = some (.done (jumpTo (st regs dmem) (callPost (st regs dmem) 5)
        (labelAddr (st regs dmem) "f"))) ∧
      retAddr (st regs dmem) 5 = (labelAddr (st regs dmem) "ret_site").toBitVec := by
  refine ⟨exec_call_label (cellAt_call regs dmem) hdm, ?_⟩
  rw [ret_site_addr]
  rfl

/-- Under `mkState`'s unit layout `ret_site` is at base plus 1, not at the
address the binary's `call` pushes. -/
theorem ret_site_unit :
    labelAddr (mkState 0 prog regs [] dmem) "ret_site" = base + 1 := by
  have h : SizeCheck base (prog.map fun d => (d, unitSize d)) [("ret_site", 1)] = true := by decide
  rw [labelAddr, ← mkStateCells_unit_exe 0 prog regs [] dmem [] {}, mkStateCells_exe]
  exact label_of_sizeCheck' h (by decide)

end Kraken.X64.Examples.SizedLayout
