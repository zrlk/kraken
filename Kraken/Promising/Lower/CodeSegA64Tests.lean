import Kraken.Promising.Lower.CodeSegA64

/-!
# Cells of a concrete program, by `CodeSegA64`

The program is the parser's reading of

    ldr  x9, [sp, #8]
    movz x10, #1
    subs x9, x9, x10
    str  x9, [sp, #56]
  L:
    b    L

laid out by `mkState`. Every instruction of the straight-line body is a
`CellAt` at `start + 4j`, and `codeAt` at `L` is the branch, without
unfolding `withAddresses`.
-/

namespace Kraken.Promising.Lower.CodeSegA64Tests

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

def x9 : RegOrZr .W64 := .low (.reg .X9) .W64
def x10 : RegOrZr .W64 := .low (.reg .X10) .W64

/-- The straight-line body. -/
def body : List Directive :=
  [.instr { operation_size := .W64,
            operation := .LDR x9 (.addr { base := .low .SP .W64, off := .imm { imm := .int64 8, index := none } }) },
   .instr { operation_size := .W64, operation := .MOVZ x10 (.int64 1) .LSL0 },
   .instr { operation_size := .W64, operation := .SUBS_s x9 x9 { reg := x10, amount := 0, shift := .LSL } },
   .instr { operation_size := .W64,
            operation := .STR x9 { base := .low .SP .W64, off := .imm { imm := .int64 56, index := none } } }]

def jmp : Directive := .instr { operation_size := .W64, operation := .B (.label "L") }

def prog : Program := body ++ [.label "L", jmp]

def st : State := mkState 0 prog {}

theorem valid : Kraken.Executable.ValidLayout st.exe :=
  mkState_validLayout 0 prog {} ∅ [] {} (by decide) (by decide)

theorem code : Kraken.Executable.codeAt st.exe st.exe.1 = body.map (·, 4) ++ [(.label "L", 0), (jmp, 4)] := by
  rw [Kraken.Executable.codeAt_start, st, mkState_exe]
  rfl

/-- Every instruction of the body is the 4-byte cell at `start + 4j`. -/
theorem cells : ∀ j d, body[j]? = some d → CellAt { st with st := (st.st.1, st.exe.1 + .ofNat (4 * j)) } d 4 :=
  fun _ _ hd => cellAt_segment4 valid (mkState_endPc ..) code (by decide) hd _

/-- `codeAt` at the label is the branch. -/
theorem atL : Kraken.Executable.codeAt st.exe ((_root_.Executable.labels st.exe).label "L") = [(jmp, 4)] := by
  have : (st.exe.2)[4]? = some (.label "L", 0) := by rw [st, mkState_exe]; rfl
  rw [@Kraken.Executable.codeAt_label st.exe valid "L" 4 0 this (by
    rw [st, mkState_exe]; simp [prog, body, jmp])]
  rw [st, mkState_exe]
  rfl

end Kraken.Promising.Lower.CodeSegA64Tests
