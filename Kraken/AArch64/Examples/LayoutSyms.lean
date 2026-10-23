/-
AArch64 data symbols (`mkStateSyms`): `bl f; ret_site: mov x0, #1; f: ret`
with a data symbol `tab` at `0x200000`. The executable is the code, a
padding cell up to `tab` and the label; the end address is the end of the
code, so `cellAt_of_codeAt` does not apply and the `CellAt` of each
instruction comes from `cellAt_mkStateSyms` (`cellAt_mov`), the layout
checked by `validLayout_of_cellsOk`.
-/
import Kraken.AArch64.Parser
import Kraken.Promising.Lower.CodeSegA64Syms

namespace Kraken.AArch64.Examples.LayoutSyms

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-- The program: `bl f`, which returns to `ret_site`. -/
def prog : Program := parseAArch64("
  bl f
ret_site:
  mov x0, #1
f:
  ret
")

/-- The data symbol. -/
abbrev syms : List (String × BitVec 64) := [("tab", 0x200000#64)]

variable (regs : Reg64s) (dmem : DataMem)

/-- Thread 0 with the symbol. -/
abbrev st : State := mkStateSyms 0 prog regs syms dmem

-- The cells: the code at 4 bytes per instruction, the padding, the label;
-- the end address is the end of the code, 12 bytes on.
#guard_msgs in
#guard (st {} ∅).exe.2.map (·.2) == [4, 0, 4, 0, 4, 0x200000 - 0x10000c, 0] &&
  (st {} ∅).endPc == Int64.ofNat 0x10000c

/-- The cells of the executable. -/
theorem st_exe : (st regs dmem).exe
    = (Int64.ofNat 0x100000, prog.map (fun d => (d, d.fakeSize)) ++
        [(.byteArray (.mk #[]), 0x200000 - 0x10000c), (.label "tab", 0)]) := rfl

theorem validLayout_st : Kraken.Executable.ValidLayout (st regs dmem).exe := by
  rw [st_exe]; exact Kraken.Executable.validLayout_of_cellsOk _ (by decide) (by decide)

/-- **The `mov` is a `CellAt`** at the base plus 4. -/
theorem cellAt_mov (m : MachineData) :
    ∃ i, CellAt { st regs dmem with st := (m, Int64.ofNat 0x100000 + .ofNat 4) } (.instr i) 4 := by
  haveI := validLayout_st regs dmem
  have h0 : Kraken.Executable.codeAt (st regs dmem).exe (st regs dmem).exe.1
      = (st regs dmem).exe.2 := by
    rw [Kraken.Executable.codeAt_start]; rfl
  have h1 := Kraken.Executable.codeAt_succ _ (z := 4) (rest := (st regs dmem).exe.2.drop 1)
    (h0.trans (by rw [st_exe]; rfl))
  exact ⟨_, cellAt_mkStateSyms rfl m _ (validLayout_st regs dmem) (h1.trans (by rw [st_exe]; rfl))⟩

end Kraken.AArch64.Examples.LayoutSyms
