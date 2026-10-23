/-
A stack-map table in data at binary instruction lengths. The program of
`SizedLayout.lean` (`call f; ret_site: movq $1, %rax; f: ret` at lengths
`[5, 7, 1]`) with a `.rodata` section

    .balign 8
    scc_stackmap:
    .quad 1
    .quad ret_site
    .quad 0

in its private memory (`mkStateData`). The word at `scc_stackmap + 8`, read
as a 64-bit value, is the address `call f` pushes: both are the thread's
base plus 5 (`call_pushes_table_word`).
-/
import Kraken.X64.Examples.SizedLayout
import Kraken.Promising.X64Data

namespace Kraken.X64.Examples.SizedLayoutData

open Kraken Kraken.DataImage Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Kraken.X64.Examples.SizedLayout

/-- The `.rodata` section. -/
def items : List Item :=
  [.align 8, .label "scc_stackmap", .quad 1, .quadLabel "ret_site", .quad 0]

/-- Where the section is placed. -/
abbrev dataBase : Nat := 0x200000

-- The table's bytes: the `.quad ret_site` word is `0x100005`, little-endian.
#guard_msgs in
#guard image (resolve (codeLabel (base, cells)) dataBase items) dataBase items ==
  [1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- `scc_stackmap` is at the base of the section; `ret_site` is a code label.
#guard_msgs in
#guard dataLabel dataBase items "scc_stackmap" == some dataBase && dataLabel dataBase items "ret_site" == none

theorem scc_stackmap_addr : dataLabel dataBase items "scc_stackmap" = some dataBase :=
  dataLabel_addrAt (n := 1) rfl (by decide)

variable (regs : Reg64s) (dmem : DataMem)

/-- Thread 0 at the binary's lengths, with the table in its memory. -/
abbrev stD : State := mkStateData 0 cells regs dataBase items [] dmem

/-- **`call f` pushes the word of the stack map**: with the stack slot
mapped, the step jumps to `f` having stored `retAddr st 5`, and the 8-byte
word at `scc_stackmap + 8` reads back as that address. -/
theorem call_pushes_table_word {j : Int}
    (hdm : Mem.loadInt (stD regs dmem).st.1.dmem (rspOf (stD regs dmem).st.1 - 8#64) 8 = some j) :
    isa.exec (stD regs dmem) = some (.done (jumpTo (stD regs dmem) (callPost (stD regs dmem) 5)
        (labelAddr (stD regs dmem) "f"))) ∧
      ((stD regs dmem).st.1.dmem.loadInt (BitVec.ofNat 64 (dataBase + 8)) 8).map (BitVec.ofInt 64)
        = some (retAddr (stD regs dmem) 5) := by
  refine ⟨exec_call_label (cellAt_call regs _) hdm, ?_⟩
  have := load_quadLabel_sized (tid := 0) (dmem := dmem) (dataBase := dataBase) (items := items)
    sizeCheck_prog (L := "ret_site") (off := 5) (by decide) rfl (by decide) (n := 3) rfl
  exact this

end Kraken.X64.Examples.SizedLayoutData
