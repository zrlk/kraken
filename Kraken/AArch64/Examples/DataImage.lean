/-
A label-valued data word on AArch64: `bl f; ret_site: mov x0, #1; f: ret`
in `mkState`'s 4-byte layout, with the section `.balign 8; tab: .quad
ret_site` in the thread's private memory (`mkStateData`). The word at `tab`
reads back as the address of `ret_site` (`tab_word`), which is the base plus
4, the address `bl f` writes to `X30`.
-/
import Kraken.AArch64.Parser
import Kraken.Promising.AArch64Data

namespace Kraken.AArch64.Examples.DataImage

open Kraken Kraken.DataImage Kraken.Promising Kraken.Promising.AArch64

/-- The program: `bl f`, which returns to `ret_site`. -/
def prog : Program := parseAArch64("
  bl f
ret_site:
  mov x0, #1
f:
  ret
")

/-- The section: one label-valued word. -/
def items : List Item := [.align 8, .label "tab", .quadLabel "ret_site"]

abbrev dataBase : Nat := 0x200000

-- The word is `0x100004`, little-endian.
#guard_msgs in
#guard image (resolve (codeLabel (mkState 0 prog {} ∅).exe) dataBase items) dataBase items ==
  [4, 0, 0x10, 0, 0, 0, 0, 0]

/-- **The word at `tab` reads back as the address of `ret_site`.** -/
theorem tab_word (regs : Reg64s) (dmem : DataMem) :
    let st := mkStateData 0 prog regs dataBase items dmem
    (st.st.1.dmem.loadInt (BitVec.ofNat 64 dataBase) 8).map (BitVec.ofInt 64)
      = some ((_root_.Executable.labels st.exe).label "ret_site").toBitVec :=
  load_quadLabel_exe (n := 2) rfl (by decide) rfl

end Kraken.AArch64.Examples.DataImage
