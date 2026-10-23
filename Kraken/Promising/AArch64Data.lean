/-
**AArch64 data images** (`Kraken/DataImage.lean`) under the 4-byte code
layout of `AArch64.mkState`.

- `codeLabel exe`: the label resolution of a laid-out executable, as 64-bit
  addresses (`Executable.labels`);
- `imageMem tid prog dmem dataBase items`: the image of the section at
  `dataBase` stored into `dmem`, a `.quad L` of a code label resolved in
  `mkState`'s layout of `prog`;
- `mkStateData`: `mkState` with that memory; `load_quadLabel_exe`: a
  `.quad L` of a code label reads back the label's address in the thread's
  executable.
-/
import Kraken.DataImage
import Kraken.Promising.AArch64

namespace Kraken.Promising.AArch64

open Kraken Kraken.DataImage

/-- The label resolution of a laid-out executable, as 64-bit addresses. -/
def codeLabel (exe : _root_.Executable) (l : String) : BitVec 64 :=
  ((_root_.Executable.labels exe).label l).toBitVec

/-- **The data image of thread `tid`**: the section `items` at `dataBase`
stored into `dmem`, its labels resolved by `resolve` against `prog` laid out
as `mkState` lays it out (which does not depend on the memory). -/
def imageMem (tid : Nat) (prog : Program) (dmem : DataMem) (dataBase : Nat) (items : List Item) : DataMem :=
  dataMem dmem dataBase
    (image (resolve (codeLabel (mkState tid prog {} ∅).exe) dataBase items) dataBase items)

/-- `mkState` with the data image of `items` at `dataBase` in its private
memory (over `dmem`). -/
def mkStateData (tid : Nat) (prog : Program) (regs : Reg64s) (dataBase : Nat) (items : List Item)
    (dmem : DataMem := ∅) (texts : List String := []) (decls : Decls := {}) : State :=
  mkState tid prog regs (imageMem tid prog dmem dataBase items) texts decls

theorem mkStateData_dmem (tid : Nat) (prog : Program) (regs : Reg64s) (dataBase : Nat) (items : List Item)
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkStateData tid prog regs dataBase items dmem texts decls).st.1.dmem
      = imageMem tid prog dmem dataBase items := rfl

/-- `mkStateData`'s executable is `mkState`'s. -/
theorem mkStateData_exe (tid : Nat) (prog : Program) (regs : Reg64s) (dataBase : Nat) (items : List Item)
    (dmem : DataMem) (texts : List String) (decls : Decls) :
    (mkStateData tid prog regs dataBase items dmem texts decls).exe
      = (mkState tid prog regs dmem texts decls).exe := rfl

/-- **A `.quad L` of a code label reads back the label's address in the
thread's executable.** -/
theorem load_quadLabel_exe {tid : Nat} {prog : Program} {regs : Reg64s} {dmem : DataMem}
    {dataBase : Nat} {items : List Item} {texts : List String} {decls : Decls} {L : String}
    (hcode : dataLabel dataBase items L = none)
    (hfit : endAddr dataBase items ≤ 2 ^ 64) {n : Nat} (hn : items[n]? = some (.quadLabel L)) :
    let st := mkStateData tid prog regs dataBase items dmem texts decls
    (st.st.1.dmem.loadInt (BitVec.ofNat 64 (addrAt dataBase items n)) 8).map (BitVec.ofInt 64)
      = some ((_root_.Executable.labels st.exe).label L).toBitVec := by
  intro st
  rw [mkStateData_dmem, imageMem, ofInt_load_quadLabel _ _ _ _ hfit hn, resolve_code hcode]
  rfl

end Kraken.Promising.AArch64
