/-
**x64 data images** (`Kraken/DataImage.lean`) under the sized code layout
(`Promising/X64Sized.lean`).

- `codeLabel exe`: the label resolution of a laid-out executable, as 64-bit
  addresses (`Executable.labels`);
- `dataSyms base items`: the data labels at their addresses, in the form of
  `mkStateCells`' `syms` (so that `leaq sym(%rip)` reaches them);
- `imageMem tid cells dmem dataBase items`: the image of the section at
  `dataBase` stored into `dmem`, a `.quad L` of a code label resolved in the
  code `cells` laid out at the thread's base (`threadBase`), at the cells'
  sizes;
- `mkStateData`: `mkStateCells` with that memory;
- `load_quadLabel_sized`: with a checked size table (`SizeCheck`), a
  `.quad L` of a code label at offset `off` reads back `threadBase + off`.
-/
import Kraken.DataImage
import Kraken.Promising.X64Sized

namespace Kraken.Promising.X64

open Kraken Kraken.DataImage

/-- The address of thread `tid`'s code (`mkState`, `mkStateCells`). -/
abbrev threadBase (tid : Nat) : Int64 := Int64.ofNat (0x100000 * (tid + 1))

/-- The label resolution of a laid-out executable, as 64-bit addresses. -/
def codeLabel (exe : _root_.Executable) (l : String) : BitVec 64 :=
  ((_root_.Executable.labels exe).label l).toBitVec

/-- The data labels of a section at `base`, as `mkStateCells`' `syms`. -/
def dataSyms (base : Nat) (items : List Item) : List (String × BitVec 64) :=
  (labelsFrom base items).map fun (l, a) => (l, BitVec.ofNat 64 a)

/-- **The data image of thread `tid`**: the section `items` at `dataBase`
stored into `dmem`, its labels resolved by `resolve` against the code `cells`
laid out at the thread's base. -/
def imageMem (tid : Nat) (cells : List (Directive × Nat)) (dmem : DataMem) (dataBase : Nat)
    (items : List Item) : DataMem :=
  dataMem dmem dataBase (image (resolve (codeLabel (threadBase tid, cells)) dataBase items) dataBase items)

/-- `mkStateCells` with the data image of `items` at `dataBase` in its
private memory (over `dmem`). -/
def mkStateData (tid : Nat) (cells : List (Directive × Nat)) (regs : Reg64s) (dataBase : Nat)
    (items : List Item) (syms : List (String × BitVec 64) := []) (dmem : DataMem := ∅)
    (texts : List String := []) (decls : Decls := {}) : State :=
  mkStateCells tid cells regs syms (imageMem tid cells dmem dataBase items) texts decls

theorem mkStateData_dmem (tid : Nat) (cells : List (Directive × Nat)) (regs : Reg64s) (dataBase : Nat)
    (items : List Item) (syms : List (String × BitVec 64)) (dmem : DataMem) (texts : List String)
    (decls : Decls) :
    (mkStateData tid cells regs dataBase items syms dmem texts decls).st.1.dmem
      = imageMem tid cells dmem dataBase items := rfl

theorem mkStateData_eq (tid : Nat) (cells : List (Directive × Nat)) (regs : Reg64s) (dataBase : Nat)
    (items : List Item) (syms : List (String × BitVec 64)) (dmem : DataMem) (texts : List String)
    (decls : Decls) :
    mkStateData tid cells regs dataBase items syms dmem texts decls
      = mkStateCells tid cells regs syms (imageMem tid cells dmem dataBase items) texts decls := rfl

/-- **A `.quad L` of a code label reads back the label's address** in the
sized layout: `L` not a data label, at checked offset `off` of the code. -/
theorem load_quadLabel_sized {tid : Nat} {cells : List (Directive × Nat)} {dmem : DataMem}
    {dataBase : Nat} {items : List Item} {offs : List (Label × Nat)}
    (hc : SizeCheck (threadBase tid) cells offs = true) {L : Label} {off : Nat} (hL : (L, off) ∈ offs)
    (hcode : dataLabel dataBase items L = none)
    (hfit : endAddr dataBase items ≤ 2 ^ 64) {n : Nat} (hn : items[n]? = some (.quadLabel L)) :
    ((imageMem tid cells dmem dataBase items).loadInt (BitVec.ofNat 64 (addrAt dataBase items n)) 8).map
      (BitVec.ofInt 64) = some (threadBase tid + .ofNat off).toBitVec := by
  rw [imageMem, ofInt_load_quadLabel _ _ _ _ hfit hn, resolve_code hcode, codeLabel,
    label_of_sizeCheck' hc hL]

/-- **A `.quad L` of a code label reads back the label's address in the
thread's executable**, without symbols. -/
theorem load_quadLabel_exe {tid : Nat} {cells : List (Directive × Nat)} {regs : Reg64s} {dmem : DataMem}
    {dataBase : Nat} {items : List Item} {texts : List String} {decls : Decls} {L : Label}
    (hcode : dataLabel dataBase items L = none)
    (hfit : endAddr dataBase items ≤ 2 ^ 64) {n : Nat} (hn : items[n]? = some (.quadLabel L)) :
    let st := mkStateData tid cells regs dataBase items [] dmem texts decls
    (st.st.1.dmem.loadInt (BitVec.ofNat 64 (addrAt dataBase items n)) 8).map (BitVec.ofInt 64)
      = some ((_root_.Executable.labels st.exe).label L).toBitVec := by
  intro st
  rw [mkStateData_dmem, imageMem, ofInt_load_quadLabel _ _ _ _ hfit hn, resolve_code hcode]
  rfl

end Kraken.Promising.X64
