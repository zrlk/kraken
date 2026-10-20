/-
The message-passing programs (MP) and the event trees of their
cells under the promising interpretation of AArch64
(`Kraken.Promising.AArch64.isa`).

Two threads with fixed roles; `X0` holds the flag address, `X1` the data
address (both words initially `0`):
```
 writer (mpWriter):          reader (mpReader):
 0   mov  w2, #1             0 spin:
 1   str  w2, [x1]           1   ldar w3, [x0]
 2   mov  w3, #1             2   cbz  w3, spin
 3   stlr w3, [x0]           3   ldr  w4, [x1]
 4 done_w:                   4 done_r:
```
The end of each text is position `5`, which shares its address with the
final label (position `4`).

Each theorem reads `isa.exec st` at the address of one cell of a laid-out
program, through `AArch64.exec_eq_of_codeAt`, as the event tree of that cell
(as `SLR/SwpTrees.lean` does for the spinlock worker): a silent step (`MOV`,
`CBZ`), a load (`LDAR`, `LDR`) or a store (`STR`, `STLR`). Both words lie
outside the thread's private data memory (`Mem.loadInt … = none`), so the
accesses go to the shared memory. The cell context `At`, `goto` and the
address lemmas are the program-independent ones of `SLR/A64Trees.lean`.
-/
import Kraken.Promising.SLR.A64Trees
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.MpTrees

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The MP writer: data `:= 1` (plain), then flag `:= 1` (release). -/
def mpWriter : Program := parseAArch64("
    mov w2, #1
    str w2, [x1]
    mov w3, #1
    stlr w3, [x0]
done_w:
")

/-- The MP reader: spin on an acquire load of the flag until it is non-zero,
then load the data into `W4`. -/
def mpReader : Program := parseAArch64("
spin:
    ldar w3, [x0]
    cbz w3, spin
    ldr w4, [x1]
done_r:
")

/-- info: (5, 5) -/
#guard_msgs in
#eval (mpWriter.length, mpReader.length)

variable [layout : _root_.Layout]

/- The generic cell helpers live in `SLR/A64Trees.lean`; re-exported here so
that `MpTrees.At`, `MpTrees.goto`, … keep resolving. -/
export Kraken.Promising.SLR.A64Trees (At goto addrOf_step addrOf_label)

open Kraken.Promising.SLR.A64Trees (next_pc)

/-! ## The writer -/

section Writer

variable [hw : Executable.ValidLayout (layout mpWriter)]

/-- The end of the writer's text (position 5) is the address of `done_w`
(position 4). -/
theorem w_addr_5 : (layout mpWriter).addrOf 5 = (layout mpWriter).addrOf 4 :=
  addrOf_label (i := 4) (l := "done_w") rfl

/-- Read the writer's cell at position `i` through `exec_eq_of_codeAt` and
unfold its interpretation. -/
local macro "wcell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := mpWriter) (i := $i)
    (d := mpWriter[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : mpWriter[$i] = d at hc
  simp only [mpWriter, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAt ($h).exe ($h).decls ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp]
  simp [goto, toEv, RegOrSp.interpBase, MachineData.rmwK, MachineData.loadK,
    MachineData.storeK, MachineData.load, MachineData.store, EvTree.access_empty, EvTree.map,
    AddrOrLit.interpLoad, AddrExpr.interpLoad, AddrExpr.interpStore, AddrExpr.checkSPAlignment,
    AddrExpr.eval, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, RegOrZr.base, RegOrZr.isZr, Reg64s.getXReg, $ts,*]))

/-- `mov w2, #1` (position 0): silent, `X2 := 1`. -/
theorem exec_w_mov2 (st : State) (h : At mpWriter st 0) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X2 1#64 } ((layout mpWriter).addrOf 1))) := by
  rw [next_pc h (by decide)]
  wcell h 0 []

/-- `str w2, [x1]` (position 1): a plain store of `X2`'s low word to the data
word. -/
theorem exec_w_str (st : State) (h : At mpWriter st 1) {d : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = d) (hdd : Mem.loadInt st.st.1.dmem d 4 = none) :
    isa.exec st = some (.store .plain false ⟨d, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X2.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout mpWriter).addrOf 2))) := by
  rw [next_pc h (by decide)]
  wcell h 1 [hx1, hdd]

/-- `mov w3, #1` (position 2): silent, `X3 := 1`. -/
theorem exec_w_mov3 (st : State) (h : At mpWriter st 2) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 1#64 } ((layout mpWriter).addrOf 3))) := by
  rw [next_pc h (by decide)]
  wcell h 2 []

/-- `stlr w3, [x0]` (position 3): a release store of `X3`'s low word to the
flag. -/
theorem exec_w_stlr (st : State) (h : At mpWriter st 3) {f : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt st.st.1.dmem f 4 = none) :
    isa.exec st = some (.store .rel false ⟨f, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X3.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout mpWriter).addrOf 4))) := by
  rw [next_pc h (by decide)]
  wcell h 3 [hx0, hdf]

end Writer

/-! ## The reader -/

section Reader

variable [hr : Executable.ValidLayout (layout mpReader)]

/-- The address of the label `spin` (position 0) is that of `ldar` (position 1). -/
theorem label_spin :
    (_root_.Executable.labels (layout mpReader)).label "spin" = (layout mpReader).addrOf 1 := by
  rw [Program.label_addrOf_drop (i := 0) (by decide) (by decide) (by decide)]
  exact (addrOf_label (i := 0) (l := "spin") rfl).symm

/-- The end of the reader's text (position 5) is the address of `done_r`
(position 4). -/
theorem r_addr_5 : (layout mpReader).addrOf 5 = (layout mpReader).addrOf 4 :=
  addrOf_label (i := 4) (l := "done_r") rfl

/-- Read the reader's cell at position `i` through `exec_eq_of_codeAt` and
unfold its interpretation. -/
local macro "rcell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := mpReader) (i := $i)
    (d := mpReader[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : mpReader[$i] = d at hc
  simp only [mpReader, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAt ($h).exe ($h).decls ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, label_spin]
  simp [goto, toEv, RegOrSp.interpBase, MachineData.rmwK, MachineData.loadK,
    MachineData.storeK, MachineData.load, MachineData.store, EvTree.access_empty, EvTree.map,
    AddrOrLit.interpLoad, AddrExpr.interpLoad, AddrExpr.interpStore, AddrExpr.checkSPAlignment,
    AddrExpr.eval, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, RegOrZr.base, RegOrZr.isZr, Reg64s.getXReg, $ts,*]))

/-- `ldar w3, [x0]` (position 1): an acquire load of the flag into `X3`. -/
theorem exec_r_ldar (st : State) (h : At mpReader st 1) {f : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt st.st.1.dmem f 4 = none) :
    isa.exec st = some (.load .acq false ⟨f, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout mpReader).addrOf 2))) := by
  rw [next_pc h (by decide)]
  rcell h 1 [hx0, hdf]

/-- `cbz w3, spin` (position 2): silent, back to `spin` when `X3`'s low word
is zero. -/
theorem exec_r_cbz (st : State) (h : At mpReader st 2) :
    isa.exec st = some (.done (goto st st.st.1
      (if BitVec.setWidth 32 st.st.1.regs.X3.toBitVec = 0#32 then (layout mpReader).addrOf 1
        else (layout mpReader).addrOf 3))) := by
  rw [next_pc h (by decide)]
  by_cases hz : BitVec.setWidth 32 st.st.1.regs.X3.toBitVec = 0#32 <;> rcell h 2 [hz]

/-- `ldr w4, [x1]` (position 3): a plain load of the data word into `X4`. -/
theorem exec_r_ldr (st : State) (h : At mpReader st 3) {d : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = d) (hdd : Mem.loadInt st.st.1.dmem d 4 = none) :
    isa.exec st = some (.load .plain false ⟨d, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout mpReader).addrOf 4))) := by
  rw [next_pc h (by decide)]
  rcell h 3 [hx1, hdd]

end Reader

end Kraken.Promising.SLR.MpTrees
