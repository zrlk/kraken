/-
**Stage 4: the event trees of the `treiber2.kl` worker**
`treiber2DWorker` (`EnvG/Treiber2DataVCGen.lean`) under the promising
interpretation of AArch64, on a valid layout. The `LiveSpinCasTrees.lean`
recipe: each theorem reads `isa.exec st` at the address of one cell through
`AArch64.exec_eq_of_codeAt` (`SLR.A64Trees.a64cell`).

```
 0 worker:                  11   CBZ X2,done
 1   STR W9,[X1]            12   LDR X4,[X2,#8]
 2 push:                    13   MOV X3,X2
 3   LDAR X2,[X0]           14   CASAL X3,X4,[X0]
 4   STR X2,[X1,#8]         15   CMP X3,X2
 5   MOV X3,X2              16   B.NE pop
 6   CASAL X3,X1,[X0]       17   MOV X10,X2
 7   CMP X3,X2              18   LDR W11,[X2]
 8   B.NE push              19   B done
 9 pop:                     20 done:
10   LDAR X2,[X0]
```

`top = X0`, the node `= X1`. A label shares the address of the next
instruction (`0 ↦ 1`, `2 ↦ 3`, `9 ↦ 10`, `20 ↦ 21`, the end of the text).
-/
import Kraken.Promising.SLR.EnvG.Treiber2DataVCGen
import Kraken.Promising.SLR.A64Trees
import Kraken.Promising.LiveSpinCasTrees

namespace Kraken.Promising.Live.TermTreiber2Trees

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker)
open Kraken.Promising.SLR.A64Trees (At goto)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiber2DWorker)]

set_option hygiene false in
local notation "pcT" => (layout treiber2DWorker).addrOf

theorem addrOf_label {i : Nat} {l : Label} (hp : treiber2DWorker[i]? = some (Directive.label l)) :
    pcT (i + 1) = pcT i :=
  SLR.A64Trees.addrOf_label hp

theorem addrOf_0 : pcT 0 = pcT 1 := (addrOf_label (i := 0) (l := "worker") rfl).symm
theorem addrOf_2 : pcT 2 = pcT 3 := (addrOf_label (i := 2) (l := "push") rfl).symm
theorem addrOf_9 : pcT 9 = pcT 10 := (addrOf_label (i := 9) (l := "pop") rfl).symm
theorem addrOf_20 : pcT 20 = pcT 21 := (addrOf_label (i := 20) (l := "done") rfl).symm

theorem label_push : (_root_.Executable.labels (layout treiber2DWorker)).label "push" = pcT 3 := by
  rw [Program.label_addrOf_drop (i := 2) (by decide) (by decide) (by decide)]
  exact addrOf_2

theorem label_pop : (_root_.Executable.labels (layout treiber2DWorker)).label "pop" = pcT 10 := by
  rw [Program.label_addrOf_drop (i := 9) (by decide) (by decide) (by decide)]
  exact addrOf_9

theorem label_done : (_root_.Executable.labels (layout treiber2DWorker)).label "done" = pcT 21 := by
  rw [Program.label_addrOf_drop (i := 20) (by decide) (by decide) (by decide)]
  exact addrOf_20

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : At treiber2DWorker st i) (hi : i < treiber2DWorker.length) :
    pcT (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.A64Trees.next_pc h hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i treiber2DWorker [treiber2DWorker] [label_push, label_pop, label_done] [goto, $ts,*])

/-- `str w9, [x1]` (position 1): a plain store of the data word. -/
theorem exec_str_d (st : State) (h : At treiber2DWorker st 1) {n : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = n) (hdm : Mem.loadInt st.st.1.dmem n 4 = none) :
    isa.exec st = some (.store .plain false ⟨n, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X9.toBitVec))
      fun _ => .done (goto st st.st.1 (pcT 3))) := by
  rw [← addrOf_2, next_pc h (by decide)]
  cell h 1 [hx1, hdm]

/-- `ldar x2, [x0]` (position 3, and 10): a load of `top` into `X2` (stated
for some load kind, so that the statement is shared with the variants whose
load of `top` is plain). -/
theorem exec_ldar3 (st : State) (h : At treiber2DWorker st 3) {t : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ k : LoadKind, isa.exec st = some (.load k false ⟨t, 8⟩
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 v) } (pcT 4))) := by
  rw [next_pc h (by decide)]
  cell h 3 [hx0, hdm]

omit layout hv in
/-- The address `[xN, #8]`. -/
theorem ofInt_add8 (n : BitVec 64) : BitVec.ofInt 64 (n.toInt + 8) = n + 8 := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_add, BitVec.toInt_ofInt]

/-- `str x2, [x1, #8]` (position 4): a plain store of the link. -/
theorem exec_str_n (st : State) (h : At treiber2DWorker st 4) {n : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = n) (hdm : Mem.loadInt st.st.1.dmem (n + 8#64) 8 = none) :
    isa.exec st = some (.store .plain false ⟨n + 8, 8⟩ (BitVec.setWidth 128 st.st.1.regs.X2.toBitVec)
      fun _ => .done (goto st st.st.1 (pcT 5))) := by
  rw [next_pc h (by decide)]
  cell h 4 [hx1, ofInt_add8, hdm]

/-- `mov x3, x2` (position 5). -/
theorem exec_mov5 (st : State) (h : At treiber2DWorker st 5) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 st.st.1.regs.X2.toBitVec } (pcT 6))) := by
  rw [next_pc h (by decide)]
  cell h 5 []

/-- `casal x3, x1, [x0]` (position 6): an RMW of `top` (of some kind) that
writes `X1` iff the old value is `X3`; `X3` receives the old value. -/
theorem exec_casal6 (st : State) (h : At treiber2DWorker st 6) {t : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ k : RmwKind, isa.exec st = some (.rmw k false ⟨t, 8⟩
      (fun old => if BitVec.setWidth 64 old = st.st.1.regs.X3.toBitVec then
          some (BitVec.setWidth 128 st.st.1.regs.X1.toBitVec) else none)
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 v) } (pcT 7))) := by
  rw [next_pc h (by decide)]
  cell h 6 [hx0, hdm]

/-- `cmp x3, x2` (position 7, and 15): silent, sets the flags; `Z` iff
`X3 = X2`. -/
theorem exec_cmp7 (st : State) (h : At treiber2DWorker st 7) :
    ∃ s : StatusFlags, isa.exec st = some (.done (goto st { st.st.1 with status := s } (pcT 8)))
      ∧ (s.z = true ↔ st.st.1.regs.X3.toBitVec = st.st.1.regs.X2.toBitVec) := by
  refine ⟨?s, ?e, ?z⟩
  case e =>
    rw [next_pc h (by decide)]
    cell h 7 []
    rfl
  case z =>
    simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    exact iff_of_eq (congrArg _ (BitVec.zero_add _))

/-- `b.ne push` (position 8): silent, back to `push` unless `Z`. -/
theorem exec_bne8 (st : State) (h : At treiber2DWorker st 8) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.status.z = true then pcT 10 else pcT 3))) := by
  rw [← addrOf_9, next_pc h (by decide)]
  by_cases hz : st.st.1.status.z = true <;> cell h 8 [hz]

/-- `ldar x2, [x0]` (position 10). -/
theorem exec_ldar10 (st : State) (h : At treiber2DWorker st 10) {t : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ k : LoadKind, isa.exec st = some (.load k false ⟨t, 8⟩
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 v) } (pcT 11))) := by
  rw [next_pc h (by decide)]
  cell h 10 [hx0, hdm]

/-- `cbz x2, done` (position 11). -/
theorem exec_cbz11 (st : State) (h : At treiber2DWorker st 11) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.regs.X2.toBitVec = 0#64 then pcT 21 else pcT 12))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.regs.X2.toBitVec = 0#64 <;> cell h 11 [hz]

/-- `ldr x4, [x2, #8]` (position 12): a plain load of the link of the node
read. -/
theorem exec_ldr12 (st : State) (h : At treiber2DWorker st 12) {a : BitVec 64}
    (hx2 : st.st.1.regs.X2.toBitVec = a) (hdm : Mem.loadInt st.st.1.dmem (a + 8#64) 8 = none) :
    isa.exec st = some (.load .plain false ⟨a + 8, 8⟩
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 v) } (pcT 13))) := by
  rw [next_pc h (by decide)]
  cell h 12 [hx2, ofInt_add8, hdm]

/-- `mov x3, x2` (position 13). -/
theorem exec_mov13 (st : State) (h : At treiber2DWorker st 13) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 st.st.1.regs.X2.toBitVec } (pcT 14))) := by
  rw [next_pc h (by decide)]
  cell h 13 []

/-- `casal x3, x4, [x0]` (position 14). -/
theorem exec_casal14 (st : State) (h : At treiber2DWorker st 14) {t : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ k : RmwKind, isa.exec st = some (.rmw k false ⟨t, 8⟩
      (fun old => if BitVec.setWidth 64 old = st.st.1.regs.X3.toBitVec then
          some (BitVec.setWidth 128 st.st.1.regs.X4.toBitVec) else none)
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 v) } (pcT 15))) := by
  rw [next_pc h (by decide)]
  cell h 14 [hx0, hdm]

/-- `cmp x3, x2` (position 15). -/
theorem exec_cmp15 (st : State) (h : At treiber2DWorker st 15) :
    ∃ s : StatusFlags, isa.exec st = some (.done (goto st { st.st.1 with status := s } (pcT 16)))
      ∧ (s.z = true ↔ st.st.1.regs.X3.toBitVec = st.st.1.regs.X2.toBitVec) := by
  refine ⟨?s, ?e, ?z⟩
  case e =>
    rw [next_pc h (by decide)]
    cell h 15 []
    rfl
  case z =>
    simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    exact iff_of_eq (congrArg _ (BitVec.zero_add _))

/-- `b.ne pop` (position 16). -/
theorem exec_bne16 (st : State) (h : At treiber2DWorker st 16) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.status.z = true then pcT 17 else pcT 10))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.z = true <;> cell h 16 [hz]

/-- `mov x10, x2` (position 17). -/
theorem exec_mov17 (st : State) (h : At treiber2DWorker st 17) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X10 st.st.1.regs.X2.toBitVec } (pcT 18))) := by
  rw [next_pc h (by decide)]
  cell h 17 []

/-- `ldr w11, [x2]` (position 18): a plain load of the popped node's data. -/
theorem exec_ldr18 (st : State) (h : At treiber2DWorker st 18) {a : BitVec 64}
    (hx2 : st.st.1.regs.X2.toBitVec = a) (hdm : Mem.loadInt st.st.1.dmem a 4 = none) :
    isa.exec st = some (.load .plain false ⟨a, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X11 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcT 19))) := by
  rw [next_pc h (by decide)]
  cell h 18 [hx2, hdm]

/-- `b done` (position 19): to the end of the text. -/
theorem exec_b19 (st : State) (h : At treiber2DWorker st 19) :
    isa.exec st = some (.done (goto st st.st.1 (pcT 21))) := by
  cell h 19 []

end Kraken.Promising.Live.TermTreiber2Trees
