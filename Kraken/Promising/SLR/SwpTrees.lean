/-
The event trees of the cells of the `SWP` spinlock worker
(`Kraken.AArch64.Examples.InvEnv.swpWorker`) under the promising
interpretation of AArch64 (`Kraken.Promising.AArch64.isa`).

Each theorem reads `isa.exec st` at the address of one cell of the laid-out
worker, through `AArch64.exec_eq_of_codeAt`, as the event tree of that cell:
a silent step (`MOV`, `ADD`, the branches), a load (`LDR`), a store (`STR`,
`STLR`) or a read-modify-write (`SWPA`). Fall-through addresses are given as
the address of the next position, branch targets as the address of the label's
position. The lock is the word at `X0 = l`, the counter the word at `X1 = c`;
both lie outside the thread's private data memory (`Mem.loadInt … = none`),
so the accesses go to the shared memory.

These are the per-instruction inputs of the tree-level rules of the SLR
spinlock proof (`EvTree.EraseWP`, `Kraken.Promising.SLR.RmwPend`).

The worker:
```
 0 worker:            8   b try
 1   mov w3, #1       9 cs:
 2 try:              10   ldr w5, [x1]
 3   swpa w3, w2, [x0]  11   add w5, w5, #1
 4   cbz w2, cs      12   str w5, [x1]
 5 spin:             13   stlr wzr, [x0]
 6   ldr w2, [x0]    14   b done
 7   cbnz w2, spin   15 done:
```
-/
import Kraken.Promising.SLR.A64Trees
import Kraken.AArch64.Examples.InvEnv

namespace Kraken.Promising.SLR.SwpTrees

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- The context of a cell: the state runs the laid-out worker, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout swpWorker
  decls : st.decls = {}
  pc : st.st.2 = (layout swpWorker).addrOf i
  ne : (st.st.2 == st.endPc) = false

/-- The state `st` moved to machine data `m` at address `pc`. -/
abbrev goto (st : State) (m : MachineData) (pc : Int64) : State :=
  { st with st := (m, pc) }

omit hv in
/-- The cell of a laid-out program at a position. -/
private theorem layout_getElem (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

omit hv in
/-- Stepping one position advances the address by that position's size. -/
theorem addrOf_step {i : Nat} (hi : i < swpWorker.length) :
    (layout swpWorker).addrOf (i + 1)
      = (layout swpWorker).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  A64Trees.addrOf_step hi

/-- A label position occupies no bytes: the next position has its address. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : swpWorker[i]? = some (Directive.label l)) :
    (layout swpWorker).addrOf (i + 1) = (layout swpWorker).addrOf i :=
  A64Trees.addrOf_label hp

/-- The address of the label `try` (position 2) is that of `swpa` (position 3). -/
theorem label_try :
    (_root_.Executable.labels (layout swpWorker)).label "try" = (layout swpWorker).addrOf 3 := by
  rw [Program.label_addrOf_drop (i := 2) (by decide) (by decide) (by decide)]
  exact (addrOf_label (i := 2) (l := "try") rfl).symm

/-- The address of the label `spin` (position 5) is that of `ldr w2` (position 6). -/
theorem label_spin :
    (_root_.Executable.labels (layout swpWorker)).label "spin" = (layout swpWorker).addrOf 6 := by
  rw [Program.label_addrOf_drop (i := 5) (by decide) (by decide) (by decide)]
  exact (addrOf_label (i := 5) (l := "spin") rfl).symm

/-- The address of the label `cs` (position 9) is that of `ldr w5` (position 10). -/
theorem label_cs :
    (_root_.Executable.labels (layout swpWorker)).label "cs" = (layout swpWorker).addrOf 10 := by
  rw [Program.label_addrOf_drop (i := 9) (by decide) (by decide) (by decide)]
  exact (addrOf_label (i := 9) (l := "cs") rfl).symm

/-- The address of the label `done` (position 15) is the end of the text
(position 16). -/
theorem label_done :
    (_root_.Executable.labels (layout swpWorker)).label "done" = (layout swpWorker).addrOf 16 := by
  rw [Program.label_addrOf_drop (i := 15) (by decide) (by decide) (by decide)]
  exact (addrOf_label (i := 15) (l := "done") rfl).symm

omit hv in
/-- The fall-through address of position `i`. -/
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < swpWorker.length) :
    (layout swpWorker).addrOf (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold its
interpretation. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i swpWorker [swpWorker] [label_try, label_spin, label_cs, label_done] [goto, $ts,*])

/-- `mov w3, #1` (position 1): silent, `X3 := 1`. -/
theorem exec_mov (st : State) (h : At st 1) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 1#64 } ((layout swpWorker).addrOf 2))) := by
  rw [next_pc h (by decide)]
  cell h 1 []

/-- `swpa w3, w2, [x0]` (position 3): an acquire swap of `X3`'s low word into
the lock, the old value into `X2`. -/
theorem exec_swpa (st : State) (h : At st 3) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.rmw .acq false ⟨l, 4⟩
      (fun _ => some (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X3.toBitVec)))
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout swpWorker).addrOf 4))) := by
  rw [next_pc h (by decide)]
  cell h 3 [hx0, hdm]

/-- `cbz w2, cs` (position 4): silent, to `cs` when `X2`'s low word is zero. -/
theorem exec_cbz (st : State) (h : At st 4) :
    isa.exec st = some (.done (goto st st.st.1
      (if BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 then (layout swpWorker).addrOf 10
        else (layout swpWorker).addrOf 5))) := by
  rw [next_pc h (by decide)]
  by_cases hz : BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 <;> cell h 4 [hz]

/-- `ldr w2, [x0]` (position 6): a plain load of the lock into `X2`. -/
theorem exec_ldr_spin (st : State) (h : At st 6) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.load .plain false ⟨l, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout swpWorker).addrOf 7))) := by
  rw [next_pc h (by decide)]
  cell h 6 [hx0, hdm]

/-- `cbnz w2, spin` (position 7): silent, back to `spin` when `X2`'s low word is
nonzero. -/
theorem exec_cbnz (st : State) (h : At st 7) :
    isa.exec st = some (.done (goto st st.st.1
      (if BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 then (layout swpWorker).addrOf 8
        else (layout swpWorker).addrOf 6))) := by
  rw [next_pc h (by decide)]
  by_cases hz : BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 <;> cell h 7 [hz]

/-- `b try` (position 8): silent, back to `try`. -/
theorem exec_b_try (st : State) (h : At st 8) :
    isa.exec st = some (.done (goto st st.st.1 ((layout swpWorker).addrOf 3))) := by
  cell h 8 []

/-- `ldr w5, [x1]` (position 10): a plain load of the counter into `X5`. -/
theorem exec_ldr_c (st : State) (h : At st 10) {c : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.load .plain false ⟨c, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout swpWorker).addrOf 11))) := by
  rw [next_pc h (by decide)]
  cell h 10 [hx1, hdc]

/-- `add w5, w5, #1` (position 11): silent, increments `X5`'s low word. -/
theorem exec_add (st : State) (h : At st 11) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      ((layout swpWorker).addrOf 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 []

/-- `str w5, [x1]` (position 12): a plain store of `X5`'s low word to the
counter. -/
theorem exec_str_c (st : State) (h : At st 12) {c : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.store .plain false ⟨c, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X5.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout swpWorker).addrOf 13))) := by
  rw [next_pc h (by decide)]
  cell h 12 [hx1, hdc]

/-- `stlr wzr, [x0]` (position 13): a release store of zero to the lock. -/
theorem exec_stlr (st : State) (h : At st 13) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.store .rel false ⟨l, 4⟩ 0#128
      fun _ => .done (goto st st.st.1 ((layout swpWorker).addrOf 14))) := by
  rw [next_pc h (by decide)]
  cell h 13 [hx0, hdm]

/-- `b done` (position 14): silent, to the end of the text. -/
theorem exec_b_done (st : State) (h : At st 14) :
    isa.exec st = some (.done (goto st st.st.1 ((layout swpWorker).addrOf 16))) := by
  cell h 14 []

end Kraken.Promising.SLR.SwpTrees
