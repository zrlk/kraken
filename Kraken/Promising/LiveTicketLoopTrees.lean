/-
**Stage 4 (repeated acquisition): the event trees of the repeated-acquire
ticket-lock worker** `tkLoopWorker` (`ticketlock_loop2.kl`,
`LiveTicketLoop.lean`) under the promising interpretation of AArch64, on a
valid layout (the `LiveTicketTrees.lean` recipe, `a64cell`).

```
 0 worker:                  9   LDR W5,[X2]
 1   MOV W6,#1             10   ADD W5,W5,#1
 2 round:                  11   STR W5,[X2]
 3   CBZ W7,done           12   ADD W4,W3,#1
 4   LDADDA W6,W3,[X0]     13   STLR W4,[X1]
 5 spin:                   14   SUB W7,W7,#1
 6   LDAR W4,[X1]          15   B round
 7   CMP W4,W3             16 done:
 8   B.NE spin
```

`next = X0`, `owner = X1`, counter `= X2`, rounds left `= X7`. Labels occupy
no bytes: `addrOf 0 = addrOf 1`, `addrOf 2 = addrOf 3`, `addrOf 5 = addrOf 6`,
`addrOf 16 = addrOf 17` (the end of the text).
-/
import Kraken.Promising.LiveTicketLoop
import Kraken.Promising.LiveTicketTrees

namespace Kraken.Promising.Live.TicketLoopTrees

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Live.TicketLoop (tkLoopWorker)
open Kraken.Promising.Live.TicketTrees (w32 isInstr)
open Kraken.Promising.SLR.A64Trees (At goto next_pc)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

/-- A label position occupies no bytes. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : tkLoopWorker[i]? = some (Directive.label l)) :
    (layout tkLoopWorker).addrOf (i + 1) = (layout tkLoopWorker).addrOf i :=
  SLR.A64Trees.addrOf_label hp

theorem addrOf_0 : (layout tkLoopWorker).addrOf 0 = (layout tkLoopWorker).addrOf 1 :=
  (addrOf_label (i := 0) (l := "worker") rfl).symm
theorem addrOf_2 : (layout tkLoopWorker).addrOf 2 = (layout tkLoopWorker).addrOf 3 :=
  (addrOf_label (i := 2) (l := "round") rfl).symm
theorem addrOf_5 : (layout tkLoopWorker).addrOf 5 = (layout tkLoopWorker).addrOf 6 :=
  (addrOf_label (i := 5) (l := "spin") rfl).symm
theorem addrOf_16 : (layout tkLoopWorker).addrOf 16 = (layout tkLoopWorker).addrOf 17 :=
  (addrOf_label (i := 16) (l := "done") rfl).symm

theorem label_round :
    (_root_.Executable.labels (layout tkLoopWorker)).label "round" = (layout tkLoopWorker).addrOf 3 := by
  rw [Program.label_addrOf_drop (i := 2) (by decide) (by decide) (by decide)]
  exact addrOf_2

theorem label_spin :
    (_root_.Executable.labels (layout tkLoopWorker)).label "spin" = (layout tkLoopWorker).addrOf 6 := by
  rw [Program.label_addrOf_drop (i := 5) (by decide) (by decide) (by decide)]
  exact addrOf_5

theorem label_done :
    (_root_.Executable.labels (layout tkLoopWorker)).label "done" = (layout tkLoopWorker).addrOf 17 := by
  rw [Program.label_addrOf_drop (i := 16) (by decide) (by decide) (by decide)]
  exact addrOf_16

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i tkLoopWorker [tkLoopWorker] [label_round, label_spin, label_done] [goto, $ts,*])

theorem exec_mov (st : State) (h : At tkLoopWorker st 1) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X6 1#64 } ((layout tkLoopWorker).addrOf 3))) := by
  rw [← addrOf_2, next_pc h (by decide)]
  cell h 1 []

/-- `cbz w7, done` (position 3): silent, to the end when no round is left. -/
theorem exec_cbz (st : State) (h : At tkLoopWorker st 3) :
    isa.exec st = some (.done (goto st st.st.1
      (if w32 st.st.1.regs.X7 = 0#32 then (layout tkLoopWorker).addrOf 17
       else (layout tkLoopWorker).addrOf 4))) := by
  rw [next_pc h (by decide)]
  by_cases hz : w32 st.st.1.regs.X7 = 0#32 <;> cell h 3 [hz]

theorem exec_ldadda (st : State) (h : At tkLoopWorker st 4) {x : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = x) (hdm : Mem.loadInt st.st.1.dmem x 4 = none) :
    isa.exec st = some (.rmw .acq false ⟨x, 4⟩
      (fun old => some (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 st.st.1.regs.X6.toBitVec)))
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout tkLoopWorker).addrOf 6))) := by
  rw [← addrOf_5, next_pc h (by decide)]
  cell h 4 [hx0, hdm]

theorem exec_ldar (st : State) (h : At tkLoopWorker st 6) {o : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = o) (hdm : Mem.loadInt st.st.1.dmem o 4 = none) :
    isa.exec st = some (.load .acq false ⟨o, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout tkLoopWorker).addrOf 7))) := by
  rw [next_pc h (by decide)]
  cell h 6 [hx1, hdm]

/-- `cmp w4, w3` (position 7): silent, sets the flags; `Z` iff the low words
agree. -/
theorem exec_cmp (st : State) (h : At tkLoopWorker st 7) :
    ∃ s : StatusFlags, isa.exec st = some (.done (goto st { st.st.1 with status := s } ((layout tkLoopWorker).addrOf 8)))
      ∧ (s.z = true ↔ w32 st.st.1.regs.X4 = w32 st.st.1.regs.X3) := by
  refine ⟨?s, ?e, ?z⟩
  case e =>
    rw [next_pc h (by decide)]
    cell h 7 []
    rfl
  case z =>
    simp only [w32, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    exact iff_of_eq (congrArg _ (BitVec.zero_add _))

/-- `b.ne spin` (position 8): silent, back to `spin` unless `Z`. -/
theorem exec_bne (st : State) (h : At tkLoopWorker st 8) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.status.z = true then (layout tkLoopWorker).addrOf 9 else (layout tkLoopWorker).addrOf 6))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.z = true <;> cell h 8 [hz]

theorem exec_ldr_c (st : State) (h : At tkLoopWorker st 9) {c : BitVec 64}
    (hx2 : st.st.1.regs.X2.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.load .plain false ⟨c, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout tkLoopWorker).addrOf 10))) := by
  rw [next_pc h (by decide)]
  cell h 9 [hx2, hdc]

theorem exec_add5 (st : State) (h : At tkLoopWorker st 10) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      ((layout tkLoopWorker).addrOf 11))) := by
  rw [next_pc h (by decide)]
  cell h 10 []

theorem exec_str_c (st : State) (h : At tkLoopWorker st 11) {c : BitVec 64}
    (hx2 : st.st.1.regs.X2.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.store .plain false ⟨c, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X5.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout tkLoopWorker).addrOf 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 [hx2, hdc]

theorem exec_add4 (st : State) (h : At tkLoopWorker st 12) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (st.st.1.regs.X3.toBitVec.take 32 + 1#32)) }
      ((layout tkLoopWorker).addrOf 13))) := by
  rw [next_pc h (by decide)]
  cell h 12 []

theorem exec_stlr (st : State) (h : At tkLoopWorker st 13) {o : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = o) (hdm : Mem.loadInt st.st.1.dmem o 4 = none) :
    isa.exec st = some (.store .rel false ⟨o, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X4.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout tkLoopWorker).addrOf 14))) := by
  rw [next_pc h (by decide)]
  cell h 13 [hx1, hdm]

/-- `sub w7, w7, #1` (position 14): silent, one round fewer left. -/
theorem exec_sub (st : State) (h : At tkLoopWorker st 14) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X7 (BitVec.setWidth 64 (st.st.1.regs.X7.toBitVec.take 32 - 1#32)) }
      ((layout tkLoopWorker).addrOf 15))) := by
  rw [next_pc h (by decide)]
  cell h 14 []

/-- `b round` (position 15): silent, back to the loop head. -/
theorem exec_b_round (st : State) (h : At tkLoopWorker st 15) :
    isa.exec st = some (.done (goto st st.st.1 ((layout tkLoopWorker).addrOf 3))) := by
  cell h 15 []

/-! ## Distinct addresses -/

/-- The positions a worker's pc takes (`0` is at the address of `1`, `2` at
that of `3`, `5` at that of `6`, `16` at that of `17`). -/
def tkLoopPcs : List Nat := [1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17]

/-- The address-distinct representative of a position. -/
def canon (i : Nat) : Nat := if i = 3 then 2 else if i = 6 then 5 else if i = 17 then 16 else i

theorem addrOf_canon (i : Nat) : (layout tkLoopWorker).addrOf (canon i) = (layout tkLoopWorker).addrOf i := by
  unfold canon
  split
  · subst_vars; exact addrOf_2
  · split
    · subst_vars; exact addrOf_5
    · split
      · subst_vars; exact addrOf_16
      · rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ tkLoopPcs) (hj : j ∈ tkLoopPcs)
    (h : (layout tkLoopWorker).addrOf i = (layout tkLoopWorker).addrOf j) : i = j :=
  SLR.A64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) tkLoopPcs canon (fun i _ => addrOf_canon i) (by decide)
    hi hj h

end Kraken.Promising.Live.TicketLoopTrees
