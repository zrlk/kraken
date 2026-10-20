/-
**Stage 3: the event trees of the ticket-lock worker**
`tkWorker` (`ticketlock2.kl`, `EnvG/TicketLockSmoke.lean`) under the
promising interpretation of AArch64, on a valid layout. The `SwpTrees.lean`
recipe: each theorem reads `isa.exec st` at the address of one cell through
`AArch64.exec_eq_of_codeAt`.

```
 0 worker:                  7   LDR W5,[X2]
 1   MOV W6,#1              8   ADD W5,W5,#1
 2   LDADDA W6,W3,[X0]      9   STR W5,[X2]
 3 spin:                   10   ADD W4,W3,#1
 4   LDAR W4,[X1]          11   STLR W4,[X1]
 5   CMP W4,W3             12   B done
 6   B.NE spin             13 done:
```

`next = X0`, `owner = X1`, counter `= X2`, all outside the thread's private
data memory. Fall-through addresses are the address of the next instruction
(`addrOf 4` past the label `spin`, `addrOf 14` past `done`).
-/
import Kraken.Promising.SLR.EnvG.TicketLockSmoke
import Kraken.Promising.SLR.A64Trees

namespace Kraken.Promising.Live.TicketTrees

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

/-- The context of a cell: the state runs the laid-out worker, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout tkWorker
  decls : st.decls = {}
  pc : st.st.2 = (layout tkWorker).addrOf i
  ne : (st.st.2 == st.endPc) = false

/-- The state `st` moved to machine data `m` at address `pc`. -/
abbrev goto (st : State) (m : MachineData) (pc : Int64) : State :=
  { st with st := (m, pc) }

omit hv in
private theorem layout_getElem (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

omit hv in
theorem addrOf_step {i : Nat} (hi : i < tkWorker.length) :
    (layout tkWorker).addrOf (i + 1) = (layout tkWorker).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.A64Trees.addrOf_step hi

/-- A label position occupies no bytes. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : tkWorker[i]? = some (Directive.label l)) :
    (layout tkWorker).addrOf (i + 1) = (layout tkWorker).addrOf i :=
  SLR.A64Trees.addrOf_label hp

theorem addrOf_3 : (layout tkWorker).addrOf 3 = (layout tkWorker).addrOf 4 :=
  (addrOf_label (i := 3) (l := "spin") rfl).symm
theorem addrOf_13 : (layout tkWorker).addrOf 13 = (layout tkWorker).addrOf 14 :=
  (addrOf_label (i := 13) (l := "done") rfl).symm
theorem addrOf_0 : (layout tkWorker).addrOf 0 = (layout tkWorker).addrOf 1 :=
  (addrOf_label (i := 0) (l := "worker") rfl).symm

theorem label_spin : (_root_.Executable.labels (layout tkWorker)).label "spin" = (layout tkWorker).addrOf 4 := by
  rw [Program.label_addrOf_drop (i := 3) (by decide) (by decide) (by decide)]
  exact addrOf_3

theorem label_done : (_root_.Executable.labels (layout tkWorker)).label "done" = (layout tkWorker).addrOf 14 := by
  rw [Program.label_addrOf_drop (i := 13) (by decide) (by decide) (by decide)]
  exact addrOf_13

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < tkWorker.length) :
    (layout tkWorker).addrOf (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i tkWorker [tkWorker] [label_spin, label_done] [goto, $ts,*])

theorem exec_mov (st : State) (h : At st 1) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X6 1#64 } ((layout tkWorker).addrOf 2))) := by
  rw [next_pc h (by decide)]
  cell h 1 []

theorem exec_ldadda (st : State) (h : At st 2) {x : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = x) (hdm : Mem.loadInt st.st.1.dmem x 4 = none) :
    isa.exec st = some (.rmw .acq false ⟨x, 4⟩
      (fun old => some (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 st.st.1.regs.X6.toBitVec)))
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout tkWorker).addrOf 4))) := by
  rw [← addrOf_3, next_pc h (by decide)]
  cell h 2 [hx0, hdm]

theorem exec_ldar (st : State) (h : At st 4) {o : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = o) (hdm : Mem.loadInt st.st.1.dmem o 4 = none) :
    isa.exec st = some (.load .acq false ⟨o, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout tkWorker).addrOf 5))) := by
  rw [next_pc h (by decide)]
  cell h 4 [hx1, hdm]

/-- The low word of an `X` register, as `CMP`/`ADD`/`STR` on `W` registers see it. -/
abbrev w32 (r : UInt64) : BitVec 32 := BitVec.setWidth 32 r.toBitVec

/-- `cmp w4, w3` (position 5): silent, sets the flags; `Z` iff the low words
agree. -/
theorem exec_cmp (st : State) (h : At st 5) :
    ∃ s : StatusFlags, isa.exec st = some (.done (goto st { st.st.1 with status := s } ((layout tkWorker).addrOf 6)))
      ∧ (s.z = true ↔ w32 st.st.1.regs.X4 = w32 st.st.1.regs.X3) := by
  refine ⟨?s, ?e, ?z⟩
  case e =>
    rw [next_pc h (by decide)]
    cell h 5 []
    rfl
  case z =>
    simp only [w32, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    exact iff_of_eq (congrArg _ (BitVec.zero_add _))

/-- `b.ne spin` (position 6): silent, back to `spin` unless `Z`. -/
theorem exec_bne (st : State) (h : At st 6) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.status.z = true then (layout tkWorker).addrOf 7 else (layout tkWorker).addrOf 4))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.z = true <;> cell h 6 [hz]

/-- `ldr w5, [x2]` (position 7): a plain load of the counter into `X5`. -/
theorem exec_ldr_c (st : State) (h : At st 7) {c : BitVec 64}
    (hx2 : st.st.1.regs.X2.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.load .plain false ⟨c, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout tkWorker).addrOf 8))) := by
  rw [next_pc h (by decide)]
  cell h 7 [hx2, hdc]

/-- `add w5, w5, #1` (position 8): silent. -/
theorem exec_add5 (st : State) (h : At st 8) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      ((layout tkWorker).addrOf 9))) := by
  rw [next_pc h (by decide)]
  cell h 8 []

/-- `str w5, [x2]` (position 9): a plain store of `X5`'s low word to the counter. -/
theorem exec_str_c (st : State) (h : At st 9) {c : BitVec 64}
    (hx2 : st.st.1.regs.X2.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.store .plain false ⟨c, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X5.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout tkWorker).addrOf 10))) := by
  rw [next_pc h (by decide)]
  cell h 9 [hx2, hdc]

/-- `add w4, w3, #1` (position 10): silent. -/
theorem exec_add4 (st : State) (h : At st 10) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (st.st.1.regs.X3.toBitVec.take 32 + 1#32)) }
      ((layout tkWorker).addrOf 11))) := by
  rw [next_pc h (by decide)]
  cell h 10 []

/-- `stlr w4, [x1]` (position 11): a release store of `X4`'s low word to the owner. -/
theorem exec_stlr (st : State) (h : At st 11) {o : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = o) (hdm : Mem.loadInt st.st.1.dmem o 4 = none) :
    isa.exec st = some (.store .rel false ⟨o, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X4.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout tkWorker).addrOf 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 [hx1, hdm]

/-- `b done` (position 12): silent, to the end of the text. -/
theorem exec_b_done (st : State) (h : At st 12) :
    isa.exec st = some (.done (goto st st.st.1 ((layout tkWorker).addrOf 14))) := by
  cell h 12 []

/-! ## Distinct addresses -/

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

/-- The address past an instruction differs from every address at or before it. -/
theorem addrOf_ne_succ {k n : Nat} (hk : k ≤ n) (h : tkWorker[n]?.map isInstr = some true) :
    (layout tkWorker).addrOf k ≠ (layout tkWorker).addrOf (n + 1) :=
  SLR.A64Trees.addrOf_ne_succ _ isInstr (fun _ => rfl) hk h

/-- The positions a worker's pc takes (`0` is at the address of `1`, `3` at
that of `4`, `13` at that of `14`). -/
def tkPcs : List Nat := [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14]

/-- The address-distinct representative of a position. -/
def canon (i : Nat) : Nat := if i = 4 then 3 else if i = 14 then 13 else i

theorem addrOf_canon (i : Nat) : (layout tkWorker).addrOf (canon i) = (layout tkWorker).addrOf i := by
  unfold canon
  split
  · subst_vars; exact addrOf_3
  · split
    · subst_vars; exact addrOf_13
    · rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ tkPcs) (hj : j ∈ tkPcs)
    (h : (layout tkWorker).addrOf i = (layout tkWorker).addrOf j) : i = j :=
  SLR.A64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) tkPcs canon (fun i _ => addrOf_canon i) (by decide) hi hj h

end Kraken.Promising.Live.TicketTrees
