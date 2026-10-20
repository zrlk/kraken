/-
**Stage 3: the event trees of the AArch64 CAS
spinlock worker** `casTtasWorker` (`spinlock_cas2.kl`, `EnvG/CasSmoke.lean`)
under the promising interpretation of AArch64, on a valid layout. The
`LiveTicketTrees.lean` recipe: each theorem reads `isa.exec st` at the
address of one cell through `AArch64.exec_eq_of_codeAt`.

```
 0 worker:                   9   B try
 1   MOV W3,#1              10 cs:
 2 try:                     11   LDR W5,[X1]
 3   MOV W2,#0              12   ADD W5,W5,#1
 4   CASA W2,W3,[X0]        13   STR W5,[X1]
 5   CBZ W2,cs              14   STLR WZR,[X0]
 6 spin:                    15   B done
 7   LDR W2,[X0]            16 done:
 8   CBNZ W2,spin
```

`lock = X0`, counter `= X1`, both outside the thread's private data memory.
A label shares the address of the next instruction (`addrOf 0 = addrOf 1`,
`2 ↦ 3`, `6 ↦ 7`, `10 ↦ 11`, `16 ↦ 17`, the end of the text).
-/
import Kraken.Promising.SLR.EnvG.CasSmoke
import Kraken.Promising.SLR.A64Trees

namespace Kraken.Promising.Live.SpinCasTrees

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

/-- The context of a cell: the state runs the laid-out worker, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout casTtasWorker
  decls : st.decls = {}
  pc : st.st.2 = (layout casTtasWorker).addrOf i
  ne : (st.st.2 == st.endPc) = false

/-- The state `st` moved to machine data `m` at address `pc`. -/
abbrev goto (st : State) (m : MachineData) (pc : Int64) : State :=
  { st with st := (m, pc) }

omit hv in
private theorem layout_getElem (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

omit hv in
theorem addrOf_step {i : Nat} (hi : i < casTtasWorker.length) :
    (layout casTtasWorker).addrOf (i + 1) =
      (layout casTtasWorker).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.A64Trees.addrOf_step hi

/-- A label position occupies no bytes. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : casTtasWorker[i]? = some (Directive.label l)) :
    (layout casTtasWorker).addrOf (i + 1) = (layout casTtasWorker).addrOf i :=
  SLR.A64Trees.addrOf_label hp

theorem addrOf_0 : (layout casTtasWorker).addrOf 0 = (layout casTtasWorker).addrOf 1 :=
  (addrOf_label (i := 0) (l := "worker") rfl).symm
theorem addrOf_2 : (layout casTtasWorker).addrOf 2 = (layout casTtasWorker).addrOf 3 :=
  (addrOf_label (i := 2) (l := "try") rfl).symm
theorem addrOf_6 : (layout casTtasWorker).addrOf 6 = (layout casTtasWorker).addrOf 7 :=
  (addrOf_label (i := 6) (l := "spin") rfl).symm
theorem addrOf_10 : (layout casTtasWorker).addrOf 10 = (layout casTtasWorker).addrOf 11 :=
  (addrOf_label (i := 10) (l := "cs") rfl).symm
theorem addrOf_16 : (layout casTtasWorker).addrOf 16 = (layout casTtasWorker).addrOf 17 :=
  (addrOf_label (i := 16) (l := "done") rfl).symm

theorem label_try : (_root_.Executable.labels (layout casTtasWorker)).label "try" =
    (layout casTtasWorker).addrOf 3 := by
  rw [Program.label_addrOf_drop (i := 2) (by decide) (by decide) (by decide)]
  exact addrOf_2

theorem label_spin : (_root_.Executable.labels (layout casTtasWorker)).label "spin" =
    (layout casTtasWorker).addrOf 7 := by
  rw [Program.label_addrOf_drop (i := 6) (by decide) (by decide) (by decide)]
  exact addrOf_6

theorem label_cs : (_root_.Executable.labels (layout casTtasWorker)).label "cs" =
    (layout casTtasWorker).addrOf 11 := by
  rw [Program.label_addrOf_drop (i := 10) (by decide) (by decide) (by decide)]
  exact addrOf_10

theorem label_done : (_root_.Executable.labels (layout casTtasWorker)).label "done" =
    (layout casTtasWorker).addrOf 17 := by
  rw [Program.label_addrOf_drop (i := 16) (by decide) (by decide) (by decide)]
  exact addrOf_16

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < casTtasWorker.length) :
    (layout casTtasWorker).addrOf (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i casTtasWorker [casTtasWorker] [label_try, label_spin, label_cs, label_done] [goto, $ts,*])

/-- The low word of an `X` register, as `W`-register instructions see it. -/
abbrev w32 (r : UInt64) : BitVec 32 := BitVec.setWidth 32 r.toBitVec

/-- `mov w3, #1` (position 1). -/
theorem exec_mov3 (st : State) (h : At st 1) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 1#64 } ((layout casTtasWorker).addrOf 3))) := by
  rw [← addrOf_2, next_pc h (by decide)]
  cell h 1 []

/-- `mov w2, #0` (position 3). -/
theorem exec_mov2 (st : State) (h : At st 3) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X2 0#64 } ((layout casTtasWorker).addrOf 4))) := by
  rw [next_pc h (by decide)]
  cell h 3 []

/-- `casa w2, w3, [x0]` (position 4): an acquire RMW that writes `W3` iff the
old low word is `W2`; `X2` receives the old low word either way. -/
theorem exec_casa (st : State) (h : At st 4) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.rmw .acq false ⟨l, 4⟩
      (fun old => if BitVec.setWidth 32 old = w32 st.st.1.regs.X2 then
          some (BitVec.setWidth 128 (w32 st.st.1.regs.X3)) else none)
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout casTtasWorker).addrOf 5))) := by
  rw [next_pc h (by decide)]
  cell h 4 [hx0, hdm]

/-- `cbz w2, cs` (position 5). -/
theorem exec_cbz (st : State) (h : At st 5) :
    isa.exec st = some (.done (goto st st.st.1
      (if w32 st.st.1.regs.X2 = 0#32 then (layout casTtasWorker).addrOf 11
       else (layout casTtasWorker).addrOf 7))) := by
  rw [← addrOf_6, next_pc h (by decide)]
  by_cases hz : w32 st.st.1.regs.X2 = 0#32 <;> cell h 5 [hz]

/-- `ldr w2, [x0]` (position 7): a plain load of the lock into `X2`. -/
theorem exec_ldr_l (st : State) (h : At st 7) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.load .plain false ⟨l, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout casTtasWorker).addrOf 8))) := by
  rw [next_pc h (by decide)]
  cell h 7 [hx0, hdm]

/-- `cbnz w2, spin` (position 8). -/
theorem exec_cbnz (st : State) (h : At st 8) :
    isa.exec st = some (.done (goto st st.st.1
      (if w32 st.st.1.regs.X2 = 0#32 then (layout casTtasWorker).addrOf 9
       else (layout casTtasWorker).addrOf 7))) := by
  rw [next_pc h (by decide)]
  by_cases hz : w32 st.st.1.regs.X2 = 0#32 <;> cell h 8 [hz]

/-- `b try` (position 9). -/
theorem exec_b_try (st : State) (h : At st 9) :
    isa.exec st = some (.done (goto st st.st.1 ((layout casTtasWorker).addrOf 3))) := by
  cell h 9 []

/-- `ldr w5, [x1]` (position 11): a plain load of the counter into `X5`. -/
theorem exec_ldr_c (st : State) (h : At st 11) {c : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.load .plain false ⟨c, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout casTtasWorker).addrOf 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 [hx1, hdc]

/-- `add w5, w5, #1` (position 12). -/
theorem exec_add5 (st : State) (h : At st 12) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      ((layout casTtasWorker).addrOf 13))) := by
  rw [next_pc h (by decide)]
  cell h 12 []

/-- `str w5, [x1]` (position 13): a plain store to the counter. -/
theorem exec_str_c (st : State) (h : At st 13) {c : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.store .plain false ⟨c, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X5.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout casTtasWorker).addrOf 14))) := by
  rw [next_pc h (by decide)]
  cell h 13 [hx1, hdc]

/-- `stlr wzr, [x0]` (position 14): a release store of `0` to the lock. -/
theorem exec_stlr (st : State) (h : At st 14) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.store .rel false ⟨l, 4⟩ 0#128
      fun _ => .done (goto st st.st.1 ((layout casTtasWorker).addrOf 15))) := by
  rw [next_pc h (by decide)]
  cell h 14 [hx0, hdm]

/-- `b done` (position 15): to the end of the text. -/
theorem exec_b_done (st : State) (h : At st 15) :
    isa.exec st = some (.done (goto st st.st.1 ((layout casTtasWorker).addrOf 17))) := by
  cell h 15 []

/-! ## Distinct addresses -/

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

/-- The address past an instruction differs from every address at or before it. -/
theorem addrOf_ne_succ {k n : Nat} (hk : k ≤ n) (h : casTtasWorker[n]?.map isInstr = some true) :
    (layout casTtasWorker).addrOf k ≠ (layout casTtasWorker).addrOf (n + 1) :=
  SLR.A64Trees.addrOf_ne_succ _ isInstr (fun _ => rfl) hk h

/-- The positions a worker's pc takes (each label at the address of the next
instruction). -/
def spPcs : List Nat := [1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 17]

/-- The address-distinct representative of a position: the label before it. -/
def canon (i : Nat) : Nat :=
  if i = 3 then 2 else if i = 7 then 6 else if i = 11 then 10 else if i = 17 then 16 else i

theorem addrOf_canon (i : Nat) : (layout casTtasWorker).addrOf (canon i) = (layout casTtasWorker).addrOf i := by
  unfold canon
  split
  · subst_vars; exact addrOf_2
  split
  · subst_vars; exact addrOf_6
  split
  · subst_vars; exact addrOf_10
  split
  · subst_vars; exact addrOf_16
  rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ spPcs) (hj : j ∈ spPcs)
    (h : (layout casTtasWorker).addrOf i = (layout casTtasWorker).addrOf j) : i = j :=
  SLR.A64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) spPcs canon (fun i _ => addrOf_canon i) (by decide) hi hj h

end Kraken.Promising.Live.SpinCasTrees
