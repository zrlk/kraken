/-
**Stage 4: the event trees of the x64 `treiber2.kl`
worker, verbatim** (`Treiber2X.treiber2CodeV`, absolute operand `(top)`) in
its image `treiber2ImageV` (the code, then the runner's data trailer) under
the promising interpretation of x64, on a valid layout of the image. The
`LiveSpinX64CmpxTrees.lean` recipe: each theorem reads `isa.exec st` at the
address of one cell through `X64.exec_eq_of_codeAt` (hence `decls = {}`).

```
 0 worker:                       8   testq %rax,%rax
 1 push:                         9   je pop
 2   movq (top),%rax            10   movq (%rax),%rcx
 3   movq %rax,(%rbx)           11   lock cmpxchgq %rcx,(top)
 4   lock cmpxchgq %rbx,(top)   12   jne pop
 5   jne push                   13   movq %rax,%r12
 6 pop:                         14   jmp done
 7   movq (top),%rax            15 done:
                                16.. the data trailer (`top`, `n1`, `n2`)
```

`top` is the word at `symT2 "top"`; the links are the words at `%rbx` (the
thread's node) and `%rax` (the node read), all outside the thread's private
data memory. `testq` leaves `AF` undefined (a `.choose`); each cell is stated
up to the register results the termination and history invariants do not
read.
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2Public
import Kraken.Promising.SLR.X64Trees

namespace Kraken.Promising.Live.TermX64Treiber2Trees

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.Treiber2X (treiber2ImageV treiber2CodeV treiber2DataV symT2 labT2
  treiber2ImageV_wf)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiber2ImageV)]

set_option hygiene false in
local notation "pcT" => (layout treiber2ImageV).addrOf

/-- The context of a cell: the state runs the laid-out image, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout treiber2ImageV
  decls : st.decls = {}
  pc : st.st.2 = pcT i
  ne : (st.st.2 == st.endPc) = false

/-- The state `st` moved to machine data `m` at address `pc`. -/
abbrev goto (st : State) (m : MachineData) (pc : Int64) : State :=
  { st with st := (m, pc) }

omit hv in
theorem addrOf_step {i : Nat} (hi : i < treiber2ImageV.length) :
    pcT (i + 1) = pcT i + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.X64Trees.addrOf_step hi

/-- A label position occupies no bytes. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : treiber2ImageV[i]? = some (Directive.label l)) :
    pcT (i + 1) = pcT i :=
  SLR.X64Trees.addrOf_label hp

theorem addrOf_1 : pcT 1 = pcT 2 := (addrOf_label (i := 1) (l := "push") rfl).symm
theorem addrOf_0 : pcT 0 = pcT 2 := ((addrOf_label (i := 0) (l := "worker") rfl).symm).trans addrOf_1
theorem addrOf_6 : pcT 6 = pcT 7 := (addrOf_label (i := 6) (l := "pop") rfl).symm
theorem addrOf_15 : pcT 15 = pcT 16 := (addrOf_label (i := 15) (l := "done") rfl).symm

theorem label_worker : (_root_.Executable.labels (layout treiber2ImageV)).label "worker" = pcT 2 := by
  rw [Program.label_addrOf_drop (i := 0) treiber2ImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_0

theorem label_push : (_root_.Executable.labels (layout treiber2ImageV)).label "push" = pcT 2 := by
  rw [Program.label_addrOf_drop (i := 1) treiber2ImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_1

theorem label_pop : (_root_.Executable.labels (layout treiber2ImageV)).label "pop" = pcT 7 := by
  rw [Program.label_addrOf_drop (i := 6) treiber2ImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_6

theorem label_done : (_root_.Executable.labels (layout treiber2ImageV)).label "done" = pcT 16 := by
  rw [Program.label_addrOf_drop (i := 15) treiber2ImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_15

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < treiber2ImageV.length) :
    pcT (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  x64cell $h $i treiber2ImageV [treiber2ImageV, treiber2CodeV]
    [label_push, label_pop, label_done, $ts,*])

omit layout hv in
/-- A relative jump lands on its target. -/
private theorem int64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

/-- `movq (top),%rax` (positions 2 and 7): a plain load of `top` into
`%rax`; `%rbx` and the private memory unchanged. -/
theorem exec_ldtop (st : State) {i : Nat} (hi : i = 2 ∨ i = 7) (h : At st i)
    (hdm : Mem.loadInt st.st.1.dmem (symT2 "top") 8 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧ (g v).regs.get64 .rax = BitVec.setWidth 64 v ∧
        (g v).regs.get64 .rbx = st.st.1.regs.get64 .rbx) ∧
      isa.exec st = some (.load .plain false ⟨symT2 "top", 8⟩ fun v => .done (goto st (g v) (pcT (i + 1)))) := by
  rcases hi with rfl | rfl
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cell h 2 [hdm, symT2]; rfl⟩
    intro v; refine ⟨rfl, ?_, ?_⟩ <;> simp
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cell h 7 [hdm, symT2]; rfl⟩
    intro v; refine ⟨rfl, ?_, ?_⟩ <;> simp

/-- `movq %rax,(%rbx)` (position 3): a plain store of `%rax` to the node's
link. -/
theorem exec_stlink (st : State) (h : At st 3)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.get64 .rbx) 8 = none) :
    isa.exec st = some (.store .plain false ⟨st.st.1.regs.get64 .rbx, 8⟩
      (BitVec.setWidth 128 (st.st.1.regs.get64 .rax)) fun _ => .done (goto st st.st.1 (pcT 4))) := by
  have hdm' : Mem.loadInt st.st.1.dmem (st.st.1.regs.rbx.toBitVec.take 64) 8 = none := by
    first | exact hdm | simpa [BitVec.take] using hdm
  rw [next_pc h (by decide)]
  cell h 3 [hdm']
  simp [BitVec.take]

/-- `lock cmpxchgq %R,(top)` (positions 4 with `%rbx`, 11 with `%rcx`): a
locked (`acqRel`) RMW of `top` that writes `%R` iff the old value is `%rax`;
afterwards `ZF` iff it was, `%rax` holds the old value (unchanged on success),
and `%rbx` is unchanged. -/
theorem exec_cas (st : State) {i : Nat} {r : Reg64} (hi : (i = 4 ∧ r = .rbx) ∨ (i = 11 ∧ r = .rcx)) (h : At st i)
    (hdm : Mem.loadInt st.st.1.dmem (symT2 "top") 8 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧
        ((g v).status.zf = true ↔ BitVec.setWidth 64 v = st.st.1.regs.get64 .rax) ∧
        (g v).regs.get64 .rax = BitVec.setWidth 64 v ∧ (g v).regs.get64 .rbx = st.st.1.regs.get64 .rbx) ∧
      isa.exec st = some (.rmw .acqRel false ⟨symT2 "top", 8⟩
        (fun old => if BitVec.setWidth 64 old = st.st.1.regs.get64 .rax then
          some (BitVec.setWidth 128 (st.st.1.regs.get64 r)) else none)
        fun v => .done (goto st (g v) (pcT (i + 1)))) := by
  have hr : st.st.1.regs.get64 .rax = st.st.1.regs.rax.toBitVec := rfl
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cell h 4 [hdm, symT2]; exact ⟨rfl, funext fun v => rfl⟩⟩
    intro v
    refine ⟨by split <;> rfl, ?_, ?_, ?_⟩
    · change (st.st.1.regs.get64 .rax - BitVec.setWidth 64 v == 0#64) = true ↔ _
      simp only [beq_iff_eq]
      constructor <;> intro e <;> bv_omega
    · by_cases e : BitVec.setWidth 64 v = st.st.1.regs.get64 .rax
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hr ▸ e))]; exact e.symm
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (hr ▸ e))]; simp
    · by_cases e : BitVec.setWidth 64 v = st.st.1.regs.get64 .rax
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hr ▸ e))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (hr ▸ e))]; simp
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cell h 11 [hdm, symT2]; exact ⟨rfl, funext fun v => rfl⟩⟩
    intro v
    refine ⟨by split <;> rfl, ?_, ?_, ?_⟩
    · change (st.st.1.regs.get64 .rax - BitVec.setWidth 64 v == 0#64) = true ↔ _
      simp only [beq_iff_eq]
      constructor <;> intro e <;> bv_omega
    · by_cases e : BitVec.setWidth 64 v = st.st.1.regs.get64 .rax
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hr ▸ e))]; exact e.symm
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (hr ▸ e))]; simp
    · by_cases e : BitVec.setWidth 64 v = st.st.1.regs.get64 .rax
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hr ▸ e))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (hr ▸ e))]; simp

/-- `jne push` (position 5): back to `push` unless `ZF`. -/
theorem exec_jne5 (st : State) (h : At st 5) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcT 6 else pcT 2))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cell h 5 [hz]

/-- `testq %rax,%rax` (position 8): `ZF` iff `%rax = 0`; `%rax`, `%rbx` and
the private memory unchanged. -/
theorem exec_test (st : State) (h : At st 8) :
    isa.exec st = some (.choose 2 fun i => .done (goto st
      { st.st.1 with
        status := StatusFlags.from_result (st.st.1.regs.get64 .rax) ⟨false, i.val == 1, false⟩ } (pcT 9))) := by
  rw [next_pc h (by decide)]
  cell h 8 []

omit layout hv in
/-- After `testq %rax,%rax`, `ZF` iff `%rax = 0`. -/
theorem test_zf (r : BitVec 64) (af : Bool) :
    (StatusFlags.from_result r ⟨false, af, false⟩).zf = true ↔ r = 0#64 := by
  change (r == 0#64) = true ↔ _
  simp only [beq_iff_eq]

/-- `je pop` (position 9): back to `pop` if `ZF`. -/
theorem exec_je (st : State) (h : At st 9) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcT 7 else pcT 10))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cell h 9 [hz]

/-- `movq (%rax),%rcx` (position 10): a plain load of the link of the node
`%rax` into `%rcx`. -/
theorem exec_ldlink (st : State) (h : At st 10)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.get64 .rax) 8 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧ (g v).regs.get64 .rax = st.st.1.regs.get64 .rax ∧
        (g v).regs.get64 .rbx = st.st.1.regs.get64 .rbx ∧ (g v).regs.get64 .rcx = BitVec.setWidth 64 v) ∧
      isa.exec st = some (.load .plain false ⟨st.st.1.regs.get64 .rax, 8⟩ fun v => .done (goto st (g v) (pcT 11))) := by
  have hdm' : Mem.loadInt st.st.1.dmem (st.st.1.regs.rax.toBitVec.take 64) 8 = none := by
    simpa [BitVec.take] using hdm
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 10 [hdm']; exact ⟨by simp [BitVec.take], rfl⟩⟩
  intro v; refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp

/-- `jne pop` (position 12): back to `pop` unless `ZF`. -/
theorem exec_jne12 (st : State) (h : At st 12) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcT 13 else pcT 7))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cell h 12 [hz]

/-- `movq %rax,%r12` (position 13): `%r12 := %rax`. -/
theorem exec_mov13 (st : State) (h : At st 13) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ md.regs.get64 .r12 = st.st.1.regs.get64 .rax ∧
      isa.exec st = some (.done (goto st md (pcT 14))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, ?_, by cell h 13 []; rfl⟩
  · rfl
  · simp

/-- `jmp done` (position 14): to the exit label. -/
theorem exec_jmp (st : State) (h : At st 14) :
    isa.exec st = some (.done (goto st st.st.1 (pcT 16))) := by
  cell h 14 [int64_add_sub]

/-! ## Distinct addresses -/

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

/-- The positions a worker's pc takes (`0`/`1` are at the address of `2`, `6`
at that of `7`, `15` at that of `16`, the first data cell). -/
def tPcs : List Nat := [2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16]

/-- The address-distinct representative of a position: the label before it. -/
def canon (i : Nat) : Nat := if i = 7 then 6 else if i = 16 then 15 else i

theorem addrOf_canon (i : Nat) : pcT (canon i) = pcT i := by
  unfold canon
  split
  · subst_vars; exact addrOf_6
  · split
    · subst_vars; exact addrOf_15
    · rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ tPcs) (hj : j ∈ tPcs) (h : pcT i = pcT j) : i = j :=
  SLR.X64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) tPcs canon (fun i _ => addrOf_canon i) (by decide) hi hj h

end Kraken.Promising.Live.TermX64Treiber2Trees
