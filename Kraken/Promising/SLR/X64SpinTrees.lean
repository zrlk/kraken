/-
The event trees of the cells of the x64 `xchg` spinlock worker (`spinWorker`,
the `worker` of `Kraken/Examples/LockFree/X64/spinlock2.kl`) under the
promising interpretation of x64 (`Kraken.Promising.X64.isa`). The x64 twin of
`SLR/SwpTrees.lean`.

Each theorem reads `isa.exec st` at the address of one cell of the laid-out
worker, through `X64.exec_eq_of_codeAt`, as the event tree of that cell: a
silent step (`movl $1`, `addl`, the branches), a choice (`testl`: x64 leaves
`AF` undefined after `test`, and the adapter turns the undefined flag into
`.choose 2`), a load (`movl (%rdi)`, `movl (%rsi)`), a store (`movl %ecx,
(%rsi)`, the unlock `movl $0, (%rdi)`: plain stores; x86-TSO's ordering of them is
the memory model's business, not the tree's) or a
read-modify-write (`xchgl`: implicitly locked, `rmwK .acqRel`, one `rmw`
event that always writes). Fall-through addresses are the address of the next
position, branch targets the address of the label's position. The lock is the
word at `%rdi = l`, the counter the word at `%rsi = c`; both lie outside the
thread's private data memory (`Mem.loadInt … = none`), so the accesses go to
the shared memory.

The `.kl` file names the lock and the counter by symbol (`(lock)`,
`(counter)`); here they are addressed through `%rdi`/`%rsi`, as the AArch64
`swpWorker` addresses them through `x0`/`x1`.

These are the per-instruction inputs of the tree-level rules of an SLR x64
spinlock proof (`EvTree.EraseWP`/`EvTree.EraseWPR`, through
`EvTree.eraseWP_map`/`EvTree.eraseWPR_map`, `SLR/TreeMap.lean`).

The worker:
```
 0 worker:                 7   jne worker
 1   movl (%rdi),%eax      8   movl (%rsi),%ecx
 2   testl %eax,%eax       9   addl $1,%ecx
 3   jne worker           10   movl %ecx,(%rsi)
 4   movl $1,%eax         11   movl $0,(%rdi)
 5   xchgl %eax,(%rdi)    12   jmp done
 6   testl %eax,%eax      13 done:
```
The end of the text is position 14.
-/
import Kraken.Promising.SLR.X64Trees
import Kraken.X64.Parser

namespace Kraken.Promising.SLR.X64SpinTrees

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.X64.Parser

/-- `worker` of `spinlock2.kl` (x64), lock at `(%rdi)`, counter at `(%rsi)`. -/
def spinWorker : Program := parse("
worker:
  movl (%rdi),%eax
  testl %eax,%eax
  jne worker
  movl $1,%eax
  xchgl %eax,(%rdi)
  testl %eax,%eax
  jne worker
  movl (%rsi),%ecx
  addl $1,%ecx
  movl %ecx,(%rsi)
  movl $0,(%rdi)
  jmp done
done:
")

/-- A 64-bit address is its own 64-bit truncation (`BitVec.toAddressSize` at
64-bit addressing). -/
@[simp] private theorem take_64 (l : BitVec 64) : l.take 64 = l := by
  simp [BitVec.take]

/-- A relative jump lands on its target. -/
@[simp] private theorem int64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

/-- After `testl %eax,%eax`, `ZF` says whether `%eax`'s low word is zero
(whatever the undefined `AF`): the condition of the following `jne`. -/
theorem zf_from_result {w : Nat} (v : BitVec w) (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).zf = (v == 0#w) := rfl

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- The context of a cell: the state runs the laid-out worker, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout spinWorker
  decls : st.decls = {}
  pc : st.st.2 = (layout spinWorker).addrOf i
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
theorem addrOf_step {i : Nat} (hi : i < spinWorker.length) :
    (layout spinWorker).addrOf (i + 1)
      = (layout spinWorker).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  X64Trees.addrOf_step hi

/-- A label position occupies no bytes: the next position has its address. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : spinWorker[i]? = some (Directive.label l)) :
    (layout spinWorker).addrOf (i + 1) = (layout spinWorker).addrOf i :=
  X64Trees.addrOf_label hp

/-- The address of the label `worker` (position 0) is that of the first `movl`
(position 1). -/
theorem label_worker :
    (_root_.Executable.labels (layout spinWorker)).label "worker" = (layout spinWorker).addrOf 1 := by
  rw [Program.label_addrOf_drop (i := 0) (by decide) (by decide) (by decide)]
  exact (addrOf_label (i := 0) (l := "worker") rfl).symm

/-- The address of the label `done` (position 13) is the end of the text
(position 14). -/
theorem label_done :
    (_root_.Executable.labels (layout spinWorker)).label "done" = (layout spinWorker).addrOf 14 := by
  rw [Program.label_addrOf_drop (i := 13) (by decide) (by decide) (by decide)]
  exact (addrOf_label (i := 13) (l := "done") rfl).symm

omit hv in
/-- The fall-through address of position `i`. -/
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < spinWorker.length) :
    (layout spinWorker).addrOf (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold its
interpretation. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := spinWorker) (i := $i)
    (d := spinWorker[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : spinWorker[$i] = d at hc
  simp only [spinWorker, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAt ($h).exe ($h).decls ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp, label_worker, label_done]
  simp [toEv, EvTree.map, EvTree.access_empty, Operand.interp, RegOrMem.interp, MachineData.set,
    MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw, AddrExpr.interp,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, label_worker,
    label_done, $ts,*]))

/-- `movl (%rdi),%eax` (position 1): a plain load of the lock into `%eax`
(zero-extended). -/
theorem exec_load_lock (st : State) (h : At st 1) {l : BitVec 64}
    (hx : st.st.1.regs.get64 .rdi = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.load .plain false ⟨l, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.set (.low .rax .W32) (BitVec.setWidth 32 v) }
        ((layout spinWorker).addrOf 2))) := by
  rw [next_pc h (by decide)]
  cell h 1 [hx, hdm]

/-- `testl %eax,%eax` (position 2): silent, sets the flags from `%eax`'s low
word; the undefined `AF` is a two-way choice. -/
theorem exec_test (st : State) (h : At st 2) :
    isa.exec st = some (.choose 2 fun i => .done (goto st
      (let f : StatusFlags := .from_result (st.st.1.regs.get (.low .rax .W32))
          { cf := false, af := i.val == 1, of := false }
       { st.st.1 with status := f })
      ((layout spinWorker).addrOf 3))) := by
  rw [next_pc h (by decide)]
  cell h 2 []

/-- `jne worker` (position 3): silent, back to `worker` unless `ZF`. -/
theorem exec_jne_spin (st : State) (h : At st 3) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.status.zf then (layout spinWorker).addrOf 4 else (layout spinWorker).addrOf 1))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cell h 3 [hz]

/-- `movl $1,%eax` (position 4): silent, `%eax := 1`. -/
theorem exec_mov_one (st : State) (h : At st 4) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.set (.low .rax .W32) 1#32 } ((layout spinWorker).addrOf 5))) := by
  rw [next_pc h (by decide)]
  cell h 4 []

/-- `xchgl %eax,(%rdi)` (position 5): a locked (`acqRel`) swap of `%eax`'s low
word into the lock, the old value into `%eax`. -/
theorem exec_xchg (st : State) (h : At st 5) {l : BitVec 64}
    (hx : st.st.1.regs.get64 .rdi = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.rmw .acqRel false ⟨l, 4⟩
      (fun _ => some (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32))))
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.set (.low .rax .W32) (BitVec.setWidth 32 v) }
        ((layout spinWorker).addrOf 6))) := by
  rw [next_pc h (by decide)]
  cell h 5 [hx, hdm]

/-- `testl %eax,%eax` (position 6), as at position 2. -/
theorem exec_test2 (st : State) (h : At st 6) :
    isa.exec st = some (.choose 2 fun i => .done (goto st
      (let f : StatusFlags := .from_result (st.st.1.regs.get (.low .rax .W32))
          { cf := false, af := i.val == 1, of := false }
       { st.st.1 with status := f })
      ((layout spinWorker).addrOf 7))) := by
  rw [next_pc h (by decide)]
  cell h 6 []

/-- `jne worker` (position 7): silent, back to `worker` unless `ZF`, else into
the critical section. -/
theorem exec_jne_retry (st : State) (h : At st 7) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.status.zf then (layout spinWorker).addrOf 8 else (layout spinWorker).addrOf 1))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cell h 7 [hz]

/-- `movl (%rsi),%ecx` (position 8): a plain load of the counter into `%ecx`. -/
theorem exec_load_counter (st : State) (h : At st 8) {c : BitVec 64}
    (hx : st.st.1.regs.get64 .rsi = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.load .plain false ⟨c, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.set (.low .rcx .W32) (BitVec.setWidth 32 v) }
        ((layout spinWorker).addrOf 9))) := by
  rw [next_pc h (by decide)]
  cell h 8 [hx, hdc]

/-- `addl $1,%ecx` (position 9): silent, increments `%ecx`'s low word and sets
the flags. -/
theorem exec_add (st : State) (h : At st 9) :
    isa.exec st = some (.done (goto st
      (let a := 1#32
       let b := st.st.1.regs.get (.low .rcx .W32)
       let v := a + b
       { st.st.1 with
         regs := st.st.1.regs.set (.low .rcx .W32) v
         status := StatusFlags.from_result v ({
           cf := v.unsigned != a.unsigned + b.unsigned
           af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
           of := v.signed != a.signed + b.signed }) })
      ((layout spinWorker).addrOf 10))) := by
  rw [next_pc h (by decide)]
  cell h 9 []

/-- `movl %ecx,(%rsi)` (position 10): a plain store of `%ecx`'s low word to the
counter. -/
theorem exec_store_counter (st : State) (h : At st 10) {c : BitVec 64}
    (hx : st.st.1.regs.get64 .rsi = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.store .plain false ⟨c, 4⟩
      (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32)))
      fun _ => .done (goto st st.st.1 ((layout spinWorker).addrOf 11))) := by
  rw [next_pc h (by decide)]
  cell h 10 [hx, hdc]

/-- `movl $0,(%rdi)` (position 11): the unlock, a plain store of zero to the
lock. -/
theorem exec_unlock (st : State) (h : At st 11) {l : BitVec 64}
    (hx : st.st.1.regs.get64 .rdi = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.store .plain false ⟨l, 4⟩ 0#128
      fun _ => .done (goto st st.st.1 ((layout spinWorker).addrOf 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 [hx, hdm]

/-- `jmp done` (position 12): silent, to the end of the text. -/
theorem exec_jmp_done (st : State) (h : At st 12) :
    isa.exec st = some (.done (goto st st.st.1 ((layout spinWorker).addrOf 14))) := by
  cell h 12 []

end Kraken.Promising.SLR.X64SpinTrees
