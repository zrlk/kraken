/-
**Stage 3: the event trees of the x64 ticket lock
worker, verbatim** (`ticketlock3.kl`'s code, `TicketX.tk3WorkerV`, absolute
operands `(next)`/`(owner)`/`(counter)`) in its image `tk3ImageV` (the code,
then the runner's data trailer) under the promising interpretation of x64, on
a valid layout of the image. The `LiveTicketTrees.lean` /
`LiveSpinX64CmpxTrees.lean` recipe: each theorem reads `isa.exec st` at the
address of one cell through `X64.exec_eq_of_codeAt` (hence `decls = {}`).

```
 0 worker:                       7   movl (counter),%edx
 1   movl $1,%eax                8   addl $1,%edx
 2   lock xaddl %eax,(next)      9   movl %edx,(counter)
 3 spin:                        10   addl $1,%ecx
 4   movl (owner),%ecx          11   movl %ecx,(owner)
 5   cmpl %eax,%ecx             12   jmp done
 6   jne spin                   13 done:
                                14.. the data trailer (`next`, `owner`, `counter`)
```

The three words are at `symTk "next"`, `symTk "owner"`, `symTk "counter"`,
outside the thread's private data memory. The ticket is `%eax`'s low word
(`eax`), the value read from `owner` `%ecx`'s (`ecx`). Each cell is stated up
to the register results the invariant does not read: what it keeps (`dmem`,
`eax`, `ecx`) and what it sets.
-/
import Kraken.Promising.SLR.EnvG.TicketXPublic
import Kraken.Promising.SLR.X64Trees

namespace Kraken.Promising.Live.TicketX64Trees

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV tk3WorkerV tk3DataV symTk tk3ImageV_wf)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk3ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk3ImageV).addrOf

/-- The context of a cell: the state runs the laid-out image, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout tk3ImageV
  decls : st.decls = {}
  pc : st.st.2 = pcA i
  ne : (st.st.2 == st.endPc) = false

/-- The state `st` moved to machine data `m` at address `pc`. -/
abbrev goto (st : State) (m : MachineData) (pc : Int64) : State :=
  { st with st := (m, pc) }

/-- `%eax`'s low word: the ticket. -/
abbrev eax (m : MachineData) : BitVec 32 := m.regs.get (.low .rax .W32)

/-- `%ecx`'s low word: the value read from `owner`. -/
abbrev ecx (m : MachineData) : BitVec 32 := m.regs.get (.low .rcx .W32)

omit hv in
private theorem layout_getElem (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

omit hv in
theorem addrOf_step {i : Nat} (hi : i < tk3ImageV.length) :
    pcA (i + 1) = pcA i + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.X64Trees.addrOf_step hi

/-- A label position occupies no bytes. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : tk3ImageV[i]? = some (Directive.label l)) :
    pcA (i + 1) = pcA i :=
  SLR.X64Trees.addrOf_label hp

theorem addrOf_0 : pcA 0 = pcA 1 := (addrOf_label (i := 0) (l := "worker") rfl).symm
theorem addrOf_3 : pcA 3 = pcA 4 := (addrOf_label (i := 3) (l := "spin") rfl).symm
theorem addrOf_13 : pcA 13 = pcA 14 := (addrOf_label (i := 13) (l := "done") rfl).symm

theorem label_worker : (_root_.Executable.labels (layout tk3ImageV)).label "worker" = pcA 1 := by
  rw [Program.label_addrOf_drop (i := 0) tk3ImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_0

theorem label_spin : (_root_.Executable.labels (layout tk3ImageV)).label "spin" = pcA 4 := by
  rw [Program.label_addrOf_drop (i := 3) tk3ImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_3

theorem label_done : (_root_.Executable.labels (layout tk3ImageV)).label "done" = pcA 14 := by
  rw [Program.label_addrOf_drop (i := 13) tk3ImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_13

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < tk3ImageV.length) :
    pcA (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  x64cell $h $i tk3ImageV [tk3ImageV, tk3WorkerV] [label_spin, label_done, $ts,*])

omit layout hv in
/-- A relative jump lands on its target. -/
private theorem int64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

/-- Register reads after the cells' writes. -/
local macro "regs" : tactic => `(tactic| simp [Reg64s.get_low32, BitVec.setWidth_setWidth_of_le])

/-- `movl $1,%eax` (position 1). -/
theorem exec_mov1 (st : State) (h : At st 1) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ eax md = 1#32 ∧
      isa.exec st = some (.done (goto st md (pcA 2))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, ?_, by cell h 1 []; rfl⟩
  · rfl
  · regs

/-- `lock xaddl %eax,(next)` (position 2): a locked (`acqRel`) RMW of `next`
that always writes the old low word plus `%eax`'s; `%eax` gets the old low
word, and the private memory is unchanged. -/
theorem exec_xadd (st : State) (h : At st 2) (hdm : Mem.loadInt st.st.1.dmem (symTk "next") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧ eax (g v) = BitVec.setWidth 32 v) ∧
      isa.exec st = some (.rmw .acqRel false ⟨symTk "next", 4⟩
        (fun old => some (BitVec.setWidth 128 (BitVec.setWidth 32 old + eax st.st.1)))
        fun v => .done (goto st (g v) (pcA 4))) := by
  rw [← addrOf_3, next_pc h (by decide)]
  refine ⟨_, fun v => ⟨?_, ?_⟩, by cell h 2 [hdm, symTk]; rfl⟩
  · rfl
  · regs

/-- `movl (owner),%ecx` (position 4): a plain load of `owner` into `%ecx`. -/
theorem exec_ldo (st : State) (h : At st 4) (hdm : Mem.loadInt st.st.1.dmem (symTk "owner") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧ eax (g v) = eax st.st.1 ∧
        ecx (g v) = BitVec.setWidth 32 v) ∧
      isa.exec st = some (.load .plain false ⟨symTk "owner", 4⟩ fun v => .done (goto st (g v) (pcA 5))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, fun v => ⟨?_, ?_, ?_⟩, by cell h 4 [hdm, symTk]; rfl⟩
  · rfl
  · regs
  · regs

/-- `cmpl %eax,%ecx` (position 5): the flags of `%ecx - %eax`; `ZF` iff the
low words agree. -/
theorem exec_cmp (st : State) (h : At st 5) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ eax md = eax st.st.1 ∧ ecx md = ecx st.st.1 ∧
      (md.status.zf = true ↔ ecx st.st.1 = eax st.st.1) ∧
      isa.exec st = some (.done (goto st md (pcA 6))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, ?_, ?_, ?_, by cell h 5 []; rfl⟩
  · rfl
  · rfl
  · rfl
  · change (ecx st.st.1 - eax st.st.1 == 0#32) = true ↔ _
    simp only [beq_iff_eq]
    constructor <;> intro e <;> bv_omega

/-- `jne spin` (position 6): back to `spin` unless `ZF`. -/
theorem exec_jne (st : State) (h : At st 6) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcA 7 else pcA 4))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cell h 6 [hz]

/-- `movl (counter),%edx` (position 7): a plain load of the counter. -/
theorem exec_ldc (st : State) (h : At st 7) (hdc : Mem.loadInt st.st.1.dmem (symTk "counter") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧ eax (g v) = eax st.st.1 ∧
        ecx (g v) = ecx st.st.1) ∧
      isa.exec st = some (.load .plain false ⟨symTk "counter", 4⟩ fun v => .done (goto st (g v) (pcA 8))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, fun v => ⟨?_, ?_, ?_⟩, by cell h 7 [hdc, symTk]; rfl⟩
  · rfl
  · regs
  · regs

/-- `addl $1,%edx` (position 8). -/
theorem exec_addd (st : State) (h : At st 8) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ eax md = eax st.st.1 ∧ ecx md = ecx st.st.1 ∧
      isa.exec st = some (.done (goto st md (pcA 9))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, ?_, ?_, by cell h 8 []; rfl⟩
  · rfl
  · regs
  · regs

/-- `movl %edx,(counter)` (position 9): a plain store to the counter. -/
theorem exec_stc (st : State) (h : At st 9) (hdc : Mem.loadInt st.st.1.dmem (symTk "counter") 4 = none) :
    ∃ (v : Val) (md : MachineData), md.dmem = st.st.1.dmem ∧ eax md = eax st.st.1 ∧ ecx md = ecx st.st.1 ∧
      isa.exec st = some (.store .plain false ⟨symTk "counter", 4⟩ v fun _ => .done (goto st md (pcA 10))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, _, ?_, ?_, ?_, by cell h 9 [hdc, symTk]; exact ⟨rfl, rfl⟩⟩
  · rfl
  · rfl
  · rfl

/-- `addl $1,%ecx` (position 10): `%ecx` gets its low word plus one. -/
theorem exec_addc (st : State) (h : At st 10) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ eax md = eax st.st.1 ∧ ecx md = ecx st.st.1 + 1#32 ∧
      isa.exec st = some (.done (goto st md (pcA 11))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, ?_, ?_, by cell h 10 []; rfl⟩
  · rfl
  · regs
  · regs; exact BitVec.add_comm _ _

/-- `movl %ecx,(owner)` (position 11): the release, a plain store of `%ecx`'s
low word to `owner`. -/
theorem exec_rel (st : State) (h : At st 11) (hdm : Mem.loadInt st.st.1.dmem (symTk "owner") 4 = none) :
    isa.exec st = some (.store .plain false ⟨symTk "owner", 4⟩ (BitVec.setWidth 128 (ecx st.st.1))
      fun _ => .done (goto st st.st.1 (pcA 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 [hdm, symTk]

/-- `jmp done` (position 12): to the exit label. -/
theorem exec_jmp (st : State) (h : At st 12) :
    isa.exec st = some (.done (goto st st.st.1 (pcA 14))) := by
  cell h 12 [int64_add_sub]

/-! ## Distinct addresses -/

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

/-- The address past an instruction differs from every address at or before it. -/
theorem addrOf_ne_succ {k n : Nat} (hk : k ≤ n) (h : tk3ImageV[n]?.map isInstr = some true) :
    pcA k ≠ pcA (n + 1) :=
  SLR.X64Trees.addrOf_ne_succ _ isInstr (fun _ => rfl) hk h

/-- The positions a worker's pc takes (`0` is at the address of `1`, `3` at
that of `4`, `13` at that of `14`). -/
def tkPcs : List Nat := [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14]

/-- The address-distinct representative of a position. -/
def canon (i : Nat) : Nat := if i = 4 then 3 else if i = 14 then 13 else i

theorem addrOf_canon (i : Nat) : pcA (canon i) = pcA i := by
  unfold canon
  split
  · subst_vars; exact addrOf_3
  · split
    · subst_vars; exact addrOf_13
    · rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ tkPcs) (hj : j ∈ tkPcs) (h : pcA i = pcA j) : i = j :=
  SLR.X64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) tkPcs canon (fun i _ => addrOf_canon i) (by decide) hi hj h

end Kraken.Promising.Live.TicketX64Trees
