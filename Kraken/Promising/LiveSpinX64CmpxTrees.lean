/-
**Stage 3: the event trees of the x64 `lock
cmpxchg` spinlock worker, verbatim** (`spinlock_cmpxchg2.kl`'s code,
`CmpxAbs.cmpxWorkerV`, absolute operands `(lock)`/`(counter)`) in its image
`cmpxImageV` (the code, then the runner's data trailer) under the promising
interpretation of x64, on a valid layout of the image. The
`LiveSpinCasTrees.lean` recipe: each theorem reads `isa.exec st` at the
address of one cell through `X64.exec_eq_of_codeAt` (hence `decls = {}`).

```
 0 worker:                     6   addl $1,%edx
 1   xorl %eax,%eax            7   movl %edx,(counter)
 2   movl $1,%ecx              8   movl $0,(lock)
 3   lock cmpxchgl %ecx,(lock) 9   jmp done
 4   jne worker               10 done:
 5   movl (counter),%edx      11.. the data trailer (`lock`, `counter`)
```

The lock is the word at `symC "lock"`, the counter the word at
`symC "counter"`, both outside the thread's private data memory. `xorl`
leaves `AF` undefined (a `.choose 2`); the critical-section cells are stated
up to their (irrelevant) register results; the `cmpxchg` cell gives `ZF`
exactly: set iff the old low word equals `%eax`'s.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxAbsPublic
import Kraken.Promising.SLR.X64Trees

namespace Kraken.Promising.Live.SpinX64CmpxTrees

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV cmpxWorkerV symC labC cmpxImageV_wf)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

/-- The context of a cell: the state runs the laid-out image, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout cmpxImageV
  decls : st.decls = {}
  pc : st.st.2 = pcA i
  ne : (st.st.2 == st.endPc) = false

/-- The state `st` moved to machine data `m` at address `pc`. -/
abbrev goto (st : State) (m : MachineData) (pc : Int64) : State :=
  { st with st := (m, pc) }

omit hv in
private theorem layout_getElem (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

omit hv in
theorem addrOf_step {i : Nat} (hi : i < cmpxImageV.length) :
    pcA (i + 1) = pcA i + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.X64Trees.addrOf_step hi

/-- A label position occupies no bytes. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : cmpxImageV[i]? = some (Directive.label l)) :
    pcA (i + 1) = pcA i :=
  SLR.X64Trees.addrOf_label hp

theorem addrOf_0 : pcA 0 = pcA 1 := (addrOf_label (i := 0) (l := "worker") rfl).symm

theorem label_worker : (_root_.Executable.labels (layout cmpxImageV)).label "worker" = pcA 1 := by
  rw [Program.label_addrOf_drop (i := 0) cmpxImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_0

theorem label_done : (_root_.Executable.labels (layout cmpxImageV)).label "done" = pcA 10 :=
  Program.label_addrOf_drop (i := 10) cmpxImageV_wf.nodup (by decide) (by decide)

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < cmpxImageV.length) :
    pcA (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  x64cell $h $i cmpxImageV [cmpxImageV, cmpxWorkerV] [label_worker, label_done, $ts,*])

omit layout hv in
/-- A relative jump lands on its target. -/
private theorem int64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

/-- `%eax`'s low word. -/
abbrev eax (m : MachineData) : BitVec 32 := m.regs.get (.low .rax .W32)

/-- `xorl %eax,%eax` (position 1): `%rax := 0`; the undefined `AF` is a
two-way choice. -/
theorem exec_xor (st : State) (h : At st 1) :
    isa.exec st = some (.choose 2 fun i => .done (goto st
      { st.st.1 with regs := st.st.1.regs.set64 .rax 0#64,
                     status := StatusFlags.from_result 0#32 { cf := false, af := i.val == 1, of := false } }
      (pcA 2))) := by
  rw [next_pc h (by decide)]
  cell h 1 []

/-- `movl $1,%ecx` (position 2). -/
theorem exec_movc (st : State) (h : At st 2) :
    isa.exec st = some (.done (goto st { st.st.1 with regs := st.st.1.regs.set64 .rcx 1#64 } (pcA 3))) := by
  rw [next_pc h (by decide)]
  cell h 2 []

/-- `lock cmpxchgl %ecx,(lock)` (position 3): a locked (`acqRel`) RMW of the
lock that writes `%ecx`'s low word iff the old low word is `%eax`'s; after
it, `ZF` is set iff it was, and the private memory is unchanged. -/
theorem exec_cmpxchg (st : State) (h : At st 3) (hdm : Mem.loadInt st.st.1.dmem (symC "lock") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧
        ((g v).status.zf = true ↔ BitVec.setWidth 32 v = eax st.st.1)) ∧
      isa.exec st = some (.rmw .acqRel false ⟨symC "lock", 4⟩
        (fun old => if BitVec.setWidth 32 old = eax st.st.1 then
          some (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32))) else none)
        fun v => .done (goto st (g v) (pcA 4))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 3 [hdm, symC]; rfl⟩
  intro v
  refine ⟨by split <;> rfl, ?_⟩
  change (eax st.st.1 - BitVec.setWidth 32 v == 0#32) = true ↔ _
  simp only [beq_iff_eq]
  constructor <;> intro e <;> bv_omega

/-- `jne worker` (position 4): back to `worker` unless `ZF`. -/
theorem exec_jne (st : State) (h : At st 4) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcA 5 else pcA 1))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cell h 4 [hz]

/-- `movl (counter),%edx` (position 5): a plain load of the counter. -/
theorem exec_ldc (st : State) (h : At st 5) (hdc : Mem.loadInt st.st.1.dmem (symC "counter") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem) ∧
      isa.exec st = some (.load .plain false ⟨symC "counter", 4⟩ fun v => .done (goto st (g v) (pcA 6))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 5 [hdc, symC]; rfl⟩
  intro _; rfl

/-- `addl $1,%edx` (position 6). -/
theorem exec_add (st : State) (h : At st 6) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ isa.exec st = some (.done (goto st md (pcA 7))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 6 []; rfl⟩
  rfl

/-- `movl %edx,(counter)` (position 7): a plain store to the counter. -/
theorem exec_stc (st : State) (h : At st 7) (hdc : Mem.loadInt st.st.1.dmem (symC "counter") 4 = none) :
    ∃ (v : Val) (md : MachineData), md.dmem = st.st.1.dmem ∧
      isa.exec st = some (.store .plain false ⟨symC "counter", 4⟩ v fun _ => .done (goto st md (pcA 8))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, _, ?_, by cell h 7 [hdc, symC]; exact ⟨rfl, rfl⟩⟩
  rfl

/-- `movl $0,(lock)` (position 8): the unlock, a plain store of `0`. -/
theorem exec_unlock (st : State) (h : At st 8) (hdm : Mem.loadInt st.st.1.dmem (symC "lock") 4 = none) :
    isa.exec st = some (.store .plain false ⟨symC "lock", 4⟩ 0#128 fun _ => .done (goto st st.st.1 (pcA 9))) := by
  rw [next_pc h (by decide)]
  cell h 8 [hdm, symC]

/-- `jmp done` (position 9): to the exit label. -/
theorem exec_jmp (st : State) (h : At st 9) :
    isa.exec st = some (.done (goto st st.st.1 (pcA 10))) := by
  cell h 9 [int64_add_sub]

/-! ## Distinct addresses -/

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

theorem addrOf_ne_succ {k n : Nat} (hk : k ≤ n) (h : cmpxImageV[n]?.map isInstr = some true) :
    pcA k ≠ pcA (n + 1) :=
  SLR.X64Trees.addrOf_ne_succ _ isInstr (fun _ => rfl) hk h

/-- The positions a worker's pc takes. -/
def spPcs : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ spPcs) (hj : j ∈ spPcs) (h : pcA i = pcA j) : i = j :=
  SLR.X64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) spPcs id (fun _ _ => rfl) (by decide) hi hj h

end Kraken.Promising.Live.SpinX64CmpxTrees
