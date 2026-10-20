/-
**Stage 3: the event trees of the x64 `xchg`
spinlock worker, verbatim** (`spinlock2.kl`'s code, `SpinAbs.spinWorkerV`,
absolute operands `(lock)`/`(counter)`) in its image `spinImageV` (the code,
then the runner's data trailer) under the promising interpretation of x64, on
a valid layout of the image. The `LiveSpinX64CmpxTrees.lean` recipe: each
theorem reads `isa.exec st` at the address of one cell through
`X64.exec_eq_of_codeAt` (hence `decls = {}`).

```
 0 worker:                     7   jne worker
 1   movl (lock),%eax          8   movl (counter),%ecx
 2   testl %eax,%eax           9   addl $1,%ecx
 3   jne worker               10   movl %ecx,(counter)
 4   movl $1,%eax             11   movl $0,(lock)
 5   xchgl %eax,(lock)        12   jmp done
 6   testl %eax,%eax          13 done:
                              14.. the data trailer (`lock`, `counter`)
```

The lock is the word at `symV "lock"`, the counter the word at
`symV "counter"`, both outside the thread's private data memory. `testl`
leaves `AF` undefined (a `.choose 2`); its cell gives `ZF` exactly: set iff
`%eax`'s low word is `0`. The `xchgl` cell is a locked RMW that always
writes (`%eax`'s low word) and loads the old low word into `%eax`.
-/
import Kraken.Promising.SLR.EnvG.X64SpinAbsPublic
import Kraken.Promising.SLR.X64Trees

namespace Kraken.Promising.Live.SpinX64XchgTrees

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV spinWorkerV spinDataV symV labV spinImageV_wf)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

set_option hygiene false in
local notation "pcA" => (layout spinImageV).addrOf

/-- The context of a cell: the state runs the laid-out image, without
declarations, at the address of position `i`, which is not the end address. -/
structure At (st : State) (i : Nat) : Prop where
  exe : st.exe = layout spinImageV
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
theorem addrOf_step {i : Nat} (hi : i < spinImageV.length) :
    pcA (i + 1) = pcA i + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.X64Trees.addrOf_step hi

/-- A label position occupies no bytes. -/
theorem addrOf_label {i : Nat} {l : Label} (hp : spinImageV[i]? = some (Directive.label l)) :
    pcA (i + 1) = pcA i :=
  SLR.X64Trees.addrOf_label hp

theorem addrOf_0 : pcA 0 = pcA 1 := (addrOf_label (i := 0) (l := "worker") rfl).symm

theorem label_worker : (_root_.Executable.labels (layout spinImageV)).label "worker" = pcA 1 := by
  rw [Program.label_addrOf_drop (i := 0) spinImageV_wf.nodup (by decide) (by decide)]
  exact addrOf_0

theorem label_done : (_root_.Executable.labels (layout spinImageV)).label "done" = pcA 13 :=
  Program.label_addrOf_drop (i := 13) spinImageV_wf.nodup (by decide) (by decide)

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : At st i) (hi : i < spinImageV.length) :
    pcA (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  x64cell $h $i spinImageV [spinImageV, spinWorkerV] [label_worker, label_done, $ts,*])

omit layout hv in
/-- A relative jump lands on its target. -/
private theorem int64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

/-- `%eax`'s low word. -/
abbrev eax (m : MachineData) : BitVec 32 := m.regs.get (.low .rax .W32)

omit layout hv in
/-- Writing a 32-bit value zero-extended into `%rax` sets `%eax`'s low word. -/
theorem eax_set64 (r : Reg64s) (x : BitVec 32) : (r.set64 .rax (BitVec.setWidth 64 x)).get (.low .rax .W32) = x := by
  simp only [Reg64s.get, Reg64s.get64_set64]
  simp only [Reg.base, Reg.offset, Width.bits, BitVec.take, BitVec.drop]
  ext i hi
  simp [hi]
  omega

/-- `movl (lock),%eax` (position 1): a plain load of the lock into `%eax`. -/
theorem exec_ldl (st : State) (h : At st 1) (hdm : Mem.loadInt st.st.1.dmem (symV "lock") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem ∧ eax (g v) = BitVec.setWidth 32 v) ∧
      isa.exec st = some (.load .plain false ⟨symV "lock", 4⟩ fun v => .done (goto st (g v) (pcA 2))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 1 [hdm, symV]; rfl⟩
  intro v
  exact ⟨rfl, eax_set64 _ _⟩

/-- `testl %eax,%eax` (positions 2 and 6): `ZF` set iff `%eax`'s low word is
`0`; the undefined `AF` is a two-way choice. -/
theorem exec_test (st : State) {i : Nat} (hi : i = 2 ∨ i = 6) (h : At st i) :
    ∃ g : Fin 2 → MachineData, (∀ j, (g j).dmem = st.st.1.dmem ∧
        ((g j).status.zf = true ↔ eax st.st.1 = 0#32)) ∧
      isa.exec st = some (.choose 2 fun j => .done (goto st (g j) (pcA (i + 1)))) := by
  rcases hi with rfl | rfl
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cell h 2 []; rfl⟩
    intro j
    refine ⟨rfl, ?_⟩
    simp
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cell h 6 []; rfl⟩
    intro j
    refine ⟨rfl, ?_⟩
    simp

/-- `jne worker` (positions 3 and 7): back to `worker` unless `ZF`. -/
theorem exec_jne (st : State) {i : Nat} (hi : i = 3 ∨ i = 7) (h : At st i) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcA (i + 1) else pcA 1))) := by
  rcases hi with rfl | rfl
  · rw [next_pc h (by decide)]
    by_cases hz : st.st.1.status.zf <;> cell h 3 [hz]
  · rw [next_pc h (by decide)]
    by_cases hz : st.st.1.status.zf <;> cell h 7 [hz]

/-- `movl $1,%eax` (position 4). -/
theorem exec_mov1 (st : State) (h : At st 4) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ isa.exec st = some (.done (goto st md (pcA 5))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 4 []; rfl⟩
  rfl

/-- `xchgl %eax,(lock)` (position 5): a locked RMW of the lock that always
writes (`%eax`'s low word) and loads the old low word into `%eax`. -/
theorem exec_xchg (st : State) (h : At st 5) (hdm : Mem.loadInt st.st.1.dmem (symV "lock") 4 = none) :
    ∃ g : Val → MachineData,
      (∀ v, (g v).dmem = st.st.1.dmem ∧ eax (g v) = BitVec.setWidth 32 v) ∧
      isa.exec st = some (.rmw .acqRel false ⟨symV "lock", 4⟩ (fun _ => some (BitVec.setWidth 128 (eax st.st.1)))
        fun v => .done (goto st (g v) (pcA 6))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 5 [hdm, symV]; rfl⟩
  intro v
  exact ⟨rfl, eax_set64 _ _⟩

/-- `movl (counter),%ecx` (position 8): a plain load of the counter. -/
theorem exec_ldc (st : State) (h : At st 8) (hdc : Mem.loadInt st.st.1.dmem (symV "counter") 4 = none) :
    ∃ g : Val → MachineData, (∀ v, (g v).dmem = st.st.1.dmem) ∧
      isa.exec st = some (.load .plain false ⟨symV "counter", 4⟩ fun v => .done (goto st (g v) (pcA 9))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 8 [hdc, symV]; rfl⟩
  intro _; rfl

/-- `addl $1,%ecx` (position 9). -/
theorem exec_add (st : State) (h : At st 9) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ isa.exec st = some (.done (goto st md (pcA 10))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, ?_, by cell h 9 []; rfl⟩
  rfl

/-- `movl %ecx,(counter)` (position 10): a plain store to the counter. -/
theorem exec_stc (st : State) (h : At st 10) (hdc : Mem.loadInt st.st.1.dmem (symV "counter") 4 = none) :
    ∃ (v : Val) (md : MachineData), md.dmem = st.st.1.dmem ∧
      isa.exec st = some (.store .plain false ⟨symV "counter", 4⟩ v fun _ => .done (goto st md (pcA 11))) := by
  rw [next_pc h (by decide)]
  refine ⟨_, _, ?_, by cell h 10 [hdc, symV]; exact ⟨rfl, rfl⟩⟩
  rfl

/-- `movl $0,(lock)` (position 11): the unlock, a plain store of `0`. -/
theorem exec_unlock (st : State) (h : At st 11) (hdm : Mem.loadInt st.st.1.dmem (symV "lock") 4 = none) :
    isa.exec st = some (.store .plain false ⟨symV "lock", 4⟩ 0#128 fun _ => .done (goto st st.st.1 (pcA 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 [hdm, symV]

/-- `jmp done` (position 12): to the exit label. -/
theorem exec_jmp (st : State) (h : At st 12) :
    isa.exec st = some (.done (goto st st.st.1 (pcA 13))) := by
  cell h 12 [int64_add_sub]

/-! ## Distinct addresses -/

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

theorem addrOf_ne_succ {k n : Nat} (hk : k ≤ n) (h : spinImageV[n]?.map isInstr = some true) :
    pcA k ≠ pcA (n + 1) :=
  SLR.X64Trees.addrOf_ne_succ _ isInstr (fun _ => rfl) hk h

/-- The positions a worker's pc takes. -/
def spPcs : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ spPcs) (hj : j ∈ spPcs) (h : pcA i = pcA j) : i = j :=
  SLR.X64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) spPcs id (fun _ _ => rfl) (by decide) hi hj h

end Kraken.Promising.Live.SpinX64XchgTrees
