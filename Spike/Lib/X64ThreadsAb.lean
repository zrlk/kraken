/-
**The threads abort phase on x86-64** (`Ac` of `Wf`'s `AcSt`): the thread
states from `wc_main`'s refused `clone` to `scc_rt_abort_threads`'s
`exit_group`, by pc and, where the code still tests it, by the data that
makes the path the refusal's (the x86-64 twin of
`Spike/Lib/A64ThreadsAb.lean`).

- `CloneRef r`: `r` is a refusal of `clone`, `-EAGAIN` or `-ENOMEM`
  (`Scc.Sem.Kernel`, the results of `CloneOne.clone_step_nodormant`).
- `raT lab pfx`: the return address of `.spawnfail5`'s `call` (its pc + 12,
  `.x23`).
- `RaW lab s ra`: the word the `call` pushed is `ra`, read where it lies at
  `s`'s pc (`raSPcs`: at `(%rsp)`, the dispatcher's and the stub's first
  instruction and `g5`'s `jmp`; `raPPcs`: at `8(%rsp)`, after the
  prologues' `pushq %rbp`; `raBPcs`: at `8(%rbp)`, every other pc of the
  dispatcher and the stub).
- `Ac lab pfx s`: one of
  - `.ret`: the `testq` after the call (`pcRet`) and the `je` after it
    (`pcJe`), `%rax` a refusal;
  - `.st`: `.x22`'s store of the result, `%rax` a refusal;
  - `.tail`: `.x22`'s tests of the stored result up to its `jl`
    (`tailPcs`), the stored result `-56(%rbp)` a refusal;
  - `.fail`: a pc of `.spawnfail5` (`failPcs`);
  - `.dispE`: a pc of the dispatcher's prologue (`WriteAb.dispEPcs`) with
    `%rdi = 5`;
  - `.dispT`: a pc of the first five tests (`dispTPcs`: the tests against
    1, 2, 3, 4 and their jumps to the next, the test against 5) with
    `-8(%rbp) = 5`;
  - `.g5`: a pc of the jump to the threads stub (`g5Pcs`);
  - `.stub`: a pc of `scc_rt_abort_threads` up to its exit call (`stubPcs`);

  the last four with `RaW lab s (raT lab pfx)`. Nothing on the path from
  the `call` to the exit call writes the pushed word (`Abort.Disp.DN.nd5 …
  ra`, `Abort.NT … ra`: `slot 8 = ra`); it tells this site from the other
  `scc_rt_abort(5)` calls (`scc_rt_alloc_tcb`'s `.full`,
  `scc_rt_thread_reserve`'s `.full`), whose `call`s are at other pcs.
- `acPcs`: every pc above; `pc_of_ac`, `not_ac_of_pc`: a state in `Ac` is
  at one of them, so a state at no such pc is not in `Ac`.
- `ac_ret`, `ac_je`, `ac_fail`, `ac_g5`, `ac_stub`: introduction at the call's return
  and at the classes with no data condition but the return address.
- `ac_x30`: a state in `Ac` past the spawn's own pcs has
  `RaW lab s (raT lab pfx)`.

**Deviation from the A64 file.** x86-64 has no link register: the return
address is the word `call` pushed, so the A64 `x30 = raT` becomes `RaW`, the
pushed word at the pc's offset from `%rsp` or `%rbp` (the twin of the
abstract `slot 8 = ra` of `Spike/Lib/X64AbortThreadsW.lean`); `ac_x30`
keeps its A64 name and concludes `RaW`. `pfx` is `.Lwc_main` (x86-64 labels
carry no numeric prefix); the spawn's pcs are offsets from `.x21`/`.x22`
(`.sp6`/`.clone9` on A64), the call's return the `testq` (A64 `cbz`); the
`je` after it (`pcJe`, `ac_je`) has no A64 counterpart (A64's `cbz` tests
and branches at once) and shares the first class's data condition.

`lab` is the executable's label map (`(_root_.Executable.labels exe).label`
at the nodes' fragments).
-/
import Spike.Lib.X64WriteAb
import Scc.Sem.Kernel

namespace Spike.Lib.X64.ThreadsAb

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (privLoad)
open Spike.Lib.X64.WriteAb (bpLoad dispEPcs)

/-- **A refused `clone`'s result**: `-EAGAIN` or `-ENOMEM`. -/
def CloneRef (r : BitVec 64) : Prop :=
  r = Scc.Sem.Kernel.neg Scc.Sem.Kernel.eagain ∨ r = Scc.Sem.Kernel.neg Scc.Sem.Kernel.enomem

/-- A refusal is negative as a signed word. -/
theorem CloneRef.slt {r : BitVec 64} (h : CloneRef r) : r.slt 0#64 = true := by
  rcases h with rfl | rfl <;> decide

/-- A refusal is not `0`. -/
theorem CloneRef.ne_zero {r : BitVec 64} (h : CloneRef r) : r ≠ 0#64 := by
  rcases h with rfl | rfl <;> decide

/-- The 8-byte word at `%rsp + o` of a state's private memory. -/
abbrev spLoad (s : State) (o : BitVec 64) : Option (BitVec 64) := privLoad s (s.st.1.regs.rsp.toBitVec + o)

variable (lab : Label → Int64) (pfx : String)

/-- The spawn's `clone` call: the `syscall` of `pfx.x21`. -/
abbrev cloneAt : Int64 := lab (pfx ++ ".x3") + 46

/-- The pc after the call: `testq %rax, %rax`. -/
abbrev pcRet : Int64 := cloneAt lab pfx + 2

/-- The `je` after the test (`.x21 + 51`; no A64 counterpart: A64's `cbz`
tests and branches in one instruction). -/
abbrev pcJe : Int64 := cloneAt lab pfx + 5

/-- `.x22`'s store of the result. -/
abbrev pcSt : Int64 := lab (pfx ++ ".x4")

/-- `.x22`'s tests of the stored result up to its `jl`. -/
def tailPcs : List Int64 :=
  [lab (pfx ++ ".x4") + 4, lab (pfx ++ ".x4") + 8, lab (pfx ++ ".x4") + 15, lab (pfx ++ ".x4") + 18]

/-- `.spawnfail5`: `movq $5, %rdi; call scc_rt_abort`. -/
def failPcs : List Int64 := [lab (pfx ++ ".spawnfail5"), lab (pfx ++ ".spawnfail5") + 7]

/-- The dispatcher's tests against 1, 2, 3, 4 and their jumps to the next,
and the test against 5 (`Disp.DN.nd5`'s `.t1` … `.t5`). -/
def dispTPcs : List Int64 :=
  [lab ".Lscc_rt_abort.entry", lab ".Lscc_rt_abort.entry" + 4, lab ".Lscc_rt_abort.entry" + 11,
   lab ".Lscc_rt_abort.entry" + 14, lab ".Lscc_rt_abort.entry" + 16,
   lab ".Lscc_rt_abort.next1", lab ".Lscc_rt_abort.next1" + 4, lab ".Lscc_rt_abort.next1" + 11,
   lab ".Lscc_rt_abort.next1" + 14, lab ".Lscc_rt_abort.next1" + 16,
   lab ".Lscc_rt_abort.next3", lab ".Lscc_rt_abort.next3" + 4, lab ".Lscc_rt_abort.next3" + 11,
   lab ".Lscc_rt_abort.next3" + 14, lab ".Lscc_rt_abort.next3" + 16,
   lab ".Lscc_rt_abort.next5", lab ".Lscc_rt_abort.next5" + 4, lab ".Lscc_rt_abort.next5" + 11,
   lab ".Lscc_rt_abort.next5" + 14, lab ".Lscc_rt_abort.next5" + 16,
   lab ".Lscc_rt_abort.next7", lab ".Lscc_rt_abort.next7" + 4, lab ".Lscc_rt_abort.next7" + 11,
   lab ".Lscc_rt_abort.next7" + 14]

/-- The dispatcher's jump to the threads stub (`Disp.g5`). -/
def g5Pcs : List Int64 :=
  [lab ".Lscc_rt_abort.is8", lab ".Lscc_rt_abort.is8" + 3, lab ".Lscc_rt_abort.is8" + 4]

/-- `scc_rt_abort_threads` (`Abort.threads`) up to its exit call: the
prologue, the message's address, the argument block `x1Threads`, the system
call, the block `x2` and the exit call. -/
def stubPcs : List Int64 :=
  [lab Abort.threads.fn, lab Abort.threads.fn + 1, lab Abort.threads.fn + 4,
   lab Abort.threads.entry, lab Abort.threads.entry + 7, lab Abort.threads.entry + 11,
   lab Abort.threads.entry + 18, lab Abort.threads.entry + 22, lab Abort.threads.entry + 29,
   lab Abort.threads.entry + 34, lab Abort.threads.entry + 36, lab Abort.threads.entry + 40,
   lab Abort.threads.entry + 47, lab Abort.threads.exit]

/-- The pcs with the return address at `(%rsp)`: the dispatcher's and the
stub's entries and `g5`'s `jmp` (after its `popq %rbp`). -/
def raSPcs : List Int64 := [lab "scc_rt_abort", lab ".Lscc_rt_abort.is8" + 4, lab Abort.threads.fn]

/-- The pcs with the return address at `8(%rsp)`: after the prologues'
`pushq %rbp`. -/
def raPPcs : List Int64 := [lab "scc_rt_abort" + 1, lab Abort.threads.fn + 1]

/-- The pcs with the return address at `8(%rbp)`: the dispatcher's and the
stub's other pcs. -/
def raBPcs : List Int64 :=
  (lab "scc_rt_abort" + 4) :: (lab "scc_rt_abort" + 8) :: dispTPcs lab ++
    [lab ".Lscc_rt_abort.is8", lab ".Lscc_rt_abort.is8" + 3] ++ (stubPcs lab).drop 2

/-- **The pushed return address is `ra`**, read where it lies at the
state's pc. -/
def RaW (s : State) (ra : BitVec 64) : Prop :=
  (s.st.2 ∈ raSPcs lab ∧ spLoad s 0 = some ra) ∨ (s.st.2 ∈ raPPcs lab ∧ spLoad s 8 = some ra) ∨
    (s.st.2 ∈ raBPcs lab ∧ bpLoad s 8 = some ra)

/-- The return address of `.spawnfail5`'s `call scc_rt_abort`. -/
abbrev raT : BitVec 64 := (lab (pfx ++ ".spawnfail5") + 12).toBitVec

/-- **The threads abort phase.** -/
def Ac (s : State) : Prop :=
  ((s.st.2 = pcRet lab pfx ∨ s.st.2 = pcJe lab pfx) ∧ CloneRef (s.st.1.regs.get64 .rax)) ∨
  (s.st.2 = pcSt lab pfx ∧ CloneRef (s.st.1.regs.get64 .rax)) ∨
  (s.st.2 ∈ tailPcs lab pfx ∧ ∃ r, bpLoad s (-56) = some r ∧ CloneRef r) ∨
  s.st.2 ∈ failPcs lab pfx ∨
  (s.st.2 ∈ dispEPcs lab ∧ s.st.1.regs.get64 .rdi = 5#64 ∧ RaW lab s (raT lab pfx)) ∨
  (s.st.2 ∈ dispTPcs lab ∧ bpLoad s (-8) = some 5#64 ∧ RaW lab s (raT lab pfx)) ∨
  (s.st.2 ∈ g5Pcs lab ∧ RaW lab s (raT lab pfx)) ∨
  (s.st.2 ∈ stubPcs lab ∧ RaW lab s (raT lab pfx))

/-- Every pc of `Ac`. -/
def acPcs : List Int64 :=
  pcRet lab pfx :: pcJe lab pfx :: pcSt lab pfx :: tailPcs lab pfx ++ failPcs lab pfx ++ dispEPcs lab ++
    dispTPcs lab ++ g5Pcs lab ++ stubPcs lab

variable {lab pfx}

/-- **A state in `Ac` is at one of its pcs.** -/
theorem pc_of_ac {s : State} (h : Ac lab pfx s) : s.st.2 ∈ acPcs lab pfx := by
  unfold acPcs
  rcases h with ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all

/-- **A state at none of `Ac`'s pcs is not in it.** -/
theorem not_ac_of_pc {s : State} (h : s.st.2 ∉ acPcs lab pfx) : ¬ Ac lab pfx s :=
  fun h' => h (pc_of_ac h')

/-- The return of a refused `clone` is in `Ac`. -/
theorem ac_ret {s : State} (hp : s.st.2 = pcRet lab pfx) (hr : CloneRef (s.st.1.regs.get64 .rax)) :
    Ac lab pfx s := .inl ⟨.inl hp, hr⟩

/-- The `je` after the test of a refused `clone`'s result is in `Ac`. -/
theorem ac_je {s : State} (hp : s.st.2 = pcJe lab pfx) (hr : CloneRef (s.st.1.regs.get64 .rax)) :
    Ac lab pfx s := .inl ⟨.inr hp, hr⟩

/-- `.spawnfail5` is in `Ac`. -/
theorem ac_fail {s : State} (h : s.st.2 ∈ failPcs lab pfx) : Ac lab pfx s := .inr (.inr (.inr (.inl h)))

/-- The jump to the threads stub is in `Ac`. -/
theorem ac_g5 {s : State} (h : s.st.2 ∈ g5Pcs lab) (hr : RaW lab s (raT lab pfx)) : Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, hr⟩))))))

/-- `scc_rt_abort_threads` is in `Ac`. -/
theorem ac_stub {s : State} (h : s.st.2 ∈ stubPcs lab) (hr : RaW lab s (raT lab pfx)) : Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨h, hr⟩))))))

/-- **A state in `Ac` at none of the spawn's own pcs** (so at the
dispatcher's or the threads stub's) has the return address `raT lab pfx`:
another `scc_rt_abort(5)` caller, whose return address differs, is not in
`Ac` there. -/
theorem ac_x30 {s : State} (h : Ac lab pfx s)
    (hn : s.st.2 ∉ pcRet lab pfx :: pcJe lab pfx :: pcSt lab pfx :: tailPcs lab pfx ++ failPcs lab pfx) :
    RaW lab s (raT lab pfx) := by
  rcases h with ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  all_goals first | exact hr | (exfalso; apply hn; simp_all)

/-! ## The return address's pcs cover the dispatcher's and the stub's -/

/-- The prologue's pcs. -/
theorem dispE_ra {pc : Int64} (h : pc ∈ dispEPcs lab) :
    pc ∈ raSPcs lab ∨ pc ∈ raPPcs lab ∨ pc ∈ raBPcs lab := by
  simp only [dispEPcs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [raSPcs, raPPcs, raBPcs]

/-- The tests' pcs are at `8(%rbp)`. -/
theorem dispT_ra {pc : Int64} (h : pc ∈ dispTPcs lab) : pc ∈ raBPcs lab := by
  simp [raBPcs, h]

/-- The jump's pcs. -/
theorem g5_ra {pc : Int64} (h : pc ∈ g5Pcs lab) :
    pc ∈ raSPcs lab ∨ pc ∈ raPPcs lab ∨ pc ∈ raBPcs lab := by
  simp only [g5Pcs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [raSPcs, raPPcs, raBPcs]

/-- The stub's pcs. -/
theorem stub_ra {pc : Int64} (h : pc ∈ stubPcs lab) :
    pc ∈ raSPcs lab ∨ pc ∈ raPPcs lab ∨ pc ∈ raBPcs lab := by
  simp only [stubPcs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [raSPcs, raPPcs, raBPcs, stubPcs]

end Spike.Lib.X64.ThreadsAb

/-- info: 'Spike.Lib.X64.ThreadsAb.CloneRef.slt' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.CloneRef.slt

/-- info: 'Spike.Lib.X64.ThreadsAb.CloneRef.ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.CloneRef.ne_zero

/-- info: 'Spike.Lib.X64.ThreadsAb.pc_of_ac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.pc_of_ac

/-- info: 'Spike.Lib.X64.ThreadsAb.not_ac_of_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.not_ac_of_pc

/-- info: 'Spike.Lib.X64.ThreadsAb.ac_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.ac_ret

/-- info: 'Spike.Lib.X64.ThreadsAb.ac_je' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.ac_je

/-- info: 'Spike.Lib.X64.ThreadsAb.ac_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.ac_fail

/-- info: 'Spike.Lib.X64.ThreadsAb.ac_g5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.ac_g5

/-- info: 'Spike.Lib.X64.ThreadsAb.ac_stub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.ac_stub

/-- info: 'Spike.Lib.X64.ThreadsAb.ac_x30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.ac_x30

/-- info: 'Spike.Lib.X64.ThreadsAb.dispE_ra' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.dispE_ra

/-- info: 'Spike.Lib.X64.ThreadsAb.dispT_ra' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.dispT_ra

/-- info: 'Spike.Lib.X64.ThreadsAb.g5_ra' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.g5_ra

/-- info: 'Spike.Lib.X64.ThreadsAb.stub_ra' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.ThreadsAb.stub_ra
