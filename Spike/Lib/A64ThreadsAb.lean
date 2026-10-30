/-
**The threads abort phase on AArch64** (the `Ac` of the clone consumer's
`AbortPathSC`, next to `Ab` of `SFactsA`, `Spike/Lib/A64SegInstA.lean`):
the thread states from a spawn's refused `clone` to `scc_rt_abort_threads`'s
`exit_group`. They are given by pc and, where the code still tests it, by the
data that makes the path the refusal's. The write twin is
`Spike/Lib/A64WriteAb.lean`.

The spawn's code is the lowering's (`Spike/Test/Cert/A64WakeCert.s`,
`wc_main`). `pfx` is the function's local label prefix (`".L21_wc_main"`):

```
pfx.sp6:   … 13 instructions …; svc #0          (cloneAt = pfx.sp6 + 52)
           cbz x0, pfx.child9
pfx.clone9:
           str x0, [sp, #48]; ldr x9, [sp, #48]; movz x10, #0
           subs xzr, x9, x10; b.lt pfx.1_spawnfail5; b pfx.2_spawned6
pfx.1_spawnfail5:
           movz x0, #5; bl scc_rt_abort
```

- `CloneRef r`: `r` is a refusal of `clone`, `-EAGAIN` or `-ENOMEM`
  (`Scc.Sem.Kernel`, the results of `CloneOne.clone_step_nodormant`).
- `raT lab pfx`: the return address of `.1_spawnfail5`'s `bl` (its pc + 4).
- `Ac lab pfx s`: one of
  - `.ret`: the `cbz` after the call (`pcRet`), `x0` a refusal;
  - `.st`: `.clone9`'s store, `x0` a refusal;
  - `.tail`: `.clone9`'s tests up to its `b.lt` (`tailPcs`), the stored
    result `[sp + 48]` a refusal;
  - `.fail`: a pc of `.1_spawnfail5` (`failPcs`);
  - `.dispE`: a pc of the dispatcher's prologue (`WriteAb.dispEPcs`) with
    `x0 = 5`;
  - `.dispT`: a pc of the first five tests (`dispTPcs`: the tests against
    1, 2, 3, 4 and their jumps to the next, the test against 5) with
    `[sp] = 5`;
  - `.g5`: a pc of the jump to the threads stub (`g5Pcs`);
  - `.stub`: a pc of `scc_rt_abort_threads` up to its exit call (`stubPcs`);

  the last four with `x30 = raT lab pfx`. Nothing on the path from the `bl`
  to the exit call writes `x30` but `g5`'s reload of the value the
  dispatcher's prologue saved, so the path keeps it
  (`Abort.Disp.DN.nd5 … ra`, `Abort.NT … ra`); it tells this site from the
  other `scc_rt_abort(5)` calls (`scc_rt_alloc_tcb`'s `.2_full`,
  `scc_rt_thread_reserve`'s `.1_full`), whose `bl`s are at other pcs.
- `acPcs`: every pc above; `pc_of_ac`, `not_ac_of_pc`: a state in `Ac` is
  at one of them, so a state at no such pc is not in `Ac`.
- `ac_ret`, `ac_fail`, `ac_g5`, `ac_stub`: introduction at the call's return
  and at the classes with no data condition but the return address.
- `ac_x30`: a state in `Ac` past the spawn's own pcs has `x30 = raT`.

`lab` is the executable's label map (`(_root_.Executable.labels exe).label`
at the nodes' fragments).
-/
import Spike.Lib.A64WriteAb
import Scc.Sem.Kernel

namespace Spike.Lib.A64.ThreadsAb

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.WriteAb (spLoad dispEPcs)

/-- **A refused `clone`'s result**: `-EAGAIN` or `-ENOMEM`. -/
def CloneRef (r : BitVec 64) : Prop :=
  r = Scc.Sem.Kernel.neg Scc.Sem.Kernel.eagain ∨ r = Scc.Sem.Kernel.neg Scc.Sem.Kernel.enomem

/-- A refusal is negative as a signed word. -/
theorem CloneRef.slt {r : BitVec 64} (h : CloneRef r) : r.slt 0#64 = true := by
  rcases h with rfl | rfl <;> decide

/-- A refusal is not `0`. -/
theorem CloneRef.ne_zero {r : BitVec 64} (h : CloneRef r) : r ≠ 0#64 := by
  rcases h with rfl | rfl <;> decide

variable (lab : Label → Int64) (pfx : String)

/-- The spawn's `clone` call: `pfx.sp6`'s 14th instruction. -/
abbrev cloneAt : Int64 := lab (pfx ++ ".sp6") + 52

/-- The pc after the call: `cbz x0, pfx.child9`. -/
abbrev pcRet : Int64 := cloneAt lab pfx + 4

/-- `.clone9`'s store of the result. -/
abbrev pcSt : Int64 := lab (pfx ++ ".clone9")

/-- `.clone9`'s tests of the stored result up to its `b.lt`. -/
def tailPcs : List Int64 :=
  [lab (pfx ++ ".clone9") + 4, lab (pfx ++ ".clone9") + 8, lab (pfx ++ ".clone9") + 12,
   lab (pfx ++ ".clone9") + 16]

/-- `.1_spawnfail5`: `movz x0, #5; bl scc_rt_abort`. -/
def failPcs : List Int64 := [lab (pfx ++ ".1_spawnfail5"), lab (pfx ++ ".1_spawnfail5") + 4]

/-- The dispatcher's tests against 1, 2, 3, 4 and their jumps to the next,
and the test against 5 (`Disp.DN.nd5`'s `.t1` … `.t5`). -/
def dispTPcs : List Int64 :=
  [lab ".L12_scc_rt_abort.0_entry", lab ".L12_scc_rt_abort.0_entry" + 4,
   lab ".L12_scc_rt_abort.0_entry" + 8, lab ".L12_scc_rt_abort.0_entry" + 12,
   lab ".L12_scc_rt_abort.0_entry" + 16,
   lab ".L12_scc_rt_abort.2_next1", lab ".L12_scc_rt_abort.2_next1" + 4,
   lab ".L12_scc_rt_abort.2_next1" + 8, lab ".L12_scc_rt_abort.2_next1" + 12,
   lab ".L12_scc_rt_abort.2_next1" + 16,
   lab ".L12_scc_rt_abort.4_next3", lab ".L12_scc_rt_abort.4_next3" + 4,
   lab ".L12_scc_rt_abort.4_next3" + 8, lab ".L12_scc_rt_abort.4_next3" + 12,
   lab ".L12_scc_rt_abort.4_next3" + 16,
   lab ".L12_scc_rt_abort.6_next5", lab ".L12_scc_rt_abort.6_next5" + 4,
   lab ".L12_scc_rt_abort.6_next5" + 8, lab ".L12_scc_rt_abort.6_next5" + 12,
   lab ".L12_scc_rt_abort.6_next5" + 16,
   lab ".L12_scc_rt_abort.8_next7", lab ".L12_scc_rt_abort.8_next7" + 4,
   lab ".L12_scc_rt_abort.8_next7" + 8, lab ".L12_scc_rt_abort.8_next7" + 12]

/-- The dispatcher's jump to the threads stub (`Disp.g5`). -/
def g5Pcs : List Int64 :=
  [lab ".L12_scc_rt_abort.9_is8", lab ".L12_scc_rt_abort.9_is8" + 4, lab ".L12_scc_rt_abort.9_is8" + 8,
   lab ".L12_scc_rt_abort.9_is8" + 12]

/-- `scc_rt_abort_threads` (`Abort.threads`) up to its exit call: the
prologue, the message's address, the argument block `b1Threads`, the system
call, the block `b2` and the exit call. -/
def stubPcs : List Int64 :=
  [lab Abort.threads.fn, lab Abort.threads.fn + 4, lab Abort.threads.fn + 8, lab Abort.threads.fn + 12,
   lab Abort.threads.entry, lab Abort.threads.entry + 4, lab Abort.threads.entry + 8,
   lab Abort.threads.entry + 12, lab Abort.threads.entry + 16, lab Abort.threads.entry + 20,
   lab Abort.threads.entry + 24, lab Abort.threads.entry + 28, lab Abort.threads.entry + 32,
   lab Abort.threads.entry + 36, lab Abort.threads.entry + 40, lab Abort.threads.exit]

/-- The return address of `.1_spawnfail5`'s `bl scc_rt_abort`. -/
abbrev raT : BitVec 64 := (lab (pfx ++ ".1_spawnfail5") + 8).toBitVec

/-- **The threads abort phase.** -/
def Ac (s : State) : Prop :=
  (s.st.2 = pcRet lab pfx ∧ CloneRef s.st.1.regs.X0.toBitVec) ∨
  (s.st.2 = pcSt lab pfx ∧ CloneRef s.st.1.regs.X0.toBitVec) ∨
  (s.st.2 ∈ tailPcs lab pfx ∧ ∃ r, spLoad s 48 = some r ∧ CloneRef r) ∨
  s.st.2 ∈ failPcs lab pfx ∨
  (s.st.2 ∈ dispEPcs lab ∧ s.st.1.regs.X0 = 5 ∧ s.st.1.regs.X30.toBitVec = raT lab pfx) ∨
  (s.st.2 ∈ dispTPcs lab ∧ spLoad s 0 = some 5#64 ∧ s.st.1.regs.X30.toBitVec = raT lab pfx) ∨
  (s.st.2 ∈ g5Pcs lab ∧ s.st.1.regs.X30.toBitVec = raT lab pfx) ∨
  (s.st.2 ∈ stubPcs lab ∧ s.st.1.regs.X30.toBitVec = raT lab pfx)

/-- Every pc of `Ac`. -/
def acPcs : List Int64 :=
  pcRet lab pfx :: pcSt lab pfx :: tailPcs lab pfx ++ failPcs lab pfx ++ dispEPcs lab ++ dispTPcs lab ++
    g5Pcs lab ++ stubPcs lab

variable {lab pfx}

/-- **A state in `Ac` is at one of its pcs.** -/
theorem pc_of_ac {s : State} (h : Ac lab pfx s) : s.st.2 ∈ acPcs lab pfx := by
  unfold acPcs
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all

/-- **A state at none of `Ac`'s pcs is not in it.** -/
theorem not_ac_of_pc {s : State} (h : s.st.2 ∉ acPcs lab pfx) : ¬ Ac lab pfx s :=
  fun h' => h (pc_of_ac h')

/-- The return of a refused `clone` is in `Ac`. -/
theorem ac_ret {s : State} (hp : s.st.2 = pcRet lab pfx) (hr : CloneRef s.st.1.regs.X0.toBitVec) :
    Ac lab pfx s := .inl ⟨hp, hr⟩

/-- `.1_spawnfail5` is in `Ac`. -/
theorem ac_fail {s : State} (h : s.st.2 ∈ failPcs lab pfx) : Ac lab pfx s := .inr (.inr (.inr (.inl h)))

/-- The jump to the threads stub is in `Ac`. -/
theorem ac_g5 {s : State} (h : s.st.2 ∈ g5Pcs lab) (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) :
    Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h, hr⟩))))))

/-- `scc_rt_abort_threads` is in `Ac`. -/
theorem ac_stub {s : State} (h : s.st.2 ∈ stubPcs lab) (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) :
    Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨h, hr⟩))))))

/-- **A state in `Ac` at none of the spawn's own pcs** (so at the
dispatcher's or the threads stub's) has `x30 = raT lab pfx`: another
`scc_rt_abort(5)` caller, whose return address differs, is not in `Ac`
there. -/
theorem ac_x30 {s : State} (h : Ac lab pfx s)
    (hn : s.st.2 ∉ pcRet lab pfx :: pcSt lab pfx :: tailPcs lab pfx ++ failPcs lab pfx) :
    s.st.1.regs.X30.toBitVec = raT lab pfx := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  all_goals first | exact hr | (exfalso; apply hn; simp_all)

end Spike.Lib.A64.ThreadsAb
