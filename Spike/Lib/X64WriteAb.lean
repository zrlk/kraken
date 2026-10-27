/-
**The write abort phase on x86-64** (`Ab` of `SFactsA`,
`Spike/Lib/X64SegInstA.lean`): the thread states from `scc_rt_print`'s
refused `write` to `scc_rt_abort_write`'s `exit_group`, by pc and, where the
code still tests it, by the data that makes the path the refusal's (the
x86-64 twin of `Spike/Lib/A64WriteAb.lean`).

- `Ab lab s`: one of
  - `.ret`: the pc after `print`'s system call, its length `-16(%rbp)`
    refused by `%rax` (`Refusal`, `Spike/Lib/Consumer1.lean`);
  - `.tail`: a pc of `print`'s tests of the result (`tailPcs`: the rest of
    the block after the call, `.chk2`, `.chk3` up to its `jle`), the length
    `-16(%rbp)` refused by the stored result `-24(%rbp)`;
  - `.fail`: a pc of `.fail` (`failPcs`);
  - `.dispE`: a pc of the dispatcher's prologue (`dispEPcs`) with
    `%rdi = 4`;
  - `.dispT`: a pc of the first four tests (`dispTPcs`: the tests against 1,
    2, 3 and their jumps to the next, the test against 4) with
    `-8(%rbp) = 4`;
  - `.g4`: a pc of the jump to the write stub (`g4Pcs`);
  - `.stub`: a pc of `scc_rt_abort_write` up to its exit call (`stubPcs`).
- `abPcs`: every pc above; `pc_of_ab`, `not_ab_of_pc`: a state in `Ab` is
  at one of them, so a state at no such pc is not in `Ab`.
- `ab_fail`, `ab_g4`, `ab_stub`: the classes with no data condition.

`lab` is the executable's label map (`(_root_.Executable.labels exe).label`
at the nodes' fragments).
-/
import Spike.Lib.X64Print
import Spike.Lib.X64Abort
import Spike.Lib.Consumer1
import Scc.Sem.TargetX64

namespace Spike.Lib.X64.WriteAb

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (privLoad)
open Spike.Lib.Consumer1 (Refusal)

variable (lab : Label → Int64)

/-- The pc after `print`'s system call (`Print.N .n5`). -/
abbrev pcRet : Int64 := lab ".Lscc_rt_print.write" + 22

/-- `print`'s tests of the stored result: the rest of the block after the
call (`x5`) and its `jmp`, `.chk2`'s block and `jmp`, `.chk3`'s block up to
its `jle .fail`. -/
def tailPcs : List Int64 :=
  [lab ".Lscc_rt_print.write" + 26, lab ".Lscc_rt_print.write" + 30, lab ".Lscc_rt_print.write" + 37,
   lab ".Lscc_rt_print.write" + 40, lab ".Lscc_rt_print.write" + 42,
   lab ".Lscc_rt_print.chk2", lab ".Lscc_rt_print.chk2" + 4, lab ".Lscc_rt_print.chk2" + 11,
   lab ".Lscc_rt_print.chk2" + 14, lab ".Lscc_rt_print.chk2" + 16,
   lab ".Lscc_rt_print.chk3", lab ".Lscc_rt_print.chk3" + 4, lab ".Lscc_rt_print.chk3" + 11,
   lab ".Lscc_rt_print.chk3" + 14]

/-- `print`'s `.fail`: `movq $4, %rdi; call scc_rt_abort`. -/
def failPcs : List Int64 := [lab ".Lscc_rt_print.fail", lab ".Lscc_rt_print.fail" + 7]

/-- The dispatcher's prologue (`Disp.d0`, which keeps `%rdi`). -/
def dispEPcs : List Int64 :=
  [lab "scc_rt_abort", lab "scc_rt_abort" + 1, lab "scc_rt_abort" + 4, lab "scc_rt_abort" + 8]

/-- The dispatcher's tests against 1, 2, 3 and their jumps to the next, and
the test against 4 (`Disp.DN.nd4`'s `.t1` … `.t4`). -/
def dispTPcs : List Int64 :=
  [lab ".Lscc_rt_abort.entry", lab ".Lscc_rt_abort.entry" + 4, lab ".Lscc_rt_abort.entry" + 11,
   lab ".Lscc_rt_abort.entry" + 14, lab ".Lscc_rt_abort.entry" + 16,
   lab ".Lscc_rt_abort.next1", lab ".Lscc_rt_abort.next1" + 4, lab ".Lscc_rt_abort.next1" + 11,
   lab ".Lscc_rt_abort.next1" + 14, lab ".Lscc_rt_abort.next1" + 16,
   lab ".Lscc_rt_abort.next3", lab ".Lscc_rt_abort.next3" + 4, lab ".Lscc_rt_abort.next3" + 11,
   lab ".Lscc_rt_abort.next3" + 14, lab ".Lscc_rt_abort.next3" + 16,
   lab ".Lscc_rt_abort.next5", lab ".Lscc_rt_abort.next5" + 4, lab ".Lscc_rt_abort.next5" + 11,
   lab ".Lscc_rt_abort.next5" + 14]

/-- The dispatcher's jump to the write stub (`Disp.g4`). -/
def g4Pcs : List Int64 :=
  [lab ".Lscc_rt_abort.is6", lab ".Lscc_rt_abort.is6" + 3, lab ".Lscc_rt_abort.is6" + 4]

/-- `scc_rt_abort_write` (`Abort.write`) up to its exit call: the prologue,
the message's address, the argument block `x1Write`, the system call, the
block `x2` and the exit call. -/
def stubPcs : List Int64 :=
  [lab Abort.write.fn, lab Abort.write.fn + 1, lab Abort.write.fn + 4,
   lab Abort.write.entry, lab Abort.write.entry + 7, lab Abort.write.entry + 11,
   lab Abort.write.entry + 18, lab Abort.write.entry + 22, lab Abort.write.entry + 29,
   lab Abort.write.entry + 34, lab Abort.write.entry + 36, lab Abort.write.entry + 40,
   lab Abort.write.entry + 47, lab Abort.write.exit]

/-- The 8-byte word at `%rbp + o` of a state's private memory. -/
abbrev bpLoad (s : State) (o : BitVec 64) : Option (BitVec 64) := privLoad s (s.st.1.regs.rbp.toBitVec + o)

/-- **The write abort phase.** -/
def Ab (s : State) : Prop :=
  (s.st.2 = pcRet lab ∧ ∃ l, bpLoad s (-16) = some l ∧ Refusal l.toNat (s.st.1.regs.get64 .rax)) ∨
  (s.st.2 ∈ tailPcs lab ∧ ∃ l r, bpLoad s (-16) = some l ∧ bpLoad s (-24) = some r ∧ Refusal l.toNat r) ∨
  s.st.2 ∈ failPcs lab ∨
  (s.st.2 ∈ dispEPcs lab ∧ s.st.1.regs.get64 .rdi = 4#64) ∨
  (s.st.2 ∈ dispTPcs lab ∧ bpLoad s (-8) = some 4#64) ∨
  s.st.2 ∈ g4Pcs lab ∨
  s.st.2 ∈ stubPcs lab

/-- Every pc of `Ab`. -/
def abPcs : List Int64 :=
  pcRet lab :: tailPcs lab ++ failPcs lab ++ dispEPcs lab ++ dispTPcs lab ++ g4Pcs lab ++ stubPcs lab

variable {lab}

/-- **A state in `Ab` is at one of its pcs.** -/
theorem pc_of_ab {s : State} (h : Ab lab s) : s.st.2 ∈ abPcs lab := by
  unfold abPcs
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | h | h <;> simp_all

/-- **A state at none of `Ab`'s pcs is not in it.** -/
theorem not_ab_of_pc {s : State} (h : s.st.2 ∉ abPcs lab) : ¬ Ab lab s := fun h' => h (pc_of_ab h')

/-- `.fail` is in `Ab`. -/
theorem ab_fail {s : State} (h : s.st.2 ∈ failPcs lab) : Ab lab s := .inr (.inr (.inl h))

/-- The jump to the write stub is in `Ab`. -/
theorem ab_g4 {s : State} (h : s.st.2 ∈ g4Pcs lab) : Ab lab s := .inr (.inr (.inr (.inr (.inr (.inl h)))))

/-- `scc_rt_abort_write` is in `Ab`. -/
theorem ab_stub {s : State} (h : s.st.2 ∈ stubPcs lab) : Ab lab s := .inr (.inr (.inr (.inr (.inr (.inr h)))))

end Spike.Lib.X64.WriteAb
