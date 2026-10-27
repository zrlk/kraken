/-
**The write abort phase on AArch64** (`Ab` of `SFactsA`,
`Spike/Lib/A64SegInstA.lean`): the thread states from `scc_rt_print`'s
refused `write` to `scc_rt_abort_write`'s `exit_group`, by pc and, where the
code still tests it, by the data that makes the path the refusal's.

- `Ab lab s`: one of
  - `.ret`: the pc after `print`'s system call, its length `[sp + 8]`
    refused by `x0` (`Refusal`, `Spike/Lib/Consumer1.lean`);
  - `.tail`: a pc of `print`'s tests of the result (`tailPcs`: the rest of
    the block after the call, `.3_chk2`, `.4_chk3` up to its `b.le`), the
    length `[sp + 8]` refused by the stored result `[sp + 16]`;
  - `.fail`: a pc of `.6_fail` (`failPcs`);
  - `.dispE`: a pc of the dispatcher's prologue (`dispEPcs`) with `x0 = 4`;
  - `.dispT`: a pc of the first four tests (`dispTPcs`: the tests against 1,
    2, 3 and their jumps to the next, the test against 4) with `[sp] = 4`;
  - `.g4`: a pc of the jump to the write stub (`g4Pcs`);
  - `.stub`: a pc of `scc_rt_abort_write` up to its exit call (`stubPcs`).
- `abPcs`: every pc above; `pc_of_ab`, `not_ab_of_pc`: a state in `Ab` is
  at one of them, so a state at no such pc is not in `Ab`.
- `ab_fail`, `ab_g4`, `ab_stub`: the classes with no data condition.

`lab` is the executable's label map (`(_root_.Executable.labels exe).label`
at the nodes' fragments).
-/
import Spike.Lib.A64Print
import Spike.Lib.A64Abort
import Spike.Lib.Consumer1
import Scc.Sem.TargetA64

namespace Spike.Lib.A64.WriteAb

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (privLoad)
open Spike.Lib.Consumer1 (Refusal)

variable (lab : Label → Int64)

/-- The pc after `print`'s system call (`Print.N .n5`). -/
abbrev pcRet : Int64 := Print.pcSvc lab + 4

/-- `print`'s tests of the stored result: the rest of the block after the
call, its `b.eq` and `b`, `.3_chk2`'s block, `b.eq` and `b`, `.4_chk3`'s
block up to its `b.le .6_fail`. -/
def tailPcs : List Int64 :=
  [Print.pcSvc lab + 8, Print.pcSvc lab + 12, Print.pcSvc lab + 16, Print.pcSvc lab + 20,
   Print.pcSvc lab + 24, Print.pcSvc lab + 28, Print.pcSvc lab + 32, Print.pcSvc lab + 36,
   lab ".L9_scc_rt_print.3_chk2", lab ".L9_scc_rt_print.3_chk2" + 4, lab ".L9_scc_rt_print.3_chk2" + 8,
   lab ".L9_scc_rt_print.3_chk2" + 12, lab ".L9_scc_rt_print.3_chk2" + 16,
   lab ".L9_scc_rt_print.3_chk2" + 20, lab ".L9_scc_rt_print.3_chk2" + 24,
   lab ".L9_scc_rt_print.3_chk2" + 28,
   lab ".L9_scc_rt_print.4_chk3", lab ".L9_scc_rt_print.4_chk3" + 4, lab ".L9_scc_rt_print.4_chk3" + 8,
   lab ".L9_scc_rt_print.4_chk3" + 12]

/-- `print`'s `.6_fail`: `movz x0, #4; bl scc_rt_abort`. -/
def failPcs : List Int64 := [lab ".L9_scc_rt_print.6_fail", lab ".L9_scc_rt_print.6_fail" + 4]

/-- The dispatcher's prologue (`Disp.d0`, which keeps `x0`). -/
def dispEPcs : List Int64 :=
  [lab "scc_rt_abort", lab "scc_rt_abort" + 4, lab "scc_rt_abort" + 8, lab "scc_rt_abort" + 12,
   lab "scc_rt_abort" + 16]

/-- The dispatcher's tests against 1, 2, 3 and their jumps to the next, and
the test against 4 (`Disp.DN.nd4`'s `.t1` … `.t4`). -/
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
   lab ".L12_scc_rt_abort.6_next5" + 8, lab ".L12_scc_rt_abort.6_next5" + 12]

/-- The dispatcher's jump to the write stub (`Disp.g4`). -/
def g4Pcs : List Int64 :=
  [lab ".L12_scc_rt_abort.7_is6", lab ".L12_scc_rt_abort.7_is6" + 4, lab ".L12_scc_rt_abort.7_is6" + 8,
   lab ".L12_scc_rt_abort.7_is6" + 12]

/-- `scc_rt_abort_write` (`Abort.write`) up to its exit call: the prologue,
the message's address, the argument block `b1Write`, the system call, the
block `b2` and the exit call. -/
def stubPcs : List Int64 :=
  [lab Abort.write.fn, lab Abort.write.fn + 4, lab Abort.write.fn + 8, lab Abort.write.fn + 12,
   lab Abort.write.entry, lab Abort.write.entry + 4, lab Abort.write.entry + 8,
   lab Abort.write.entry + 12, lab Abort.write.entry + 16, lab Abort.write.entry + 20,
   lab Abort.write.entry + 24, lab Abort.write.entry + 28, lab Abort.write.entry + 32,
   lab Abort.write.entry + 36, lab Abort.write.entry + 40, lab Abort.write.exit]

/-- The 8-byte word at `sp + o` of a state's private memory. -/
abbrev spLoad (s : State) (o : BitVec 64) : Option (BitVec 64) := privLoad s (s.st.1.regs.SP.toBitVec + o)

/-- **The write abort phase.** -/
def Ab (s : State) : Prop :=
  (s.st.2 = pcRet lab ∧ ∃ l, spLoad s 8 = some l ∧ Refusal l.toNat s.st.1.regs.X0.toBitVec) ∨
  (s.st.2 ∈ tailPcs lab ∧ ∃ l r, spLoad s 8 = some l ∧ spLoad s 16 = some r ∧ Refusal l.toNat r) ∨
  s.st.2 ∈ failPcs lab ∨
  (s.st.2 ∈ dispEPcs lab ∧ s.st.1.regs.X0 = 4) ∨
  (s.st.2 ∈ dispTPcs lab ∧ spLoad s 0 = some 4#64) ∨
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

/-- `.6_fail` is in `Ab`. -/
theorem ab_fail {s : State} (h : s.st.2 ∈ failPcs lab) : Ab lab s := .inr (.inr (.inl h))

/-- The jump to the write stub is in `Ab`. -/
theorem ab_g4 {s : State} (h : s.st.2 ∈ g4Pcs lab) : Ab lab s := .inr (.inr (.inr (.inr (.inr (.inl h)))))

/-- `scc_rt_abort_write` is in `Ab`. -/
theorem ab_stub {s : State} (h : s.st.2 ∈ stubPcs lab) : Ab lab s := .inr (.inr (.inr (.inr (.inr (.inr h)))))

end Spike.Lib.A64.WriteAb
