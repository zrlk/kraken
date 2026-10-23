/-
**Tests of `Spike/Lib/X64Ret0Correct.lean`**: the canonical x86-64
target's run of `ret0Asm`'s load (the load `ret0_load` names) exits with
`42`. (`ret0Src` against the frontend: `Spike/Test/A64Ret0Correct.lean`.)
-/
import Spike.Lib.X64Ret0Correct
import Scc.Sem.Test.Run

namespace Spike.Test.X64Ret0Correct

open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link.X64
open Spike.Lib.X64Consumer (T)
open Spike.Lib.X64.Flow.Ret0.Inst (μ0)
open SccCode (ret0Λ ret0Cells ret0Asm ret0Secs)

/-! ## The run

The canonical target's run of the load exits with `42`, `main`'s result,
with no shared write to the stack pool: `ret0_correct_of`'s hypotheses are
about a program that runs. -/

-- The parse equation `ret0_correct_of` takes (the trust boundary).
#guard parsesTo ret0Asm ret0Cells ret0Secs

-- Release criterion 3(a), the positive witness: the canonical loader loads
-- `ret0Asm` (the kernel-checked form at the parsed values is `ret0_loadP`),
-- and the run below of the load exits with `42`.
#guard (T.load ret0Asm ret0Λ).isSome

/-- info: "out=\"\" events=[exit 42] stop=exited steps=277 poolMsgs=0" -/
#guard_msgs in
#eval match T.load ret0Asm ret0Λ with
  | some c =>
    let μ := Scc.Sem.Test.RunMarks.mk (μ0.site .take) (μ0.site .release) μ0.abortAt false
    let r := Scc.Sem.Test.run abi Arch.tso pcOf μ 400 0 { cfg := c }
    s!"out={repr r.outText} events={r.other} stop={r.stop} steps={r.steps} " ++
      s!"poolMsgs={Scc.Sem.Test.msgsIn r.cfg ret0Λ.stackPool}"
  | none => "load refused"

/-- info: 'Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_parsed

/-- info: 'Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_of

/-- info: 'Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_inst_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_inst_parsed

/-- info: 'Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_inst

/-- info: 'Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_pending

/-- info: 'Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct

/-- info: 'Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_asm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Flow.Ret0.Correct.ret0_correct_asm

end Spike.Test.X64Ret0Correct
