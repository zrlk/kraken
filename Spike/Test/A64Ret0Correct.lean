/-
**Tests of `Spike/Lib/A64Ret0Correct.lean`**: the source program `ret0Src`
is the frontend's program of `Scc/Test/ret0.w`, and the canonical target's
run of `ret0Asm`'s load (the load `ret0_load` names) exits with `42`.
-/
import Spike.Lib.A64Ret0Correct
import Scc.Frontend
import Scc.Sem.Test.Run

namespace Spike.Test.A64Ret0Correct

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link.A64
open Spike.Lib.A64Consumer (T)
open Spike.Lib.Ret0Src (ret0Src)
open Spike.Lib.A64.Flow.Ret0.Inst (μ0)
open SccCode (ret0Λ ret0Prog ret0Asm ret0Secs)

/-- The text of `Scc/Test/ret0.w`. -/
def ret0W : String :=
  "-- main returns 40 + 2 = 42: one thread, no allocation, no output; the first\n" ++
  "-- certification target.\n\n" ++
  "def main(u : Unit) : Int =\n  let x = 40\n  let y = x + 2\n  ret y\n"

/-- A code block's fields, as text (`Decl` has no `Repr`). -/
def declText (d : Decl) : String :=
  s!"{d.name} {d.tparams.length} {d.idx} {d.arg} {reprStr d.argTy} {reprStr d.retTy} {reprStr d.body}"

-- The frontend's program of `ret0.w` is `ret0Src`.
#guard match Scc.Frontend.run ret0W with
  | .ok c => c.prog.map declText == ret0Src.map declText
  | .error _ => false


/-! ## The run

The canonical target's run of the load exits with `42`, `main`'s result,
with no shared write to the stack pool: `ret0_correct_of`'s hypotheses are
about a program that runs. -/

-- The parse equation `ret0_correct_of` takes (the trust boundary).
#guard parsesTo ret0Asm ret0Prog ret0Secs

-- Release criterion 3(a), the positive witness: the canonical loader loads
-- `ret0Asm` (the kernel-checked form at the parsed values is `ret0_loadP`),
-- and the run below of the load exits with `42`.
#guard (T.load ret0Asm ret0Λ).isSome

/-- info: "out=\"\" events=[exit 42] stop=exited steps=294 poolMsgs=0" -/
#guard_msgs in
#eval match T.load ret0Asm ret0Λ with
  | some c =>
    let μ := Scc.Sem.Test.RunMarks.mk (μ0.site .take) (μ0.site .release) μ0.abortAt false
    let r := Scc.Sem.Test.run abi Arch.armv8 pcOf μ 400 0 { cfg := c }
    s!"out={repr r.outText} events={r.other} stop={r.stop} steps={r.steps} " ++
      s!"poolMsgs={Scc.Sem.Test.msgsIn r.cfg ret0Λ.stackPool}"
  | none => "load refused"

/-- info: 'Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_inst

/-- info: 'Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_parsed

/-- info: 'Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_inst_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_inst_parsed

/-- info: 'Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_pending

/-- info: 'Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct

/-- info: 'Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_asm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Ret0.Correct.ret0_correct_asm

end Spike.Test.A64Ret0Correct
