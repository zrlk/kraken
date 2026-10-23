import Scc.Test.StackTest
import Scc.Emit.A64

/-!
# `relocIR` for AArch64

The AArch64 emitter accepts the stack relocation test of
`Scc/Test/StackTest.lean`, and `writeReloc` writes it for `run.sh` (one module
per architecture: no module may import both emitters).
-/

namespace Scc.Test.Stack.Arm

#guard (relocIR.bind Emit.A64.emitProgram).toOption.isSome

-- Every abort kind's `exit_group` trap instruction carries its label
-- `scc_rt_abort_<kind>_exit` (`Names.abortExit`): the label line is
-- immediately followed by the trap, once per kind.
open Scc.Lower in
#guard match relocIR.bind Emit.A64.emitProgram with
  | .ok x =>
    let ls := x.splitOn "\n"
    Runtime.abortKinds.all fun k =>
      ((ls.zip ls.tail).filter fun (a, b) =>
        a == Names.abortExit k ++ ":" && b == "\tsvc #0").length == 1 &&
      (ls.filter (· == Names.abortExit k ++ ":")).length == 1
  | .error _ => false

/-- Write `relocIR` as `<dir>/reloc_arm.s`. -/
def writeReloc (args : List String) : IO UInt32 := do
  let dir := args.headD "."
  IO.FS.createDirAll dir
  match relocIR.bind Emit.A64.emitProgram with
  | .ok a => IO.FS.writeFile s!"{dir}/reloc_arm.s" a; return 0
  | .error e => IO.eprintln e; return 1

end Scc.Test.Stack.Arm
