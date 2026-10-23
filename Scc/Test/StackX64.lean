import Scc.Test.StackTest
import Scc.Emit.X64

/-!
# `relocIR` for x64

The x64 emitter accepts the stack relocation test of `Scc/Test/StackTest.lean`,
and `writeReloc` writes it for `run.sh` (one module per architecture: no module
may import both emitters).
-/

namespace Scc.Test.Stack.X64

#guard (relocIR.bind Emit.X64.emit).toOption.isSome

-- Every abort kind's `exit_group` trap instruction carries its label
-- `scc_rt_abort_<kind>_exit` (`Names.abortExit`): the label line is
-- immediately followed by the trap, once per kind.
open Scc.Lower in
#guard match relocIR.bind Emit.X64.emit with
  | .ok x =>
    let ls := x.splitOn "\n"
    Runtime.abortKinds.all fun k =>
      ((ls.zip ls.tail).filter fun (a, b) =>
        a == Names.abortExit k ++ ":" && b == "\tsyscall").length == 1 &&
      (ls.filter (· == Names.abortExit k ++ ":")).length == 1
  | .error _ => false

/-- Write `relocIR` as `<dir>/reloc_x64.s`. -/
def writeReloc (args : List String) : IO UInt32 := do
  let dir := args.headD "."
  IO.FS.createDirAll dir
  match relocIR.bind Emit.X64.emit with
  | .ok x => IO.FS.writeFile s!"{dir}/reloc_x64.s" x; return 0
  | .error e => IO.eprintln e; return 1

end Scc.Test.Stack.X64
