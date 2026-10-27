import Spike.Lib.LowerProgC2
import Scc.Frontend
import Scc.Test.Src

/-!
# Tests of the whole-program lowering of `Accepted2` programs

On `hello1L.w` (setup block, `main` taking its result, the output extern)
and `call1.w` (an `Accepted1` program): `checkedOf` gives `checked2`'s
entry and externs, the compiled blocks are `compiled2`, the setup words are
`setupWords2`, and the lowering's IR has the runtime functions followed by
one function per compiled block (`lowerWithMarks_accepted2_ok`).
-/

namespace Spike.Test.LowerProgC2

open CoreTerm Scc.Lower Scc.Lower.Inv Spike.Lib.LowerNode

/-- The program of a source file the frontend accepts (`[]` otherwise). -/
def progOf (src : String) : Prog :=
  match Scc.Frontend.run src with
  | .ok c => c.prog
  | .error _ => []

/-- `checkedOf p` has `checked2 p`'s entry and externs, and `lowerWithMarks`
of it builds the runtime functions for `entry2 p` and `setupWords2 p`, then
one function per block of `compiled2 p`, named after it. -/
def agrees (p : Prog) : Bool :=
  match checkedOf p with
  | .error _ => false
  | .ok c =>
    c.entry.arg == (entry2 p).arg && c.entry.retInt == (entry2 p).retInt &&
      c.externs.map (·.1) == (checked2 p).externs.map (·.1) &&
      match lowerWithMarks {} c, rtFuncs ({} : Scc.Config).layout (entry2 p) (setupWords2 p) with
      | .ok (ir, ms), .ok rt =>
        ir.funcs.map (·.name) == rt.map (·.name) ++ (compiled2 p).map (Names.user ·.name) &&
          ms.map (·.1) == (compiled2 p).map (Names.user ·.name)
      | _, _ => false

#guard Accepted2 (progOf (w_src% "Scc/Test/hello1L.w"))
#guard (compiled2 (progOf (w_src% "Scc/Test/hello1L.w"))).length == 2
#guard (entry2 (progOf (w_src% "Scc/Test/hello1L.w"))).arg == .setupTid
#guard setupWords2 (progOf (w_src% "Scc/Test/hello1L.w")) == 4
#guard agrees (progOf (w_src% "Scc/Test/hello1L.w"))

#guard Accepted2 (progOf (w_src% "Scc/Test/call1.w"))
#guard (entry2 (progOf (w_src% "Scc/Test/call1.w"))).arg == .unit
#guard setupWords2 (progOf (w_src% "Scc/Test/call1.w")) == 0
#guard agrees (progOf (w_src% "Scc/Test/call1.w"))

/-- info: 'Spike.Lib.LowerNode.lowerIR_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerIR_accepted2

/-- info: 'Spike.Lib.LowerNode.lowerAll_accepted2_a64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerAll_accepted2_a64

/-- info: 'Spike.Lib.LowerNode.mem_progOf_funcs2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_progOf_funcs2

end Spike.Test.LowerProgC2
