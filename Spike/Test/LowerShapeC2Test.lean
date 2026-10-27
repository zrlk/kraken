import Spike.Lib.LowerShapeC2Some
import Scc.Frontend
import Scc.Lower.Spec2
import Scc.Test.Src

/-!
# Tests of the `Accepted2` closed form

`Spike.Lib.LowerShape.lowerC2` against the lowering (`lowerDeclMarks`,
as `lowerWithMarks` calls it) on the compiled code blocks of `Accepted2`
programs: the function and the trace agree with `func2` and `marks2`
(`lowerDeclMarks_lowerC2`).
-/

namespace Spike.Test.LowerShapeC2

open CoreTerm Scc.Lower Scc.Lower.Inv Spike.Lib.LowerShape

/-- `lowerDeclMarks` of every compiled code block of `prog` (its externs
excluded) agrees with `lowerC2`'s `func2` and `marks2` (blocks, marked
registers and trace nodes). -/
def agrees (prog : Prog) : Bool :=
  let ext := Scc.Frontend.externs prog
  (prog.filter fun d => !(ext.any (·.1 == d.name))).all fun d =>
    match Scc.Obj.valWords d.argTy with
    | none => false
    | some na =>
      match markR d.argTy ((paramsR d na).map .reg),
          lowerC2 { prog, externs := ext, fn := d.name, obj := {} } (env2 d na) 0 "entry" 0 d.body,
          lowerDeclMarks prog ext d {} with
      | some (sc, hp), some r, .ok (f, ms) =>
        let g := func2 (Names.user d.name) (paramsR d na) sc hp r
        f.name == g.name && f.params == g.params && f.blocks == g.blocks && f.scalarRegs == g.scalarRegs &&
          f.heapRegs == g.heapRegs && (ms.toList.map (·.1)) == ((marks2 d na r).toList.map (·.1))
      | _, _, _ => false

/-- The program of a source file the frontend accepts (`[]` otherwise). -/
def progOf (src : String) : Prog :=
  match Scc.Frontend.run src with
  | .ok c => c.prog
  | .error _ => []

-- `hello1L.w`: the setup block (`newBuf`, lane stores, a pair), `main`
-- with its two-word parameter split, and the output extern's call.
#guard (progOf (w_src% "Scc/Test/hello1L.w")).length == 4
#guard Accepted2 (progOf (w_src% "Scc/Test/hello1L.w"))
#guard agrees (progOf (w_src% "Scc/Test/hello1L.w"))

-- `call1.w`: an `Accepted1` program (calls, `if`, `-`).
#guard agrees (progOf (w_src% "Scc/Test/call1.w"))

/-- info: 'Spike.Lib.LowerShape.lowerC2_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerC2_isSome

/-- info: 'Spike.Lib.LowerShape.accepted2_lowerDeclMarks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepted2_lowerDeclMarks

end Spike.Test.LowerShapeC2
