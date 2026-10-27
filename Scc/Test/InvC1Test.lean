import Scc.Lower.InvC1
import Scc.Frontend
import Scc.Test.Src

/-!
# Tests of the closed form with calls

`Scc.Lower.Inv.lowerC` against the lowering (`lowerDeclMarks`) on the
code blocks of `Accepted1` programs, with and without the depth counter:
the function and the trace agree with `func1` and `marks1`
(`lowerDeclMarks_lowerC`).
-/

namespace Scc.Test.InvC1

open Scc.Lower Scc.Lower.Inv

/-- `lowerDeclMarks` of every code block of `prog` agrees with `lowerC`'s
`func1` and `marks1` (blocks, scalar registers and trace). -/
def agrees (prog : CoreTerm.Prog) (frames : Option Nat) : Bool :=
  prog.all fun d =>
    match lowerC { prog, externs := [], fn := d.name, frames } (env1 d) 0 "entry" 0 d.body,
        lowerDeclMarks prog [] d {} frames with
    | some r, .ok (f, ms) =>
      let g := func1 (Names.user d.name) (params1R d) r
      f.name == g.name && f.params == g.params && f.blocks == g.blocks && f.scalarRegs == g.scalarRegs &&
        (ms.toList.map (·.1)) == ((marks1 d r).toList.map (·.1))
    | _, _ => false

/-- A program as WeakCore terms: `main` calls `g` on `1`. -/
def callProg : CoreTerm.Prog :=
  [{ name := "g", idx := [], arg := "n", argTy := .int, retTy := .int, body := .ret (.var "n") },
   { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "r" (.call "g" [] (.lit 1)) (.ret (.var "r")) }]

#guard agrees callProg none
#guard agrees callProg (some 64)

/-- The program of a source file the frontend accepts (`[]` otherwise). -/
def progOf (src : String) : CoreTerm.Prog :=
  match Scc.Frontend.run src with
  | .ok c => c.prog
  | .error _ => []

-- `call1.w`: a call after a `let`, a callee with an `if` and a `-`.
#guard (progOf (w_src% "Scc/Test/call1.w")).length == 2
#guard agrees (progOf (w_src% "Scc/Test/call1.w")) none
#guard agrees (progOf (w_src% "Scc/Test/call1.w")) (some 1000)

-- The counter: `call1.w`'s `main` consumes one name per call, seven with
-- the depth counter (`lowerC_next`).
#guard (progOf (w_src% "Scc/Test/call1.w")).all fun d =>
  [none, some 1000].all fun fr =>
    (lowerC { prog := progOf (w_src% "Scc/Test/call1.w"), externs := [], fn := d.name, frames := fr }
      (env1 d) 0 "entry" 0 d.body).map (·.next) == some (cntC fr d.body)

-- An `Accepted1` program has no externs (`externs_accepted1`).
#guard (Scc.Frontend.externs (progOf (w_src% "Scc/Test/call1.w"))).isEmpty

end Scc.Test.InvC1
