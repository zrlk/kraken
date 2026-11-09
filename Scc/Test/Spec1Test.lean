import Scc.Lower.Spec1
import Scc.Frontend
import Scc.Test.Src

/-!
# Tests of the fragment `Accepted1`

`Scc.Lower.Accepted1` on test programs, parsed and checked by scc's
frontend (`Scc.Frontend.run`) at elaboration time.
-/

namespace Scc.Test.Spec1

open Scc.Lower

/-- `Accepted0` and `Accepted1` of a program the frontend accepts (`none`
when it does not). -/
def verdicts (src : String) : Option (Bool × Bool) :=
  match Scc.Frontend.run src with
  | .ok c => some (Accepted0 c.prog, Accepted1 c.prog)
  | .error _ => none

-- `ret0.w`: in both fragments.
#guard verdicts (w_src% "Scc/Test/ret0.w") == some (true, true)

-- `call1.w`: a call, an `if` and a `-`, in `Accepted1` only.
#guard verdicts (w_src% "Scc/Test/call1.w") == some (false, true)

-- `hello1.w`: a setup block, output and allocation, in neither.
#guard verdicts (w_src% "Scc/Test/hello1.w") == some (false, false)

-- Non-tail recursion (`deeprec.w`), tail calls (`tailloop.w`, `stackdepth.w`)
-- and memory (`spill.w`) are outside.
#guard verdicts (w_src% "Scc/Test/deeprec.w") == some (false, false)
#guard verdicts (w_src% "Scc/Test/tailloop.w") == some (false, false)
#guard verdicts (w_src% "Scc/Test/stackdepth.w") == some (false, false)
#guard verdicts (w_src% "Scc/Test/spill.w") == some (false, false)

/-- A program as WeakCore terms: `main` calls `g`, declared in `ds` before
or after it. -/
def callProg (gFirst : Bool) (gArg : CoreLang.Ty := .int) : CoreTerm.Prog :=
  let g : CoreTerm.Decl :=
    { name := "g", idx := [], arg := "n", argTy := gArg, retTy := .int, body := .ret (.var "n") }
  let m : CoreTerm.Decl :=
    { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
      body := .let_ "r" (.call "g" [] (.lit 1)) (.ret (.var "r")) }
  if gFirst then [g, m] else [m, g]

-- A call of an earlier code block is in; of a later one (the order that
-- rules out cycles) is not.
#guard Accepted1 (callProg true)
#guard !Accepted1 (callProg false)

-- A callee must take an `Int`.
#guard !Accepted1 (callProg true .unit)

-- Duplicate names, and no `main`, are out.
#guard !Accepted1 (callProg true ++ callProg true)
#guard !Accepted1 ((callProg true).take 1)

/-- `main` calling itself: out (only earlier code blocks, and never `main`). -/
def selfCall : CoreTerm.Prog :=
  [{ name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "r" (.call "main" [] .unit) (.ret (.var "r")) }]

#guard !Accepted1 selfCall

/-- `main` with `if u' = 0 then (let x = a  ret x) else (let x = b  ret x)`:
the term `ret x` is reached with `x` bound to `a` and to `b`. -/
def twoArms (a b : Nat) : CoreTerm.Prog :=
  [{ name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "v" (.atom (.lit 0)) <| .ifeq (.var "v") (.lit 0)
       (.let_ "x" (.atom (.lit a)) (.ret (.var "x")))
       (.let_ "x" (.atom (.lit b)) (.ret (.var "x"))) }]

-- Coherent immediates: one literal per variable at each term.
#guard Accepted1 (twoArms 1 1)
#guard !immsCoherent (twoArms 1 2)
#guard !Accepted1 (twoArms 1 2)

/-- Two code blocks, each `let x = n  ret x`, and `main` calling both. -/
def twoDecls (a b : Nat) : CoreTerm.Prog :=
  let f (name : String) (n : Nat) : CoreTerm.Decl :=
    { name, idx := [], arg := "n", argTy := .int, retTy := .int,
      body := .let_ "x" (.atom (.lit n)) (.ret (.var "x")) }
  [f "f" a, f "g" b,
   { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "r" (.call "f" [] (.lit 0)) <| .let_ "s" (.call "g" [] (.var "r")) (.ret (.var "s")) }]

-- `f` and `g` reuse the name `x` with different literals at the same term `ret x`: refused.
#guard Accepted1 (twoDecls 3 3)
#guard !Accepted1 (twoDecls 3 4)
#guard decls1 [] (twoDecls 3 4) && !immsCoherent (twoDecls 3 4)

-- The keyed form agrees with `Accepted1` and `immsCoherent`, accepted or refused.
#guard [callProg true, callProg false, selfCall, twoArms 1 1, twoArms 1 2, twoDecls 3 3, twoDecls 3 4].all
  fun p => Accepted1K p == Accepted1 p && immsCoherentK p == immsCoherent p

-- `Accepted1` by the kernel through the keyed form (`accepted1_of_K`).
example : Accepted1 (twoDecls 3 3) = true := accepted1_of_K (by decide +kernel)

/-! ## Bounded blocks (`blocksOk1`) -/

/-- `k` checked `+`s of `x` from `x0`, then `tail`. -/
def adds (k : Nat) (x0 : CoreTerm.At) (tail : CoreTerm.Expr) : CoreTerm.Expr :=
  match k with
  | 0 => .let_ "s" (.atom x0) tail
  | k + 1 => .let_ "s" (.add x0 (.lit 1)) (adds k (.var "s") tail)

/-- `main` of `k` checked `+`s and `ret`: one block of `k + 2` units. -/
def chain (k : Nat) : CoreTerm.Prog :=
  [{ name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := adds k (.lit 0) (.ret (.var "s")) }]

/-- `f(n : Int)` of `k` checked `+`s and `ret` (its parameter costs one
unit in block `entry`), and `main` calling it. -/
def chainF (k : Nat) : CoreTerm.Prog :=
  [{ name := "f", idx := [], arg := "n", argTy := .int, retTy := .int,
     body := adds k (.var "n") (.ret (.var "s")) },
   { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "r" (.call "f" [] (.lit 0)) (.ret (.var "r")) }]

/-- `main` with an `if` whose `then` arm is `k` checked `+`s and `ret`:
block `entry` is the `br` (1 unit), the arm `k + 2` units. -/
def chainArm (k : Nat) : CoreTerm.Prog :=
  [{ name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "v" (.atom (.lit 0)) <|
       .ifeq (.var "v") (.lit 0) (adds k (.lit 0) (.ret (.var "s"))) (.ret (.var "v")) }]

-- The bound is exact: 510 `+`s and the `ret` are 512 units, 511 are 513.
#guard Accepted1 (chain 510) && !Accepted1 (chain 511) && !blocksOk1 (chain 511)
-- The parameter counts in the first block.
#guard Accepted1 (chainF 509) && !Accepted1 (chainF 510)
-- An arm of an `if` is a block of its own.
#guard Accepted1 (chainArm 510) && !Accepted1 (chainArm 511)
-- Every `Accepted0` program is bounded (`maxAdds0` = 508).
#guard Accepted0 (chain 508) && blocksOk1 (chain 508)

/-- `Scc.IR.blocksOk` of the IR functions `p`'s code blocks lower to
(`lowerDeclMarks`, without the depth counter), `none` if one fails. -/
def loweredOk (p : CoreTerm.Prog) : Option Bool :=
  p.foldlM (fun ok d => match lowerDeclMarks p [] d with
    | .ok (f, _) => some (ok && Scc.IR.blocksOk f)
    | .error _ => none) true

-- `blocksOk1` is the bound on the lowered code, accepted or refused, with
-- calls, `-`, `if`s and the parameter.
#guard [chain 510, chain 511, chainF 509, chainF 510, chainArm 510, chainArm 511, callProg true,
    twoArms 1 1, twoDecls 3 3].all fun p => loweredOk p == some (blocksOk1 p)
#guard verdicts (w_src% "Scc/Test/call1.w") == some (false, true) &&
  (match Scc.Frontend.run (w_src% "Scc/Test/call1.w") with
   | .ok c => loweredOk c.prog == some true
   | .error _ => false)

end Scc.Test.Spec1
