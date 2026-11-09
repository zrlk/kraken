import Scc.Lower.Spec2
import Scc.Frontend
import Scc.Test.Src

/-!
# Tests of the bound of the fragment `Accepted2`

`Scc.Lower.blocksOk2` on test programs, against `Scc.IR.blocksOk` of the IR functions their
compiled blocks lower to (`lowerDeclMarks`, without the depth counter). The programs are scc's
test sources, parsed and checked by its frontend (`Scc.Frontend.run`) at elaboration time, and
those programs padded with checked `+`s up to the bound and one past it.
-/

namespace Scc.Test.Spec2

open Scc.Lower

/-- `Scc.IR.blocksOk` of the IR functions `p`'s compiled blocks (not the externs `ex`) lower to
(`lowerDeclMarks`, without the depth counter), `none` if one fails. -/
def loweredOk2 (p : CoreTerm.Prog) (ex : List (String × Frontend.Extern)) : Option Bool :=
  (p.filter fun d => !(ex.any (·.1 == d.name))).foldlM (fun ok d =>
    match lowerDeclMarks p ex d with
    | .ok (f, _) => some (ok && Scc.IR.blocksOk f)
    | .error _ => none) true

/-- `Accepted2`, `blocksOk2`, and `loweredOk2` with the frontend's externs. -/
def report (p : CoreTerm.Prog) : Bool × Bool × Option Bool :=
  (Accepted2 p, blocksOk2 p, loweredOk2 p (Scc.Frontend.externs p))

/-- `blocksOk2` is the bound on the lowered code. -/
def agrees (p : CoreTerm.Prog) : Bool :=
  loweredOk2 p (Scc.Frontend.externs p) == some (blocksOk2 p)

/-- `k` checked `+`s of `x` from `x0`, then `tail`. -/
def adds (k : Nat) (x0 : CoreTerm.At) (tail : CoreTerm.Expr) : CoreTerm.Expr :=
  match k with
  | 0 => .let_ "s" (.atom x0) tail
  | k + 1 => .let_ "s" (.add x0 (.lit 1)) (adds k (.var "s") tail)

/-- The program of `src`, `[]` if the frontend refuses it. -/
def progOf (src : String) : CoreTerm.Prog :=
  match Scc.Frontend.run src with
  | .ok c => c.prog
  | .error _ => []

def hello1 : CoreTerm.Prog := progOf (w_src% "Scc/Test/hello1.w")
def hello1L : CoreTerm.Prog := progOf (w_src% "Scc/Test/hello1L.w")
def hello : CoreTerm.Prog := progOf (w_src% "Scc/Test/hello.w")

/-! ## The test sources -/

-- `hello1L.w` (the output extern with its loop) is in `Accepted2`; `hello1.w` (the extern
-- without its loop) and `hello.w` (spawn, park) are not, but are bounded.
#guard report hello1L == (true, true, some true)
#guard report hello1 == (false, true, some true)
#guard report hello == (false, true, some true)

/-! ## The bound, exactly

`rodata` of `hello1L.w`: no parameter word; `newBuf` 5, two `xchg`s 2 each, and the `ret` of
its 4-word slice 5: 14 units, so 498 `+`s fit and 499 do not. `main`: 5 parameter words (the
slice and the thread word), the `print` call 8 and `ret` 2: 15 units, so 497 `+`s fit. -/

/-- `p` with `k` checked `+`s at the start of block `rodata`'s body. -/
def padRodata (k : Nat) (p : CoreTerm.Prog) : CoreTerm.Prog :=
  p.map fun d => if d.name == "rodata" then { d with body := adds k (.lit 0) d.body } else d

/-- `p` with `k` checked `+`s in block `main`, after its `let (x, y)` (`mainArgOk`). -/
def padMain (k : Nat) (p : CoreTerm.Prog) : CoreTerm.Prog :=
  p.map fun d => if d.name == "main" then
    { d with body := match d.body with
      | .split a x y e => .split a x y (adds k (.lit 0) e)
      | e => adds k (.lit 0) e }
  else d

-- `newBuf`, `xchg` and a multi-word `ret`.
#guard report (padRodata 498 hello1L) == (true, true, some true)
#guard report (padRodata 499 hello1L) == (false, false, some false)
-- The parameter words and the `print` call.
#guard report (padMain 497 hello1L) == (true, true, some true)
#guard report (padMain 498 hello1L) == (false, false, some false)

/-- `main` calling `g` (`k` `+`s, then `ret`), declared before it; `g` of argument and result
types `gArg`, `gRet`. -/
def callG (k : Nat) (gArg gRet : CoreLang.Ty := .int) : CoreTerm.Prog :=
  [{ name := "g", idx := [], arg := "n", argTy := gArg, retTy := gRet,
     body := adds k (.lit 0) (.ret (.var "s")) },
   { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "r" (.call "g" [] (.lit 1)) (.ret (.var "r")) }]

-- A callee's parameter word and `ret`: 1 + 509 + 2 units fit, 510 `+`s do not.
#guard report (callG 509) == (true, true, some true)
#guard report (callG 510) == (false, false, some false)

-- A call weighs 3 (`call [r] g [w]`) because an ordinary callee is `plain2`, `Int` to `Int`:
-- callees with a multi-word argument or result are refused.
#guard !Accepted2 (callG 3 (.prod .int .int)) && agrees (callG 3 (.prod .int .int))
#guard !Accepted2 (callG 3 .int (.prod .int .int)) && agrees (callG 3 .int (.prod .int .int))

end Scc.Test.Spec2
