/-
**`main`'s body ends, on every path, in a call returning its result or a
literal** (`Scc.Lower.mainRetOk`): `hello1o` and `hello1L.w` pass;
`ret0.w` and `ifsub1.w` (call-free, a bare `ret` on every path) are
rejected, as are a `main` that is `ret 0`, one with a `let` before its
`ret`, an `ifeq` with one bare-`ret` branch, a call other than `print` then
`ret` of a literal (a plain block named `print` among them), and a `case`
above the last call. A call then `ret` of its result, an `ifeq` whose two
branches each do that, and two `print`s then `ret 0` pass. The sources here
have no setup block, so they are not `Accepted2`: they test `mainRetOk`
alone.
-/
import Scc.Frontend
import Scc.Lower.Spec2
import Scc.Test.Src
import Spike.Test.Hello1MainSrc

namespace Spike.Test.MainRetOk

open Scc

/-- `mainRetOk` of a `.w` source (`none` if it does not parse). -/
def retOk (src : String) : Option Bool :=
  match Frontend.parse src with
  | .ok p => some (Lower.mainRetOk p)
  | .error _ => none

/-- `main` is a bare `ret`. -/
def bareRet : String := "
def main(u : Unit) : Int =
  ret 0
"

/-- `main` binds a value, then returns it. -/
def letRet : String := "
def main(u : Unit) : Int =
  let z = 0
  ret z
"

/-- `main` calls a block, then returns its result. -/
def callRet : String := "
def g(u : Unit) : Int =
  ret 7

def main(u : Unit) : Int =
  let z = 0
  let x = g(u)
  ret x
"

/-- `main` calls a block, then returns another variable. -/
def callRetOther : String := "
def g(u : Unit) : Int =
  ret 7

def main(u : Unit) : Int =
  let z = 0
  let x = g(u)
  ret z
"

/-- `main` branches; each branch calls a block, then returns its result or a
literal (rejected: a literal only after `print`). -/
def ifCallRet : String := "
def g(u : Unit) : Int =
  ret 7

def main(u : Unit) : Int =
  let z = 0
  if z = 0 then
    let x = g(u)
    ret x
  else
    let y = g(u)
    ret 3
"

/-- `main` branches; one branch calls then returns its result, the other is a
bare `ret`. -/
def ifOneBare : String := "
def g(u : Unit) : Int =
  ret 7

def main(u : Unit) : Int =
  let z = 0
  if z = 0 then
    let x = g(u)
    ret x
  else
    ret z
"

/-- `main` branches; each branch calls a block, then returns its result. -/
def ifCallRetV : String := "
def g(u : Unit) : Int =
  ret 7

def main(u : Unit) : Int =
  let z = 0
  if z = 0 then
    let x = g(u)
    ret x
  else
    let y = g(u)
    ret y
"

/-- `hello1o`'s `main` with the body `b`. -/
def mainWith (b : CoreTerm.Expr) : CoreTerm.Prog := [{ Spike.Test.Hello1MainSrc.mainD with body := b }]

/-- `main` prints twice, then returns `0` (a call before the last one is
walked through). -/
def twoPrints : CoreTerm.Prog :=
  mainWith <| .split (.var "a") "sl0" "me" <| .unpack (.var "sl0") "q" "sl" <|
    .let_ "u" (.call "print" ["q"] (.var "sl") []) <|
    .let_ "v" (.call "print" ["q"] (.var "sl") []) <|
    .ret (.lit 0)

/-- `main` calls a plain block named `print` (no index, not the output
extern), then returns a literal (rejected). -/
def userPrintLit : CoreTerm.Prog :=
  mainWith <| .let_ "x" (.call "print" [] (.var "a") []) <| .ret (.lit 3)

/-- `main` has a `case` above its last call (not walked through). -/
def caseAbove : CoreTerm.Prog :=
  mainWith <| .let_ "z" (.inl .int (.lit 0)) <|
    .case (.var "z") "l" (.let_ "x" (.call "g" [] (.var "l") []) (.ret (.var "x")))
      "r" (.let_ "y" (.call "g" [] (.var "r") []) (.ret (.var "y")))

theorem hello1o_mainRetOk : Lower.mainRetOk Spike.Test.Hello1MainSrc.hello1o = true := by decide

#guard retOk (w_src% "Scc/Test/hello1L.w") == some true
#guard retOk (w_src% "Spike/Gen/ret0.w") == some false
#guard retOk (w_src% "Scc/Test/ifsub1.w") == some false
#guard retOk bareRet == some false
#guard retOk letRet == some false
#guard retOk callRet == some true
#guard retOk callRetOther == some false
#guard retOk ifCallRet == some false
#guard retOk ifCallRetV == some true
#guard retOk ifOneBare == some false
#guard Lower.mainRetOk twoPrints
#guard !Lower.mainRetOk userPrintLit
#guard !Lower.mainRetOk caseAbove

end Spike.Test.MainRetOk
