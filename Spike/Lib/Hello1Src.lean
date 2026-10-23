import Scc.Frontend
import Scc.Test.Src

/-!
# `hello1.w`'s source program as a term

`hello1Src`, for both ISAs (`Spike/Test/A64Hello1PlaceOKE.lean`,
`Spike/Test/X64PlaceData.lean`, `Spike/Test/X64Hello1PlaceOKE.lean`): the
program the frontend reads from `Scc/Test/hello1.w`, written out so that
the kernel can reduce scc's pipeline on it (the frontend's parser is
`partial`, so the kernel does not reduce `Frontend.run`), and checked
against the frontend's reading by `#guard`.
-/

namespace Spike.Lib.Hello1Src

open CoreLang CoreTerm

/-- The type of `hello1.w`'s byte slice with its length: `print`'s owned
signature (`Frontend.printOwnSig`). -/
def sliceTy : Ty :=
  .prod (.prod (.refine (.loc .own (.array (.var 0) (.lanes false .w8))) (.ini (.var 0)))
    (.intS (.var 0))) .int

/-- **`hello1.w`'s source program**: `print` (the output extern), the setup
block `rodata` and `main`. -/
def hello1Src : Prog :=
  [{ name := "print", tparams := [], idx := ["m"], arg := "a", argTy := sliceTy, retTy := .unit,
     body := .ret .unit },
   { name := "rodata", tparams := [], idx := [], arg := "u", argTy := .unit, retTy := .iex sliceTy,
     body :=
      .let_ "two" (.atom (.lit 2)) <|
      .let_ "m" (.nameI (.var "two")) <|
      .let_ "b" (.newBuf (.var "m") (.lanes false .w8)) <|
      .let_ "w0" (.asLanes false .w8 (.lit 8583909746840200520)) <|
      .let_ "o0" (.xchgAt (.var "b") (.lit 0) (.var "w0")) <|
      .let_ "w1" (.asLanes false .w8 (.lit 44634501743)) <|
      .let_ "o1" (.xchgAt (.var "b") (.lit 1) (.var "w1")) <|
      .let_ "n" (.atom (.lit 13)) <|
      .let_ "sm" (.pair (.var "b") (.var "m")) <|
      .let_ "sl0" (.pair (.var "sm") (.var "n")) <|
      .let_ "sl" (.pack (.var "sl0") "m" (.iex sliceTy)) <|
      .ret (.var "sl") },
   { name := "main", tparams := [], idx := [], arg := "a",
     argTy := .prod (.iex sliceTy) (.ptr .pub .void), retTy := .int,
     body :=
      .split (.var "a") "sl0" "me" <|
      .unpack (.var "sl0") "q" "sl" <|
      .let_ "u" (.call "print" ["q"] (.var "sl") []) <|
      .ret (.lit 0) }]

deriving instance Repr for Decl

/-- `hello1Src` is the frontend's reading of `Scc/Test/hello1.w` (compared by
their printed forms: `Decl` has no equality instance). -/
def hello1SrcOk : Bool :=
  match Scc.Frontend.run (w_src% "Scc/Test/hello1.w") with
  | .ok c => reprStr c.prog == reprStr hello1Src
  | .error _ => false

#guard hello1SrcOk

end Spike.Lib.Hello1Src
