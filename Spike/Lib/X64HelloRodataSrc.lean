/-
**`hello.w`'s setup block `rodata`: the source terms** (x86-64 side): `rdBody` and its tails
`eM` … `eRet` (`rdBody_eq`: it is `rodata`'s body in `X64HelloSrc.helloSrc`), and `sliceTyP`,
hello's published slice type. The terms of `Spike/Lib/HelloRodataSrc.lean`, token for token.

Unlike AArch64 (`Spike.Lib.HelloRodataSrc`, which imports `Spike.Lib.HelloSrc` and so AArch64's
syntax), this module reads the program from `Spike.Lib.X64HelloSrc`; the controls and their
source steps are a separate module.
-/
import Spike.Lib.X64HelloSrc
import Spike.Lib.Hello1RodataSrc

namespace Spike.Lib.X64HelloRodataSrc

open CoreLang CoreTerm
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2 τ8)

/-! ## The terms -/

/-- **hello's slice type**: `print`'s published signature, the buffer `pub`. -/
def sliceTyP : Ty :=
  .prod (.prod (.refine (.loc .pub (.array (.var 0) τ8)) (.ini (.var 0))) (.intS (.var 0))) .int

def eRet : Expr := .ret (.var "sl")
def ePack : Expr := .let_ "sl" (.pack (.var "sl0") "m" (.iex sliceTyP)) eRet
def eSl0 : Expr := .let_ "sl0" (.pair (.var "sm") (.var "n")) ePack
def eSm : Expr := .let_ "sm" (.pair (.var "s") (.var "m")) eSl0
def eN : Expr := .let_ "n" (.atom (.lit 13)) eSm
def eS : Expr := .let_ "s" (.publish (.var "b")) eN
def eO1 : Expr := .let_ "o1" (.xchgAt (.var "b") (.lit 1) (.var "w1")) eS
def eW1 : Expr := .let_ "w1" (.asLanes false .w8 (.lit rdK2)) eO1
def eO0 : Expr := .let_ "o0" (.xchgAt (.var "b") (.lit 0) (.var "w0")) eW1
def eW0 : Expr := .let_ "w0" (.asLanes false .w8 (.lit rdK1)) eO0
def eB : Expr := .let_ "b" (.newBuf (.var "m") τ8) eW0
def eM : Expr := .let_ "m" (.nameI (.var "two")) eB

/-- `rodata`'s body in hello.w. -/
def rdBody : Expr := .let_ "two" (.atom (.lit 2)) eM

theorem rdBody_eq : helloSrc[2]?.map (·.body) = some rdBody := rfl

theorem rodata_name : helloSrc[2]?.map (·.name) = some "rodata" := rfl

end Spike.Lib.X64HelloRodataSrc
