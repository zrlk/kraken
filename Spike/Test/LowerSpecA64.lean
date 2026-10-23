import Scc.Lower.SpecA64
import Scc.Test.Src
import Spike.Lib.Ret0Src
import Spike.Lib.A64Ret0Code
import Spike.Lib.A64Hello1Code

/-!
# `lowerAll` on AArch64 against what `scc --code` emits

`Scc.Lower.A64.lowerAll` on `ret0.w` and `hello1.w` gives the instruction
list, the data sections, the stack depth limit and the stack need table of
the committed `scc --arch arm --code` outputs (`Spike/Lib/A64Ret0Code.lean`,
`Spike/Lib/A64Hello1Code.lean`), and its rendered items are their assembler
text. `Accepted0` holds of `ret0.w` and not of `hello1.w`.
-/

namespace Spike.Test.LowerSpecA64

open Scc Scc.Lower Scc.Lower.A64

/-- The AArch64 configuration. -/
def cfgA : Config := { arch := .arm }

/-- `hello1.w` as the frontend reads it. -/
def hello1Src : CoreTerm.Prog :=
  match Frontend.run (w_src% "Scc/Test/hello1.w") with
  | .ok c => c.prog
  | .error _ => []

/-- A program's blocks as comparable data: names, parameters, types and
the bodies' `repr` (`CoreTerm.Expr` has no decidable equality). -/
def shape (p : CoreTerm.Prog) : List (String × List String × String × String) :=
  p.map fun d => (d.name, d.idx, d.arg, toString (repr d.body))

-- The frontend's program of `ret0.w` is `ret0Src`.
#guard match Frontend.run (w_src% "Scc/Test/ret0.w") with
  | .ok c => shape c.prog == shape Spike.Lib.Ret0Src.ret0Src &&
      c.prog.map (·.argTy) == [.unit] && c.prog.map (·.retTy) == [.int] &&
      c.prog.all (·.tparams.isEmpty)
  | .error _ => false

#guard !hello1Src.isEmpty

/-! ## `ret0.w` -/

/-- The emission of `ret0.w`, or the empty one. -/
def ret0E : Emitted := lowerAll cfgA Spike.Lib.Ret0Src.ret0Src

#guard (lowerAll? cfgA Spike.Lib.Ret0Src.ret0Src).isOk

#guard decide (ret0E.prog = SccCode.ret0Prog)

#guard ret0E.secs.data == SccCode.ret0Secs.data && ret0E.secs.bss == SccCode.ret0Secs.bss &&
  ret0E.secs.rodata == SccCode.ret0Secs.rodata

#guard ret0E.low.budget.frames == SccCode.ret0Frames

#guard ret0E.need == some SccCode.ret0Need

#guard match ret0E.listing with
  | .ok l => l.text == SccCode.ret0Asm
  | .error _ => false

/-! ## `hello1.w` -/

/-- The emission of `hello1.w`, or the empty one. -/
def hello1E : Emitted := lowerAll cfgA hello1Src

#guard (lowerAll? cfgA hello1Src).isOk

#guard decide (hello1E.prog = SccCode.hello1Prog)

#guard hello1E.secs.data == SccCode.hello1Secs.data && hello1E.secs.bss == SccCode.hello1Secs.bss &&
  hello1E.secs.rodata == SccCode.hello1Secs.rodata

#guard hello1E.low.budget.frames == SccCode.hello1Frames

#guard hello1E.need == some SccCode.hello1Need

#guard match hello1E.listing with
  | .ok l => l.text == SccCode.hello1Asm
  | .error _ => false

/-! ## The fragment -/

#guard Accepted0 Spike.Lib.Ret0Src.ret0Src = true

#guard Accepted0 hello1Src = false

/-- `Accepted0` of `ret0.w`, by the kernel. -/
theorem ret0_accepted0 : Accepted0 Spike.Lib.Ret0Src.ret0Src = true := by decide

/-- `main` whose body is `n` checked `+`s of `1` to the previous result
(`let x0 = 0`, `let x(k+1) = xk + 1`, `ret xn`). -/
def chain (n : Nat) : CoreTerm.Prog :=
  let rec go : Nat → CoreTerm.Expr
    | 0 => .ret (.var s!"x{n}")
    | k + 1 => .let_ s!"x{n - k}" (.add (.var s!"x{n - k - 1}") (.lit 1)) (go k)
  match Spike.Lib.Ret0Src.ret0Src with
  | [d] => [{ d with body := .let_ "x0" (.atom (.lit 0)) (go n) }]
  | p => p

-- The bound on the body's `+`s is exact: 508 are accepted, 509 are not.
#guard Accepted0 (chain 3) = true
#guard Accepted0 (chain 508) = true
#guard Accepted0 (chain 509) = false

end Spike.Test.LowerSpecA64
