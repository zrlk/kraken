import Scc.Lower.SpecX64
import Scc.Test.Src
import Spike.Lib.Ret0Src
import Spike.Lib.X64Ret0Code
import Spike.Lib.X64Hello1Code

/-!
# `lowerAll` on x86-64 against what `scc --code` emits

`Scc.Lower.X64.lowerAll` on `ret0.w` and `hello1.w` gives the instruction
list, the data sections, the stack depth limit and the stack need table of
the committed `scc --arch arm --code` outputs (`Spike/Lib/A64Ret0Code.lean`,
`Spike/Lib/A64Hello1Code.lean`), and its rendered items are their assembler
text. `Accepted0` holds of `ret0.w` and not of `hello1.w`.
-/

namespace Spike.Test.LowerSpecX64

open Scc Scc.Lower Scc.Lower.X64

/-- The x86-64 configuration. -/
def cfgX : Config := { arch := .x64 }

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
def ret0E : Emitted := lowerAll cfgX Spike.Lib.Ret0Src.ret0Src

#guard (lowerAll? cfgX Spike.Lib.Ret0Src.ret0Src).isOk

#guard decide ((ret0E.prog.bind (Kraken.Promising.X64.sizedCells · SccCode.ret0Asm.sizes)) = some SccCode.ret0Cells)

#guard ret0E.secs.data == SccCode.ret0Secs.data && ret0E.secs.bss == SccCode.ret0Secs.bss &&
  ret0E.secs.rodata == SccCode.ret0Secs.rodata

#guard ret0E.low.budget.frames == SccCode.ret0Frames

#guard ret0E.need == some SccCode.ret0Need

#guard match ret0E.listing with
  | .ok l => l.text == SccCode.ret0Text
  | .error _ => false

/-! ## `hello1.w` -/

/-- The emission of `hello1.w`, or the empty one. -/
def hello1E : Emitted := lowerAll cfgX hello1Src

#guard (lowerAll? cfgX hello1Src).isOk

#guard decide ((hello1E.prog.bind (Kraken.Promising.X64.sizedCells · SccCode.hello1Asm.sizes)) = some SccCode.hello1Cells)

#guard hello1E.secs.data == SccCode.hello1Secs.data && hello1E.secs.bss == SccCode.hello1Secs.bss &&
  hello1E.secs.rodata == SccCode.hello1Secs.rodata

#guard hello1E.low.budget.frames == SccCode.hello1Frames

#guard hello1E.need == some SccCode.hello1Need

#guard match hello1E.listing with
  | .ok l => l.text == SccCode.hello1Text
  | .error _ => false

/-! ## The fragment -/

#guard Accepted0 Spike.Lib.Ret0Src.ret0Src = true

#guard Accepted0 hello1Src = false

/-- `Accepted0` of `ret0.w`, by the kernel. -/
theorem ret0_accepted0 : Accepted0 Spike.Lib.Ret0Src.ret0Src = true := by decide

end Spike.Test.LowerSpecX64
