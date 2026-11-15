import Scc.Cert.Sizes
import Scc.Emit.GranuleX64
import Scc.Emit.X64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# The assembler's size table of a granule-placed x64 text

`hello.w`'s x64 items through the granule pass (`Scc.Emit.Granule.granuleX64`),
sized by GNU `as` (`Scc.Cert.Sizes.sizesOf`, at elaboration time): the filler
`.zero k` and the descriptor word `.quad scc_gc_desc - .` are cells of `k` and 8
bytes, `.text` is exactly one granule (the empty `.text.scc_galign` section
of the tail is not counted), and the table is the pass's own layout without
its empty items (labels and directive lines).
-/

namespace Scc.Test.SizesGranule
open Scc.Emit.X64 Scc.Emit.Granule

/-- `hello.w`'s x64 items, placed in granules, and their text. -/
def placed : Except String (List Item × String) := do
  let c ← match Frontend.run (w_src% "Scc/Test/hello.w") with
    | .ok c => pure c
    | .error _ => throw "frontend"
  let ir ← Lower.lowerProgram { arch := .x64 } c
  let out ← granuleX64 ir (← emitItems ir)
  pure (out, ← render out)

/-- The text, with a definition of `scc_gc_desc` (which the runtime will
provide) so that it assembles. -/
def placedAsm : String :=
  match placed with
  | .ok (_, s) => s ++ "\t.section .rodata\n\t.balign 8\n\t.globl scc_gc_desc\nscc_gc_desc:\n\t.quad 0\n"
  | .error _ => ""

/-- The pass's layout without its empty items. -/
def planned : List Nat :=
  match placed with
  | .ok (out, _) => ((layout isaX64 out).toOption.getD []).filter (· != 0)
  | .error _ => []

open Lean Elab Term in
/-- `x64_sizes% c`: the assembler's size table of the text constant `c`. -/
elab "x64_sizes% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let text ← unsafe evalConst String n
  match ← Scc.Cert.Sizes.sizesOf ".lake/scc-sizes-granule-test" text with
  | .ok (sizes, _) => return toExpr sizes
  | .error msg => throwError "cannot size the text: {msg}"

/-- The assembler's table. -/
def sizes : List Nat := x64_sizes% placedAsm

#guard sizes.sum == granule
#guard sizes.getLast? == some 8
#guard sizes == planned
#guard planned.length > 100

end Scc.Test.SizesGranule
