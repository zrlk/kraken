import Scc.Cert.X64
import Scc.Cert.Sizes
import Scc.Cert.Rt.LayoutX64
import Scc.Test.Src

/-!
# Code at labels of an emitted x86-64 program

The checks of `Scc/Cert/Rt/LayoutX64.lean` on the program scc emits for
`hello.w`, laid out with the assembler's sizes (`Scc.Cert.Sizes.sizesOf`,
GNU `as` and `objdump` at elaboration time, as `scc --cert` does): the
prologue of `scc_rt_print` and its fall-through to `.Lscc_rt_print.entry`,
by `decide +kernel`.
-/

namespace Scc.Test.RtX64

open Kraken.Promising.X64 Scc.Cert.Rt.X64

/-- scc's x64 listing of `hello.w`. -/
def helloAsm : String :=
  match Scc.Cert.X64.compile {} (w_src% "Scc/Test/hello.w") with
  | .ok s => s
  | .error _ => ""

/-- The listing, parsed by Kraken. -/
def helloProg : _root_.Program := scc_x64_reparse% helloAsm

open Lean Elab Term in
/-- `x64_sizes% c`: the assembler's size table of the text constant `c`. -/
elab "x64_sizes% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let text ← unsafe evalConst String n
  match ← Scc.Cert.Sizes.sizesOf ".lake/scc-rtx64-test" text with
  | .ok (sizes, _) => return toExpr sizes
  | .error msg => throwError "cannot size the text: {msg}"

/-- The size table. -/
def helloSizes : List Nat := x64_sizes% helloAsm

/-- The laid-out cells. -/
def helloCells : List (_root_.Directive × Nat) := (sizedCells helloProg helloSizes).getD []

/-- info: some 5 -/
#guard_msgs in
#eval (run helloCells "scc_rt_print").length |> fun n => if n = 0 then none else some n

/-- The prologue: `pushq %rbp` (1 byte), `movq %rsp, %rbp` (3), `subq $32, %rsp` (4), two stores (4 each). -/
theorem print_entry : labelGap helloCells "scc_rt_print" ".Lscc_rt_print.entry" 5 16 = true := by
  decide +kernel

end Scc.Test.RtX64
