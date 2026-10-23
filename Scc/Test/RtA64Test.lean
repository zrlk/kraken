import Scc.Cert.Arm
import Scc.Cert.Rt.A64Print
import Scc.Cert.Rt.A64Morestack
import Scc.Test.Src

/-!
# Runtime routines in emitted AArch64 programs

`printIn` (`Scc/Cert/Rt/A64Print.lean`) and `morestackIn`
(`Scc/Cert/Rt/A64Morestack.lean`) hold of the program scc emits for
`hello.w`, by `decide +kernel`: `seg_print_of` and `seg_morestack` apply to
every valid layout of it.
-/

namespace Scc.Test.RtA64

open Kraken.Promising.AArch64

/-- scc's AArch64 listing of `hello.w`. -/
def helloAsm : String :=
  match Scc.Cert.Arm.compile { arch := .arm } (w_src% "Scc/Test/hello.w") with
  | .ok s => s
  | .error _ => ""

/-- The listing, parsed by Kraken. -/
def helloProg : Program := scc_arm_reparse% helloAsm

theorem hello_printIn : Scc.Cert.Rt.A64.Print.printIn helloProg = true := by decide +kernel

theorem hello_morestackIn : Scc.Cert.Rt.A64.Morestack.morestackIn helloProg = true := by decide +kernel

end Scc.Test.RtA64
