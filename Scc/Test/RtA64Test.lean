import Scc.Cert.Arm
import Scc.Cert.Rt.A64Print
import Scc.Cert.Rt.A64Morestack
import Scc.Test.Src

/-!
# Runtime routines in emitted AArch64 programs

`morestackIn` (`Scc/Cert/Rt/A64Morestack.lean`) holds of the program scc
emits for `hello.w`, by `decide +kernel`: `seg_morestack` applies to every
valid layout of it. (`printIn`, `Scc/Cert/Rt/A64Print.lean`, describes the
unfenced print of a spawn-free program; see below.)
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

-- No `printIn` for `hello.w`: it spawns, so its `scc_rt_print` has the
-- barrier before `write` (`Runtime.printF`), which `printIn` (the unfenced
-- routine) does not describe. Removed until the fenced variant `printInF`
--; `hello1.w`'s print keeps `printIn`
-- (`Spike/Test/A64Hello1Print.lean`).

theorem hello_morestackIn : Scc.Cert.Rt.A64.Morestack.morestackIn helloProg = true := by decide +kernel

end Scc.Test.RtA64
