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

-- No `printIn` theorem for `hello.w` here (yet). `printIn` now describes the
-- one AArch64 `scc_rt_print` every program has, spawning or not: `.2_write`
-- is led by the barrier `bF` (`dmb ish`, `Runtime.printF`) at offset 0, the
-- rest of the block one instruction on (`Scc/Cert/Rt/A64Print.lean`). So it is
-- the statement for `hello.w`'s print as for `hello1.w`'s
-- (`Spike/Test/A64Hello1Print.lean`); no separate fenced variant is needed.

theorem hello_morestackIn : Scc.Cert.Rt.A64.Morestack.morestackIn helloProg = true := by decide +kernel

end Scc.Test.RtA64
