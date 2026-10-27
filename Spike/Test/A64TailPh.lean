import Spike.Lib.A64TailPh
import Spike.Lib.A64Hello1Code

/-!
# The write tail's phase check on `hello1.w` (AArch64)

`tailOffC` (`Spike/Lib/A64TailPh.lean`) holds on `hello1.w` at its link,
and fails closed: with the release site's label at `scc_rt_print`'s loop
head (a site there, so that pc is not off the sites), and with the label
`.L9_scc_rt_print.7_done` renamed (a branch target that does not resolve).
-/

namespace Spike.Test.A64TailPh

open Kraken Scc.Cert.Link.A64 SccCode

/-- The check holds at `hello1.w`'s link. -/
example : Spike.Lib.A64.StubW.tailOffC (linkOf hello1Prog hello1Secs).code.lo (linkOf hello1Prog hello1Secs)
    hello1Prog = true := by
  decide +kernel

/-- An unresolved branch target fails it. -/
example :
    let p := hello1Prog.map fun d => if d == .label ".L9_scc_rt_print.7_done" then .label ".Lx" else d
    Spike.Lib.A64.StubW.tailOffC (linkOf hello1Prog hello1Secs).code.lo (linkOf hello1Prog hello1Secs) p = false := by
  decide +kernel

/-- The release site at the loop head fails it. -/
example :
    let q := (hello1Prog.map fun d => if d == .label "scc_rt_release_site" then .label ".Ly" else d).flatMap
      fun d => if d == .label ".L9_scc_rt_print.1_loop" then [.label "scc_rt_release_site", d] else [d]
    Spike.Lib.A64.StubW.tailOffC (linkOf hello1Prog hello1Secs).code.lo (linkOf hello1Prog hello1Secs) q = false := by
  decide +kernel

end Spike.Test.A64TailPh
