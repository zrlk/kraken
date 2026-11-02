import Spike.Test.HelloLinkedX64L1
import Spike.Lib.X64HelloRootBaseInh

/-!
# `hello.w` on x86-64: the root base and premises at `Λ1` (non-vacuity of `HelloRootBase` at `ms2HX`)

At `Λ1`'s `layoutEX_1` (`Spike/Test/HelloLinkedX64L1.lean`), `RootBaseInh.LayoutEX.baseEX` and `premEX` build
hello's root base at `H2RtX.ms2HX` and the root premises `HelloRootPremX` from the listing's parse alone.

Unlike AArch64 (`Spike/Test/A64HelloRootBaseInhSmoke.lean`, which decides `LayoutE` here), the layout facts are
`HelloLinkedX64L1`'s, and the base and premises are at main's owned words with the self words (`ownGHXW`).
-/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.HelloImms (iRdM)

/-- **The root's base at `Λ1`** at `ms2HX`, from the listing's parse. -/
noncomputable example
    (hparse : Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) :
    Spike.Lib.X64.HelloPh.HelloRootBase L1 (Spike.Lib.X64WakeLoadT.L0T L1.Λ)
      (Spike.Lib.X64.WakeOD.arW placeWX_1 (iRdM Λ1))
      (Spike.Lib.X64.HelloPh.H2RtX.ms2HX SccCode.helloAsm placeWX_1 (iRdM Λ1) E) :=
  layoutEX_1.baseEX hparse E ls

/-- **The root's premises at `Λ1`** (`HelloRootPremX`), from the listing's parse. -/
noncomputable example
    (hparse : Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.X64Consumer.Lsize) :
    Spike.Lib.X64.HelloPh.HelloRootPremX L1 (Spike.Lib.X64WakeLoadT.L0T L1.Λ) :=
  layoutEX_1.premEX hparse E ls

end Spike.Test.HelloLinkedX64
