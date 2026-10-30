import Scc.Cert.SrcTerm
import Scc.Test.Src
import Spike.Lib.WakeA64

/-!
# `wake.w`'s source program is `wakeSrc`

`Spike.Lib.WakeT1.wakeSrc` (the source of `WakeA64.wakeS`, the program of
`Spike.Test.WakeLinkedA64.wake_linkedU`) is written out as a term so that the
kernel can reduce scc's pipeline on it (the frontend's parser is `partial`).
`wakeSrcOk` checks, by evaluation, that the frontend reads `Scc/Test/wake.w`
as it (`Scc.Cert.SrcTerm.reads`, as `Spike.Lib.Hello1Src.hello1SrcOk` for
`hello1.w`); `Spike.Test.WakeLinkedA64Root` imports this module, so its build
checks it.
-/

namespace Spike.Lib.WakeSrc

/-- **`wakeSrc` is the frontend's reading of `Scc/Test/wake.w`** (compared by
printed forms, `SrcTerm.reads`: `Decl` has no equality instance). -/
def wakeSrcOk : Bool := Scc.Cert.SrcTerm.reads (w_src% "Scc/Test/wake.w") Spike.Lib.WakeT1.wakeSrc

#guard wakeSrcOk

end Spike.Lib.WakeSrc
