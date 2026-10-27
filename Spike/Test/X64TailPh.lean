import Spike.Test.X64Hello1PlaceOKELit
import Spike.Test.X64Ret0PlaceOKELit
import Spike.Lib.X64TailPh

/-!
# The write tail's phase check on scc's own x86-64 outputs

`tailOffC` (`Spike/Lib/X64TailPh.lean`) decided by the kernel on
`hello1.w`'s and `ret0.w`'s outputs at their static links: `scc_rt_print`,
the dispatcher's code-2 and code-4 paths and the heap and write stubs are off
the sites and in their phases in both.
-/

namespace Spike.Test.X64TailPh

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.StubW (tailOffC)

set_option maxRecDepth 100000

theorem hello1_tailOff :
    tailOffC (tablesOf Config.canonical Spike.Test.X64Hello1PlaceOKE.hello1L).Λ.code.lo
      (tablesOf Config.canonical Spike.Test.X64Hello1PlaceOKE.hello1L).Λ
      Spike.Test.X64Hello1PlaceOKE.hello1L.prog = true := by
  decide +kernel

theorem ret0_tailOff :
    tailOffC (tablesOf Config.canonical Spike.Test.X64Ret0PlaceOKE.ret0L).Λ.code.lo
      (tablesOf Config.canonical Spike.Test.X64Ret0PlaceOKE.ret0L).Λ
      Spike.Test.X64Ret0PlaceOKE.ret0L.prog = true := by
  decide +kernel

end Spike.Test.X64TailPh
