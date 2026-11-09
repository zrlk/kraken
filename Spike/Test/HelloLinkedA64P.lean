import Spike.Test.HelloLinkedA64Root
import Scc.Sem.PlatformA64

/-!
# `hello.w` on AArch64 in `CorrectP` form

`hello_linkedA` restated at the Linux platform (`Scc.Sem.A64.linuxPlatform`) by `CorrectE.toP`, which is `rfl`
(`Scc.Sem.A64.correctE_eq_correctP`): no new proof. Scaffolding (`Scc/Sem/Platform.lean`).
-/

namespace Spike.Test.HelloLinkedA64

/-- **hello.w's AArch64 statement at `Le.Λ` in `CorrectP` form**: `hello_linkedA` at the Linux platform. -/
theorem hello_linkedA_P {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : Scc.Cert.Link.A64.parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.A64.CorrectP Scc.Sem.A64.linuxPlatform 2 (Spike.Lib.HelloSrc.helloS arch) Le.Λ B SccCode.helloAsm :=
  Scc.Sem.A64.CorrectE.toP (hello_linkedA hparse hB)

end Spike.Test.HelloLinkedA64

/-- info: 'Spike.Test.HelloLinkedA64.hello_linkedA_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.hello_linkedA_P
