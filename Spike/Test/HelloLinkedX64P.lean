import Spike.Test.HelloLinkedX64Root
import Scc.Sem.PlatformX64

/-!
# `hello.w` on x86-64 in `CorrectP` form

`hello_linkedX` restated at the Linux platform (`Scc.Sem.X64.linuxPlatform`) by `CorrectE.toP`, which is `rfl`
(`Scc.Sem.X64.correctE_eq_correctP`): no new proof. Scaffolding (`Scc/Sem/Platform.lean`).
-/

namespace Spike.Test.HelloLinkedX64

/-- **hello.w's x86-64 statement at `Λe` in `CorrectP` form**: `hello_linkedX` at the Linux platform. -/
theorem hello_linkedX_P {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.X64.CorrectP Scc.Sem.X64.linuxPlatform 2 (helloSX arch) { Λe with imms := iH } B SccCode.helloAsm :=
  Scc.Sem.X64.CorrectE.toP (hello_linkedX hparse hB)

end Spike.Test.HelloLinkedX64

/-- info: 'Spike.Test.HelloLinkedX64.hello_linkedX_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedX64.hello_linkedX_P
