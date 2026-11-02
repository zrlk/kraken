import Spike.Test.HelloLinkedX64Le
import Spike.Lib.X64HelloRootFinal

/-!
# `hello.w` on x86-64 at the linked executable's layout `Λe`

`RootFinal.hello_correct` instantiated at `Λe` (`HelloLinkedX64Elf`: path, SHA, `Λe`), at the layout facts
`layoutEX_e : LayoutEX Λe` (every field decided in `HelloLinkedX64Le`).

- `hello_linkedX`: the fixed goal `HelloLinkedXGoal Λe iH` (`HelloLinkedX64`).
- `hello_linkedX_linux`: non-vacuity. The Linux entry is admissible at `Le.Λ` (`linux_ok_e`), so the
  statement gives `Correct` at the Linux kernel target.

Its other premises are the goal's: the loader's check `hparse` (the trust boundary, also checked by evaluation
below) and the budget `hB`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The statement is the fixed goal `HelloLinkedXGoal Λe iH`: its source semantics is `helloSX` (`helloS_eq`) and
  its layout `{ Λe with imms := iH }`, `Le.Λ` by `rfl` (AArch64: `hello_linkedA` at `HelloSrc.helloS` and `Le.Λ`).
- The layout facts are `LayoutEX` (`HelloLinkedX64Le.layoutEX_e`), not `LayoutE`.
-/

namespace Spike.Test.HelloLinkedX64

-- The loader check holds (evaluation; the statement takes it as `hparse`).
#guard Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs

/-- **hello.w's x86-64 statement at `Λe`** (`HelloLinkedXGoal Λe iH`): every layout fact decided; open the loader
check `hparse` and the budget's cells `hB`. -/
theorem hello_linkedX : HelloLinkedXGoal Λe iH := fun {arch} {B} hparse hB => by
  rw [← helloS_eq]
  exact Spike.Lib.X64.HelloPh.RootFinal.hello_correct layoutEX_e hparse hB

/-- **Non-vacuity**: the Linux entry is admissible at `Le.Λ` (`linux_ok_e`), so `CorrectE` there gives `Correct`
at the Linux kernel target. -/
theorem hello_linkedX_linux {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.Correct (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) .linux)
      (Spike.Lib.X64HelloSrc.helloS arch) Le.Λ B SccCode.helloAsm :=
  Spike.Lib.X64.HelloPh.RootFinal.hello_correct layoutEX_e hparse hB _ linux_ok_e

end Spike.Test.HelloLinkedX64

/-- info: 'Spike.Test.HelloLinkedX64.hello_linkedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedX64.hello_linkedX

/-- info: 'Spike.Test.HelloLinkedX64.hello_linkedX_linux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedX64.hello_linkedX_linux
