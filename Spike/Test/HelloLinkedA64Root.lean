import Spike.Test.HelloLinkedA64
import Spike.Lib.A64HelloRootFinal

/-!
# `hello.w` on AArch64 at the linked executable's layout `Λe`

`RootFinal.hello_correct` instantiated at `Λe` (`HelloLinkedA64Elf`: path, SHA, `Λe`): the layout facts
`layoutE_e : LayoutE Λe` (`placeW_e`, `hlo`, `hstat`, `hnz`, `hA13_e`, `hinit2`, all decided in `HelloLinkedA64`),
`HelloRootPrem` at `Le` from them (`LayoutE.premE`, the root's premises' non-vacuity at a real `ld.lld` layout), and
`hello_linkedA`: `CorrectE 2` at `Le.Λ` for every budget with the certificate's heap cells, from the loader check
`hparse` (the trust boundary, also checked by evaluation below).
-/

namespace Spike.Test.HelloLinkedA64

open Spike.Lib.A64.HelloPh.RootBaseInh (LayoutE)

/-- **hello's layout facts at `Λe`.** -/
theorem layoutE_e : LayoutE Λe := ⟨placeW_e, hlo, hstat, hnz, hA13_e, hinit2⟩

/-- The root's premises at `Le` from the layout facts (non-vacuity). -/
noncomputable example (hparse : Scc.Cert.Link.A64.parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (E : Scc.Sem.Entry) (ls : Spike.Lib.A64Consumer.Lsize) :
    Spike.Lib.A64.HelloPh.HelloRootPrem Le (Spike.Lib.WakeLoadT.L0T Le.Λ) :=
  layoutE_e.premE hparse E ls

-- The loader check holds (evaluation; `hello_linkedA` takes it as `hparse`).
#guard Scc.Cert.Link.A64.parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs

/-- **hello.w's AArch64 statement at the linked executable's layout**: `CorrectE 2` at `Le.Λ`, every layout fact
decided; open the loader check `hparse` and the budget's cells `hB`. -/
theorem hello_linkedA {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    (hparse : Scc.Cert.Link.A64.parsesTo SccCode.helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.A64.CorrectE 2 (Spike.Lib.HelloSrc.helloS arch) Le.Λ B SccCode.helloAsm :=
  Spike.Lib.A64.HelloPh.RootFinal.hello_correct layoutE_e hparse hB

end Spike.Test.HelloLinkedA64

/-- info: 'Spike.Test.HelloLinkedA64.layoutE_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.layoutE_e

/-- info: 'Spike.Test.HelloLinkedA64.hello_linkedA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedA64.hello_linkedA
