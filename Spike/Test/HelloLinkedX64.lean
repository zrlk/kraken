import Scc.Sem.SrcOut
import Scc.Cert.SrcTerm
import Scc.Test.Src
import Scc.Sem.CorrectEX64
import Scc.Cert.SpawnX64
import Spike.Lib.X64HelloCode
import Spike.Lib.X64HelloSrc
import Spike.Lib.X64HelloOut

/-!
# `hello.w` on x86-64: the statement

The x86-64 twin of `Spike/Test/HelloLinkedA64.lean`, statement part, fixed before the proof
(every module of the proof is downstream of this one).

* `helloSX arch`: the source semantics of hello.w at `n = 2`, the neutral
  `Scc.Sem.SrcSem.srcPo` at `Spike.Lib.X64HelloSrc.helloSrc` (the frontend's reading of
  `Scc/Test/hello.w`, `#guard`ed below); `helloS_eq` identifies the proof's `helloS` with it.
* `HelloGoalAt Λ`: from the loader's check `hparse` and the budget `hB` only, `CorrectE 2` of
  hello's listing `SccCode.helloAsm` at the layout `Λ`.
* `HelloLinkedXGoal Λ0 iH`: `HelloGoalAt` at `{ Λ0 with imms := iH }`, the layout of an
  executable `Λ0` extended with the root's immediate table `iH`. At the checked-in
  executable's layout `Λe` (`HelloLinkedX64Elf`, with the fixture) it is the twin of
  `WakeLinkedXGoal`.

The program, its sections and the code are the listing's (`SccCode.helloCells`,
`SccCode.helloSecs`, `Spike/Lib/X64HelloCode.lean`): the loader's parse is the trust boundary
(`hparse`, by evaluation below).

Unlike AArch64 (`hello_linkedA` at `Spike.Lib.HelloSrc.helloS`, `Le.Λ`), the source semantics
is the neutral `SrcSem.srcPo` form (as x86-64 wake's `wakeSX`), and the statement is stated
at a layout parameter `Λ0` until the executable's layout `Λe` is pinned. Unlike x86-64 wake
(`WakeLinkedXGoal`, at the certificate's `asm`, `outLit`, `prog_src`), it names the listing's
`SccCode.*` and `helloSrc`, not `SccCertificate.*`: the proof does not import hello's
certificate (wake's is in its closure).
-/

namespace Spike.Test.HelloLinkedX64

open Scc.Sem

/-- **The source semantics of hello.w** at `n = 2` (the twin of `HelloSrc.helloS`). -/
abbrev helloSX (arch : WeakMem.Arch) : SrcSem :=
  SrcSem.source (SrcSem.srcPo 2 arch Spike.Lib.X64HelloSrc.helloSrc) Spike.Lib.X64HelloSrc.helloSrc

/-- The proof's source semantics (`X64HelloSrc.helloS`, through `X64WakeT1.srcPo`) is the goal's. -/
theorem helloS_eq (arch : WeakMem.Arch) : Spike.Lib.X64HelloSrc.helloS arch = helloSX arch :=
  Spike.Lib.X64HelloSrc.helloS_eq arch

-- `helloSrc` is the frontend's reading of `Scc/Test/hello.w` (evaluation).
#guard Scc.Cert.SrcTerm.reads (w_src% "Scc/Test/hello.w") Spike.Lib.X64HelloSrc.helloSrc

-- The loader check holds (evaluation; the goal takes it as `hparse`).
#guard Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs

/-- **hello.w's x86-64 statement at a layout `Λ`**: from the loader's check `hparse` and the
budget `hB` only, `CorrectE 2` of hello's listing at `Λ`. -/
def HelloGoalAt (Λ : Scc.Sem.Layout) : Prop :=
  ∀ {arch : WeakMem.Arch} {B : Scc.Sem.Budget},
    Scc.Cert.Link.X64.parsesTo SccCode.helloAsm SccCode.helloCells SccCode.helloSecs = true →
    B.cells = Scc.Cert.PlaceOK.allocCells →
    Scc.Sem.X64.CorrectE 2 (helloSX arch) Λ B SccCode.helloAsm

/-- **hello.w's x86-64 statement at an executable's layout `Λ0`** extended with the root's
immediate table `iH` (the twin of `WakeLinkedXGoal ie` at `Λ0 := Λe`). -/
def HelloLinkedXGoal (Λ0 : Scc.Sem.Layout) (iH : CoreTerm.Expr → String → Nat → Option Nat) : Prop :=
  HelloGoalAt { Λ0 with imms := iH }

/-! ## A layout without an executable (non-vacuity) -/

/-- The static link of hello's listing with GNU `ld`'s section bases: the code at `0x401000`
(`X64.HelloPh.lo`, `ld`'s default `.text`) of the listing's `5651` bytes, `.rodata` at `0x403000`,
`.data` at `0x407a10`, the arena, pool and pinned region at the canonical bases. A concrete
layout at which the placement checks pass, no executable needed. -/
def Λ1 : Scc.Sem.Layout :=
  Scc.Cert.Link.link
    { Scc.Cert.Link.canonical with codeLo := 0x401000, codeSize := 5651, roLo := 0x403000, dataLo := 0x407a10 }
    SccCode.helloSecs (Scc.Sem.X64.codeLabel 0x401000 SccCode.helloCells)

-- hello's output passes `placeOK2At` at `Λ1` (evaluation; the components are decided by the layout modules).
#guard Scc.Cert.Spawn.X64.placeOK2At Spike.Lib.X64.HelloPh.RootLit.pcfgH Λ1 Spike.Lib.X64.HelloPh.RootLit.oH

-- `placeOKAt` (without the spawn checks) fails at hello's output: a theorem taking it is vacuous here.
#guard !Scc.Cert.PlaceOK.X64.placeOKAt Spike.Lib.X64.HelloPh.RootLit.pcfgH Λ1 Spike.Lib.X64.HelloPh.RootLit.oH

end Spike.Test.HelloLinkedX64

/-- info: 'Spike.Test.HelloLinkedX64.helloS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloLinkedX64.helloS_eq
