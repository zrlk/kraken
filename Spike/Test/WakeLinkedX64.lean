import Spike.Test.WakeLinkedX64A1
import Spike.Test.WakeLinkedX64A2
import Spike.Test.WakeLinkedX64A3
import Spike.Test.WakeLinkedX64A4
import Spike.Test.WakeLinkedX64A5
import Spike.Test.WakeLinkedX64A6
import Spike.Test.WakeLinkedX64A7
import Spike.Test.WakeLinkedX64A8
import Spike.Test.WakeLinkedX64A9
import Spike.Test.WakeLinkedX64A11
import Spike.Test.WakeLinkedX64A12c
import Spike.Test.WakeLinkedX64A12p
import Spike.Test.WakeLinkedX64A13
import Spike.Test.WakeLinkedX64Fill
import Scc.Sem.SrcOut
import Scc.Cert.SrcTerm
import Scc.Test.Src
import Scc.Sem.CorrectEX64

/-!
# `wake.w` on x86-64 at the linked executable's layout `Λe`

The x86-64 twin of `Spike/Test/WakeLinkedA64.lean`, layout part.
`WakeLinkedX64Elf` pins the executable (path, SHA, `Λe`). Decided at `Λe` (each
by `decide +kernel`, one module per component):

* `wake_placeOK2At`: `Scc.Cert.Spawn.X64.placeOK2At placeCfg Λe outLit` from
  A1–A9, A11', A12' (code and phases) and A13 (`placeOK2At_of`). x86-64 checks
  every component, unlike AArch64's `PlaceW` subset (A1, A2, A4, A6, A8);
* `wake_codeEnd`: the code the loader lays out from `outLit` fills `.text`
  exactly (`Scc.Cert.E2E.X64.codeFills`).

The statement itself, `WakeLinkedXGoal`, is a `Prop` here; it is proved by
the x86-64 root `Spike.Test.WakeLinkedX64Root.wake_linkedX` (downstream of this
module, so the statement is fixed before the proof). The source semantics `wakeSX` is the neutral
`Scc.Sem.SrcSem.srcPo` (upstream of AArch64's local copy `WakeT1.srcPo`) at the
certificate's `prog_src`, the frontend's reading of `wake.w`
(`Spike.Lib.WakeA64` imports AArch64's syntax and cannot be imported here).
`prog_src` is tied to `Scc/Test/wake.w` by evaluation (`SrcTerm.reads`, below);
`WakeT1.srcPo = SrcSem.srcPo` is `Spike.Test.WakeSrcPoEq.srcPo_eq`.
-/

namespace Spike.Test.WakeLinkedX64

open Scc.Sem
open SccCertificate (asm sizes labelOffs outLit placeCfg prog_src)

/-- **`placeOK2At` of wake's output at the executable's layout**, from its
components (`Scc.Cert.Spawn.X64.placeOK2At_of`). -/
theorem wake_placeOK2At : Scc.Cert.Spawn.X64.placeOK2At placeCfg Λe outLit = true :=
  Scc.Cert.Spawn.X64.placeOK2At_of wake_a1 wake_a2 wake_a3 wake_a4 wake_a5 wake_a6 wake_a7 wake_a8 wake_a9
    wake_a11 wake_a12c wake_a12p wake_a13

/-- **The code ends where the executable's code region does** (kernel-checked
in `WakeLinkedX64Fill`). -/
theorem wake_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size :=
  Scc.Cert.E2E.X64.codeEnd_eq_of_codeFills wake_codeFills

/-- **The source semantics of wake.w** at `n = 2` (the twin of `WakeA64.wakeS`). -/
abbrev wakeSX (arch : WeakMem.Arch) : SrcSem := SrcSem.source (SrcSem.srcPo 2 arch prog_src) prog_src

-- `prog_src` is the frontend's reading of `Scc/Test/wake.w` (evaluation; the x86-64 twin of
-- `Spike.Lib.WakeSrc.wakeSrcOk`, compared by printed forms).
#guard Scc.Cert.SrcTerm.reads (w_src% "Scc/Test/wake.w") prog_src

-- The loader check holds (evaluation; `wake_linkedX` takes it as `hP`).
#guard Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ outLit.prog outLit.secs

-- `placeOKAt` (without the spawn checks) fails at wake's output: a theorem taking it is vacuous here.
#guard !Scc.Cert.PlaceOK.X64.placeOKAt placeCfg Λe outLit

/-- **wake.w's x86-64 statement at `Λe`** (the goal of `wake_linkedX`): from the
loader check `hP` and the budget `hB` only, `CorrectE 2` at a layout `Λ` that
extends `Λe` with the root's immediate table (the twin of `Le.Λ`,
`{ Λe with imms := ie }`). -/
def WakeLinkedXGoal (ie : CoreTerm.Expr → String → Nat → Option Nat) : Prop :=
  ∀ {arch : WeakMem.Arch} {B : Budget},
    Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ outLit.prog outLit.secs = true →
    B.cells = Scc.Cert.PlaceOK.allocCells →
    Scc.Sem.X64.CorrectE 2 (wakeSX arch) { Λe with imms := ie } B ⟨asm, sizes, labelOffs⟩

end Spike.Test.WakeLinkedX64

/-- info: 'Spike.Test.WakeLinkedX64.wake_placeOK2At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.wake_placeOK2At
