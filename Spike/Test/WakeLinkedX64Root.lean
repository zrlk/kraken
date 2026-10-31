import Spike.Test.WakeLinkedX64RootL

/-!
# `wake.w` on x86-64 at `Λe`: the final root

`wake_linkedX : WakeLinkedXGoal ie` is `WakeLinkedX64RootL.wake_linkedXL` with
the per-entry label sizes `ls0` and frames `frM` fixed to constants: they
parametrise the root's invariants only (every leaf is closed for all of
them), so any choice gives the statement. Its premises are the goal's: the
loader's check `hP` (the trust boundary) and the budget `hB`.

The general forms stay importable: `WakeLinkedX64RootU.wake_linkedXU` (the
assembly from the per-entry rows and `hlo`) and `wake_linkedXL` (every row
closed, `ls0` and `frM` general).

Unlike AArch64 (`Spike/Test/WakeLinkedA64Root.lean`), where `wake_linkedU`
keeps `ls0` and `frM` general and the post file of `certify.sh` fixes them,
here the constants are fixed in this module, so the theorem is literally
`WakeLinkedXGoal ie` and the post file applies it to `hP` and `hB` only. The
constants are AArch64's post-file ones.
-/

namespace Spike.Test.WakeLinkedX64Root

open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Test.WakeLinkedX64
open SccCertificate (asm sizes labelOffs outLit)

/-- **wake.w's x86-64 statement at `Λe`** (`WakeLinkedXGoal ie`): from the
loader's check and the budget, `ls0`/`frM` fixed (see the module doc). -/
theorem wake_linkedX : WakeLinkedXGoal ie := fun {arch} {B} hP hB =>
  Spike.Test.WakeLinkedX64RootL.wake_linkedXL (arch := arch) (B := B) (fun _ _ => 0)
    (fun _ => ⟨"a", CoreTerm.Expr.ret CoreTerm.At.unit, [], [], CoreLang.Ty.unit⟩) hP hB

/-- The post file's use: applied to the loader's check and the budget. -/
example {arch : WeakMem.Arch} {B : Budget}
    (hP : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    Scc.Sem.X64.CorrectE 2 (wakeSX arch) { Λe with imms := Spike.Lib.X64.WakeImms.iW Λe } B
      ⟨asm, sizes, labelOffs⟩ := by
  rw [← Spike.Test.WakeLinkedX64Br.ie_eq]
  exact wake_linkedX hP hB

end Spike.Test.WakeLinkedX64Root

/-- info: 'Spike.Test.WakeLinkedX64Root.wake_linkedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64Root.wake_linkedX
