/-
**The write abort path inside `SFactsA`** (`Spike/Lib/A64StubWA.lean`): the
dispatcher's prologue keeps `x0`, and `stubWW_sfactsA` and its node lemmas
rest on the standard axioms only.
-/
import Spike.Lib.A64StubWA

namespace Spike.Lib.A64.StubW.Test

open Kraken Kraken.Promising.AArch64

/-- Before the prologue's last instruction `x0` is the entry's. -/
example (lab : Label → Int64) (pc : Int64) (σ : Spike.Lib.A64.Flow.AS) :
    (Spike.Lib.A64.Flow.arun lab (Abort.Disp.d0.take 4) ⟨pc, Abort.oE, σ⟩).σ.regs.X0 = σ.regs.X0 :=
  d0_x0 pc σ (by decide)

/-- The write stub's system call is in the write abort phase's pcs. -/
example (lab : Label → Int64) : Abort.pcSvc lab Abort.write ∈ Spike.Lib.A64.WriteAb.stubPcs lab := memSvc

/-- info: 'Spike.Lib.A64.StubW.stubWW_sfactsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stubWW_sfactsA

/-- info: 'Spike.Lib.A64.StubW.blkW_writeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blkW_writeA

/-- info: 'Spike.Lib.A64.StubW.sfactsA_svcW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sfactsA_svcW

end Spike.Lib.A64.StubW.Test
