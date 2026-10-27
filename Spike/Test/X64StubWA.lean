/-
**The write abort path inside `SFactsA`** (`Spike/Lib/X64StubWA.lean`): the
dispatcher's prologue keeps `%rdi`, and `stubWW_sfactsA` and its node lemmas
rest on the standard axioms only.
-/
import Spike.Lib.X64StubWA

namespace Spike.Lib.X64.StubW.Test

open Kraken Kraken.Promising.X64

/-- Before the prologue's last instruction `%rdi` is the entry's. -/
example (lab : Label → Int64) (pc : Int64) (σ : Spike.Lib.X64.AS) :
    (Spike.Lib.X64.arun lab (Abort.Disp.d0.take 3) ⟨pc, Abort.oE, σ⟩).σ.regs.get64 .rdi =
      σ.regs.get64 .rdi :=
  d0_rdi pc σ (by decide)

/-- The write stub's system call is in the write abort phase's pcs. -/
example (lab : Label → Int64) : Abort.pcSys lab Abort.write ∈ Spike.Lib.X64.WriteAb.stubPcs lab := memSys

/-- info: 'Spike.Lib.X64.StubW.stubWW_sfactsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stubWW_sfactsA

/-- info: 'Spike.Lib.X64.StubW.blkW_writeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blkW_writeA

/-- info: 'Spike.Lib.X64.StubW.sfactsA_sysW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sfactsA_sysW

end Spike.Lib.X64.StubW.Test
