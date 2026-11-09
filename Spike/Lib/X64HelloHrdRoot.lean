/-
**`wc_rodata`'s level obligations at a frame condition holding for no memory** (x86-64; the twin of
`Spike/Lib/A64HelloHrdRoot.lean`'s live part): `HelloRd.RdPreW` is vacuous when the frame condition holds for no
memory. The root's `hrd` (`X64HelloHrdRootX.hrd_RX`) uses it at every first-stack top `v` but the actual one: the
start's frame condition `FS` pins `v` at the first stack's top.

- `rdPreW_vac`: `RdPreW` at a frame condition holding for no memory.

## Unlike AArch64

- `rdPreW_vac`'s prologue is x86-64's five-node `XProW` (AArch64 `ProW`, four).
- The root's `hrd` (AArch64 `hrd_R`, `hrd_RdH`, at `ownGH`) is at `ownGHXW`: `X64HelloHrdRootX.hrd_RX`, `hrd_RdHX`;
  the region and allocator differences (`MainGlue.RS helloLsw v`, `.Lwc_rodata.x0`, `%fs`'s base) are listed
  there.
- AArch64's `hrd_RH` (at `Land.CtxRH`) is dead and not twinned.
-/
import Spike.Lib.X64HelloHrdArena
import Spike.Lib.X64HelloHrdS
import Spike.Lib.X64HelloHrdTp
import Spike.Lib.X64HelloLandRU
import Spike.Lib.X64HelloHrdR
import Spike.Lib.X64WakeRootUL
import Spike.Lib.X64WakeTP
import Spike.Lib.X64WakeHClC

namespace Spike.Lib.X64.HelloPh.HrdRoot

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Frag MemSide Region)
open Spike.Lib.X64.Flow.HelloRd (RdPreW)
open Spike.Lib.X64.WakePh.WcWfR (blkW_vac nodeW_vac allocW_vac)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-- **`wc_rodata` up to the allocator's return at a frame condition holding for no memory** (`WcWfR.blkW_vac`,
`nodeW_vac`, `allocW_vac` per field). -/
theorem rdPreW_vac {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {J0 J1 : FAS → Spike.Lib.Ctl → Prop}
    (hF : ∀ m, ¬ F m) : RdPreW W K exe endPc R F ms J0 J1 :=
  ⟨⟨blkW_vac hF, blkW_vac hF, nodeW_vac hF, blkW_vac hF, blkW_vac hF⟩, blkW_vac hF,
    fun _ _ _ => allocW_vac fun m h => hF m h.1⟩

end Spike.Lib.X64.HelloPh.HrdRoot

/-- info: 'Spike.Lib.X64.HelloPh.HrdRoot.rdPreW_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdRoot.rdPreW_vac
