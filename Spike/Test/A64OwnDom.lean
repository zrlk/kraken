/-
**The private-memory domain invariant along the AArch64 runs**
(`Kernel.OwnDom`, `Scc/Sem/OwnDom.lean`; checker `Scc/Sem/Test/OwnDomCheck.lean`):
the deterministic runs of the emitted `ret0.w` and `hello1.w` on the
canonical target (`target (kernel slots) Entry.linux`, `Arch.armv8`), from
the load to the exit, with `E := initDom Entry.linux`.

At every configuration each thread's private memory maps as many bytes as
its initial stack and its held ranges; at the load, the exit and on both
sides of every take and release it maps exactly those bytes; the held
ranges are nonempty, in the pool, live and disjoint; and before the take
no byte of the range is mapped (`OwnDom.take_unmapped`). Each program
takes once and releases nothing before the exit.
-/
import Scc.Sem.Test.RunA64
import Scc.Sem.Test.OwnDomCheck
import Spike.Lib.A64Ret0Code
import Spike.Lib.A64Hello1Code

namespace Spike.Test.A64OwnDom

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Test Scc.Sem.Test.RunA64

/-- `checkRun` on the run of `asm` from its load. -/
def check (asm : String) : Option DomRun :=
  let prog := progOf asm
  let Λ := (layoutIn asm prog).1
  ((target (kernel slots) Entry.linux).load asm Λ).map fun c =>
    checkRun abi Arch.armv8 pcOf (marksIn prog) Entry.linux.stack 4000 0 c {}

/-- info: (some { steps := 294, stop := "exited", cheap := 295, full := 3, takes := 1, releases := 0, bad := none },
 some { steps := 516, stop := "exited", cheap := 517, full := 3, takes := 1, releases := 0, bad := none }) -/
#guard_msgs in
#eval (check SccCode.ret0Asm, check SccCode.hello1Asm)

end Spike.Test.A64OwnDom
