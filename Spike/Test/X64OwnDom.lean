/-
**The private-memory domain invariant along the x86-64 runs**
(`Kernel.OwnDom`, `Scc/Sem/OwnDom.lean`; checker `Scc/Sem/Test/OwnDomCheck.lean`):
the x64 twin of `Spike/Test/A64OwnDom.lean`, for the emitted `ret0.w` and
`hello1.w` (`SccCode.ret0Asm`, `SccCode.hello1Asm`) under `Arch.tso`: the
same checks, the same outcome (one take, no release, no failure).
-/
import Scc.Sem.Test.RunX64
import Scc.Sem.Test.OwnDomCheck
import Spike.Lib.X64Ret0Code
import Spike.Lib.X64Hello1Code

namespace Spike.Test.X64OwnDom

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Test Scc.Sem.Test.RunX64

/-- `checkRun` on the run of `a` from its load. -/
def check (a : Asm) (cells : List (Directive × Nat)) : Option DomRun :=
  let Λ := (layoutIn a cells).1
  ((target (kernel slots) Entry.linux).load a Λ).map fun c =>
    checkRun abi Arch.tso pcOf (marksIn cells) Entry.linux.stack 4000 0 c {}

/-- info: (some { steps := 277, stop := "exited", cheap := 278, full := 3, takes := 1, releases := 0, bad := none },
 some { steps := 480, stop := "exited", cheap := 481, full := 3, takes := 1, releases := 0, bad := none }) -/
#guard_msgs in
#eval (check SccCode.ret0Asm SccCode.ret0Cells, check SccCode.hello1Asm SccCode.hello1Cells)

end Spike.Test.X64OwnDom
