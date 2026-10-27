/-
**The source at `print`'s output `write`**, on any ISA: the pair-local fact
the per-pair facts (`W2`'s `svc1`) carry at a `write(1, buf, n)` system
call, from which the emit rows (`EmitA`) of the consumer through `print`'s
`write` are derived from the fragment's own closure.

- `PrintSvc c fs`: the source is inside a call (`fs ≠ []`) at the top of
  `printL` (`PrintSrc.PrintC`) with a byte left (`k < printN n m`).
-/
import Spike.Lib.PrintSrc

namespace Spike.Lib.PrintSvc

open CoreLang CoreTerm
open Spike.Lib

/-- At the output `write(1, …)` the source is at print's loop top, inside a call. -/
def PrintSvc (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  fs ≠ [] ∧ ∃ pw wn n m k, PrintSrc.PrintC pw wn n m k c ∧ k < PrintSrc.printN n m

end Spike.Lib.PrintSvc
