/-
**The semantic twins: fault freedom on the semantic machine**. The fault-freedom
theorems of `Kraken/Examples/LockFree/THEOREMS.md`
conclude `Config.FaultFree A fuel init`: no configuration `Reachable`
from `init` has a faulting step. Their `#sem_twin` twins (`ChainK/SemTwin.lean`)
conclude `Config.FaultFreeSem A fuel init`, the same with `ReachableSem`.

- `#chaink_clone` of `Faults.lean`, `EnvG/MemValsGen.lean` and
  `EnvG/MemVals.lean` gives the K-world `Config.FaultFreeK` and the
  K-world lemmas that the per-program fault-freedom clones use.
  `Config.FaultStep.mem_succs` is skipped: it is about `succs` itself.
- `Config.FaultFreeSem` is defined here.
- `Config.FaultFreeSem.of_K` transports `FaultFreeK` (any fuel) to
  `FaultFreeSem` from a bounded start (`ReachableK.of_reachableSem'`).
-/
import Kraken.Promising.SLR.ChainK.Final
import Kraken.Promising.Faults
import Kraken.Promising.SLR.EnvG.MemValsGen
import Kraken.Promising.SLR.EnvG.MemVals
import Kraken.Promising.PromProjection

open Kraken.Promising.Live.Bridge

#chaink_clone "../../Faults.lean" skip ["Config.FaultStep.mem_succs"]

#chaink_clone "../EnvG/MemValsGen.lean"

#chaink_clone "../EnvG/MemVals.lean"

namespace Kraken.Promising

open Kraken.Promising.Live.Bridge

variable {I : ISA}

/-- **Fault freedom on the semantic machine**: no configuration
`ReachableSem`-reachable from `init` (at certification fuel `fuel`) has a
faulting step. This is `Config.FaultFree` with `ReachableSem` for `Reachable`. -/
def Config.FaultFreeSem (A : Arch) (fuel : Nat) (init : Config I) : Prop :=
  ∀ c, ReachableSem A fuel init c → ∀ tid m, ¬ c.FaultStep A tid m

/-- K-world fault freedom (at any fuel) gives fault freedom on the semantic
machine, from a bounded start. -/
theorem Config.FaultFreeSem.of_K {A : Arch} {fuel fuel' : Nat} {init : Config I} (hb : init.Bnd)
    (h : Config.FaultFreeK A fuel' init) : Config.FaultFreeSem A fuel init :=
  fun c hc => h c (ReachableK.of_reachableSem' hb hc)

end Kraken.Promising
