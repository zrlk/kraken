/-
**The K-world chain clone: Theorem 1′'s run machinery at the K world**.
`#chaink_clone` (`ChainK/Clone.lean`) re-elaborates the
declarations of `Theorem1Run.lean`, `Theorem1Proof.lean` and
`Theorem1D1.lean` that mention the executable machine, with `Path ↦ PathK`,
`Reachable ↦ ReachableKF`, `succs ↦ succsK` (fuel a phantom: `ReachableKF A
fuel` is `ReachableK A`), and every other cloned name `x ↦ xK`. Everything is
kernel-checked again; the source text is shared, not copied. The modules
are imported so that lake rebuilds this one when they change.
-/
import Kraken.Promising.SLR.Theorem1Run
import Kraken.Promising.SLR.Theorem1Proof
import Kraken.Promising.SLR.Theorem1D1
import Kraken.Promising.ChainK.Clone

open Kraken.Promising.Live.Bridge

#chaink_clone "../Theorem1Run.lean"

#chaink_clone "../Theorem1Proof.lean" skip ["Theorem1IIPure.theorem1II"]

#chaink_clone "../Theorem1D1.lean"
