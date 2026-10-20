/-
**The K-world chain clone: the Stage 2 hubs at the K world, AArch64 side**.
`#chaink_clone` (`ChainK/Clone.lean`) re-elaborates the
declarations of the listed modules that mention the executable machine or
an earlier clone (see `ChainK/Theorem1.lean`): `final_of_relPureSafely(D)`.
The ISA-neutral `ticket_counter_core` and `spin_counter_core` clones are in
`ChainK/HubsN.lean` (imported). The F/S-chain bridges of `A64DeclsLink` are skipped (they
conclude existing `Reachable`-based statements). The modules are imported so that lake rebuilds this
one when they change.
-/
import Kraken.Promising.SLR.ChainK.PromisePure
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.ChainK.HubsN
import Kraken.Promising.SLR.EnvG.A64DeclsLink

open Kraken.Promising.Live.Bridge

#chaink_clone "../EnvG/RelPureEnvA64.lean"

#chaink_clone "../EnvG/A64DeclsLink.lean" skip ["final_of_relPureSafelyFD", "final_of_relPureSafelySD"]
