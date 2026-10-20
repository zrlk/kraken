/-
**The K-world chain clone: the Stage 2 hubs at the K world, x64 side**.
`#chaink_clone` (`ChainK/Clone.lean`) re-elaborates the
declarations of the listed modules that mention the executable machine or
an earlier clone (see `ChainK/Theorem1.lean`): `final_of_relPureSafelyX`,
`final_of_relPureSafelyQX_tso(D)`. The modules are imported so that lake
rebuilds this one when they change.
-/
import Kraken.Promising.SLR.ChainK.PromisePure
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.X64DeclsLink

open Kraken.Promising.Live.Bridge

#chaink_clone "../EnvG/RelPureEnvX64.lean"

#chaink_clone "../EnvG/X64DeclsLink.lean" skip ["final_of_relPureSafelyQX_tsoFD", "final_of_relPureSafelyQX_tsoSD"]
