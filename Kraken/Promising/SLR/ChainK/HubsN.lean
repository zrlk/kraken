/-
**The K-world chain clone: the ISA-neutral Stage 2 hubs at the K world**.
`#chaink_clone` (`ChainK/Clone.lean`) re-elaborates
the declarations of the listed modules that mention the executable machine
or an earlier clone (see `ChainK/Theorem1.lean`): `ticket_counter_core`,
`spin_counter_core`. The modules are imported so that lake rebuilds this one
when they change.
-/
import Kraken.Promising.SLR.ChainK.PromisePure
import Kraken.Promising.SLR.EnvG.TicketCounterCore
import Kraken.Promising.SLR.EnvG.SpinStart

open Kraken.Promising.Live.Bridge

#chaink_clone "../EnvG/TicketCounterCore.lean"

#chaink_clone "../EnvG/SpinStart.lean"
