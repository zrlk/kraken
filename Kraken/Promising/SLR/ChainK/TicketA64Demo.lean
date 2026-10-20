/-
**The K-world chain demo: the AArch64 ticket lock on the semantic machine**.
`#chaink_clone` re-elaborates `ticket_counter_of` and
`ticket_counter_envG` at the K world (`ticket_counter_ofK`,
`ticket_counter_envGK`, over `ReachableKF`, whose fuel is phantom); the
hand-written `ticket_counter_envG_reachK` states the result fuel-free over
`ReachableK`, and `ticket_counter_envG_sem` over the semantic machine
`ReachableSem` (with a real fuel), through `ReachableK.of_reachableSem'`
(`Proj.promProjection`) and `Config.init_bnd`.
-/
import Kraken.Promising.SLR.ChainK.HubsA64
import Kraken.Promising.SLR.EnvG.TicketLockPublic
import Kraken.Promising.PromProjection

open Kraken.Promising.Live.Bridge

#chaink_clone "../EnvG/TicketLockPublic.lean"

namespace Kraken.Promising.SLR.EnvG.TicketLock
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.Live.Bridge

/-- **`counter = N` for the AArch64 ticket lock workers along `ReachableK`**
(`ticket_counter_envG` with the fuel-free reachability along `SuccKind`
steps; `ticket_counter_envGK` at the phantom fuel `0`). -/
theorem ticket_counter_envG_reachK [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartState x o c s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config isa} (hc : ReachableK Arch.armv8 (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  ticket_counter_envGK (fuel := 0) N x o c hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf

/-- **`counter = N` for the AArch64 ticket lock workers on the semantic
machine**: every configuration `ReachableSem` under `Arch.armv8` (any fuel)
from the initial one that is final has the counter word at `N`. The
hypotheses are those of `ticket_counter_envG`. -/
theorem ticket_counter_envG_sem [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]
    {fuel : Nat}
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartState x o c s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config isa} (hc : ReachableSem Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  ticket_counter_envG_reachK N x o c hxo hxc hoc hN32 hst hN hX0 hO0 hC0
    (ReachableK.of_reachableSem' (Config.init_bnd _ _) hc) hf

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_counter_envG_sem
