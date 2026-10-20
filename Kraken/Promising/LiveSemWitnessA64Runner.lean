/-
**Stage 3: `Progressive` at the AArch64 runner
starts** (threads with declarations `decls = ds`: `TkStartD`, `CasStartD`,
`SwpStartGD`; executable machine).

`Witness.progressive_of_mapC` along `State.noDecls` (`RunnerA64.execSimA`),
from the declaration-free instances of `LiveSemWitnessA64.lean`. A fair
trace from a runner start is then
`Witness.fair_exists (*_progressive_runner hs) (startPF_init _ _) fuel`
(resp. `fairSem_exists`). The `ldaddal` ticket lock is in
`LiveSemWitnessTicketAl.lean`.
-/
import Kraken.Promising.LiveSemWitnessA64
import Kraken.Promising.LiveSemWitnessRunner
import Kraken.Promising.LiveRunnerA64Ticket
import Kraken.Promising.LiveRunnerA64Cas
import Kraken.Promising.LiveRunnerA64Swp

namespace Kraken.Promising.Live.WitnessA64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.Witness Kraken.Promising.Live.RunnerSim Kraken.Promising.Live.RunnerA64

variable [layout : _root_.Layout]

theorem tk_progressive_runner [Executable.ValidLayout (layout SLR.EnvG.TicketLock.tkWorker)] {ds : Decls}
    {N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : RunnerA64Ticket.TkStartD ds N x o c states initMem) :
    Progressive Arch.armv8 (Config.init states initMem) := by
  refine progressive_of_mapC
    (execSimA SLR.EnvG.TicketLock.tkWorker_noPairs (RunnerA64Ticket.stepOK_tk hs.agX hs.agO hs.agC))
    (goodC_initA initMem fun s h => ⟨(hs.hst s h).1, RunnerA64Ticket.sTk_of_start (hs.hst s h).2⟩) ?_
  erw [mapC_init]
  refine tk_progressive ⟨hs.hxo, hs.hxc, hs.hoc, hs.hN32, fun s h => ?_,
    (@List.length_map _ _ states State.noDecls).trans hs.hN, hs.hX0, hs.hO0, hs.hC0⟩
  obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
  exact (hs.hst s' h').2

theorem cas_progressive_runner [Executable.ValidLayout (layout SLR.EnvG.CasSmoke.casTtasWorker)] {ds : Decls}
    {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : RunnerA64Cas.CasStartD ds l c states initMem) : Progressive Arch.armv8 (Config.init states initMem) := by
  refine progressive_of_mapC
    (execSimA SLR.EnvG.CasSmoke.casTtasWorker_noPairs (RunnerA64Cas.stepOK_cas hs.agL hs.agC))
    (goodC_initA initMem fun s h => ⟨(hs.hst s h).1, RunnerA64Cas.sCas_of_start (hs.hst s h).2⟩) ?_
  erw [mapC_init]
  exact cas_progressive (RunnerA64Cas.casStart_noDecls hs)

/-- Any SWP-shaped program `P` without `LDXP`/`STXP` (`swpWorker`,
`swplWorker`), at start states `Start` that are `StartG P` states. -/
theorem swp_progressive_runner {P : Program} [Executable.ValidLayout (layout P)] (hC : SpinSwpTrees.SwpCode P)
    (hnp : Kraken.Executable.noPairs (layout P) = true) {Start : BitVec 64 → BitVec 64 → isa.State → Prop}
    (hStart : ∀ l c s, Start l c s → SpinSwp.StartG P l c s) {ds : Decls} {l c : BitVec 64}
    {states : List isa.State} {initMem : List (Loc × Val)} (hs : RunnerA64Swp.SwpStartGD ds Start l c states initMem) :
    Progressive Arch.armv8 (Config.init states initMem) := by
  refine progressive_of_mapC (execSimA hnp (RunnerA64Swp.stepOK_swp hC hs.agL hs.agC))
    (goodC_initA initMem fun s h =>
      ⟨(hs.hst s h).1, RunnerA64Swp.sSwp_of_start hC (hStart _ _ _ (hs.hst s h).2)⟩) ?_
  erw [mapC_init]
  have hs' := RunnerA64Swp.swpStart_noDecls hs
  exact swp_progressive hC ⟨hs'.hlc, fun s h => hStart _ _ _ (hs'.hst s h), hs'.hL0⟩

end Kraken.Promising.Live.WitnessA64
