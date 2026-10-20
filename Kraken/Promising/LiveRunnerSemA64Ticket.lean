/-
**Liveness of the AArch64 `ldadda` ticket lock with promises in the runner's
declarations form.**

`Live.TicketSem.ticket_live_sem` (Stage 3, the machine with semantic
certification) is stated for threads with no declarations (`Ticket.TkStart`:
`StartState x o c`, `decls = {}`). The `.kl` runner's threads carry the typed
header's declarations (`ConcreteTicketD.tkDeclsD`). With the bridge of the
promise-free form (`LiveRunnerA64Ticket`: `STk`, `stepOK_tk`, `TkStartD`,
`execSimA`) unchanged:

- **`ticket_live_sem_runner`**: the with-promises liveness statement
  (`Fair = WeakFairSem ∧ MemFair`, as `ticket_live_sem`) from every
  `TkStartD ds` configuration (the safety side's start states
  `WithDeclsD ds (StartState x o c)` and `ds.AgreesAt` at the three words;
  the same hypotheses as `ticket_live_pf_runner`), by `liveFromSem_transfer`
  (`LiveRunnerSemSim`) from `ticket_live_sem` along `State.noDecls`;
- `ticket_live_sem_runner_concrete` (the runner's layout `tkLayoutD`, any
  `ds`) and `ticket_live_sem_runnerN` (`N` copies of the runner's
  `tkWorkerD0`, declarations `tkDeclsD` included, its initial memory; only the
  existing theorem's own `N + 1 < 2 ^ 32` left).

Memory fairness `MemFair`: AArch64 basis Arm ARM B2.7.1 (see `MemFair`).
-/
import Kraken.Promising.LiveRunnerSemSim
import Kraken.Promising.LiveRunnerA64Ticket
import Kraken.Promising.LiveTicketSem

namespace Kraken.Promising.Live.RunnerSemA64Ticket

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.Sem Kraken.Promising.Live.RunnerSemSim
open Kraken.Promising.Live.RunnerA64 Kraken.Promising.Live.RunnerA64Ticket
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker tkWorker_noPairs)

section Generic

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

/-- **The with-promises ticket-lock liveness statement with declarations
`ds`** (`TicketSem.TicketLiveSem` at `TkStartD ds`; `Fair = WeakFairSem ∧
MemFair`). -/
def TicketLiveSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ N x o c states initMem, TkStartD ds N x o c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) Ticket.TkWaiting Ticket.TkDone

/-- **Liveness of the AArch64 ticket lock with promises and the runner's
declarations** (Stage 3, semantic certification; `ticketlock2.kl` worker
verbatim): on a valid layout of `tkWorker`, for every `ds` that resolves
`next`, `owner`, counter (4 bytes) to themselves, on every `TraceSem`
`Arch.armv8` trace from a `TkStartD ds` configuration under
`WeakFairSem ∧ MemFair`, every waiting thread eventually leaves its spin
loop. `ticket_live_sem` transferred along `State.noDecls`
(`liveFromSem_transfer`, `execSimA`). -/
theorem ticket_live_sem_runner (ds : Decls) (fuel : Nat) : TicketLiveSemD ds fuel := by
  intro N x o c states initMem hs
  refine liveFromSem_transfer (execSimA tkWorker_noPairs (stepOK_tk hs.agX hs.agO hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).1, sTk_of_start (hs.hst s h).2⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact TicketSem.ticket_live_sem fuel N x o c _ initMem
    ⟨hs.hxo, hs.hxc, hs.hoc, hs.hN32,
      fun s h => by
        obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
        exact (hs.hst s' h').2,
      (@List.length_map _ _ states State.noDecls).trans hs.hN, hs.hX0, hs.hO0, hs.hC0⟩

end Generic

/-! ## The runner's configuration -/

section Concrete

open Kraken.Promising.SLR.EnvG.ConcreteTicketD
open Kraken.Promising.SLR.EnvG.ConcreteTicketAl (nextAddr ownerAddr counterAddr tkAlInitMem tkAl_disj_xo
  tkAl_disj_xc tkAl_disj_oc)
attribute [local instance] tkLayoutD

/-- `ticket_live_sem_runner` at the runner's layout `tkLayoutD`. No
hypothesis left. -/
theorem ticket_live_sem_runner_concrete (ds : Decls) (fuel : Nat) : @TicketLiveSemD tkLayoutD ds fuel :=
  @ticket_live_sem_runner tkLayoutD tkValidD ds fuel

/-- **The runner's own configuration with promises, `N` workers**
(`ticketlock2.kl`: `N = 2`, `ticketlock3.kl`: `N = 3`): `N` copies of the
runner's prepared worker `tkWorkerD0` (declarations `tkDeclsD` included), the
runner's initial memory, at its layout, under `WeakFairSem ∧ MemFair`. No
hypothesis left except `N + 1 < 2 ^ 32`. -/
theorem ticket_live_sem_runnerN (fuel N : Nat) (hN32 : N + 1 < 2 ^ 32) :
    LiveFromSem Arch.armv8 fuel (Config.init (List.replicate N tkWorkerD0) tkAlInitMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg)
      (@Ticket.TkWaiting tkLayoutD) (@Ticket.TkDone tkLayoutD) :=
  ticket_live_sem_runner_concrete tkDeclsD fuel N nextAddr ownerAddr counterAddr _ _
    ⟨rfl, rfl, rfl, tkAl_disj_xo, tkAl_disj_xc, tkAl_disj_oc, hN32,
      fun s hs => (List.eq_of_mem_replicate hs) ▸
        Kraken.Promising.SLR.EnvG.A64Whole.withDeclsD_of rfl tkWorker0_start,
      List.length_replicate, by simp only [Config.init]; decide, by simp only [Config.init]; decide,
      by simp only [Config.init]; decide⟩

end Concrete

end Kraken.Promising.Live.RunnerSemA64Ticket

#print axioms Kraken.Promising.Live.RunnerSemA64Ticket.ticket_live_sem_runner
#print axioms Kraken.Promising.Live.RunnerSemA64Ticket.ticket_live_sem_runner_concrete
#print axioms Kraken.Promising.Live.RunnerSemA64Ticket.ticket_live_sem_runnerN
