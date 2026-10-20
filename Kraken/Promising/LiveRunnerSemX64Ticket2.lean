/-
**Liveness of the x64 ticket lock `ticketlock2.kl` (unlocked `incl` release)
with promises in the runner's declarations form.**

`Live.X64Sem2Ticket.ticket2_x64_live_sem` (Stage 3, the machine with semantic
certification) is stated for threads with no declarations
(`Ticket2X64.Tk2StartX`: `StartStateTk2 {}`). With the bridge of the
promise-free form (`LiveRunnerX64Ticket2`: `tk2ImageV_cellsDeclsAgree`,
`Tk2StartXD`, `startStateTk2_noDecls`; `LiveRunnerX64.execSimD`) unchanged:

- **`ticket2_x64_live_sem_runner`**: the with-promises liveness statement
  (`Fair = WeakFairSem ∧ MemFair`, as `ticket2_x64_live_sem`; on x86
  `MemFair` is a modelling assumption — store buffers drain in finite time,
  see `LiveTrace.lean`) from every `Tk2StartXD ds` configuration
  (`ds.AgreesAt` at the three words; the same hypotheses as
  `ticket2_x64_live_pf_runner`), by `liveFromSem_transfer`
  (`LiveRunnerSemSim`) along `State.noDecls`;
- `ticket2_x64_live_sem_runner_concrete` (the runner's layout `tk2LayoutV`
  and declarations `tk2DeclsD`) and `ticket2_x64_live_sem_runnerN` (`N`
  copies of `tk2WorkerD0`, the runner's initial memory; only the existing
  theorem's own `N + 1 < 2 ^ 32` left).
-/
import Kraken.Promising.LiveRunnerSemSim
import Kraken.Promising.LiveRunnerX64Ticket2
import Kraken.Promising.LiveX64Sem2Ticket

namespace Kraken.Promising.Live.RunnerSemX64Ticket2

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.Sem Kraken.Promising.Live.RunnerSemSim
open Kraken.Promising.Live.RunnerX64 Kraken.Promising.Live.RunnerX64Ticket2
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV symTk2)

section Generic

variable [layout : _root_.Layout]

/-- **The with-promises `ticketlock2` liveness statement with declarations
`ds`** (`X64Sem2.Ticket2X64LiveSem` at `Tk2StartXD ds`; `Fair = WeakFairSem ∧
MemFair`). -/
def Ticket2X64LiveSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ N states initMem, Tk2StartXD ds N states initMem →
    LiveFromSem Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) Ticket2X64.Tk2WaitingX Ticket2X64.Tk2DoneX

/-- **Liveness of the x64 `ticketlock2` with promises and the runner's
declarations** (Stage 3, semantic certification; `ticketlock2.kl`
verbatim): on a valid layout of `tk2ImageV`, for every `ds` that resolves
`next`, `owner`, `counter` (4 bytes) to themselves, on every `TraceSem`
`Arch.tso` trace from a `Tk2StartXD ds` configuration under
`WeakFairSem ∧ MemFair` (x86 `MemFair`: a modelling assumption), every
waiting thread eventually leaves its spin loop. `ticket2_x64_live_sem`
transferred along `State.noDecls` (`liveFromSem_transfer`, `execSimD`). -/
theorem ticket2_x64_live_sem_runner [Executable.ValidLayout (layout tk2ImageV)] (ds : Decls) (fuel : Nat) :
    Ticket2X64LiveSemD ds fuel := by
  intro N states initMem hs
  refine liveFromSem_transfer (execSimD (tk2ImageV_cellsDeclsAgree hs.agX hs.agO hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩) (fun _ _ => ?_) (fun _ _ => ?_) ?_
  · exact exists_mapC _ _ _ _
  · exact exists_mapC _ _ _ _
  · rw [mapC_init]
    exact X64Sem2Ticket.ticket2_x64_live_sem fuel N _ initMem
      ⟨hs.hxo, hs.hxc, hs.hoc, hs.hN32,
        fun s h => by
          obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
          exact startStateTk2_noDecls (hs.hst s' h'),
        by rw [List.length_map]; exact hs.hN, hs.hX0, hs.hO0, hs.hC0⟩

end Generic

/-! ## The runner's configuration -/

section Concrete

open Kraken.Promising.X64.EnvG.TicketX2.Concrete
attribute [local instance] tk2LayoutV

/-- `ticket2_x64_live_sem_runner` at the runner's layout `tk2LayoutV` and
declarations `tk2DeclsD`. No hypothesis left. -/
theorem ticket2_x64_live_sem_runner_concrete (fuel : Nat) : @Ticket2X64LiveSemD tk2LayoutV tk2DeclsD fuel :=
  @ticket2_x64_live_sem_runner tk2LayoutV tk2ValidV tk2DeclsD fuel

/-- **The runner's own configuration with promises, `N` workers**
(`ticketlock2.kl`: `N = 2`): `N` copies of the runner's prepared worker
`tk2WorkerD0` (declarations `tk2DeclsD` included), the runner's initial
memory, at its layout, under `WeakFairSem ∧ MemFair`. No hypothesis left
except `N + 1 < 2 ^ 32`. -/
theorem ticket2_x64_live_sem_runnerN (fuel N : Nat) (hN32 : N + 1 < 2 ^ 32) :
    LiveFromSem Arch.tso fuel (Config.init (List.replicate N tk2WorkerD0) tk2InitMemV)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg)
      (@Ticket2X64.Tk2WaitingX tk2LayoutV) (@Ticket2X64.Tk2DoneX tk2LayoutV) := by
  refine ticket2_x64_live_sem_runner_concrete fuel N _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, hN32,
    fun s hs => (List.eq_of_mem_replicate hs) ▸ tk2WorkerD0_start, List.length_replicate, ?_, ?_, ?_⟩
  · show tk2DeclsD.resolve _ 4 = _; rw [symTk2_next]; rfl
  · show tk2DeclsD.resolve _ 4 = _; rw [symTk2_owner]; rfl
  · show tk2DeclsD.resolve _ 4 = _; rw [symTk2_counter]; rfl
  · rw [symTk2_next, symTk2_owner]; decide
  · rw [symTk2_next, symTk2_counter]; decide
  · rw [symTk2_owner, symTk2_counter]; decide
  · rw [symTk2_next]; simp only [Config.init_mem]; decide
  · rw [symTk2_owner]; simp only [Config.init_mem]; decide
  · rw [symTk2_counter]; simp only [Config.init_mem]; decide

end Concrete

end Kraken.Promising.Live.RunnerSemX64Ticket2

#print axioms Kraken.Promising.Live.RunnerSemX64Ticket2.ticket2_x64_live_sem_runner
#print axioms Kraken.Promising.Live.RunnerSemX64Ticket2.ticket2_x64_live_sem_runner_concrete
#print axioms Kraken.Promising.Live.RunnerSemX64Ticket2.ticket2_x64_live_sem_runnerN
