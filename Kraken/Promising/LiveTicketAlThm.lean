/-
**Stage 3: the liveness table of the AArch64
`ldaddal` ticket lock, stated explicitly** (`ticketlock_al2/3.kl`, worker
`tkWorkerAl`).

Each theorem below writes out its full statement at `tkWorkerAl` (and, for the
concrete forms, at `ConcreteTicketAl.tkAlLayout`, the layout of
`ticket_al_counter_envG_concrete2` and of the runner). Its proof is the
corresponding theorem of the clone modules `LiveTicketAl{PF,Sem,CexG}.lean`,
`LiveRunner{,Sem}A64TicketAl.lean`, which re-elaborate the `ldadda` proofs at
`tkWorkerAl` (`#ticket_al_clone`, `LiveTicketAlClone.lean`; a source-level
instantiation, every declaration kernel-checked again). The clone-produced
names (`TicketAlPF.ticket_al_live_pf`, …) are internal lemmas.

| statement | machine | fairness | theorem |
|---|---|---|---|
| `TicketAlLivePF` | `succs`/`TraceS` | `WeakFair ∧ MemFair ∧ PromiseFree` | `ticket_al_live_pf` (+ `_concrete`) |
| `TicketAlLiveSem` | `CertOkN`/`TraceSem` | `WeakFairSem ∧ MemFair` | `ticket_al_live_sem` (+ `_concrete`) |
| `TicketAlLiveWF` | `succs`/`TraceS` | `WeakFair` | refuted: `ticketAlLiveWF_false` |
| runner PF | `succs`/`TraceS` | as PF | `ticket_al_live_pf_runner{,_concrete,N}` |
| runner Sem | `CertOkN`/`TraceSem` | as Sem | `ticket_al_live_sem_runner{,_concrete,N}` |
| `TicketAlLive` | `succs`/`TraceS` | `WeakFair ∧ MemFair` | open (as `Ticket.TicketLive`) |

The runner forms take `TkStartAlD ds`: `TkStartAl` with the start states
`WithDeclsD ds (StartStateAl x o c)` and `ds.AgreesAt` for the three words
(no `StrictSized`, no `prom = []`).
-/
import Kraken.Promising.LiveTicketAlSem
import Kraken.Promising.LiveTicketAlCexG
import Kraken.Promising.LiveRunnerSemA64TicketAl

namespace Kraken.Promising.Live.TicketAl

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorkerAl StartStateAl)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD)
open Kraken.Promising.SLR.EnvG.ConcreteTicketAl (tkAlLayout tkAlValid tkAlWorkerD0 tkAlInitMem)

/-! ## What the clones are about -/

section Sanity

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]

/-- The cloned ticket RMW cell is the `ldaddal` (`.acqRel`) one of `tkWorkerAl`. -/
example (st : State) (h : TicketAlTrees.At st 2) {x : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = x) (hdm : Mem.loadInt st.st.1.dmem x 4 = none) :
    isa.exec st = some (.rmw .acqRel false ⟨x, 4⟩
      (fun old => some (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 st.st.1.regs.X6.toBitVec)))
      fun v => .done (TicketAlTrees.goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout tkWorkerAl).addrOf 4))) :=
  TicketAlTrees.exec_ldaddal st h hx0 hdm

/-- The cloned cell context and invariants run `tkWorkerAl`. -/
example (st : State) (i : Nat) (h : TicketAlTrees.At st i) : st.exe = layout tkWorkerAl := h.exe
example (x o c : BitVec 64) (s : isa.State) (h : TicketAlInv.Static x o c s) : s.exe = layout tkWorkerAl := h.exe
example (x o c : BitVec 64) (s : isa.State) (h : TicketAlDrop.SInv x o c s) :
    TicketAlInv.Static x o c s := h.1
example (x o c : BitVec 64) (s : isa.State) (h : StartStateAl x o c s) :
    RunnerA64TicketAl.STk x o c s := RunnerA64TicketAl.sTk_of_start h

end Sanity

/-! ## The theorems at a valid layout -/

section Valid

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]

/-- **Promise-free liveness of the `ldaddal` ticket lock** (executable machine
`succs`/`TraceS`): on a valid layout of `tkWorkerAl`, on every promise-free
stuttering trace from a `TkStartAl` configuration under weak fairness and
memory fairness, every waiting thread eventually leaves its spin loop. -/
theorem ticket_al_live_pf (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAl N x o c states initMem →
      LiveFrom Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
        TkWaitingAl TkDoneAl :=
  TicketAlPF.ticket_al_live_pf fuel

/-- **Liveness of the `ldaddal` ticket lock with promises** (semantic machine
`CertOkN`/`TraceSem`): on a valid layout of `tkWorkerAl`, for every `fuel`,
on every semantic trace from a `TkStartAl` configuration under semantic weak
fairness and memory fairness, every waiting thread is eventually done. -/
theorem ticket_al_live_sem (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAl N x o c states initMem →
      LiveFromSem Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) TkWaitingAl TkDoneAl :=
  TicketAlSem.ticket_al_live_sem fuel

/-- **The start configurations with declarations `ds`** (runner form):
`TkStartAl` with the workers at `WithDeclsD ds (StartStateAl x o c)` (the start
states of `ticket_al_counter_envG_runner`), where `ds` resolves the three
4-byte words to themselves (`Decls.AgreesAt`). -/
structure TkStartAlD (ds : Decls) (N : Nat) (x o c : BitVec 64) (states : List isa.State)
    (initMem : List (Loc × Val)) : Prop where
  agX : ds.AgreesAt x 4
  agO : ds.AgreesAt o 4
  agC : ds.AgreesAt c 4
  hxo : Decls.overlaps x 4 o 4 = false
  hxc : Decls.overlaps x 4 c 4 = false
  hoc : Decls.overlaps o 4 c 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, WithDeclsD ds (StartStateAl x o c) s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0

omit [Executable.ValidLayout (layout tkWorkerAl)] in
/-- The clone's start structure is this one. -/
theorem TkStartAlD.toClone {ds : Decls} {N : Nat} {x o c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (h : TkStartAlD ds N x o c states initMem) :
    RunnerA64TicketAl.TkStartAlD ds N x o c states initMem :=
  ⟨h.agX, h.agO, h.agC, h.hxo, h.hxc, h.hoc, h.hN32, h.hst, h.hN, h.hX0, h.hO0, h.hC0⟩

/-- **Promise-free liveness of the `ldaddal` ticket lock with the runner's
declarations** (executable machine `succs`/`TraceS`): on a valid layout of
`tkWorkerAl`, for every `ds` that resolves `next`, `owner`, counter to
themselves. -/
theorem ticket_al_live_pf_runner (ds : Decls) (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAlD ds N x o c states initMem →
      LiveFrom Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
        TkWaitingAl TkDoneAl :=
  fun N x o c states initMem h =>
    RunnerA64TicketAl.ticket_al_live_pf_runner ds fuel N x o c states initMem h.toClone

/-- **Liveness of the `ldaddal` ticket lock with promises and the runner's
declarations** (semantic machine `CertOkN`/`TraceSem`). -/
theorem ticket_al_live_sem_runner (ds : Decls) (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAlD ds N x o c states initMem →
      LiveFromSem Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) TkWaitingAl TkDoneAl :=
  fun N x o c states initMem h =>
    RunnerSemA64TicketAl.ticket_al_live_sem_runner ds fuel N x o c states initMem h.toClone

end Valid

/-! ## The concrete instances, at `ConcreteTicketAl.tkAlLayout` -/

section Concrete

attribute [local instance] tkAlLayout

/-- `ticket_al_live_pf` at `tkAlLayout`: no hypothesis left. -/
theorem ticket_al_live_pf_concrete (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAl N x o c states initMem →
      LiveFrom Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
        TkWaitingAl TkDoneAl :=
  @ticket_al_live_pf tkAlLayout tkAlValid fuel

/-- `ticket_al_live_sem` at `tkAlLayout`: no hypothesis left. -/
theorem ticket_al_live_sem_concrete (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAl N x o c states initMem →
      LiveFromSem Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) TkWaitingAl TkDoneAl :=
  @ticket_al_live_sem tkAlLayout tkAlValid fuel

/-- **`TicketAlLiveWF` is false** (executable machine, at `tkAlLayout`, every
`fuel`): two `tkWorkerAl` workers from a `TkStartAl` configuration have a
weakly fair, promise-free trace on which one waits forever. -/
theorem ticketAlLiveWF_false (fuel : Nat) :
    ¬ ∀ N x o c states initMem, TkStartAl N x o c states initMem →
      LiveFrom Arch.armv8 fuel (Config.init states initMem) (fun cfg => WeakFair Arch.armv8 fuel cfg)
        TkWaitingAl TkDoneAl :=
  TicketAlCexG.ticketAlLiveWF_false fuel

/-- `ticket_al_live_pf_runner` at `tkAlLayout`: no hypothesis left. -/
theorem ticket_al_live_pf_runner_concrete (ds : Decls) (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAlD ds N x o c states initMem →
      LiveFrom Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
        TkWaitingAl TkDoneAl :=
  @ticket_al_live_pf_runner tkAlLayout tkAlValid ds fuel

/-- `ticket_al_live_sem_runner` at `tkAlLayout`: no hypothesis left. -/
theorem ticket_al_live_sem_runner_concrete (ds : Decls) (fuel : Nat) :
    ∀ N x o c states initMem, TkStartAlD ds N x o c states initMem →
      LiveFromSem Arch.armv8 fuel (Config.init states initMem)
        (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) TkWaitingAl TkDoneAl :=
  @ticket_al_live_sem_runner tkAlLayout tkAlValid ds fuel

/-- **The runner's own configuration, `N` workers, promise-free**
(`ticketlock_al2.kl`: `N = 2`, `ticketlock_al3.kl`: `N = 3`; executable
machine): `N` copies of the runner's prepared worker `tkAlWorkerD0`
(declarations `tkDeclsD` included), the runner's initial memory, at its
layout. Only `N + 1 < 2 ^ 32` is left. -/
theorem ticket_al_live_pf_runnerN (fuel N : Nat) (hN32 : N + 1 < 2 ^ 32) :
    LiveFrom Arch.armv8 fuel (Config.init (List.replicate N tkAlWorkerD0) tkAlInitMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      TkWaitingAl TkDoneAl :=
  RunnerA64TicketAl.ticket_al_live_pf_runnerN fuel N hN32

/-- **The runner's own configuration, `N` workers, with promises** (semantic
machine `CertOkN`/`TraceSem`, `WeakFairSem ∧ MemFair`). Only
`N + 1 < 2 ^ 32` is left. -/
theorem ticket_al_live_sem_runnerN (fuel N : Nat) (hN32 : N + 1 < 2 ^ 32) :
    LiveFromSem Arch.armv8 fuel (Config.init (List.replicate N tkAlWorkerD0) tkAlInitMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg)
      TkWaitingAl TkDoneAl :=
  RunnerSemA64TicketAl.ticket_al_live_sem_runnerN fuel N hN32

end Concrete

end Kraken.Promising.Live.TicketAl

#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_pf
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_sem
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_pf_concrete
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_sem_concrete
#print axioms Kraken.Promising.Live.TicketAl.ticketAlLiveWF_false
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_pf_runner
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_sem_runner
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_pf_runner_concrete
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_sem_runner_concrete
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_pf_runnerN
#print axioms Kraken.Promising.Live.TicketAl.ticket_al_live_sem_runnerN
