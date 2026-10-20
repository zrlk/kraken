/-
**Liveness of the AArch64 `ldadda` ticket lock (`ticketlock{2,3}.kl`) in the
runner's declarations form.**

`Live.TicketPF.ticket_live_pf` is stated for threads with no declarations
(`Ticket.TkStart`: `StartState x o c`, `decls = {}`). The `.kl` runner's
threads carry the typed header's declarations (`ConcreteTicketD.tkDeclsD`:
the three 4-byte words, strict). Here:

- `STk x o c`: the dynamic invariant of the bridge (`LiveRunnerA64`): the
  existing proof's `TicketInv.Static` (program, end address, `X0`/`X1`/`X2` =
  `next`/`owner`/counter, private memory) and the pc on one of the worker's
  positions (`TicketTrees.tkPcs`);
- `stepOK_tk`: every `STk` state's tree (`TicketTrees.exec_*`) accesses only
  `⟨x, 4⟩`, `⟨o, 4⟩`, `⟨c, 4⟩` and stays in `STk`, so it agrees with any `ds`
  that resolves those three words to themselves (`Decls.AgreesAt`);
- `TkStartD ds`: `Ticket.TkStart` with the safety side's start states
  `WithDeclsD ds (StartState x o c)` (as `ticket_counter_envG_runner`) and the
  three `AgreesAt` facts (the safety side's `ds.StrictSized` is not needed);
- **`ticket_live_pf_runner`**: the promise-free liveness statement
  (`WeakFair ∧ MemFair ∧ PromiseFree`) from every `TkStartD ds` configuration,
  by `liveFrom_transfer` from `ticket_live_pf` along `State.noDecls`;
- `ticket_live_pf_runner_concrete` (the runner's layout `tkLayoutD`, any
  `ds`) and `ticket_live_pf_runnerN` (`N` copies of the runner's
  `tkWorkerD0`, declarations `tkDeclsD` included, its initial memory; only
  the existing theorem's own `N + 1 < 2 ^ 32` left).

Promise-free fragment only, as for the theorem it transfers.
-/
import Kraken.Promising.LiveRunnerA64
import Kraken.Promising.LiveTicketPF
import Kraken.Promising.SLR.EnvG.A64TicketRunner

namespace Kraken.Promising.Live.RunnerA64Ticket

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.RunnerA64 Kraken.Promising.Live.TicketTrees Kraken.Promising.Live.TicketInv
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState tkWorker_noPairs)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD)

section Generic

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkWorker).addrOf

/-- **The bridge's invariant for the ticket worker** (states without
declarations): `Static` and the pc at one of the worker's positions. -/
def STk (x o c : BitVec 64) (s : State) : Prop := Static x o c s ∧ ∃ i ∈ tkPcs, s.st.2 = pcA i

/-- **Every tree of an `STk` state agrees with `ds` and stays in `STk`.** -/
theorem stepOK_tk {ds : Decls} {x o c : BitVec 64} (hx : ds.AgreesAt x 4) (ho : ds.AgreesAt o 4)
    (hc : ds.AgreesAt c 4) : StepOK ds (layout tkWorker) (STk x o c) where
  exe _ h := h.1.exe
  decls _ h := h.1.decls
  ok s h t hex := by
    obtain ⟨hS, i, hi, hpc⟩ := h
    have hat : ∀ {j}, j ∈ tkPcs → j ≠ 14 → s.st.2 = pcA j → At s j := fun hj h14 hp => hS.at hj h14 hp
    have lf : ∀ md j, md.regs.X0 = s.st.1.regs.X0 → md.regs.X1 = s.st.1.regs.X1 →
        md.regs.X2 = s.st.1.regs.X2 → md.dmem = s.st.1.dmem → j ∈ tkPcs →
        STk x o c (TicketTrees.goto s md (pcA j)) :=
      fun md j h0 h1 h2 hd hj => ⟨hS.goto md _ h0 h1 h2 hd, j, hj, rfl⟩
    simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [exec_mov _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 2 rfl rfl rfl rfl (by decide)
    · rw [exec_ldadda _ (hat (by decide) (by decide) hpc) hS.x0 hS.dx] at hex; cases hex
      exact ⟨hx, fun _ => lf _ 4 rfl rfl rfl rfl (by decide)⟩
    · rw [exec_ldar _ (hat (by decide) (by decide) hpc) hS.x1 hS.dO] at hex; cases hex
      exact ⟨ho, fun _ => lf _ 5 rfl rfl rfl rfl (by decide)⟩
    · obtain ⟨sf, hex', -⟩ := exec_cmp _ (hat (by decide) (by decide) hpc)
      rw [hex'] at hex; cases hex
      exact lf _ 6 rfl rfl rfl rfl (by decide)
    · rw [exec_bne _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      by_cases hz : s.st.1.status.z = true
      · simp only [hz, ite_true]; exact lf _ 7 rfl rfl rfl rfl (by decide)
      · simp only [hz]; exact lf _ 4 rfl rfl rfl rfl (by decide)
    · rw [exec_ldr_c _ (hat (by decide) (by decide) hpc) hS.x2 hS.dc] at hex; cases hex
      exact ⟨hc, fun _ => lf _ 8 rfl rfl rfl rfl (by decide)⟩
    · rw [exec_add5 _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 9 rfl rfl rfl rfl (by decide)
    · rw [exec_str_c _ (hat (by decide) (by decide) hpc) hS.x2 hS.dc] at hex; cases hex
      exact ⟨hc, fun _ => lf _ 10 rfl rfl rfl rfl (by decide)⟩
    · rw [exec_add4 _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 11 rfl rfl rfl rfl (by decide)
    · rw [exec_stlr _ (hat (by decide) (by decide) hpc) hS.x1 hS.dO] at hex; cases hex
      exact ⟨ho, fun _ => lf _ 12 rfl rfl rfl rfl (by decide)⟩
    · rw [exec_b_done _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 14 rfl rfl rfl rfl (by decide)
    · have hn : isa.exec s = none := by
        show AArch64.exec s = none
        unfold AArch64.exec
        rw [hpc, hS.endPc]
        simp
      rw [hn] at hex; cases hex

/-- A start state is in the invariant. -/
theorem sTk_of_start {x o c : BitVec 64} {s : State} (h : StartState x o c s) : STk x o c s :=
  ⟨⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.x2, h.dx, h.dO, h.dc⟩, 1, by decide, h.pc.trans addrOf_0⟩

/-! ## The statement with declarations -/

/-- **The start configurations with declarations `ds`**: `Ticket.TkStart`
with the workers at `WithDeclsD ds (StartState x o c)` (the start states of
`ticket_counter_envG_runner`), where `ds` resolves the three 4-byte words to
themselves (`Decls.AgreesAt`; nothing is assumed about other declarations). -/
structure TkStartD (ds : Decls) (N : Nat) (x o c : BitVec 64) (states : List isa.State)
    (initMem : List (Loc × Val)) : Prop where
  agX : ds.AgreesAt x 4
  agO : ds.AgreesAt o 4
  agC : ds.AgreesAt c 4
  hxo : Decls.overlaps x 4 o 4 = false
  hxc : Decls.overlaps x 4 c 4 = false
  hoc : Decls.overlaps o 4 c 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, WithDeclsD ds (StartState x o c) s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0

/-- **The promise-free ticket-lock liveness statement with declarations
`ds`** (`Ticket.TicketLivePF` at `TkStartD ds`). -/
def TicketLivePFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ N x o c states initMem, TkStartD ds N x o c states initMem →
    LiveFrom Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      Ticket.TkWaiting Ticket.TkDone

/-- **Promise-free liveness of the AArch64 ticket lock with the runner's
declarations** (Stage 3, promise-free fragment; `ticketlock2.kl` worker
verbatim): on a valid layout of `tkWorker`, for every `ds` that resolves
`next`, `owner`, counter (4 bytes) to themselves, on every promise-free
stuttering `Arch.armv8` trace from a `TkStartD ds` configuration under weak
fairness and memory fairness, every waiting thread eventually leaves its
spin loop. `ticket_live_pf` transferred along `State.noDecls`
(`liveFrom_transfer`, `execSimA`). -/
theorem ticket_live_pf_runner (ds : Decls) (fuel : Nat) : TicketLivePFD ds fuel := by
  intro N x o c states initMem hs
  refine liveFrom_transfer (execSimA tkWorker_noPairs (stepOK_tk hs.agX hs.agO hs.agC))
    (goodC_initA initMem fun s h => ⟨(hs.hst s h).1, sTk_of_start (hs.hst s h).2⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact TicketPF.ticket_live_pf fuel N x o c _ initMem
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

/-- `ticket_live_pf_runner` at the runner's layout `tkLayoutD`. No
hypothesis left. -/
theorem ticket_live_pf_runner_concrete (ds : Decls) (fuel : Nat) : @TicketLivePFD tkLayoutD ds fuel :=
  @ticket_live_pf_runner tkLayoutD tkValidD ds fuel

/-- **The runner's own configuration, `N` workers** (`ticketlock2.kl`:
`N = 2`, `ticketlock3.kl`: `N = 3`): `N` copies of the runner's prepared
worker `tkWorkerD0` (declarations `tkDeclsD` included), the runner's initial
memory, at its layout, under `WeakFair ∧ MemFair ∧ PromiseFree`. No
hypothesis left except `N + 1 < 2 ^ 32`. -/
theorem ticket_live_pf_runnerN (fuel N : Nat) (hN32 : N + 1 < 2 ^ 32) :
    LiveFrom Arch.armv8 fuel (Config.init (List.replicate N tkWorkerD0) tkAlInitMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      (@Ticket.TkWaiting tkLayoutD) (@Ticket.TkDone tkLayoutD) :=
  ticket_live_pf_runner_concrete tkDeclsD fuel N nextAddr ownerAddr counterAddr _ _
    ⟨rfl, rfl, rfl, tkAl_disj_xo, tkAl_disj_xc, tkAl_disj_oc, hN32,
      fun s hs => (List.eq_of_mem_replicate hs) ▸
        Kraken.Promising.SLR.EnvG.A64Whole.withDeclsD_of rfl tkWorker0_start,
      List.length_replicate, by simp only [Config.init]; decide, by simp only [Config.init]; decide,
      by simp only [Config.init]; decide⟩

end Concrete

end Kraken.Promising.Live.RunnerA64Ticket

#print axioms Kraken.Promising.Live.RunnerA64Ticket.ticket_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerA64Ticket.ticket_live_pf_runner_concrete
#print axioms Kraken.Promising.Live.RunnerA64Ticket.ticket_live_pf_runnerN
