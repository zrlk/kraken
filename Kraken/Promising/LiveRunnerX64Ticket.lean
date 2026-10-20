/-
**Liveness of the x64 ticket lock (`ticketlock3.kl`) in the runner's
declarations form.**

`ticket3_x64_live_pf` is stated for threads with no declarations
(`TkStartX`, `StartStateTk {}`). The `.kl` runner's threads carry the typed
header's declarations (`tk3DeclsD`: the three 4-byte words, strict). Here:

- `tk3ImageV_cellsDeclsAgree`: every cell of the image makes only accesses
  at `(next)`, `(owner)`, `(counter)`, 4 bytes, so it agrees with any `ds`
  under which those three resolve to themselves (`Decls.AgreesAt`);
- `TkStartXD ds`: `TkStartX` with `StartStateTk ds` and the three
  `AgreesAt` facts. `AgreesAt` is weaker than the safety side's
  `ds.Sized` (`ticket3_counter_envG_runner`) for this purpose: it constrains
  only the three symbols the code touches; it holds for `{}` and for the
  runner's strict sized declarations;
- **`ticket3_x64_live_pf_runner`**: the promise-free liveness statement
  (`WeakFair ∧ MemFair ∧ PromiseFree`) from every `TkStartXD ds`
  configuration, by `liveFrom_transfer` (`LiveRunnerSim`) from
  `ticket3_x64_live_pf` along `State.noDecls`;
- `ticket3_x64_live_pf_runner_concrete` (the runner's layout `tk3LayoutV`,
  declarations `tk3DeclsD`, any `N` workers `tk3WorkerD0` with the runner's
  initial memory; no hypothesis left) and `_runnerN` (the same as a
  `LiveFrom` at `Config.init (List.replicate N tk3WorkerD0) tk3InitMemV`).

Promise-free fragment only, as for the theorem it transfers.
-/
import Kraken.Promising.LiveRunnerX64
import Kraken.Promising.LiveX64TicketPF

namespace Kraken.Promising.Live.RunnerX64Ticket

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.RunnerX64
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV tk3WorkerV tk3DataV symTk StartStateTk)

section Generic

variable [layout : _root_.Layout]

/-- The address an absolute operand `(x)` computes in the image. -/
theorem addrTk (x : Label) (regs : Reg64s) (rng : Std.Rco Int64) :
    @AddrExpr.interp (_root_.Executable.labels (layout tk3ImageV)) ⟨.W64⟩ ⟨none, none, .label x⟩ regs rng =
      symTk x := by
  have := @AddrExpr.zeroExtend_interp_abs_label (_root_.Executable.labels (layout tk3ImageV)) x regs rng
  simpa using this

theorem tk3ImageV_cellsDeclsAgree {ds : Decls} (hx : ds.AgreesAt (symTk "next") 4)
    (ho : ds.AgreesAt (symTk "owner") 4) (hc : ds.AgreesAt (symTk "counter") 4) :
    CellsDeclsAgree ds (layout tk3ImageV) := by
  refine cellsDeclsAgree_layoutL ?_
  intro d hd' s rng next jmp hn hj
  simp only [tk3ImageV, tk3WorkerV, tk3DataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd'
  repeat' (rcases hd' with rfl | hd')
  all_goals simp [Directive.interp, Instr.interp, Effects.DeclsAgree, Operation.interp, hn, hj,
    RelRegOrMem.interp, RegOrMem.interp, Operand.interp, MachineData.load, MachineData.store, MachineData.rmwK,
    RegOrMem.rmw, MachineData.set, addrTk]
  all_goals (repeat' (first | split | simp [Effects.DeclsAgree, hn, hj, hx, ho, hc]))

/-! ## The statement with declarations -/

/-- **The start configurations with declarations `ds`**: `TkStartX` with
the workers at `StartStateTk ds`, where `ds` resolves the three symbols'
4-byte words to themselves (`Decls.AgreesAt`; weaker than `ds.Sized` here:
nothing is assumed about other declarations). -/
structure TkStartXD (ds : Decls) (N : Nat) (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  agX : ds.AgreesAt (symTk "next") 4
  agO : ds.AgreesAt (symTk "owner") 4
  agC : ds.AgreesAt (symTk "counter") 4
  hxo : Decls.overlaps (symTk "next") 4 (symTk "owner") 4 = false
  hxc : Decls.overlaps (symTk "next") 4 (symTk "counter") 4 = false
  hoc : Decls.overlaps (symTk "owner") 4 (symTk "counter") 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, StartStateTk ds s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨symTk "next", 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨symTk "owner", 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨symTk "counter", 4⟩ = 0

/-- **The promise-free x64 ticket-lock liveness statement with declarations
`ds`** (`TicketX64.TicketX64LivePF` at `TkStartXD ds`). -/
def TicketX64LivePFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ N states initMem, TkStartXD ds N states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      TicketX64.TkWaitingX TicketX64.TkDoneX

theorem startStateTk_noDecls {ds : Decls} {s : isa.State} (h : StartStateTk ds s) :
    StartStateTk {} (noD s) :=
  ⟨h.exe, rfl, h.pc, h.endPc, h.split⟩

/-- **Promise-free liveness of the x64 ticket lock with the runner's
declarations** (Stage 3, promise-free fragment; `ticketlock3.kl` verbatim):
on a valid layout of `tk3ImageV`, for every `ds` that resolves `next`,
`owner`, `counter` (4 bytes) to themselves, on every promise-free
stuttering `Arch.tso` trace from a `TkStartXD ds` configuration under weak
fairness and memory fairness, every waiting thread eventually leaves its
spin loop. `ticket3_x64_live_pf` transferred along `State.noDecls`
(`liveFrom_transfer`). -/
theorem ticket3_x64_live_pf_runner [Executable.ValidLayout (layout tk3ImageV)] (ds : Decls) (fuel : Nat) :
    TicketX64LivePFD ds fuel := by
  intro N states initMem hs
  refine liveFrom_transfer (execSimD (tk3ImageV_cellsDeclsAgree hs.agX hs.agO hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩) (fun _ _ => ?_) (fun _ _ => ?_) ?_
  · exact exists_mapC _ _ _ _
  · exact exists_mapC _ _ _ _
  · rw [mapC_init]
    exact TicketX64PF.ticket3_x64_live_pf fuel N _ initMem
      ⟨hs.hxo, hs.hxc, hs.hoc, hs.hN32,
        fun s h => by
          obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
          exact startStateTk_noDecls (hs.hst s' h'),
        by rw [List.length_map]; exact hs.hN, hs.hX0, hs.hO0, hs.hC0⟩

end Generic

/-! ## The runner's configuration -/

section Concrete

open Kraken.Promising.X64.EnvG.TicketX.Concrete
attribute [local instance] tk3LayoutV

/-- `ticket3_x64_live_pf_runner` at the runner's layout `tk3LayoutV` and
declarations `tk3DeclsD`. No hypothesis left. -/
theorem ticket3_x64_live_pf_runner_concrete (fuel : Nat) : @TicketX64LivePFD tk3LayoutV tk3DeclsD fuel :=
  @ticket3_x64_live_pf_runner tk3LayoutV tk3ValidV tk3DeclsD fuel

/-- **The runner's own configuration, `N` workers** (`ticketlock3.kl`:
`N = 3`): `N` copies of the runner's prepared worker `tk3WorkerD0`
(declarations `tk3DeclsD` included), the runner's initial memory, at its
layout, under `WeakFair ∧ MemFair ∧ PromiseFree`. No hypothesis left except
`N + 1 < 2 ^ 32`. -/
theorem ticket3_x64_live_pf_runnerN (fuel N : Nat) (hN32 : N + 1 < 2 ^ 32) :
    LiveFrom Arch.tso fuel (Config.init (List.replicate N tk3WorkerD0) tk3InitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      (@TicketX64.TkWaitingX tk3LayoutV) (@TicketX64.TkDoneX tk3LayoutV) := by
  refine ticket3_x64_live_pf_runner_concrete fuel N _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, hN32,
    fun s hs => (List.eq_of_mem_replicate hs) ▸ tk3WorkerD0_start, List.length_replicate, ?_, ?_, ?_⟩
  · show tk3DeclsD.resolve _ 4 = _; rw [symTk_next]; rfl
  · show tk3DeclsD.resolve _ 4 = _; rw [symTk_owner]; rfl
  · show tk3DeclsD.resolve _ 4 = _; rw [symTk_counter]; rfl
  · rw [symTk_next, symTk_owner]; decide
  · rw [symTk_next, symTk_counter]; decide
  · rw [symTk_owner, symTk_counter]; decide
  · rw [symTk_next]; simp only [Config.init_mem]; decide
  · rw [symTk_owner]; simp only [Config.init_mem]; decide
  · rw [symTk_counter]; simp only [Config.init_mem]; decide

end Concrete

end Kraken.Promising.Live.RunnerX64Ticket

#print axioms Kraken.Promising.Live.RunnerX64Ticket.ticket3_x64_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerX64Ticket.ticket3_x64_live_pf_runner_concrete
#print axioms Kraken.Promising.Live.RunnerX64Ticket.ticket3_x64_live_pf_runnerN
