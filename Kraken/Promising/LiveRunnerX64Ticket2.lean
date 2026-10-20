/-
**Liveness of the unlocked-release x64 ticket lock (`ticketlock2.kl`) in the runner's
declarations form.**

`ticket2_x64_live_pf` is stated for threads with no declarations
(`Tk2StartX`, `StartStateTk2 {}`). The `.kl` runner's threads carry the typed
header's declarations (`tk2DeclsD`: the three 4-byte words, strict). Here:

- `tk2ImageV_cellsDeclsAgree`: every cell of the image makes only accesses
  at `(next)`, `(owner)`, `(counter)`, 4 bytes (`incl (owner)` included), so it agrees with any `ds`
  under which those three resolve to themselves (`Decls.AgreesAt`);
- `Tk2StartXD ds`: `Tk2StartX` with `StartStateTk2 ds` and the three
  `AgreesAt` facts. `AgreesAt` is weaker than the safety side's
  `ds.Sized` (`ticket2_counter_envG_runner`) for this purpose: it constrains
  only the three symbols the code touches; it holds for `{}` and for the
  runner's strict sized declarations;
- **`ticket2_x64_live_pf_runner`**: the promise-free liveness statement
  (`WeakFair ∧ MemFair ∧ PromiseFree`) from every `Tk2StartXD ds`
  configuration, by `liveFrom_transfer` (`LiveRunnerSim`) from
  `ticket2_x64_live_pf` along `State.noDecls`;
- `ticket2_x64_live_pf_runner_concrete` (the runner's layout `tk2LayoutV`,
  declarations `tk2DeclsD`, any `N` workers `tk2WorkerD0` with the runner's
  initial memory; no hypothesis left) and `_runnerN` (the same as a
  `LiveFrom` at `Config.init (List.replicate N tk2WorkerD0) tk2InitMemV`).

Promise-free fragment only, as for the theorem it transfers.
-/
import Kraken.Promising.LiveRunnerX64
import Kraken.Promising.LiveX64Ticket2PF

namespace Kraken.Promising.Live.RunnerX64Ticket2

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.RunnerX64
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV tk2WorkerV tk2DataV symTk2 StartStateTk2)

section Generic

variable [layout : _root_.Layout]

/-- The address an absolute operand `(x)` computes in the image. -/
theorem addrTk2 (x : Label) (regs : Reg64s) (rng : Std.Rco Int64) :
    @AddrExpr.interp (_root_.Executable.labels (layout tk2ImageV)) ⟨.W64⟩ ⟨none, none, .label x⟩ regs rng =
      symTk2 x := by
  have := @AddrExpr.zeroExtend_interp_abs_label (_root_.Executable.labels (layout tk2ImageV)) x regs rng
  simpa using this

theorem tk2ImageV_cellsDeclsAgree {ds : Decls} (hx : ds.AgreesAt (symTk2 "next") 4)
    (ho : ds.AgreesAt (symTk2 "owner") 4) (hc : ds.AgreesAt (symTk2 "counter") 4) :
    CellsDeclsAgree ds (layout tk2ImageV) := by
  refine cellsDeclsAgree_layoutL ?_
  intro d hd' s rng next jmp hn hj
  simp only [tk2ImageV, tk2WorkerV, tk2DataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd'
  repeat' (rcases hd' with rfl | hd')
  all_goals simp [Directive.interp, Instr.interp, Effects.DeclsAgree, Operation.interp, hn, hj,
    RelRegOrMem.interp, RegOrMem.interp, Operand.interp, MachineData.load, MachineData.store, MachineData.rmwK,
    RegOrMem.rmw, MachineData.set, addrTk2]
  all_goals (repeat' (first | (intro x) | split | simp [Effects.DeclsAgree, hn, hj, hx, ho, hc]))

/-! ## The statement with declarations -/

/-- **The start configurations with declarations `ds`**: `Tk2StartX` with
the workers at `StartStateTk2 ds`, where `ds` resolves the three symbols'
4-byte words to themselves (`Decls.AgreesAt`; weaker than `ds.Sized` here:
nothing is assumed about other declarations). -/
structure Tk2StartXD (ds : Decls) (N : Nat) (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  agX : ds.AgreesAt (symTk2 "next") 4
  agO : ds.AgreesAt (symTk2 "owner") 4
  agC : ds.AgreesAt (symTk2 "counter") 4
  hxo : Decls.overlaps (symTk2 "next") 4 (symTk2 "owner") 4 = false
  hxc : Decls.overlaps (symTk2 "next") 4 (symTk2 "counter") 4 = false
  hoc : Decls.overlaps (symTk2 "owner") 4 (symTk2 "counter") 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, StartStateTk2 ds s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨symTk2 "next", 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨symTk2 "owner", 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨symTk2 "counter", 4⟩ = 0

/-- **The promise-free x64 ticket-lock liveness statement with declarations
`ds`** (`Ticket2X64.Ticket2X64LivePF` at `Tk2StartXD ds`). -/
def Ticket2X64LivePFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ N states initMem, Tk2StartXD ds N states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      Ticket2X64.Tk2WaitingX Ticket2X64.Tk2DoneX

theorem startStateTk2_noDecls {ds : Decls} {s : isa.State} (h : StartStateTk2 ds s) :
    StartStateTk2 {} (noD s) :=
  ⟨h.exe, rfl, h.pc, h.endPc, h.split⟩

/-- **Promise-free liveness of the x64 ticket lock with the runner's
declarations** (Stage 3, promise-free fragment; `ticketlock2.kl` verbatim):
on a valid layout of `tk2ImageV`, for every `ds` that resolves `next`,
`owner`, `counter` (4 bytes) to themselves, on every promise-free
stuttering `Arch.tso` trace from a `Tk2StartXD ds` configuration under weak
fairness and memory fairness, every waiting thread eventually leaves its
spin loop. `ticket2_x64_live_pf` transferred along `State.noDecls`
(`liveFrom_transfer`). -/
theorem ticket2_x64_live_pf_runner [Executable.ValidLayout (layout tk2ImageV)] (ds : Decls) (fuel : Nat) :
    Ticket2X64LivePFD ds fuel := by
  intro N states initMem hs
  refine liveFrom_transfer (execSimD (tk2ImageV_cellsDeclsAgree hs.agX hs.agO hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩) (fun _ _ => ?_) (fun _ _ => ?_) ?_
  · exact exists_mapC _ _ _ _
  · exact exists_mapC _ _ _ _
  · rw [mapC_init]
    exact Ticket2X64PF.ticket2_x64_live_pf fuel N _ initMem
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

/-- `ticket2_x64_live_pf_runner` at the runner's layout `tk2LayoutV` and
declarations `tk2DeclsD`. No hypothesis left. -/
theorem ticket2_x64_live_pf_runner_concrete (fuel : Nat) : @Ticket2X64LivePFD tk2LayoutV tk2DeclsD fuel :=
  @ticket2_x64_live_pf_runner tk2LayoutV tk2ValidV tk2DeclsD fuel

/-- **The runner's own configuration, `N` workers** (`ticketlock2.kl`:
`N = 2`): `N` copies of the runner's prepared worker `tk2WorkerD0`
(declarations `tk2DeclsD` included), the runner's initial memory, at its
layout, under `WeakFair ∧ MemFair ∧ PromiseFree`. No hypothesis left except
`N + 1 < 2 ^ 32`. -/
theorem ticket2_x64_live_pf_runnerN (fuel N : Nat) (hN32 : N + 1 < 2 ^ 32) :
    LiveFrom Arch.tso fuel (Config.init (List.replicate N tk2WorkerD0) tk2InitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      (@Ticket2X64.Tk2WaitingX tk2LayoutV) (@Ticket2X64.Tk2DoneX tk2LayoutV) := by
  refine ticket2_x64_live_pf_runner_concrete fuel N _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, hN32,
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

end Kraken.Promising.Live.RunnerX64Ticket2

#print axioms Kraken.Promising.Live.RunnerX64Ticket2.ticket2_x64_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerX64Ticket2.ticket2_x64_live_pf_runner_concrete
#print axioms Kraken.Promising.Live.RunnerX64Ticket2.ticket2_x64_live_pf_runnerN
