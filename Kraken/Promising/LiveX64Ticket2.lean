/-
**Stage 3: the liveness statements of the x64 ticket
lock with an unlocked release** for the verbatim worker of
`X64/ticketlock2.kl` (`TicketX2.tk2WorkerV`: `lock xaddl` take,
`movl (owner)`/`cmpl`/`jne` spin, release `incl (owner)`, a plain load and a
plain store), run in its image `tk2ImageV` (the code, then the runner's data
trailer; absolute operands `(next)`, `(owner)`, `(counter)`, declarations
`{}`), under `Arch.tso`. The `ticketlock2` twins of `LiveX64Ticket.lean`'s
statements (same shape: `TicketX64LiveUnder` with `tk3ImageV` replaced by
`tk2ImageV`).

Same start states as `TicketX2.ticket2_counter_envG_verbatim`
(`Tk2StartX`: `N` workers at `StartStateTk2 {}`, the three symbols' words
pairwise disjoint, `N + 1 < 2 ^ 32`, the three words at `0`). A thread is
*waiting* (`Tk2WaitingX`) in its spin loop (positions 4–6 of `tk2ImageV`),
and *done* (`Tk2DoneX`) once past it (in or after its critical section).

- `Ticket2X64Live`: weak fairness and memory fairness, with promises (open).
- `Ticket2X64LivePF`: the promise-free fragment. **Proved at valid layouts**:
  `Live.Ticket2X64PF.ticket2_x64_live_pf` (`[ValidLayout (layout tk2ImageV)]`,
  `LiveX64Ticket2PF.lean`).
- `Ticket2X64LiveWF`: weak fairness alone. False at the runner layout:
  `Live.Ticket2X64Cex.ticket2X64LiveWF_false` (`LiveX64Ticket2Cex.lean`), a
  lasso of the same shape as ticketlock3's (a waiter reads the initial
  `owner` forever after the holder halted).

`MemFair` on x86 is a modelling assumption (store buffers drain in finite
time, as in x86-TSO); see its docstring in `LiveTrace.lean`.
-/
import Kraken.Promising.SLR.EnvG.X64Ticket2Public
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.Ticket2X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV symTk2 StartStateTk2)

variable [layout : _root_.Layout]

/-- The spin loop's addresses: `movl (owner),%ecx`, `cmpl`, `jne` (positions
4–6 of `tk2ImageV`; the label `spin`, position 3, is at the address of
position 4). -/
def tk2SpinPcsX : List Int64 := [4, 5, 6].map (layout tk2ImageV).addrOf

/-- The addresses before the critical section (positions 0–6). -/
def tk2PrePcsX : List Int64 := (List.range 7).map (layout tk2ImageV).addrOf

/-- Thread `tid` holds its ticket and spins. -/
def Tk2WaitingX (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ tk2SpinPcsX

/-- Thread `tid` is past its spin loop: in or after its critical section. -/
def Tk2DoneX (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ tk2PrePcsX

/-- **The start configurations of `ticket2_counter_envG_verbatim`**: `N`
verbatim workers at `StartStateTk2 {}`, the symbols' 4-byte words pairwise
disjoint, `N + 1 < 2 ^ 32`, the three words at `0`. -/
structure Tk2StartX (N : Nat) (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  hxo : Decls.overlaps (symTk2 "next") 4 (symTk2 "owner") 4 = false
  hxc : Decls.overlaps (symTk2 "next") 4 (symTk2 "counter") 4 = false
  hoc : Decls.overlaps (symTk2 "owner") 4 (symTk2 "counter") 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, StartStateTk2 {} s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨symTk2 "next", 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨symTk2 "owner", 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨symTk2 "counter", 4⟩ = 0

/-- `ticketlock2` liveness under the trace hypothesis `Fair`: from every
start configuration, on every stuttering `Arch.tso` trace satisfying `Fair`,
every waiting thread is eventually done. -/
def Ticket2X64LiveUnder (fuel : Nat) (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ N states initMem, Tk2StartX N states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem) Fair Tk2WaitingX Tk2DoneX

/-- **`ticketlock2` liveness under weak and memory fairness** (open, with
promises). -/
def Ticket2X64Live (fuel : Nat) : Prop :=
  Ticket2X64LiveUnder fuel fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg

/-- **The promise-free fragment** of `Ticket2X64Live`. Proved at valid
layouts: `Live.Ticket2X64PF.ticket2_x64_live_pf`. -/
def Ticket2X64LivePF (fuel : Nat) : Prop :=
  Ticket2X64LiveUnder fuel fun cfg =>
    WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg

/-- **Weak scheduler fairness alone**: false at the runner layout
(`Live.Ticket2X64Cex.ticket2X64LiveWF_false`). -/
def Ticket2X64LiveWF (fuel : Nat) : Prop :=
  Ticket2X64LiveUnder fuel fun cfg => WeakFair Arch.tso fuel cfg

/-- A stronger hypothesis gives a weaker statement. -/
theorem Ticket2X64LiveUnder.mono {fuel : Nat} {F F' : (Nat → Config isa) → Prop} (h : Ticket2X64LiveUnder fuel F)
    (hF : ∀ cfg, F' cfg → F cfg) : Ticket2X64LiveUnder fuel F' :=
  fun N states initMem hs tr h0 hf => h N states initMem hs tr h0 (hF _ hf)

theorem ticket2X64LivePF_of_live {fuel : Nat} (h : Ticket2X64Live fuel) : Ticket2X64LivePF fuel :=
  h.mono fun _ hf => ⟨hf.1, hf.2.1⟩

theorem ticket2X64Live_of_wf {fuel : Nat} (h : Ticket2X64LiveWF fuel) : Ticket2X64Live fuel :=
  h.mono fun _ hf => hf.1

end Kraken.Promising.Live.Ticket2X64
