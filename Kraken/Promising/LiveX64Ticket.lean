/-
**Stage 3: the x64 ticket lock's liveness
statements** for the verbatim worker of `X64/ticketlock3.kl`
(`TicketX.tk3WorkerV`: `lock xaddl` take, `movl (owner)`/`cmpl`/`jne` spin,
release `addl $1,%ecx; movl %ecx,(owner)`), run in its image `tk3ImageV`
(the code, then the runner's data trailer; absolute operands `(next)`,
`(owner)`, `(counter)`, declarations `{}`), under `Arch.tso`. The x64
counterparts of `LiveTicket.lean`'s AArch64 statements.

Same start states as `TicketX.ticket3_counter_envG_verbatim`
(`TkStartX`: `N` workers at `StartStateTk {}`, the three symbols' words
pairwise disjoint, `N + 1 < 2 ^ 32`, the three words at `0`). A thread is
*waiting* (`TkWaitingX`) in its spin loop (positions 4–6 of `tk3ImageV`), and
*done* (`TkDoneX`) once past it (in or after its critical section).

- `TicketX64Live`: weak fairness and memory fairness, with promises (open).
- `TicketX64LivePF`: the promise-free fragment. **Proved at valid layouts**:
  `Live.TicketX64PF.ticket3_x64_live_pf` (`[ValidLayout (layout tk3ImageV)]`,
  `LiveX64TicketPF.lean`).
- `TicketX64LiveWF`: weak fairness alone. **False**, as on AArch64: a waiter
  can read the initial `owner` forever (`Live.TicketX64Cex.ticketX64LiveWF_false`
  at the runner's layout, a kernel-checked lasso, `LiveX64TicketCex.lean`).
  So `MemFair` is needed on TSO too.

`MemFair` on x86 is a modelling assumption (store buffers drain in finite
time, as in x86-TSO); see its docstring in `LiveTrace.lean`.
-/
import Kraken.Promising.SLR.EnvG.TicketXPublic
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.TicketX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV symTk StartStateTk)

variable [layout : _root_.Layout]

/-- The spin loop's addresses: `movl (owner),%ecx`, `cmpl`, `jne` (positions
4–6 of `tk3ImageV`; the label `spin`, position 3, is at the address of
position 4). -/
def tkSpinPcsX : List Int64 := [4, 5, 6].map (layout tk3ImageV).addrOf

/-- The addresses before the critical section (positions 0–6). -/
def tkPrePcsX : List Int64 := (List.range 7).map (layout tk3ImageV).addrOf

/-- Thread `tid` holds its ticket and spins. -/
def TkWaitingX (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ tkSpinPcsX

/-- Thread `tid` is past its spin loop: in or after its critical section. -/
def TkDoneX (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ tkPrePcsX

/-- **The start configurations of `ticket3_counter_envG_verbatim`**: `N`
verbatim workers at `StartStateTk {}`, the symbols' 4-byte words pairwise
disjoint, `N + 1 < 2 ^ 32`, the three words at `0`. -/
structure TkStartX (N : Nat) (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  hxo : Decls.overlaps (symTk "next") 4 (symTk "owner") 4 = false
  hxc : Decls.overlaps (symTk "next") 4 (symTk "counter") 4 = false
  hoc : Decls.overlaps (symTk "owner") 4 (symTk "counter") 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, StartStateTk {} s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨symTk "next", 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨symTk "owner", 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨symTk "counter", 4⟩ = 0

/-- x64 ticket-lock liveness under the trace hypothesis `Fair`: from every
start configuration, on every stuttering `Arch.tso` trace satisfying `Fair`,
every waiting thread is eventually done. -/
def TicketX64LiveUnder (fuel : Nat) (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ N states initMem, TkStartX N states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem) Fair TkWaitingX TkDoneX

/-- **x64 ticket-lock liveness under weak and memory fairness** (open, with
promises). -/
def TicketX64Live (fuel : Nat) : Prop :=
  TicketX64LiveUnder fuel fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg

/-- **The promise-free fragment** of `TicketX64Live`. Proved at valid
layouts: `Live.TicketX64PF.ticket3_x64_live_pf`. -/
def TicketX64LivePF (fuel : Nat) : Prop :=
  TicketX64LiveUnder fuel fun cfg =>
    WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg

/-- **Weak scheduler fairness alone**: false (`Live.TicketX64Cex.ticketX64LiveWF_false`,
at the runner's layout `tk3LayoutV`). -/
def TicketX64LiveWF (fuel : Nat) : Prop :=
  TicketX64LiveUnder fuel fun cfg => WeakFair Arch.tso fuel cfg

/-- A stronger hypothesis gives a weaker statement. -/
theorem TicketX64LiveUnder.mono {fuel : Nat} {F F' : (Nat → Config isa) → Prop} (h : TicketX64LiveUnder fuel F)
    (hF : ∀ cfg, F' cfg → F cfg) : TicketX64LiveUnder fuel F' :=
  fun N states initMem hs tr h0 hf => h N states initMem hs tr h0 (hF _ hf)

theorem ticketX64LivePF_of_live {fuel : Nat} (h : TicketX64Live fuel) : TicketX64LivePF fuel :=
  h.mono fun _ hf => ⟨hf.1, hf.2.1⟩

theorem ticketX64Live_of_wf {fuel : Nat} (h : TicketX64LiveWF fuel) : TicketX64Live fuel :=
  h.mono fun _ hf => hf.1

end Kraken.Promising.Live.TicketX64
