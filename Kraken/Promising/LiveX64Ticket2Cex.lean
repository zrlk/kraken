/-
**Stage 3: `Ticket2X64LiveWF` is false**: weak
scheduler fairness alone does not give liveness of the x64 ticket lock with
the unlocked release (`X64/ticketlock2.kl`), even without promise steps and
under `Arch.tso`. The `ticketlock2` twin of `LiveX64TicketCex.lean`
(`ticketX64LiveWF_false`), an instance of the generic lasso `Lasso.Spec`
(`LiveLasso.lean`) at `lassoSpec2`.

Configuration (`c0T2`): two verbatim `ticketlock2.kl` workers (`tk2ImageV`)
laid out by the `.kl` runner's layout `tk2LayoutV`, no declarations
(`StartStateTk2 {}`), the runner's initial memory (`tk2InitMemV`); it is a
`Tk2StartX` configuration (`c0T2_start`).

**The lasso**: T0 takes ticket 0, T1 ticket 1 (both `lock xaddl`); T0 reads
`owner = 0`, runs its critical section, releases (`incl (owner)`: it reads
the initial `owner` message and appends `owner := 1`) and halts at `done`;
T1 then reads the *initial* `owner` message in its spin loop, forever (its
coherence bound stays below the release's timestamp). The prefix is 14
steps of the two workers and one spin iteration of T1 plus T1's next
`movl (owner),%ecx` (16 steps, `Lasso.Spec`'s prefix length); the loop is
T1's `cmpl`/`jne`/`movl` rotation, returning to `cST2`. T0 is halted, hence
not enabled; the trace is weakly fair and promise-free, and T1 waits forever.

The configurations are evaluated by the kernel (`decide +kernel`) with
`ReachX64Core`'s `reachExecK`/`reachDeps`; the loop configuration is
`@[irreducible]`.
-/
import Kraken.Promising.LiveX64Ticket2
import Kraken.Promising.LiveX64TicketCex
import Kraken.Promising.SLR.EnvG.X64Ticket2Runner

namespace Kraken.Promising.Live.Ticket2X64Cex

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Reach Kraken.Promising.Live
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV StartStateTk2)
open Kraken.Promising.X64.EnvG.TicketX2.Concrete (tk2LayoutV tk2InitMemV labTk2_at symTk2_next symTk2_owner
  symTk2_counter)
open Kraken.Promising.Live.Ticket2X64 (Tk2StartX Tk2WaitingX Tk2DoneX Ticket2X64LiveWF tk2SpinPcsX tk2PrePcsX)
open Kraken.Promising.Live.TicketX64Cex (exK dpK exK_eq dpK_eq spinPcs prePcs)

/-! ## The configuration -/

/-- A verbatim `ticketlock2` worker as the runner lays it out, with no
declarations: the image at `tk2LayoutV`, pc at `worker` (`0x100000`), end at
`done` (`0x10000a`), empty registers and private memory. -/
def tk2WorkerE : X64.State where
  exe := tk2LayoutV tk2ImageV
  endPc := 0x100000 + 10
  st := ({}, 0x100000)
  decls := {}

/-- Two workers from `tk2WorkerE`, the runner's initial memory. -/
def c0T2 : Config isa := Config.init [tk2WorkerE, tk2WorkerE] tk2InitMemV

/-! ## The lasso's data -/

/-- To the lasso's loop: both tickets; T0's spin read, critical section,
release (`incl (owner)`: read selection `0`, write selection `4`) and `jmp`;
T1's first spin iteration and next `movl (owner),%ecx`, reading the initial
`owner`. -/
def prefixTr2 : List (Nat × List Nat) :=
  [(0, []), (0, [0, 1]), (1, []), (1, [1, 2]),
   (0, [0]), (0, []), (0, []), (0, [0]), (0, []), (0, [3]), (0, [0, 4]), (0, []),
   (1, [0]), (1, []), (1, []), (1, [0])]

/-- T1's `cmpl`/`jne`/`movl (owner),%ecx` (reading the initial `owner`). -/
def loopTr2 : List (Nat × List Nat) := [(1, []), (1, []), (1, [0])]

/-- The lasso's data at `Arch.tso`; the spin addresses at `tk2LayoutV` are
ticketlock3's (`0x100002`–`0x100004`). -/
noncomputable def lassoSpec2 : Lasso.Spec isa where
  A := Arch.tso
  ex := exK
  dp := dpK
  ex_eq := exK_eq
  dp_eq := dpK_eq
  pcOf s := s.st.2
  spinPcs := spinPcs
  prePcs := prePcs
  spin_pre _ h := List.mem_append_right _ h
  prefixTr := prefixTr2
  loopTr := loopTr2
  prefix_len := rfl
  loop_len := rfl
  loop_tid r h := by
    simp only [loopTr2, List.length] at h
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> rfl

/-! ## The kernel checks at `c0T2` -/

theorem prefix2_isSome : (reachRun exK dpK Arch.tso c0T2 prefixTr2).isSome = true := by decide +kernel

/-- The loop configuration from `c0T2`. -/
@[irreducible] noncomputable def cST2 : Config isa := (reachRun exK dpK Arch.tso c0T2 prefixTr2).getD c0T2

theorem prefix2_eq : reachRun isa.exec isa.deps Arch.tso c0T2 prefixTr2 = some cST2 := by
  rw [← exK_eq, ← dpK_eq]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp prefix2_isSome
  simp [cST2, hc]

theorem loop2_check :
    (match reachRun exK dpK Arch.tso cST2 loopTr2 with
      | some c => liveCfgEq cST2 c
      | none => false) = true := by decide +kernel

/-- **The cycle**: T1's `cmpl`/`jne`/`movl` returns to `cST2`. -/
theorem loop2_eq : reachRun isa.exec isa.deps Arch.tso cST2 loopTr2 = some cST2 := by
  have h := loop2_check
  rw [exK_eq, dpK_eq] at h
  split at h
  · rename_i c hc
    rw [hc, liveCfgEq_sound (reachRun_liveStatic Arch.tso hc) h]
  · cases h

theorem lassoChecks2 : lassoSpec2.Checks c0T2 cST2 where
  pre := prefix2_eq
  loop := loop2_eq
  ok := by decide +kernel
  prom := by decide +kernel

/-! ## `c0T2` is a start configuration -/

section
attribute [local instance] tk2LayoutV

theorem tk2WorkerE_start : StartStateTk2 {} tk2WorkerE :=
  ⟨rfl, rfl, by show _ = Kraken.Promising.X64.EnvG.TicketX2.labTk2 "worker"; rw [labTk2_at 0]; decide,
    by show _ = Kraken.Promising.X64.EnvG.TicketX2.labTk2 "done"; rw [labTk2_at 12]; decide, Split.empty _⟩

/-- `c0T2` is a `Tk2StartX` configuration at the runner's layout. -/
theorem c0T2_start : Tk2StartX 2 [tk2WorkerE, tk2WorkerE] tk2InitMemV where
  hxo := by rw [symTk2_next, symTk2_owner]; decide
  hxc := by rw [symTk2_next, symTk2_counter]; decide
  hoc := by rw [symTk2_owner, symTk2_counter]; decide
  hN32 := by decide
  hst := fun s hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact tk2WorkerE_start
    rcases List.mem_cons.mp hs with rfl | hs
    · exact tk2WorkerE_start
    exact absurd hs List.not_mem_nil
  hN := rfl
  hX0 := by rw [symTk2_next]; simp only [Config.init_mem]; decide
  hO0 := by rw [symTk2_owner]; simp only [Config.init_mem]; decide
  hC0 := by rw [symTk2_counter]; simp only [Config.init_mem]; decide

theorem tk2Waiting_iff (tid : Nat) (c : Config isa) : Tk2WaitingX tid c ↔ lassoSpec2.Waiting tid c := by
  have : tk2SpinPcsX = spinPcs := by decide +kernel
  simp only [Tk2WaitingX, Lasso.Spec.Waiting, lassoSpec2, this]

theorem tk2Done_iff (tid : Nat) (c : Config isa) : Tk2DoneX tid c ↔ lassoSpec2.Done tid c := by
  have : tk2PrePcsX = [0x100000, 0x100000, 0x100001, 0x100002, 0x100002, 0x100003, 0x100004] := by
    decide +kernel
  have hm : ∀ p : Int64, p ∈ tk2PrePcsX ↔ p ∈ prePcs := by
    intro p
    rw [this]
    simp only [prePcs, spinPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h | h | h | h | h) <;> simp [h]
    · rintro (h | h | h | h | h) <;> simp [h]
  simp only [Tk2DoneX, Lasso.Spec.Done, lassoSpec2, hm]

end

/-! ## The theorem -/

/-- **`Ticket2X64LiveWF` is false** (at the runner's layout `tk2LayoutV`, for
every `fuel`): two verbatim `ticketlock2` workers from the `Tk2StartX`
configuration `c0T2` have a weakly fair, promise-free `Arch.tso` trace on
which T1 waits forever. Weak fairness alone does not give liveness of the
unlocked-release ticket lock either: `MemFair` is needed on TSO. -/
theorem ticket2X64LiveWF_false (fuel : Nat) : ¬ @Ticket2X64LiveWF tk2LayoutV fuel := by
  intro h
  refine Lasso.Spec.lasso_not_live lassoChecks2 fuel fun tr h0 hf tid i hw => ?_
  obtain ⟨j, hj, hd⟩ := h 2 _ _ c0T2_start tr h0 hf.1 tid i ((tk2Waiting_iff tid _).mpr hw)
  exact ⟨j, hj, (tk2Done_iff tid _).mp hd⟩

end Kraken.Promising.Live.Ticket2X64Cex
