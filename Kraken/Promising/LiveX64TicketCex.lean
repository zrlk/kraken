/-
**Stage 3: `TicketX64LiveWF` is false**:
weak scheduler fairness alone does not give x64 ticket-lock liveness, even
without promise steps and under `Arch.tso`. So `MemFair` is needed on TSO in
this model too (as on AArch64: `LiveTicketCex.lean`, `LiveTicketCexG.lean`).

Configuration (`c0X`): two verbatim `ticketlock3.kl` workers (`tk3ImageV`)
laid out by the `.kl` runner's layout `tk3LayoutV`, no declarations
(`StartStateTk {}`), the runner's initial memory (`tk3InitMemV`); it is a
`TkStartX` configuration (`c0X_start`).

**The lasso**: T0 takes ticket 0, T1 ticket 1 (both `lock xaddl`); T0 reads
`owner = 0`, runs its critical section, releases (`movl %ecx,(owner)`, `owner
:= 1`) and halts at `done`; T1 then reads the *initial* `owner` message in
its spin loop: a plain load's coherence bound (`max readPre (coh owner)`)
stays below the release's timestamp, the fences of T1's `lock xaddl` only
raise it to that RMW's own write. One `movl`/`cmpl`/`jne` iteration returns
to the same configuration `cSX`. T0 is halted, hence not enabled. The trace
is weakly fair (for all steps and for instruction steps), has no promise
step, and T1 waits forever.

The configurations are evaluated by the kernel (`decide +kernel`) with
`ReachX64Core`'s kernel-evaluable `reachExecK`/`reachDeps`; the cycle's
equality is `liveCfgEq_sound`. The loop configuration is `@[irreducible]`.

`LassoChecksX`/`lassoX`/`lassoX_*`/`lassoX_not_live` are `LiveTicketCex.lean`'s
generic lasso (`TicketCexG.LassoChecks`, …) at x64 and `Arch.tso`; both are
instances of the ISA- and architecture-generic
`Lasso.Spec` lasso (`LiveLasso.lean`, at `lassoSpecX` here).
-/
import Kraken.Promising.LiveX64Ticket
import Kraken.Promising.ReachX64Core
import Kraken.Promising.LiveReach
import Kraken.Promising.LiveLasso
import Kraken.Promising.CertifyX64
import Kraken.Promising.SLR.EnvG.TicketXRunner

namespace Kraken.Promising.Live.TicketX64Cex

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Reach Kraken.Promising.Live
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV StartStateTk)
open Kraken.Promising.X64.EnvG.TicketX.Concrete (tk3LayoutV tk3InitMemV labTk_at symTk_next symTk_owner
  symTk_counter)
open Kraken.Promising.Live.TicketX64 (TkStartX TkWaitingX TkDoneX TicketX64LiveWF tkSpinPcsX tkPrePcsX)

/-! ## The configuration -/

/-- A verbatim worker as the runner lays it out, with no declarations: the
image at `tk3LayoutV`, pc at `worker` (`0x100000`), end at `done`
(`0x10000b`), empty registers and private memory. -/
def tk3WorkerE : X64.State where
  exe := tk3LayoutV tk3ImageV
  endPc := 0x100000 + 11
  st := ({}, 0x100000)
  decls := {}

/-- Two workers from `tk3WorkerE`, the runner's initial memory. -/
def c0X : Config isa := Config.init [tk3WorkerE, tk3WorkerE] tk3InitMemV

/-- The spin loop's addresses at `tk3LayoutV`. -/
def spinPcs : List Int64 := [0x100002, 0x100003, 0x100004]

/-- The addresses before the critical section at `tk3LayoutV`. -/
def prePcs : List Int64 := [0x100000, 0x100001] ++ spinPcs

/-- Thread `tid` holds a ticket and spins. -/
def Waiting (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ spinPcs

/-- Thread `tid` is past the spin loop. -/
def Done (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ prePcs

/-! ## The runs -/

/-- `exec`/`deps` the kernel evaluates. -/
noncomputable abbrev exK := (reachExecK : isa.State → Option (EvTree isa.State))
noncomputable abbrev dpK := (reachDeps : isa.State → InstrDeps isa.RegId)

theorem exK_eq : exK = isa.exec := reachExecK_eq
theorem dpK_eq : dpK = isa.deps := reachDeps_eq

/-- To the lasso's loop: both tickets, T0's critical section and release,
T1's first spin iteration (reading the initial `owner`). The selections are
the read/write timestamps (`ReachSel`). -/
def prefixTr : List (Nat × List Nat) :=
  [(0, []), (0, [0, 1]), (1, []), (1, [1, 2]),
   (0, [0]), (0, []), (0, []), (0, [0]), (0, []), (0, [3]), (0, []), (0, [4]), (0, []),
   (1, [0]), (1, []), (1, [])]

/-- One spin iteration of T1 reading the initial `owner` message. -/
def loopTr : List (Nat × List Nat) := [(1, [0]), (1, []), (1, [])]

/-- T0 halted, T1 spinning, two threads, no promises. -/
noncomputable def loopOk (c : Config isa) : Bool :=
  c.threads.size == 2 &&
    (match c.threads[0]? with | some t => (exK t.st).isNone | none => false) &&
    (match c.threads[1]? with | some t => spinPcs.contains t.st.st.2 | none => false) &&
    c.threads.all (·.prom.isEmpty)

/-- A promise step leaves its thread with an outstanding promise (formerly a
copy of `TicketCex.promiseBy_prom`; `PromiseBy.prom_ne`). -/
theorem promiseBy_prom {A : Arch} {tid : Nat} {c c' : Config isa} (h : PromiseBy A tid c c') :
    ∃ t', c'.threads[tid]? = some t' ∧ t'.prom ≠ [] :=
  h.prom_ne

/-! ## The lasso, generic in the start configuration (`Lasso.Spec` at `lassoSpecX`) -/

/-- The kernel checks the lasso needs (`TicketCexG.LassoChecks` at x64). -/
structure LassoChecksX (c0 cS : Config isa) : Prop where
  pre : reachRun isa.exec isa.deps Arch.tso c0 prefixTr = some cS
  loop : reachRun isa.exec isa.deps Arch.tso cS loopTr = some cS
  ok : (List.range 3).all (fun r => loopOk (liveRunAt exK dpK Arch.tso cS loopTr r)) = true
  prom : (List.range 17).all
    (fun k => (liveRunAt exK dpK Arch.tso c0 prefixTr k).threads.all (·.prom.isEmpty)) = true

section Generic

/-- The lasso's data: the traces and addresses at `Arch.tso`, for
the ISA-generic lasso `LiveLasso.lean`, whose lemmas the ones below are. -/
noncomputable def lassoSpecX : Lasso.Spec isa where
  A := Arch.tso
  ex := exK
  dp := dpK
  ex_eq := exK_eq
  dp_eq := dpK_eq
  pcOf s := s.st.2
  spinPcs := spinPcs
  prePcs := prePcs
  spin_pre _ h := List.mem_append_right _ h
  prefixTr := prefixTr
  loopTr := loopTr
  prefix_len := rfl
  loop_len := rfl
  loop_tid r h := by
    simp only [loopTr, List.length] at h
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> rfl

variable {c0 cS : Config isa}

theorem loopOk_spec (c : Config isa) : loopOk c = lassoSpecX.loopOk c := by
  simp only [loopOk, Lasso.Spec.loopOk, lassoSpecX]
  cases c.threads[0]? <;> cases c.threads[1]? <;> rfl

theorem LassoChecksX.toSpec (hL : LassoChecksX c0 cS) : lassoSpecX.Checks c0 cS :=
  ⟨hL.pre, hL.loop, by have h := hL.ok; simp only [loopOk_spec] at h; exact h, hL.prom⟩

/-- The lasso from `c0`: `prefixTr`, then `loopTr` forever. -/
@[irreducible] noncomputable def lassoX (c0 cS : Config isa) (i : Nat) : Config isa :=
  if i < 16 then liveRunAt isa.exec isa.deps Arch.tso c0 prefixTr i
  else liveRunAt isa.exec isa.deps Arch.tso cS loopTr ((i - 16) % 3)

theorem lassoX_eq_spec : lassoX c0 cS = lassoSpecX.lasso c0 cS := by
  funext i
  simp only [lassoX, Lasso.Spec.lasso]
  rfl

theorem lassoX_step (hL : LassoChecksX c0 cS) (i : Nat) : ∃ tid sel,
    reachStep isa.exec isa.deps Arch.tso (lassoX c0 cS i) tid sel = some (lassoX c0 cS (i + 1)) ∧
      (16 ≤ i → tid = 1) := by
  rw [lassoX_eq_spec]; exact Lasso.Spec.lasso_step hL.toSpec i

theorem lassoX_loopOk (hL : LassoChecksX c0 cS) {i : Nat} (hi : 16 ≤ i) :
    (lassoX c0 cS i).threads.size = 2 ∧ (∃ t, (lassoX c0 cS i).threads[0]? = some t ∧ t.halted = true) ∧
      Waiting 1 (lassoX c0 cS i) ∧ ¬ Done 1 (lassoX c0 cS i) := by
  rw [lassoX_eq_spec]; exact Lasso.Spec.lasso_loopOk hL.toSpec hi

theorem lassoX_prom (hL : LassoChecksX c0 cS) (i tid : Nat) (t : Thread isa)
    (ht : (lassoX c0 cS i).threads[tid]? = some t) : t.prom = [] := by
  rw [lassoX_eq_spec] at ht; exact Lasso.Spec.lasso_prom hL.toSpec i tid t ht

theorem lassoX_scheduled (hL : LassoChecksX c0 cS) {fuel i : Nat} (hi : 16 ≤ i) :
    InstrScheduledAt Arch.tso fuel (lassoX c0 cS) 1 i := by
  rw [lassoX_eq_spec]; exact Lasso.Spec.lasso_scheduled hL.toSpec hi

theorem lassoX_not_enabled (hL : LassoChecksX c0 cS) {fuel tid i : Nat} (hi : 16 ≤ i) (htid : tid ≠ 1) :
    ¬ Enabled Arch.tso fuel tid (lassoX c0 cS i) := by
  rw [lassoX_eq_spec]; exact Lasso.Spec.lasso_not_enabled hL.toSpec hi htid

/-- The lasso as a trace. -/
noncomputable def lassoTraceX (hL : LassoChecksX c0 cS) (fuel : Nat) : TraceS Arch.tso fuel isa :=
  ⟨lassoX c0 cS, fun i => .inl (reachStep_sound Arch.tso fuel (lassoX_step hL i).choose_spec.choose_spec.1)⟩

/-- **The lasso refutes weak-fairness-only liveness from any `c0` passing
the kernel checks.** -/
theorem lassoX_not_live (hL : LassoChecksX c0 cS) (fuel : Nat) :
    ¬ LiveFrom Arch.tso fuel c0
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ WeakFairInstr Arch.tso fuel cfg ∧ PromiseFree Arch.tso cfg)
      Waiting Done :=
  Lasso.Spec.lasso_not_live hL.toSpec fuel

end Generic

/-! ## The kernel checks at `c0X` -/

theorem prefix_isSome : (reachRun exK dpK Arch.tso c0X prefixTr).isSome = true := by decide +kernel

/-- The loop configuration from `c0X`. -/
@[irreducible] noncomputable def cSX : Config isa := (reachRun exK dpK Arch.tso c0X prefixTr).getD c0X

theorem prefix_eq : reachRun isa.exec isa.deps Arch.tso c0X prefixTr = some cSX := by
  rw [← exK_eq, ← dpK_eq]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp prefix_isSome
  simp [cSX, hc]

theorem loop_check :
    (match reachRun exK dpK Arch.tso cSX loopTr with
      | some c => liveCfgEq cSX c
      | none => false) = true := by decide +kernel

/-- **The cycle**: one spin iteration of T1 returns to `cSX`. -/
theorem loop_eq : reachRun isa.exec isa.deps Arch.tso cSX loopTr = some cSX := by
  have h := loop_check
  rw [exK_eq, dpK_eq] at h
  split at h
  · rename_i c hc
    rw [hc, liveCfgEq_sound (reachRun_liveStatic Arch.tso hc) h]
  · cases h

theorem lassoChecks : LassoChecksX c0X cSX where
  pre := prefix_eq
  loop := loop_eq
  ok := by decide +kernel
  prom := by decide +kernel

/-! ## `c0X` is a start configuration -/

section
attribute [local instance] tk3LayoutV

theorem tk3WorkerE_start : StartStateTk {} tk3WorkerE :=
  ⟨rfl, rfl, by show _ = Kraken.Promising.X64.EnvG.TicketX.labTk "worker"; rw [labTk_at 0]; decide,
    by show _ = Kraken.Promising.X64.EnvG.TicketX.labTk "done"; rw [labTk_at 13]; decide, Split.empty _⟩

/-- `c0X` is a `TkStartX` configuration at the runner's layout. -/
theorem c0X_start : TkStartX 2 [tk3WorkerE, tk3WorkerE] tk3InitMemV where
  hxo := by rw [symTk_next, symTk_owner]; decide
  hxc := by rw [symTk_next, symTk_counter]; decide
  hoc := by rw [symTk_owner, symTk_counter]; decide
  hN32 := by decide
  hst := fun s hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact tk3WorkerE_start
    rcases List.mem_cons.mp hs with rfl | hs
    · exact tk3WorkerE_start
    exact absurd hs List.not_mem_nil
  hN := rfl
  hX0 := by rw [symTk_next]; simp only [Config.init_mem]; decide
  hO0 := by rw [symTk_owner]; simp only [Config.init_mem]; decide
  hC0 := by rw [symTk_counter]; simp only [Config.init_mem]; decide

theorem tkWaiting_iff (tid : Nat) (c : Config isa) : TkWaitingX tid c ↔ Waiting tid c := by
  have : tkSpinPcsX = spinPcs := by decide +kernel
  simp only [TkWaitingX, Waiting, this]

theorem tkDone_iff (tid : Nat) (c : Config isa) : TkDoneX tid c ↔ Done tid c := by
  have : tkPrePcsX = [0x100000, 0x100000, 0x100001, 0x100002, 0x100002, 0x100003, 0x100004] := by
    decide +kernel
  have hm : ∀ p : Int64, p ∈ tkPrePcsX ↔ p ∈ prePcs := by
    intro p
    rw [this]
    simp only [prePcs, spinPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h | h | h | h | h) <;> simp [h]
    · rintro (h | h | h | h | h) <;> simp [h]
  simp only [TkDoneX, Done, hm]

end

/-! ## The theorem -/

/-- **`TicketX64LiveWF` is false** (at the runner's layout `tk3LayoutV`, for
every `fuel`): two verbatim workers from the `TkStartX` configuration `c0X`
have a weakly fair, promise-free `Arch.tso` trace on which T1 waits
forever. Weak fairness alone does not give x64 ticket-lock liveness:
`MemFair` is needed on TSO too. -/
theorem ticketX64LiveWF_false (fuel : Nat) : ¬ @TicketX64LiveWF tk3LayoutV fuel := by
  intro h
  refine lassoX_not_live lassoChecks fuel fun tr h0 hf tid i hw => ?_
  obtain ⟨j, hj, hd⟩ := h 2 _ _ c0X_start tr h0 hf.1 tid i ((tkWaiting_iff tid _).mpr hw)
  exact ⟨j, hj, (tkDone_iff tid _).mp hd⟩

end Kraken.Promising.Live.TicketX64Cex
