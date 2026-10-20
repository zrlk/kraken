/-
**Stage 3 liveness: weak scheduler fairness alone
does not give ticket-lock liveness**, even without promise steps; and the
official Stage 3 hypothesis `WeakFair ∧ MemFair` is satisfiable.

Program: `ticketlock2.kl` (the A64 `ldadda` ticket lock, the program of
`TicketLock.ticket_counter_envG`), two threads, from the runner's exact
initial configuration `c0` (checked by `reachA64RunnerMatches`).

**The lasso** (`ticket_lasso`): T0 takes ticket 0, T1 ticket 1; T0 reads
`owner = 0`, runs its critical section, releases (`stlr owner := 1`) and
halts; T1 then reads the *initial* `owner` message in its spin loop.
`readSuccs` lets a load read any message of the location with no write of
it in `(t, max νpre (coh l)]`; T1's bound stays below the release's
timestamp, so the stale message stays readable, and one `LDAR`/`CMP`/`B.NE`
iteration returns to the same configuration `cStar`. T0 is halted, hence
not enabled (`not_enabled_of_halted`). The periodic trace is weakly fair
(for all steps and for instruction steps), has no promise step, and T1
waits forever (`ticket_not_live_weakFair`).

**Non-vacuity** (`ticket_fair_exists`): a terminating run to a final
configuration, stuttering there, is a trace from `c0` satisfying
`WeakFair`, `WeakFairInstr`, `PromiseFree` and `MemFair`.

Concrete configurations are evaluated by the kernel (`decide +kernel`) with
`ReachA64Core`'s kernel-evaluable `exec`/`deps`; the cycle's equality is
`liveCfgEq_sound` (`LiveReach.lean`).

The lasso argument, generic in the start and loop configurations
(the promise-free liveness proofs' `TicketCexG.LassoChecks`, `lassoG`,
`lassoG_*`, `lasso_not_live`),
is stated in this file (namespace `TicketCexG`, same names), and this file's
`lasso` facts are its instances (`lasso_eq`, `lassoChecks`).
Those generic lemmas are in turn instances of the ISA- and
architecture-generic `Lasso.Spec` lasso (`LiveLasso.lean`) at `lassoSpec`,
shared with `LiveX64TicketCex.lean`.
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.LiveReach
import Kraken.Promising.LiveLasso
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Live.TicketCex

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Reach Kraken.Promising.Live

/-- The `code` block of `ticketlock2.kl`, verbatim. -/
def code : Program := parseAArch64("
worker:
  MOV W6,#1
  LDADDA W6,W3,[X0]
spin:
  LDAR W4,[X1]
  CMP W4,W3
  B.NE spin
  LDR W5,[X2]
  ADD W5,W5,#1
  STR W5,[X2]
  ADD W4,W3,#1
  STLR W4,[X1]
  B done
done:
")

/-- The runner's declarations for the typed header (`uint32_t next, owner,
counter`). -/
def decls : Decls := { locs := [⟨0x1000, 4⟩, ⟨0x1100, 4⟩, ⟨0x1200, 4⟩] }

/-- The initial memory: the three words at `0`. -/
def initMem : List (Loc × Val) := [(⟨0x1000, 4⟩, 0), (⟨0x1100, 4⟩, 0), (⟨0x1200, 4⟩, 0)]

/-- The runner's initial configuration: both threads from `worker` to
`done`, `X0 = next`, `X1 = owner`, `X2 = counter`. -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100000 0x10002c,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100000 0x10002c] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/ticketlock2.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-! ## Waiting and done -/

/-- The spin loop's addresses (`LDAR`, `CMP`, `B.NE`). -/
def spinPcs : List Int64 := [0x100008, 0x10000c, 0x100010]

/-- The addresses before the critical section. -/
def prePcs : List Int64 := [0x100000, 0x100004] ++ spinPcs

/-- Thread `tid` holds a ticket and spins. -/
def Waiting (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ spinPcs

/-- Thread `tid` is past the spin loop (in or after its critical section). -/
def Done (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ prePcs

/-! ## The runs -/

/-- `exec`/`deps` the kernel evaluates. -/
noncomputable abbrev exK := (reachA64ExecK : isa.State → Option (EvTree isa.State))
noncomputable abbrev dpK := (reachA64Deps : isa.State → InstrDeps isa.RegId)

theorem exK_eq : exK = isa.exec := reachA64ExecK_eq
theorem dpK_eq : dpK = isa.deps := reachA64Deps_eq

/-- To the lasso's loop: both tickets, T0's critical section and release,
T1's first spin iteration (reading the initial `owner`). -/
def prefixTr : List (Nat × List Nat) :=
  [(0, []), (0, [0, 1]), (1, []), (1, [1, 2]),
   (0, [0]), (0, []), (0, []), (0, [0]), (0, []), (0, [3]), (0, []), (0, [4]), (0, []),
   (1, [0]), (1, []), (1, [])]

/-- One spin iteration of T1 reading the initial `owner` message. -/
def loopTr : List (Nat × List Nat) := [(1, [0]), (1, []), (1, [])]

/-- From the loop to the end: T1 reads `owner = 1` and finishes. -/
def finTr : List (Nat × List Nat) :=
  [(1, [4]), (1, []), (1, []), (1, [3]), (1, []), (1, [5]), (1, []), (1, [6]), (1, [])]

theorem prefix_isSome : (reachRun exK dpK Arch.armv8 c0 prefixTr).isSome = true := by decide +kernel

/-- The configuration the lasso loops at. -/
@[irreducible] noncomputable def cStar : Config isa := (reachRun exK dpK Arch.armv8 c0 prefixTr).getD c0

theorem prefix_eq : reachRun isa.exec isa.deps Arch.armv8 c0 prefixTr = some cStar := by
  rw [← exK_eq, ← dpK_eq]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp prefix_isSome
  simp [cStar, hc]

theorem loop_check :
    (match reachRun exK dpK Arch.armv8 cStar loopTr with
      | some c => liveCfgEq cStar c
      | none => false) = true := by decide +kernel

/-- **The cycle**: one spin iteration of T1 returns to `cStar`. -/
theorem loop_eq : reachRun isa.exec isa.deps Arch.armv8 cStar loopTr = some cStar := by
  have h := loop_check
  rw [exK_eq, dpK_eq] at h
  split at h
  · rename_i c hc
    rw [hc, liveCfgEq_sound (reachRun_liveStatic Arch.armv8 hc) h]
  · cases h

/-! ## Facts about the configurations, by evaluation -/

/-- T0 halted, T1 spinning, two threads, no promises. -/
noncomputable def loopOk (c : Config isa) : Bool :=
  c.threads.size == 2 &&
    (match c.threads[0]? with | some t => (exK t.st).isNone | none => false) &&
    (match c.threads[1]? with | some t => spinPcs.contains t.st.st.2 | none => false) &&
    c.threads.all (·.prom.isEmpty)

theorem loopOk_all : (List.range 3).all (fun r => loopOk (liveRunAt exK dpK Arch.armv8 cStar loopTr r)) = true := by
  decide +kernel

theorem prefix_prom : (List.range 17).all
    (fun k => (liveRunAt exK dpK Arch.armv8 c0 prefixTr k).threads.all (·.prom.isEmpty)) = true := by
  decide +kernel

/-- A promise step leaves its thread with an outstanding promise (`PromiseBy.prom_ne`). -/
theorem promiseBy_prom {A : Arch} {tid : Nat} {c c' : Config isa} (h : PromiseBy A tid c c') :
    ∃ t', c'.threads[tid]? = some t' ∧ t'.prom ≠ [] :=
  h.prom_ne

end Kraken.Promising.Live.TicketCex

/-! ## The lasso, generic in the start configuration

Moved here from `LiveTicketCexG.lean` (same names, namespace
`Kraken.Promising.Live.TicketCexG`), so that this file's lasso `lasso` is
its instance at `c0`/`cStar` (`TicketCex.lasso_eq`, `TicketCex.lassoChecks`).
`lassoG_promiseFree`, `lassoG_weakFair` and `lassoG_weakFairInstr` are new:
`lasso_not_live`'s three fairness facts, stated once. -/

namespace Kraken.Promising.Live.TicketCexG

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Reach Kraken.Promising.Live
open Kraken.Promising.Live.TicketCex (prefixTr loopTr spinPcs prePcs Waiting Done loopOk exK dpK exK_eq dpK_eq
  promiseBy_prom)

/-- The kernel checks the lasso needs: the prefix replays from `c0` to `cS`,
one spin iteration of T1 returns to `cS`, the loop's configurations have T0
halted and T1 spinning (`loopOk`), and the prefix makes no promise. -/
structure LassoChecks (c0 cS : Config isa) : Prop where
  pre : reachRun isa.exec isa.deps Arch.armv8 c0 prefixTr = some cS
  loop : reachRun isa.exec isa.deps Arch.armv8 cS loopTr = some cS
  ok : (List.range 3).all (fun r => loopOk (liveRunAt exK dpK Arch.armv8 cS loopTr r)) = true
  prom : (List.range 17).all
    (fun k => (liveRunAt exK dpK Arch.armv8 c0 prefixTr k).threads.all (·.prom.isEmpty)) = true

section Generic

/-- The lasso's data: `ticketlock2`'s traces and addresses at
`Arch.armv8`, for the ISA-generic lasso `LiveLasso.lean`, whose lemmas the
ones below are. -/
noncomputable def lassoSpec : Lasso.Spec isa where
  A := Arch.armv8
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

theorem loopOk_spec (c : Config isa) : loopOk c = lassoSpec.loopOk c := by
  simp only [loopOk, Lasso.Spec.loopOk, lassoSpec]
  cases c.threads[0]? <;> cases c.threads[1]? <;> rfl

theorem LassoChecks.toSpec (hL : LassoChecks c0 cS) : lassoSpec.Checks c0 cS :=
  ⟨hL.pre, hL.loop, by have h := hL.ok; simp only [loopOk_spec] at h; exact h, hL.prom⟩

/-- The lasso from `c0`: `prefixTr`, then `loopTr` forever. -/
@[irreducible] noncomputable def lassoG (c0 cS : Config isa) (i : Nat) : Config isa :=
  if i < 16 then liveRunAt isa.exec isa.deps Arch.armv8 c0 prefixTr i
  else liveRunAt isa.exec isa.deps Arch.armv8 cS loopTr ((i - 16) % 3)

theorem lassoG_eq_spec : lassoG c0 cS = lassoSpec.lasso c0 cS := by
  funext i
  simp only [lassoG, Lasso.Spec.lasso]
  rfl

theorem lassoG_step (hL : LassoChecks c0 cS) (i : Nat) : ∃ tid sel,
    reachStep isa.exec isa.deps Arch.armv8 (lassoG c0 cS i) tid sel = some (lassoG c0 cS (i + 1)) ∧
      (16 ≤ i → tid = 1) := by
  rw [lassoG_eq_spec]; exact Lasso.Spec.lasso_step hL.toSpec i

theorem lassoG_loopOk (hL : LassoChecks c0 cS) {i : Nat} (hi : 16 ≤ i) :
    (lassoG c0 cS i).threads.size = 2 ∧ (∃ t, (lassoG c0 cS i).threads[0]? = some t ∧ t.halted = true) ∧
      Waiting 1 (lassoG c0 cS i) ∧ ¬ Done 1 (lassoG c0 cS i) := by
  rw [lassoG_eq_spec]; exact Lasso.Spec.lasso_loopOk hL.toSpec hi

theorem lassoG_prom (hL : LassoChecks c0 cS) (i tid : Nat) (t : Thread isa)
    (ht : (lassoG c0 cS i).threads[tid]? = some t) : t.prom = [] := by
  rw [lassoG_eq_spec] at ht; exact Lasso.Spec.lasso_prom hL.toSpec i tid t ht

theorem lassoG_scheduled (hL : LassoChecks c0 cS) {fuel i : Nat} (hi : 16 ≤ i) :
    InstrScheduledAt Arch.armv8 fuel (lassoG c0 cS) 1 i := by
  rw [lassoG_eq_spec]; exact Lasso.Spec.lasso_scheduled hL.toSpec hi

theorem lassoG_not_enabled (hL : LassoChecks c0 cS) {fuel tid i : Nat} (hi : 16 ≤ i) (htid : tid ≠ 1) :
    ¬ Enabled Arch.armv8 fuel tid (lassoG c0 cS i) := by
  rw [lassoG_eq_spec]; exact Lasso.Spec.lasso_not_enabled hL.toSpec hi htid

/-- The lasso makes no promise step. -/
theorem lassoG_promiseFree (hL : LassoChecks c0 cS) : PromiseFree Arch.armv8 (lassoG c0 cS) := by
  rw [lassoG_eq_spec]; exact Lasso.Spec.lasso_promiseFree hL.toSpec

/-- The lasso is weakly fair. -/
theorem lassoG_weakFair (hL : LassoChecks c0 cS) (fuel : Nat) : WeakFair Arch.armv8 fuel (lassoG c0 cS) := by
  rw [lassoG_eq_spec]; exact Lasso.Spec.lasso_weakFair hL.toSpec fuel

/-- The lasso is weakly fair for instruction steps. -/
theorem lassoG_weakFairInstr (hL : LassoChecks c0 cS) (fuel : Nat) :
    WeakFairInstr Arch.armv8 fuel (lassoG c0 cS) := by
  rw [lassoG_eq_spec]; exact Lasso.Spec.lasso_weakFairInstr hL.toSpec fuel

/-- The lasso as a trace. -/
noncomputable def lassoTraceG (hL : LassoChecks c0 cS) (fuel : Nat) : TraceS Arch.armv8 fuel isa :=
  ⟨lassoG c0 cS, fun i => .inl (reachStep_sound Arch.armv8 fuel (lassoG_step hL i).choose_spec.choose_spec.1)⟩

/-- **The lasso refutes weak-fairness-only liveness from any `c0` passing
the kernel checks** (`LiveTicketCex.ticket_not_live_weakFair`, generic). -/
theorem lasso_not_live (hL : LassoChecks c0 cS) (fuel : Nat) :
    ¬ LiveFrom Arch.armv8 fuel c0
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ WeakFairInstr Arch.armv8 fuel cfg ∧ PromiseFree Arch.armv8 cfg)
      Waiting Done :=
  Lasso.Spec.lasso_not_live hL.toSpec fuel

end Generic

end Kraken.Promising.Live.TicketCexG

namespace Kraken.Promising.Live.TicketCex

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Reach Kraken.Promising.Live
open Kraken.Promising.Live.TicketCexG (LassoChecks lassoG lassoG_step lassoG_loopOk lassoG_prom lassoG_not_enabled
  lassoG_promiseFree lassoG_scheduled lassoG_weakFair lassoG_weakFairInstr)

/-! ## The lasso trace -/

/-- The lasso: `prefixTr`, then `loopTr` forever. -/
@[irreducible] noncomputable def lasso (i : Nat) : Config isa :=
  if i < 16 then liveRunAt isa.exec isa.deps Arch.armv8 c0 prefixTr i
  else liveRunAt isa.exec isa.deps Arch.armv8 cStar loopTr ((i - 16) % 3)

/-- `lasso` is the generic lasso at `c0`/`cStar`. -/
theorem lasso_eq : lasso = lassoG c0 cStar := by
  funext i
  simp only [lasso, lassoG]

/-- The kernel checks at `c0`/`cStar`. -/
theorem lassoChecks : LassoChecks c0 cStar := ⟨prefix_eq, loop_eq, loopOk_all, prefix_prom⟩

theorem lasso_step (i : Nat) : ∃ tid sel, reachStep isa.exec isa.deps Arch.armv8 (lasso i) tid sel =
    some (lasso (i + 1)) ∧ (16 ≤ i → tid = 1) := by
  rw [lasso_eq]; exact lassoG_step lassoChecks i

/-- The lasso as a trace. -/
noncomputable def lassoTrace (fuel : Nat) : TraceS Arch.armv8 fuel isa :=
  ⟨lasso, fun i => .inl (reachStep_sound Arch.armv8 fuel (lasso_step i).choose_spec.choose_spec.1)⟩

theorem lasso_loopOk {i : Nat} (hi : 16 ≤ i) :
    (lasso i).threads.size = 2 ∧ (∃ t, (lasso i).threads[0]? = some t ∧ t.halted = true) ∧ Waiting 1 (lasso i) ∧
      ¬ Done 1 (lasso i) := by
  rw [lasso_eq]; exact lassoG_loopOk lassoChecks hi

theorem lasso_prom (i tid : Nat) (t : Thread isa) (ht : (lasso i).threads[tid]? = some t) : t.prom = [] := by
  rw [lasso_eq] at ht; exact lassoG_prom lassoChecks i tid t ht

/-! ## Fairness of the lasso -/

theorem lasso_not_enabled {fuel tid i : Nat} (hi : 16 ≤ i) (htid : tid ≠ 1) :
    ¬ Enabled Arch.armv8 fuel tid (lasso i) := by
  rw [lasso_eq]; exact lassoG_not_enabled lassoChecks hi htid

theorem lasso_promiseFree : PromiseFree Arch.armv8 lasso := by
  rw [lasso_eq]; exact lassoG_promiseFree lassoChecks

theorem lasso_scheduled {fuel i : Nat} (hi : 16 ≤ i) : InstrScheduledAt Arch.armv8 fuel lasso 1 i := by
  rw [lasso_eq]; exact lassoG_scheduled lassoChecks hi

theorem lasso_weakFair (fuel : Nat) : WeakFair Arch.armv8 fuel lasso := by
  rw [lasso_eq]; exact lassoG_weakFair lassoChecks fuel

theorem lasso_weakFairInstr (fuel : Nat) : WeakFairInstr Arch.armv8 fuel lasso := by
  rw [lasso_eq]; exact lassoG_weakFairInstr lassoChecks fuel

/-! ## The theorems -/

/-- **The lasso**: `cStar` is reachable from the runner's configuration
`c0`; from index 16 on, every step of `lasso` is an instruction step of T1,
T0 is halted (not enabled), and T1 waits (holds ticket 1, in its spin
loop) without reaching its critical section; `lasso` is `cStar` at index
16 and again at index 19, after one `LDAR`/`CMP`/`B.NE` iteration
(`loop_eq`). -/
theorem ticket_lasso (fuel : Nat) :
    Reachable Arch.armv8 fuel c0 cStar ∧
      (∀ i, 16 ≤ i → StepBy Arch.armv8 fuel 1 (lasso i) (lasso (i + 1)) ∧
        ¬ Enabled Arch.armv8 fuel 0 (lasso i) ∧ Waiting 1 (lasso i) ∧ ¬ Done 1 (lasso i)) ∧
      lasso 16 = cStar ∧ lasso 19 = cStar := by
  refine ⟨reachRun_sound Arch.armv8 fuel prefix_eq, fun i hi => ⟨?_, lasso_not_enabled hi (by omega),
    (lasso_loopOk hi).2.2⟩, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := lasso_scheduled (fuel := fuel) hi
    exact ⟨h1, .inl h2⟩
  · simp [lasso, liveRunAt_zero]
  · simp [lasso, liveRunAt_zero]

/-- **Weak fairness alone does not give ticket-lock liveness** (the
originally proposed statement is false): on `ticketlock2.kl` with two
threads, from the runner's configuration, some trace that is weakly fair
(for all steps and for instruction steps) and has no promise step has a
thread that waits forever. -/
theorem ticket_not_live_weakFair (fuel : Nat) :
    ¬ LiveFrom Arch.armv8 fuel c0
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ WeakFairInstr Arch.armv8 fuel cfg ∧ PromiseFree Arch.armv8 cfg)
      Waiting Done := by
  intro h
  obtain ⟨j, hj, hd⟩ := h (lassoTrace fuel) (by simp [lassoTrace, lasso, liveRunAt_zero])
    ⟨lasso_weakFair fuel, lasso_weakFairInstr fuel, lasso_promiseFree⟩ 1 16 (lasso_loopOk (Nat.le_refl _)).2.2.1
  exact (lasso_loopOk hj).2.2.2 hd

/-! ## Non-vacuity of `WeakFair ∧ MemFair` -/

theorem fin_check : reachCheck exK dpK Arch.armv8 c0 (prefixTr ++ finTr) (fun _ => true) = true := by
  decide +kernel

/-- The final configuration of the terminating run. -/
@[irreducible] noncomputable def cFin : Config isa := (reachRun isa.exec isa.deps Arch.armv8 c0 (prefixTr ++ finTr)).getD c0

theorem fin_eq : reachRun isa.exec isa.deps Arch.armv8 c0 (prefixTr ++ finTr) = some cFin ∧ cFin.final = true := by
  have h := fin_check
  rw [exK_eq, dpK_eq] at h
  unfold reachCheck at h
  split at h
  · rename_i c hc
    have hf : c.final = true := (Bool.and_eq_true _ _ ▸ h).1
    exact ⟨by simp [cFin, hc], by simpa [cFin, hc] using hf⟩
  · cases h

/-- The terminating run, then its final configuration forever. -/
@[irreducible] noncomputable def finRun (i : Nat) : Config isa :=
  if i < 25 then liveRunAt isa.exec isa.deps Arch.armv8 c0 (prefixTr ++ finTr) i else cFin

theorem finRun_reachStep {i : Nat} (hi : i < 25) :
    ∃ tid sel, reachStep isa.exec isa.deps Arch.armv8 (finRun i) tid sel = some (finRun (i + 1)) := by
  have := liveRunAt_step isa.exec isa.deps Arch.armv8 fin_eq.1 (k := i)
    (by simp only [prefixTr, finTr, List.length_append, List.length]; omega)
  by_cases hi' : i + 1 < 25
  · exact ⟨_, _, by simpa only [finRun, hi, ↓reduceIte, hi', ↓reduceIte] using this⟩
  · obtain rfl : i = 24 := by omega
    have hl : liveRunAt isa.exec isa.deps Arch.armv8 c0 (prefixTr ++ finTr) (24 + 1) = cFin :=
      liveRunAt_length _ _ _ fin_eq.1
    rw [hl] at this
    exact ⟨_, _, by simpa only [finRun, hi, ↓reduceIte, hi', ↓reduceIte] using this⟩

theorem finRun_ge {i : Nat} (hi : 25 ≤ i) : finRun i = cFin := by
  simp only [finRun, show ¬ i < 25 by omega, ↓reduceIte]

theorem fin_prom : (List.range 25).all
    (fun k => (liveRunAt exK dpK Arch.armv8 c0 (prefixTr ++ finTr) k).threads.all (·.prom.isEmpty)) = true := by
  decide +kernel

theorem finRun_prom (i tid : Nat) (t : Thread isa) (ht : (finRun i).threads[tid]? = some t) : t.prom = [] := by
  have hall : (finRun i).threads.all (·.prom.isEmpty) = true := by
    by_cases hi : i < 25
    · have h := List.all_eq_true.mp fin_prom i (List.mem_range.mpr hi)
      rw [exK_eq, dpK_eq] at h
      simpa only [finRun, hi, ↓reduceIte] using h
    · rw [finRun_ge (by omega)]
      exact Array.all_eq_true.mpr fun j hj => by
        have := (Array.all_eq_true.mp fin_eq.2) j hj
        simp only [Bool.and_eq_true] at this
        exact this.2
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  exact List.isEmpty_iff.mp ((Array.all_eq_true.mp hall) tid hlt)

theorem finRun_step (fuel i : Nat) : finRun (i + 1) ∈ (succs Arch.armv8 (finRun i) fuel).1 ∨
    ((finRun i).final = true ∧ finRun (i + 1) = finRun i) := by
  by_cases hi : i < 25
  · obtain ⟨_, _, h⟩ := finRun_reachStep hi
    exact .inl (reachStep_sound Arch.armv8 fuel h)
  · right
    rw [finRun_ge (by omega), finRun_ge (by omega)]
    exact ⟨fin_eq.2, rfl⟩

/-- The terminating run as a stuttering trace. -/
noncomputable def finTrace (fuel : Nat) : TraceS Arch.armv8 fuel isa := ⟨finRun, finRun_step fuel⟩

/-- A halted thread's `stepOne` is `none`. -/
theorem stepOne_halted {A : Arch} {t : Thread isa} {tid : Nat} {mem : Memory} (hh : t.halted = true) :
    stepOne A t tid mem = none := by
  simp only [Thread.halted, Option.isNone_iff_eq_none] at hh
  simp [stepOne, hh]

/-- At `cFin` every thread is halted. -/
theorem cFin_halted {tid : Nat} {t : Thread isa} (ht : cFin.threads[tid]? = some t) : t.halted = true := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  have hh := (Array.all_eq_true.mp fin_eq.2) tid hlt
  simp only [Bool.and_eq_true] at hh
  exact hh.1

/-- **`WeakFair ∧ MemFair` (with `WeakFairInstr` and `PromiseFree`) is
satisfiable from the runner's configuration**: the terminating run,
stuttering at its final configuration. From index 25 on no thread is
enabled and no thread reads, so every fairness condition holds. -/
theorem ticket_fair_exists (fuel : Nat) :
    ∃ tr : TraceS Arch.armv8 fuel isa, tr.cfg 0 = c0 ∧ WeakFair Arch.armv8 fuel tr.cfg ∧
      WeakFairInstr Arch.armv8 fuel tr.cfg ∧ PromiseFree Arch.armv8 tr.cfg ∧ MemFair Arch.armv8 tr.cfg := by
  have hfin : ∀ i, 25 ≤ i → finRun i = cFin := fun i hi => finRun_ge hi
  have hne : ∀ tid i, 25 ≤ i → ¬ Enabled Arch.armv8 fuel tid (finRun i) := fun tid i hi => by
    rw [hfin i hi]; exact not_enabled_of_final fin_eq.2
  refine ⟨finTrace fuel, by simp [finTrace, finRun, liveRunAt_zero], ?_, ?_, ?_, ?_⟩
  · rintro tid ⟨n, hn⟩
    exact absurd (hn (n + 25) (by omega)) (hne tid _ (by omega))
  · rintro tid ⟨n, hn⟩
    obtain ⟨c', h1, h2⟩ := hn (n + 25) (by omega)
    exact absurd ⟨c', h1, .inl h2⟩ (hne tid _ (by omega))
  · intro i tid hp
    obtain ⟨t', ht', hne'⟩ := promiseBy_prom hp
    exact hne' (finRun_prom (i + 1) tid t' ht')
  · intro tid l hinf
    obtain ⟨i, hi, ts, t, outs, o, ht, hs, -⟩ := hinf 25
    rw [show (finTrace fuel).cfg i = finRun i from rfl, hfin i hi] at ht hs
    rw [stepOne_halted (cFin_halted ht)] at hs
    cases hs

end Kraken.Promising.Live.TicketCex

#print axioms Kraken.Promising.Live.TicketCex.ticket_lasso
#print axioms Kraken.Promising.Live.TicketCex.ticket_not_live_weakFair
#print axioms Kraken.Promising.Live.TicketCex.ticket_fair_exists
