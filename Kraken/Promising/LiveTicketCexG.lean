/-
**Stage 3: `TicketLiveWF` is false, literally.**

`LiveTicketCex.lean` refutes weak-fairness-only liveness on the runner's
configuration of `ticketlock2.kl` (typed declarations). `TicketLiveWF`
(`LiveTicket.lean`) quantifies over `TkStart` configurations, whose threads
have `decls = {}` and the ambient layout. This file closes the gap:

- `lasso_not_live`: the lasso argument of `LiveTicketCex`, generic in the
  start configuration `c0` and the loop configuration `cS`, with the kernel
  checks as hypotheses (`LassoChecks`) (now stated in
  `LiveTicketCex.lean`, same names, and `LiveTicketCex`'s lasso is its
  instance);
- `c0E`: the `TkStart` configuration of two `tkWorker` threads with no
  declarations, `next`/`owner`/counter at `0x1000`/`0x1100`/`0x1200`, laid out
  by `Layout.ofSize 0x100000 Directive.fakeSize tkWorker` (`tkLayoutE`);
  `c0E_start : TkStart 2 …`, and the kernel checks at `c0E`;
- **`ticketLiveWF_false : ¬ TicketLiveWF fuel`** at that layout (every `fuel`).

So the statement `TicketLiveWF` is refuted as a Lean theorem, not only "in
substance": the docstring of `LiveTicket.lean`'s "the literal refutation at a
`decls = {}` `StartState` configuration is not yet formalised" is superseded
by `ticketLiveWF_false`.
-/
import Kraken.Promising.LiveTicketCex
import Kraken.Promising.LiveTicket

namespace Kraken.Promising.Live.TicketCexG

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Reach Kraken.Promising.Live
open Kraken.Promising.Live.TicketCex (prefixTr loopTr spinPcs prePcs Waiting Done loopOk exK dpK exK_eq dpK_eq
  promiseBy_prom)
open Kraken.Promising.Live.Ticket (TkStart TkWaiting TkDone TicketLiveWF tkSpinPcs tkPrePcs)
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState)

-- the generic lasso (`LassoChecks`, `lassoG`, `lassoG_*`, `lassoTraceG`,
-- `lasso_not_live`; same names) moved to `LiveTicketCex.lean`, whose lasso is
-- now its instance.

/-! ## A `TkStart` configuration -/

/-- The layout the runner uses for `tkWorker`: at `0x100000`, `fakeSize`. -/
abbrev tkLayoutE : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize tkWorker

/-- A `tkWorker` thread with no declarations, `X0 = next`, `X1 = owner`,
`X2 = counter`. -/
def thE : AArch64.State :=
  reachA64Thread (reachA64Exe tkWorker) {} [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100000 0x10002c

/-- The three words at `0`. -/
def initMemE : List (Loc × Val) := [(⟨0x1000, 4⟩, 0), (⟨0x1100, 4⟩, 0), (⟨0x1200, 4⟩, 0)]

/-- Two workers from `thE`. -/
def c0E : Config isa := Config.init [thE, thE] initMemE

theorem prefixE_isSome : (reachRun exK dpK Arch.armv8 c0E prefixTr).isSome = true := by decide +kernel

/-- The loop configuration from `c0E`. -/
@[irreducible] noncomputable def cSE : Config isa := (reachRun exK dpK Arch.armv8 c0E prefixTr).getD c0E

theorem prefixE_eq : reachRun isa.exec isa.deps Arch.armv8 c0E prefixTr = some cSE := by
  rw [← exK_eq, ← dpK_eq]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp prefixE_isSome
  simp [cSE, hc]

theorem loopE_check :
    (match reachRun exK dpK Arch.armv8 cSE loopTr with
      | some c => liveCfgEq cSE c
      | none => false) = true := by decide +kernel

theorem loopE_eq : reachRun isa.exec isa.deps Arch.armv8 cSE loopTr = some cSE := by
  have h := loopE_check
  rw [exK_eq, dpK_eq] at h
  split at h
  · rename_i c hc
    rw [hc, liveCfgEq_sound (reachRun_liveStatic Arch.armv8 hc) h]
  · cases h

theorem lassoChecksE : LassoChecks c0E cSE where
  pre := prefixE_eq
  loop := loopE_eq
  ok := by decide +kernel
  prom := by decide +kernel

/-- `c0E` is a `TkStart` configuration at `tkLayoutE`. -/
theorem c0E_start : @TkStart tkLayoutE 2 0x1000 0x1100 0x1200 [thE, thE] initMemE := by
  letI : _root_.Layout := tkLayoutE
  have hst : StartState 0x1000 0x1100 0x1200 thE :=
    { exe := (Kraken.Layout.ofSize_apply _ _ _).symm
      decls := rfl
      endPc := by decide
      pc := by decide
      x0 := by decide
      x1 := by decide
      x2 := by decide
      dx := by rw [← reachLoadInt_eq]; decide +kernel
      dO := by rw [← reachLoadInt_eq]; decide +kernel
      dc := by rw [← reachLoadInt_eq]; decide +kernel }
  exact
    { hxo := by decide
      hxc := by decide
      hoc := by decide
      hN32 := by decide
      hst := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hst
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hst
        exact absurd hs List.not_mem_nil
      hN := rfl
      hX0 := by decide
      hO0 := by decide
      hC0 := by decide }

theorem tkWaiting_iff (tid : Nat) (c : Config isa) : @TkWaiting tkLayoutE tid c ↔ Waiting tid c := by
  have : @tkSpinPcs tkLayoutE = spinPcs := by decide +kernel
  simp only [TkWaiting, Waiting, this]

theorem tkDone_iff (tid : Nat) (c : Config isa) : @TkDone tkLayoutE tid c ↔ Done tid c := by
  have : @tkPrePcs tkLayoutE = [0x100000, 0x100000, 0x100004, 0x100008, 0x100008, 0x10000c, 0x100010] := by
    decide +kernel
  have hm : ∀ p : Int64, p ∈ @tkPrePcs tkLayoutE ↔ p ∈ prePcs := by
    intro p
    rw [this]
    simp only [prePcs, spinPcs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h | h | h | h | h) <;> simp [h]
    · rintro (h | h | h | h | h) <;> simp [h]
  simp only [TkDone, Done, hm]

/-- **`TicketLiveWF` is false** (at the runner's layout `tkLayoutE`, for every
`fuel`): two workers from the `TkStart` configuration `c0E` have a weakly
fair, promise-free trace on which T1 waits forever. -/
theorem ticketLiveWF_false (fuel : Nat) : ¬ @TicketLiveWF tkLayoutE fuel := by
  intro h
  refine lasso_not_live lassoChecksE fuel fun tr h0 hf tid i hw => ?_
  obtain ⟨j, hj, hd⟩ := h 2 _ _ _ _ _ c0E_start tr h0 hf.1 tid i ((tkWaiting_iff tid _).mpr hw)
  exact ⟨j, hj, (tkDone_iff tid _).mp hd⟩

end Kraken.Promising.Live.TicketCexG

#print axioms Kraken.Promising.Live.TicketCexG.ticketLiveWF_false
