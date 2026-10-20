/-
**Part 6: `counter = N` for the AArch64
ticket lock** (`ticketlock2.kl`), public form.

- **Rule** (`tkRule`): `ThreadRuleRXGSXE.ofSafelyEnvGTD` from the `vcgen`
  proof `tkWorker_envGTD`, with `hB_tk` (`TPost` from `QEnd` under the clean
  flag: the resource is the thread's own, the own `next` message and the
  matching `owner` message move from the snapshot to the configuration).
- **No fault** (`tkRule_noFault`): `noFaultRule_ofSafelyEnvGTD_struct` from
  `DirsNoFault`, unconditional in the thread's promises.
- **Start** (`tkInv_init`): `invGTD_init` at `σInit` with `thRes`/`tkGhost`
  (`start_init`: `1/N` of `next` and `owner`, all of `kLoc tid`, initial
  views), `QA64TD` by `qa64TD_of_partialTripleEnv`.
- **Purity and phases** (`tkPure`, `tkSingleRmw`): `J tid := ∃ b,
  (tkDispSpec …).Holds b` is kept by every instruction (`dispSpec_step`), so
  `promisePure_of_relWrites` and `SingleRmwDispenser.ofCells` apply.
- **Assembly** (`ticket_counter_envG`): `theorem1IIPureX_G₀_S_singleRmw`
  with `erase_tkInit`, `tx_tkInit`, then `ticket_final`.
-/
import Kraken.Promising.SLR.EnvG.TicketLockVCGen
import Kraken.Promising.SLR.EnvG.TicketLockPure
import Kraken.Promising.SLR.EnvG.CasPublic
import Kraken.Promising.SLR.DispenserFresh
import Kraken.Promising.SLR.Theorem1FinalP
import Kraken.Promising.SLR.EnvG.TicketCounterCore

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.CasSmoke (reachable_nil')

-- `tkSys` (the parameters at addresses `x`, `o`, `c`) is in `EnvG/TicketCounterCore.lean`.

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]

/-- The worker's postcondition: the end of its text and `QEnd`. -/
abbrev postTk (P : Sys) (tid : Nat) : MachineState × EStateA → Prop :=
  postOf tkWorker fun _ σ => ∃ _ : Nat, QEnd P tid σ

omit [Executable.ValidLayout (layout tkWorker)] in
/-- **`hB` for the worker**: `TPost` from `QEnd` under the clean flag. -/
theorem hB_tk (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postTk P tid (t.st.st, σ) → t.prom = [] → EnvRel tid (tkPlan P) σ c t r g cl → cl → TPost P c r := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · obtain ⟨hO, hK, tw, w, hw, hl, ht, ts, v, hr, hv⟩ := hQ (hrel.cl hcl)
    exact ⟨hO, tid, hK, tw, w, Memory.get?_of_prefix hrel.snap.msgs hw, hl, ht, ts, v, hrel.snap.read? hr, hv⟩
  · rw [hp] at hts; cases hts

/-- **The ticket lock worker's rule on `EnvGTD`.** -/
noncomputable def tkRule (P : Sys) (hL : Locs P) (tid : Nat) :
    ThreadRuleRXGSXE (I := isa) G₀ (disp P hL.xo).TX Arch.armv8 (fun c r _ => TPost P c r) tid :=
  ThreadRuleRXGSXE.ofSafelyEnvGTD (post := postTk P tid) (tkPlan_valid P) tkWorker_rmwLive tkWorker_phase1
    postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_tk P tid)

/-- **The worker's rule excludes faults** (unconditional in promises). -/
theorem tkRule_noFault (P : Sys) (hL : Locs P) (tid : Nat) : NoFaultRuleSXE (tkRule P hL tid) :=
  noFaultRule_ofSafelyEnvGTD_struct _ _ _ _ _ _ tkWorker_noFault

end Rule

/-! ## The start -/

/-- **`Start` at the initial state**: `1/N` of `next` and `owner`, all of
`kLoc tid`, the initial ghost, and the initial (zero) views. -/
theorem start_init {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) (m : Memory) (tid : Nat)
    (snap : Config isa) :
    Start (tkSys N x o c) tid (σInit snap (thRes m (tkSys N x o c) tid) (tkGhost m (tkSys N x o c))) :=
  start_initG hL m tid snap

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]

/-- **The worker's initial invariant** (thread `tid`). -/
theorem tkInv_init {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) {tid : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartState x o c s) :
    InvGTD (I := isa) Arch.armv8 tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo)
      (QA64TD Arch.armv8 tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo) (layout tkWorker)
        ((layout tkWorker).addrOf tkWorker.length) (postTk (tkSys N x o c) tid))
      True (Config.init states initMem) (thRes (Config.init states initMem).mem (tkSys N x o c) tid)
      (tkGhost (Config.init states initMem).mem (tkSys N x o c)) := by
  letI : CodeEnv := ⟨layout tkWorker⟩
  exact invGTD_init hs rfl (qa64TD_of_partialTripleEnv (tkWorker_envGTD N x o c hL tid).uncount rfl hst.exe
    hst.decls hst.endPc hst.pc ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc, start_init hL _ tid _⟩)

end Start

/-! ## The theorem -/

/-- **The ticket lock's assembly** (shared by `ticket_counter_envG`
and `ticket_al_counter_envG`; an instance of `ticket_counter_core`): from a
purity-and-phase specification `DS`
holding at every start state and each thread's `NPSafeP` at the initial
configuration, `theorem1IIPureX_G₀_S_singleRmw` and `ticket_final` give
`counter = N` at every final reachable configuration. -/
theorem ticket_counter_of {fuel : Nat}
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)} (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (DS : ∀ Q : Loc → Val → Prop, DispSpec Arch.armv8 Q ⟨x, 4⟩ (N + 1))
    (hDS : ∀ Q : Loc → Val → Prop, (∀ v, Q ⟨x, 4⟩ v) → (∀ v, Q ⟨c, 4⟩ v) → ∀ s ∈ states, (DS Q).Holds false s)
    (hsafe : ∀ (hL : Locs (tkSys N x o c)) tid s, states[tid]? = some s → ∀ n m,
      NPSafeP (modelX isa (disp (tkSys N x o c) hL.xo).TX) Arch.armv8 (fun cf r _ => TPost (tkSys N x o c) cf r) tid
        G₀ (K2Scope (model isa) AllocIds) n m True (Config.init states initMem)
        (thRes (Config.init states initMem).mem (tkSys N x o c) tid) (tkGhost (Config.init states initMem).mem
          (tkSys N x o c)))
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  ticket_counter_core Arch.armv8 N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 (fun _ b s => (DS _).Holds b s)
    (fun _ hc' => Config.ntFree_armv8 hc') (fun _ _ _ _ _ h hex => dispSpec_step _ h _ hex)
    (fun hL _ s hs => hDS _ (tkGhost_pure_x hL _) (tkGhost_pure_c hL _) s (List.mem_of_getElem? hs)) hsafe hc hf

/-- **`counter = N` for the AArch64 ticket lock workers**, public form (the
shape of `SwplLock.swpl_counter_envG` / `CasSmoke.cas_counter_envG`; see
there for what is and is not covered: undeclared 4-byte footprints, the
disjointness hypotheses for the model's mixed-size gap, final configurations
only).

For every valid layout of `tkWorker` (the worker of `ticketlock2.kl`: ticket
by `ldadda` on `next`, `ldar` spin on `owner`, plain increment, `stlr` of
`ticket + 1` to `owner`), every number of threads `N` with `N + 1 < 2 ^ 32`
(the 32-bit tickets `0..N` do not wrap) and all addresses `x`, `o`, `c`
whose 4-byte words are pairwise disjoint: if `states` consists of `N`
threads, each at the start of the worker with `X0 = x`, `X1 = o`, `X2 = c`
(`StartState`), and the initial memory has the three words at `0`, then
every configuration `Reachable` under `Arch.armv8` that is final has the
counter word at `N`.

Proved on the ticket environment `EnvGTD`: one `vcgen` call per worker
(`tkWorker_envGTD`), `ThreadRuleRXGSXE.ofSafelyEnvGTD` (`tkRule`), purity and
the dispenser phases by `vcgen` (`tkWorker_dispPure`),
`theorem1IIPureX_G₀_S_singleRmw` and `ticket_final`. No fault for the
worker's rule: `tkRule_noFault`. -/
theorem ticket_counter_envG [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)] {fuel : Nat}
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartState x o c s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  have hxo' : x ≠ o := by rintro rfl; simp [Decls.overlaps] at hxo
  have hxc' : x ≠ c := by rintro rfl; simp [Decls.overlaps] at hxc
  exact ticket_counter_of N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 (tkDispSpec · N x)
    (fun _ hQx hQc s hs => tkDispSpec_holds hN32 hxo' hxc' hQx hQc (hst s hs))
    (fun hL tid s hs n m => npSafeP_of_safelyEnvGTD (tkPlan_valid _) tkWorker_rmwLive tkWorker_phase1 postOf_end
      (not_instrStepEnv_of_end_labels _ 1) (hB_tk _ tid) n m (tkInv_init hL hs (hst s (List.mem_of_getElem? hs))))
    hc hf

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkRule_noFault
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_counter_envG
