/-
**Item 2, part 4: `counter = N` for the
AArch64 `ldaddal` ticket lock** (`ticketlock_al2.kl`, `ticketlock_al3.kl`),
public form (`EnvG/TicketLockPublic.lean` for `tkWorkerAl` on `EnvGTDR`).

- **Rule** (`tkRuleAl`): `ThreadRuleRXGSXE.ofSafelyEnvGTDR` from the `vcgen`
  proof `tkWorkerAl_envGTDR` (`Phase1TreeR`: the `ldaddal` is a release-kind
  RMW), with `hB_tkAl` (`hB_tk` at `tkWorkerAl`).
- **No fault** (`tkRuleAl_noFault`): `noFaultRule_ofSafelyEnvGTDR_struct`.
- **Start** (`tkAlInv_init`): `invGTDR_init` with `start_init`.
- **Assembly** (`ticket_al_counter_envG`): `theorem1IIPureX_G₀_S_singleRmw`
  (purity and the phases by `tkWorkerAl_dispPure`), then `ticket_final`; the
  ghost, final and VC layers of `TicketLock` are reused unchanged.
-/
import Kraken.Promising.SLR.EnvG.TicketAlVCGen
import Kraken.Promising.SLR.EnvG.TicketAlPure
import Kraken.Promising.SLR.EnvG.TicketLockPublic

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.CasSmoke (reachable_nil')

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]

/-- The worker's postcondition: the end of its text and `QEnd`. -/
abbrev postTkAl (P : Sys) (tid : Nat) : MachineState × EStateA → Prop :=
  postOf tkWorkerAl fun _ σ => ∃ _ : Nat, QEnd P tid σ

omit [Executable.ValidLayout (layout tkWorkerAl)] in
/-- **`hB` for the worker**: `TPost` from `QEnd` under the clean flag. -/
theorem hB_tkAl (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postTkAl P tid (t.st.st, σ) → t.prom = [] → EnvRel tid (tkPlan P) σ c t r g cl → cl → TPost P c r := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · obtain ⟨hO, hK, tw, w, hw, hl, ht, ts, v, hr, hv⟩ := hQ (hrel.cl hcl)
    exact ⟨hO, tid, hK, tw, w, Memory.get?_of_prefix hrel.snap.msgs hw, hl, ht, ts, v, hrel.snap.read? hr, hv⟩
  · rw [hp] at hts; cases hts

/-- **The ticket lock worker's rule on `EnvGTD`.** -/
noncomputable def tkRuleAl (P : Sys) (hL : Locs P) (tid : Nat) :
    ThreadRuleRXGSXE (I := isa) G₀ (disp P hL.xo).TX Arch.armv8 (fun c r _ => TPost P c r) tid :=
  ThreadRuleRXGSXE.ofSafelyEnvGTDR (post := postTkAl P tid) (tkPlan_valid P) tkWorkerAl_rmwLive tkWorkerAl_phase1R
    postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_tkAl P tid)

/-- **The worker's rule excludes faults** (unconditional in promises). -/
theorem tkRuleAl_noFault (P : Sys) (hL : Locs P) (tid : Nat) : NoFaultRuleSXE (tkRuleAl P hL tid) :=
  noFaultRule_ofSafelyEnvGTDR_struct _ _ _ _ _ _ tkWorkerAl_noFault

end Rule

/-! ## The start -/

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]

/-- **The worker's initial invariant** (thread `tid`). -/
theorem tkAlInv_init {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) {tid : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartStateAl x o c s) :
    InvGTDR (I := isa) tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo)
      (QA64TDR Arch.armv8 tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo) (layout tkWorkerAl)
        ((layout tkWorkerAl).addrOf tkWorkerAl.length) (postTkAl (tkSys N x o c) tid))
      True (Config.init states initMem) (thRes (Config.init states initMem).mem (tkSys N x o c) tid)
      (tkGhost (Config.init states initMem).mem (tkSys N x o c)) := by
  letI : CodeEnv := ⟨layout tkWorkerAl⟩
  exact invGTDR_init hs rfl (qa64TDR_of_partialTripleEnv (tkWorkerAl_envGTDR N x o c hL tid).uncount rfl hst.exe
    hst.decls hst.endPc hst.pc ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc, start_init hL _ tid _⟩)

end Start

/-! ## The theorem -/

/-- **`counter = N` for the AArch64 `ldaddal` ticket lock workers**, public
form (the shape of `TicketLock.ticket_counter_envG`; see
`SwplLock.swpl_counter_envG` for what is and is not covered: undeclared
4-byte footprints, the disjointness hypotheses for the model's mixed-size
gap, final configurations only).

For every valid layout of `tkWorkerAl` (the worker of `ticketlock_al2.kl` and
`ticketlock_al3.kl`: ticket by `ldaddal` on `next`, `ldar` spin on `owner`,
plain increment, `stlr` of `ticket + 1` to `owner`), every number of threads
`N` with `N + 1 < 2 ^ 32` and all addresses `x`, `o`, `c` whose 4-byte words
are pairwise disjoint: if `states` consists of `N` threads, each at the start
of the worker with `X0 = x`, `X1 = o`, `X2 = c` (`StartStateAl`), and the
initial memory has the three words at `0`, then every configuration
`Reachable` under `Arch.armv8` that is final has the counter word at `N`.

Proved on the ticket environment with a release-kind ticket RMW `EnvGTDR`:
one `vcgen` call per worker (`tkWorkerAl_envGTDR`),
`ThreadRuleRXGSXE.ofSafelyEnvGTDR` (`tkRuleAl`), purity and the dispenser
phases by `vcgen` (`tkWorkerAl_dispPure`), `theorem1IIPureX_G₀_S_singleRmw`
and `ticket_final`. No fault for the worker's rule: `tkRuleAl_noFault`. -/
theorem ticket_al_counter_envG [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)] {fuel : Nat}
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateAl x o c s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  have hxo' : x ≠ o := by rintro rfl; simp [Decls.overlaps] at hxo
  have hxc' : x ≠ c := by rintro rfl; simp [Decls.overlaps] at hxc
  exact ticket_counter_of N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 (tkAlDispSpec · N x)
    (fun _ hQx hQc s hs => tkAlDispSpec_holds hN32 hxo' hxc' hQx hQc (hst s hs))
    (fun hL tid s hs n m => npSafeP_of_safelyEnvGTDR (tkPlan_valid _) tkWorkerAl_rmwLive tkWorkerAl_phase1R
      postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_tkAl _ tid) n m
      (tkAlInv_init hL hs (hst s (List.mem_of_getElem? hs))))
    hc hf

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkRuleAl_noFault
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_al_counter_envG
