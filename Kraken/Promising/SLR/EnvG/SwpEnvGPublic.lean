/-
**Part 5: the SWP spinlock of
`spinlock_swp2.kl`/`spinlock_swp3.kl` on `EnvGC`, end to end**:
`swp_counter_envG`, `counter = N` for `N` workers `swpWorker` under
`Arch.armv8`.

The statement is the existing `SwpPublic.swp_counter_public`'s, verbatim (same
start predicate `SwpPublic.StartState`, same hypotheses, same conclusion:
`swp_counter_envG_type_eq`); the proof is new, on the EnvG route, in the shape
of `SwplLock.swpl_counter_envG` (the existing cell-route theorems
`SwpInv.swp_counter_armv8` / `SwpPublic.swp_counter_public` are unchanged).
Being on the EnvG route it has a `QA64*` invariant, from which the
runner-exact (`A64SwpRunner.lean`) and no-fault (`A64SwpNoFault.lean`)
companions follow as for the `swpl` lock.

- **Rule** (`swpRule_envGC`): `ThreadRuleRX.ofSafelyEnvGRC`
  (`EnvG/RmwGhostA64.lean`) from `swpWorker_envGC`, with `Phase1TreeR`
  (`swpWorker_phase1R`). `hB` is the `swpl` lock's (`SwplLock.hB_swpl`'s proof).
- **No fault** (`swpRule_envGC_noFault`): `noFaultRule_ofSafelyEnvGRC_struct`
  from `DirsNoFault`, unconditional in the thread's promises.
- **Start** (`swpInv_init`): `invGRC_init` at `σInit` with the spinlock's
  initial resources and ghost, `QA64C` from `swpWorker_envGC` by
  `qa64C_of_partialTripleEnv`.
- **Assembly** as `SwplLock.swpl_counter_envG`: `final_of_relPureSafely`
  (purity `swpPureSpec_holds`), `erase_init_lockPred`, `Spinlock.adequacy`
  through `CasSmoke.spin_counter_core`.

Phase-1 limits apply (single-access trees, read-side acquire only, releases
are stores).
-/
import Kraken.Promising.SLR.EnvG.SwpEnvGVCGen
import Kraken.Promising.SLR.EnvG.SwpEnvGRelPure
import Kraken.Promising.SLR.EnvG.SwplLockPublic

namespace Kraken.Promising.SLR.EnvG.SwpEnvG

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.SwpPublic (StartState)
open Kraken.Promising.SLR.EnvG.SwplLock (QEnd threadRes_lkLe)
open Kraken.Promising.SLR.EnvG.X64Spin (xlockPlan xlockPlan_valid)
open Kraken.Promising.SLR.EnvG.CasSmoke (ghostSys ghostSys_spinLocs world_spinGhost' threadRes_fresh' reachable_nil'
  spin_counter_core spinGhost_pure_lk spinGhost_pure_c)

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]

/-- The worker's postcondition: the end of its text and `QEnd`. -/
abbrev postSwp (P : Sys) : MachineState × EStateA → Prop := postOf swpWorker fun _ σ => ∃ _ : Nat, QEnd P σ

omit [Executable.ValidLayout (layout swpWorker)] in
/-- **`hB` for the worker**: `Post` from `QEnd` under the clean flag
(`SwplLock.hB_swpl`'s proof). -/
theorem hB_swp (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postSwp P (t.st.st, σ) → t.prom = [] → EnvRel tid (xlockPlan P tid) σ c t r g cl → cl →
      Post P.N P.Lk P.K r := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hQ (hrel.cl hcl)
  · rw [hp] at hts; cases hts

/-- **The SWP worker's rule on `EnvGC`.** -/
noncomputable def swpRule_envGC (P : Sys) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRC (post := postSwp P) (xlockPlan_valid P tid) swpWorker_rmwLive swpWorker_phase1R
    postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_swp P tid)

/-- **The SWP worker's rule excludes faults** (unconditional in promises). -/
theorem swpRule_envGC_noFault (P : Sys) (tid : Nat) : NoFaultRule (swpRule_envGC P tid) :=
  noFaultRule_ofSafelyEnvGRC_struct _ _ _ _ _ _ swpWorker_noFault

end Rule

/-! ## The start -/

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]

/-- **The worker's initial invariant** (thread `tid` of `N`). -/
theorem swpInv_init {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N)
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartState l c s) (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (swpRule_envGC (ghostSys N l c) tid).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout swpWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  refine invGRC_init hs rfl (qa64C_of_partialTripleEnv
    (swpWorker_envGC (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_,
      threadRes_lkLe hLk0 _⟩)
  intro f hf
  simp [σInit, Views.getFwd] at hf

end Start

/-! ## The theorem -/

/-- **`counter = N` for the AArch64 SWP spinlock workers, on `EnvGC`**,
public form: the statement of `SwpPublic.swp_counter_public` (see there and
`CasSmoke.cas_counter_envG` for what is and is not covered: undeclared 4-byte
footprints, `hdisj` for the model's mixed-size gap, final configurations
only, `N < 2 ^ 32` for the 32-bit counter).

For every valid layout of `swpWorker` (the worker of `spinlock_swp2.kl`:
`swpa` acquire, `ldr` test-and-test-and-set spin, plain increment, `stlr wzr`
release), every number of threads `N < 2 ^ 32` and all addresses `l`, `c`
whose 4-byte words are disjoint: if `states` consists of `N` threads, each at
the start of the worker with `X0 = l`, `X1 = c` (`SwpPublic.StartState`), and
the initial memory has the lock and counter words at `0`, then every
configuration `Reachable` under `Arch.armv8` that is final has the counter
word at `N`.

Proved on the claim-conditional environment: one `vcgen` call per worker
(`swpWorker_envGC`), `ThreadRuleRX.ofSafelyEnvGRC` (`swpRule_envGC`), purity
by `vcgen` (`swpPureSpec_holds`), `final_of_relPureSafely` and
`Spinlock.adequacy`. No-fault for the worker's rule: `swpRule_envGC_noFault`. -/
theorem swp_counter_envG [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)] {fuel : Nat}
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartState l c s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafely Arch.armv8 fuel (B := fun _ r _ => Post N ⟨l, 4⟩ (ghostSys N l c).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N)
      (fun _ hc' => Config.ntFree_armv8 hc')
      (erase_init_lockPred (C := ⟨c, 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0) pend_init (fun _ => swpPureSpec _)
      (fun tid s hs => swpPureSpec_holds (spinGhost_pure_lk _) (spinGhost_pure_c hlc _)
        (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (swpInv_init hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

/-- **The new theorem has the existing public statement**: the type of
`swp_counter_envG` is that of `SwpPublic.swp_counter_public` (the proofs
differ: EnvG route here, cell route there). -/
theorem swp_counter_envG_type_eq :
    type_of% @swp_counter_envG = type_of% @SwpPublic.swp_counter_public := rfl

end Kraken.Promising.SLR.EnvG.SwpEnvG

#print axioms Kraken.Promising.SLR.EnvG.SwpEnvG.swp_counter_envG
#print axioms Kraken.Promising.SLR.EnvG.SwpEnvG.swpRule_envGC_noFault
