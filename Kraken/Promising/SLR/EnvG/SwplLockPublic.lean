/-
**Part 5: the SWP spinlock released by a
release-only swap, end to end** (`spinlock_swpl2.kl`/`spinlock_swpl3.kl`, on
the claim-conditional environment `EnvGC`): `swpl_counter_envG`, `counter =
N` for `N` workers `swplWorker` under `Arch.armv8`, in the shape and with the
conclusion of `CasSmoke.cas_counter_envG` (and `SwpPublic.swp_counter_public`).

This is the first lock whose release is an RMW: the release gives away the
counter share and part of the lock, which the existing environment's RMW
release (`RelRmwGiveOk`, `Plan.Whole`) cannot express; on `EnvGC` the
release-only swap claims nothing and gives from the thread's own resource.

- **Rule** (`swplRule_envGC`): `ThreadRuleRX.ofSafelyEnvGRC`
  (`EnvG/RmwGhostA64.lean`) from `swplWorker_envGC`, with `Phase1TreeR`
  (`swplWorker_phase1R`). `hB` is the CAS lock's (`CasSmoke.hB_cas`'s proof).
- **No fault** (`swplRule_envGC_noFault`): `noFaultRule_ofSafelyEnvGRC_struct`
  from `DirsNoFault`, unconditional in the thread's promises.
- **Start** (`swplInv_init`): `invGRC_init` at `σInit` with the spinlock's
  initial resources and ghost, `QA64C` from `swplWorker_envGC` by
  `qa64C_of_partialTripleEnv`.
- **Assembly** as `CasSmoke.cas_counter_envG`: `final_of_relPureSafely`
  (purity `swplPureSpec_holds`), `erase_init_lockPred`, `Spinlock.adequacy`.

Reused: `SpinStart` (`ghostSys`, `world_spinGhost'`, `threadRes_fresh'`),
`CasSmoke.reachable_nil'`. Local copy: `threadRes_lkLe`
(`X64SpinPublicG.threadRes_lkLe`, stated there for the x64 `LkLe`).
-/
import Kraken.Promising.SLR.EnvG.SwplLockVCGen
import Kraken.Promising.SLR.EnvG.SwplLockRelPure
import Kraken.Promising.SLR.EnvG.RmwGhostA64
import Kraken.Promising.SLR.EnvG.CasPublic

namespace Kraken.Promising.SLR.EnvG.SwplLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.EnvG.X64Spin (xlockPlan xlockPlan_valid)
open Kraken.Promising.SLR.EnvG.CasSmoke (ghostSys ghostSys_spinLocs world_spinGhost' threadRes_fresh' reachable_nil'
  spin_counter_core spinGhost_pure_lk spinGhost_pure_c)

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]

/-- The worker's postcondition: the end of its text and `QEnd`. -/
abbrev postSwpl (P : Sys) : MachineState × EStateA → Prop := postOf swplWorker fun _ σ => ∃ _ : Nat, QEnd P σ

omit [Executable.ValidLayout (layout swplWorker)] in
/-- **`hB` for the worker**: `Post` from `QEnd` under the clean flag
(`CasSmoke.hB_cas`'s proof). -/
theorem hB_swpl (P : Sys) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postSwpl P (t.st.st, σ) → t.prom = [] → EnvRel tid (xlockPlan P tid) σ c t r g cl → cl →
      Post P.N P.Lk P.K r := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, -, hQ⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact hQ (hrel.cl hcl)
  · rw [hp] at hts; cases hts

/-- **The `swpl` worker's rule on `EnvGC`.** -/
noncomputable def swplRule_envGC (P : Sys) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRC (post := postSwpl P) (xlockPlan_valid P tid) swplWorker_rmwLive swplWorker_phase1R
    postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_swpl P tid)

/-- **The `swpl` worker's rule excludes faults** (unconditional in promises). -/
theorem swplRule_envGC_noFault (P : Sys) (tid : Nat) : NoFaultRule (swplRule_envGC P tid) :=
  noFaultRule_ofSafelyEnvGRC_struct _ _ _ _ _ _ swplWorker_noFault

end Rule

/-! ## The start -/

/-- The initial thread resource writes only the lock's initial message `0`,
so `LkLe` holds at any views (`X64SpinPublicG.threadRes_lkLe`). -/
theorem threadRes_lkLe {P : Sys} {tid : Nat} {m : Memory} (h0 : m.initVal P.Lk = 0) (vs : Views) :
    LkLe P (threadRes m P.N P.Lk P.K P.F tid) vs :=
  LockVC.threadRes_lkLe h0 vs

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]

/-- **The worker's initial invariant** (thread `tid` of `N`). -/
theorem swplInv_init {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N)
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartState l c s) (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (swplRule_envGC (ghostSys N l c) tid).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout swplWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  refine invGRC_init hs rfl (qa64C_of_partialTripleEnv
    (swplWorker_envGC (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_,
      threadRes_lkLe hLk0 _⟩)
  intro f hf
  simp [σInit, Views.getFwd] at hf

end Start

/-! ## The theorem -/

/-- **`counter = N` for the AArch64 SWP spinlock workers released by `swpl`,
on `EnvGC`**, public form (the shape and conclusion of
`CasSmoke.cas_counter_envG` / `SwpPublic.swp_counter_public`; see there for
what is and is not covered: undeclared 4-byte footprints, `hdisj` for the
model's mixed-size gap, final configurations only, `N < 2 ^ 32` for the
32-bit counter).

For every valid layout of `swplWorker` (the worker of `spinlock_swpl2.kl`:
`swpa` acquire, `ldr` test-and-test-and-set spin, plain increment,
`swpl wzr` release), every number of threads `N < 2 ^ 32` and all addresses
`l`, `c` whose 4-byte words are disjoint: if `states` consists of `N`
threads, each at the start of the worker with `X0 = l`, `X1 = c`
(`StartState`), and the initial memory has the lock and counter words at `0`,
then every configuration `Reachable` under `Arch.armv8` that is final has
the counter word at `N`.

Proved on the claim-conditional environment: one `vcgen` call per worker
(`swplWorker_envGC`), `ThreadRuleRX.ofSafelyEnvGRC` (`swplRule_envGC`),
purity by `vcgen` (`swplPureSpec_holds`), `final_of_relPureSafely` and
`Spinlock.adequacy`. No-fault for the worker's rule:
`swplRule_envGC_noFault`. -/
theorem swpl_counter_envG [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)] {fuel : Nat}
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
      (erase_init_lockPred (C := ⟨c, 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0) pend_init (fun _ => swplPureSpec _)
      (fun tid s hs => swplPureSpec_holds (spinGhost_pure_lk _) (spinGhost_pure_c hlc _)
        (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (swplInv_init hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.SLR.EnvG.SwplLock
