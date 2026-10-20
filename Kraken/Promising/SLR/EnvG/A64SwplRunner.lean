/-
**`spinlock_swpl2.kl` / `spinlock_swpl3.kl` for AArch64 from the runner's
exact configuration**: `swpl_counter_envG_runner`,
`SwplLock.swpl_counter_envG` for threads that carry the `.kl` runner's
declarations (the typed header `uint32_t lock, counter`: strict sized,
`Decls.StrictSized`), and its concrete instances
`swpl_counter_envG_runner_concrete2`/`_concrete3` (`A64Whole.runnerIsD`:
declarations and initial memory included).

The proof is `SwplLockPublic`'s with the D form of the claim-conditional
link from `EnvG/A64DeclsLinkMore.lean`: `swplRule_envGC_decls`
(`ThreadRuleRX.ofSafelyEnvGRCMD` with `MaskOf.refl`), `swplInv_init_decls`
(`invGRCMD_init`), `RelPureSpec.holdsD_of_noDecls`,
`final_of_relPureSafelyD`. The start states are the verbatim `StartState`
with declarations (`A64Whole.WithDeclsD`). The old theorems are unchanged.
Faults are not covered (see `EnvG/A64DeclsBridge.lean`);
`swplRule_envGC_noFault` stays at `decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeCounters
import Kraken.Promising.SLR.EnvG.A64DeclsRunner
import Kraken.Promising.SLR.EnvG.A64DeclsLinkMore

namespace Kraken.Promising.SLR.EnvG.SwplLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.EnvG.X64Spin (xlockPlan xlockPlan_valid)
open Kraken.Promising.SLR.EnvG.CasSmoke (ghostSys ghostSys_spinLocs world_spinGhost' threadRes_fresh' reachable_nil'
  spin_counter_core spinGhost_pure_lk spinGhost_pure_c)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rule and the start, with declarations -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]

omit [Executable.ValidLayout (layout swplWorker)] in
/-- The worker has no `LDXP`/`STXP`. -/
theorem swplWorker_noPairs : Kraken.Executable.noPairs (layout swplWorker) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The `swpl` worker's rule on `EnvGC` with strict sized declarations
`ds`** (`swplRule_envGC` through `ofSafelyEnvGRCMD`). -/
noncomputable def swplRule_envGC_decls {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRCMD (post := postSwpl P) hsz swplWorker_noPairs (MaskOf.refl _) (xlockPlan_valid P tid)
    swplWorker_rmwLive swplWorker_phase1R postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_swpl P tid)

/-- **The worker's initial invariant with declarations** (`swplInv_init`). -/
theorem swplInv_init_decls {ds : Decls} (hsz : ds.StrictSized) {N : Nat} {l c : BitVec 64} (hlc : l ≠ c)
    (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hs : states[tid]? = some s) (hst : WithDeclsD ds (StartState l c) s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (swplRule_envGC_decls hsz (ghostSys N l c) tid).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout swplWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  obtain ⟨hds, hst⟩ := hst
  refine invGRCMD_init hs rfl (QA64MD.of_noDecls hds (qa64C_of_partialTripleEnv
    (swplWorker_envGC (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_,
      threadRes_lkLe hLk0 _⟩))
  intro f hf
  simp [σInit, Views.getFwd] at hf

end Rule

/-! ## The theorem -/

/-- **`counter = N` for the AArch64 SWP spinlock workers released by `swpl`,
with the runner's declarations**: `swpl_counter_envG` for threads whose
declarations are strict sized (`ds.StrictSized`: the `.kl` runner's, from
the typed header) and which otherwise start as there (`StartState` of the
thread with its declarations dropped). -/
theorem swpl_counter_envG_runner [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]
    {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafelyD Arch.armv8 fuel (B := fun _ r _ => Post N ⟨l, 4⟩ (ghostSys N l c).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N)
      (fun _ hc' => Config.ntFree_armv8 hc')
      (erase_init_lockPred (C := ⟨c, 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0) pend_init (fun _ => swplPureSpec _)
      (fun _ => ds) (fun _ => hsz) (fun _ => swplWorker_noPairs)
      (fun tid s hs => RelPureSpec.holdsD_of_noDecls (hst s (List.mem_of_getElem? hs)).1
        (swplPureSpec_holds (spinGhost_pure_lk _) (spinGhost_pure_c hlc _) (hst s (List.mem_of_getElem? hs)).2))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (swplInv_init_decls hsz hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.SLR.EnvG.SwplLock

/-! ## The runner's configuration -/

namespace Kraken.Promising.SLR.EnvG.ConcreteSwpl

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.SwplLock
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-- The runner's declarations for the typed `spinlock_swpl{2,3}.kl`: `lock`,
`counter` 4-byte words (strict). -/
def swplDeclsD : Decls := { locs := [⟨lockAddr, 4⟩, ⟨counterAddr, 4⟩], unsizedDefault := false }

theorem swplDeclsD_sized : swplDeclsD.StrictSized := ⟨rfl, by decide⟩

/-- A worker as the runner prepares it, declarations included. -/
def swplWorkerD0 : AArch64.State := { swplWorker0 with decls := swplDeclsD }

/-- The runner's configurations are `Config.init [swplWorkerD0, …]
swplInitMem` (two and three workers) in everything the theorem reads
(declarations and initial memory included: the typed header's initial
memory is the existing `swplInitMem`). -/
def runnerMatchesDSwpl : Bool :=
  A64Whole.runnerIsD swpl2Kl (List.replicate 2 swplWorkerD0) swplInitMem &&
    A64Whole.runnerIsD swpl3Kl (List.replicate 3 swplWorkerD0) swplInitMem

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDSwpl

/-- **`counter = N`** for `N < 2 ^ 32` `swpl`-released workers carrying the
runner's declarations, concrete instance of `swpl_counter_envG_runner`. -/
theorem swpl_counter_envG_runner_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N :=
  swpl_counter_envG_runner (layout := swplLayout) swplDeclsD_sized N lockAddr counterAddr swpl_disj hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl swplWorker0_start) List.length_replicate
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

/-- **`counter = 2`** for `spinlock_swpl2.kl` under `Arch.armv8`, from the
runner's exact configuration (the whole `code` block at `0x100000`, the
typed header's declarations and initial memory). -/
theorem swpl_counter_envG_runner_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 2 swplWorkerD0) swplInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 2 :=
  swpl_counter_envG_runner_concreteN 2 (by decide) hc hf

/-- **`counter = 3`** for `spinlock_swpl3.kl`, from the runner's exact
configuration. -/
theorem swpl_counter_envG_runner_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 3 swplWorkerD0) swplInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 3 :=
  swpl_counter_envG_runner_concreteN 3 (by decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteSwpl

#print axioms Kraken.Promising.SLR.EnvG.SwplLock.swpl_counter_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.ConcreteSwpl.swpl_counter_envG_runner_concrete2
#print axioms Kraken.Promising.SLR.EnvG.ConcreteSwpl.swpl_counter_envG_runner_concrete3
