/-
**`spinlock_swp2.kl` / `spinlock_swp3.kl` for AArch64 from the runner's exact
configuration**: `swp_counter_envG_runner`,
`SwpEnvG.swp_counter_envG` for threads that carry the `.kl` runner's
declarations (the typed header `uint32_t lock, counter`: strict sized,
`Decls.StrictSized`), and its concrete instances
`swp_counter_envG_runner_concreteN`/`_concrete2`/`_concrete3`
(`A64Whole.runnerIsD`: declarations and initial memory included).

The proof is `SwpEnvGPublic`'s with the D form of the claim-conditional link
from `EnvG/A64DeclsLinkMore.lean`, as `A64SwplRunner.lean` for the `swpl`
lock: `swpRule_envGC_decls` (`ThreadRuleRX.ofSafelyEnvGRCMD` with
`MaskOf.refl`), `swpInv_init_decls` (`invGRCMD_init`),
`RelPureSpec.holdsD_of_noDecls`, `final_of_relPureSafelyD`. The start states
are the existing `SwpPublic.StartState` with declarations
(`A64Whole.WithDeclsD`); the concretes are the existing `SwpConcrete.worker0`
(at `SwpConcrete.swpLayout`) with the runner's declarations. The existing
cell-route theorems (`SwpInv.swp_counter_armv8`, `SwpPublic`,
`SwpConcrete.swp_counter_2`) are unchanged. Faults: `A64SwpNoFault.lean`.
-/
import Kraken.Promising.SLR.EnvG.SwpEnvGPublic
import Kraken.Promising.SLR.EnvG.A64WholeCounters
import Kraken.Promising.SLR.EnvG.A64DeclsRunner
import Kraken.Promising.SLR.EnvG.A64DeclsLinkMore

namespace Kraken.Promising.SLR.EnvG.SwpEnvG

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.SwpPublic (StartState)
open Kraken.Promising.SLR.EnvG.SwplLock (threadRes_lkLe)
open Kraken.Promising.SLR.EnvG.X64Spin (xlockPlan xlockPlan_valid)
open Kraken.Promising.SLR.EnvG.CasSmoke (ghostSys ghostSys_spinLocs world_spinGhost' threadRes_fresh' reachable_nil'
  spin_counter_core spinGhost_pure_lk spinGhost_pure_c)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-! ## The rule and the start, with declarations -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]

omit [Executable.ValidLayout (layout swpWorker)] in
/-- The worker has no `LDXP`/`STXP`. -/
theorem swpWorker_noPairs : Kraken.Executable.noPairs (layout swpWorker) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The SWP worker's rule on `EnvGC` with strict sized declarations `ds`**
(`swpRule_envGC` through `ofSafelyEnvGRCMD`). -/
noncomputable def swpRule_envGC_decls {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat) :
    ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRCMD (post := postSwp P) hsz swpWorker_noPairs (MaskOf.refl _) (xlockPlan_valid P tid)
    swpWorker_rmwLive swpWorker_phase1R postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_swp P tid)

/-- **The worker's initial invariant with declarations** (`swpInv_init`). -/
theorem swpInv_init_decls {ds : Decls} (hsz : ds.StrictSized) {N : Nat} {l c : BitVec 64} (hlc : l ≠ c)
    (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hs : states[tid]? = some s) (hst : WithDeclsD ds (StartState l c) s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (swpRule_envGC_decls hsz (ghostSys N l c) tid).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout swpWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  obtain ⟨hds, hst⟩ := hst
  refine invGRCMD_init hs rfl (QA64MD.of_noDecls hds (qa64C_of_partialTripleEnv
    (swpWorker_envGC (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_,
      threadRes_lkLe hLk0 _⟩))
  intro f hf
  simp [σInit, Views.getFwd] at hf

end Rule

/-! ## The theorem -/

/-- **`counter = N` for the AArch64 SWP spinlock workers, with the runner's
declarations**: `swp_counter_envG` for threads whose declarations are strict
sized (`ds.StrictSized`: the `.kl` runner's, from the typed header) and which
otherwise start as there (`SwpPublic.StartState` of the thread with its
declarations dropped). -/
theorem swp_counter_envG_runner [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]
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
      (erase_init_lockPred (C := ⟨c, 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0) pend_init (fun _ => swpPureSpec _)
      (fun _ => ds) (fun _ => hsz) (fun _ => swpWorker_noPairs)
      (fun tid s hs => RelPureSpec.holdsD_of_noDecls (hst s (List.mem_of_getElem? hs)).1
        (swpPureSpec_holds (spinGhost_pure_lk _) (spinGhost_pure_c hlc _) (hst s (List.mem_of_getElem? hs)).2))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (swpInv_init_decls hsz hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.SLR.EnvG.SwpEnvG

/-! ## The runner's configuration -/

namespace Kraken.Promising.SLR.EnvG.A64SwpRunner

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.SwpEnvG
open Kraken.Promising.SLR.SwpConcrete (swpLayout swpValid lockAddr counterAddr worker0 initMem2 swpKl)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-- The runner's declarations for the typed `spinlock_swp{2,3}.kl`: `lock`,
`counter` 4-byte words (strict). -/
def swpDeclsD : Decls := { locs := [⟨lockAddr, 4⟩, ⟨counterAddr, 4⟩], unsizedDefault := false }

theorem swpDeclsD_sized : swpDeclsD.StrictSized := ⟨rfl, by decide⟩

/-- A worker as the runner prepares it, declarations included (the existing
`SwpConcrete.worker0` with `swpDeclsD`). -/
def swpWorkerD0 : AArch64.State := { worker0 with decls := swpDeclsD }

/-- The runner's configurations are `Config.init [swpWorkerD0, …] initMem2`
(two and three workers) in everything the theorem reads (declarations and
initial memory included: the typed header's initial memory is the existing
`SwpConcrete.initMem2`). -/
def runnerMatchesDSwp : Bool :=
  A64Whole.runnerIsD swpKl (List.replicate 2 swpWorkerD0) initMem2 &&
    A64Whole.runnerIsD A64WholeCounters.swp3Kl (List.replicate 3 swpWorkerD0) initMem2

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDSwp

theorem swp_disjD : Decls.overlaps lockAddr 4 counterAddr 4 = false := by decide

/-- **`counter = N`** for `N < 2 ^ 32` SWP spinlock workers carrying the
runner's declarations, concrete instance of `swp_counter_envG_runner`. -/
theorem swp_counter_envG_runner_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate N swpWorkerD0) initMem2) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N :=
  swp_counter_envG_runner (layout := swpLayout) swpDeclsD_sized N lockAddr counterAddr swp_disjD hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl SwpPublic.worker0_start) List.length_replicate
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

/-- **`counter = 2`** for `spinlock_swp2.kl` under `Arch.armv8`, from the
runner's exact configuration (the whole `code` block at `0x100000`, the
typed header's declarations and initial memory). -/
theorem swp_counter_envG_runner_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 2 swpWorkerD0) initMem2) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 2 :=
  swp_counter_envG_runner_concreteN 2 (by decide) hc hf

/-- **`counter = 3`** for `spinlock_swp3.kl`, from the runner's exact
configuration. -/
theorem swp_counter_envG_runner_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 3 swpWorkerD0) initMem2) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 3 :=
  swp_counter_envG_runner_concreteN 3 (by decide) hc hf

end Kraken.Promising.SLR.EnvG.A64SwpRunner

#print axioms Kraken.Promising.SLR.EnvG.SwpEnvG.swp_counter_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_concrete2
#print axioms Kraken.Promising.SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_concrete3
