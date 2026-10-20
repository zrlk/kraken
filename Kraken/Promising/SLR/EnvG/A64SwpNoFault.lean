/-
**No fault, rule-level and program-level, at the runner's declarations for
`spinlock_swp2/3.kl`**, on the EnvG route of
`EnvG/SwpEnvGPublic.lean`, as the AArch64 no-fault-at-declarations proofs
(`A64NoFaultDLocks.lean`) and the AArch64 fault-freedom proofs
(`A64FaultFreeFixed.lean`) did for the `swpl` lock.

- The worker's **address run** in `SharedEnv.invTop (casS l c)`
  (`swpWorker_addr`: `vcgen` with a register-only table; `X0`/`X1` hold the
  lock and the counter words, the private memory maps neither), giving
  `AddrSafeA` at the start.
- **Rule level**: the worker's rule with the address run
  (`swpRule_envGC_declsA`, `ofSafelyEnvGRCMAD`; same `B` as
  `swpRule_envGC_decls`), its initial invariant at the runner's start
  (`swpInv_init_declsA`), and the rule's no-fault at `decls = ds` for
  declarations agreeing on the two words (`swp_counter_envG_runner_noFault`),
  concrete at the runner's declarations
  (`swp_counter_envG_runner_noFault_concrete`).
- **Program level**: the address run as a value specification at `G = ⊤`
  (`swpSpecA`, `ValSpecA.ofAddr`), so no configuration reachable from the
  runner's start states, under any architecture and promises included, has a
  faulting step (`swp_counter_envG_runner_faultFree`,
  `a64_faultFree_of_addrSpecs`); concrete
  `swp_counter_envG_runner_faultFree_concreteN`.

Phase-1 limit: single-access trees (`RootOnlyDA`).
-/
import Kraken.Promising.SLR.EnvG.A64SwpRunner
import Kraken.Promising.SLR.EnvG.A64NoFaultDLocks
import Kraken.Promising.SLR.EnvG.MemValsA64

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP

namespace Kraken.Promising.SLR.EnvG.SwpEnvG

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.SwpPublic (StartState)
open Kraken.Promising.SLR.EnvG.SwplLock (threadRes_lkLe)
open Kraken.Promising.SLR.EnvG.X64Spin (xlockPlan xlockPlan_valid)
open Kraken.Promising.SLR.EnvG.CasSmoke (ghostSys ghostSys_spinLocs world_spinGhost' threadRes_fresh' casS)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

set_option mvcgen.warning false
set_option experimental.vcgen true

section Addr

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]

local instance swpAddr.env : CodeEnv := ⟨layout swpWorker⟩

/-- The address table: `X0`, `X1` hold the lock and the counter, unmapped. -/
abbrev swpAddrTable (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.invTop (casS l c))).State → Prop :=
  fun _ s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
    Mem.loadInt s.dmem c 4 = none

/-- **The worker's address run**: every access is the lock or the counter
word. -/
theorem swpWorker_addr (l c : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.invTop (casS l c)))
      (fun s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
        Mem.loadInt s.dmem c 4 = none)
      swpWorker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (swpAddrTable l c) (hP := by funext s g; simp [swpAddrTable])
  cfg_cases_env [swpWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdl, hdc⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

end Addr

/-! ## Rule level -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]

/-- **The SWP worker's rule with the address run** (`swpRule_envGC_decls`
through `ofSafelyEnvGRCMAD` on the lock and the counter). -/
noncomputable def swpRule_envGC_declsA {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat)
    (l c : BitVec 64) : ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRCMAD (post := postSwp P) (casS l c) hsz swpWorker_noPairs (MaskOf.refl _)
    (xlockPlan_valid P tid) swpWorker_rmwLive swpWorker_phase1R postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_swp P tid)

/-- **The worker's initial invariant with the address run**
(`swpInv_init_decls`). -/
theorem swpInv_init_declsA {ds : Decls} (hsz : ds.StrictSized) {N : Nat} {l c : BitVec 64} (hlc : l ≠ c)
    (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hs : states[tid]? = some s) (hst : WithDeclsD ds (StartState l c) s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (swpRule_envGC_declsA hsz (ghostSys N l c) tid l c).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout swpWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  obtain ⟨hds, hst⟩ := hst
  refine invGRCMAD_init hs rfl ⟨QA64MD.of_noDecls hds (qa64C_of_partialTripleEnv
    (swpWorker_envGC (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_,
      threadRes_lkLe hLk0 _⟩),
    addrSafeA_of_partialTripleEnv (swpWorker_addr l c).uncount rfl hst.pc ⟨0, hst.x0, hst.x1, hst.dl, hst.dc⟩⟩
  intro f hf
  simp [σInit, Views.getFwd] at hf

end Rule

/-- **No fault at the runner's declarations** for the SWP worker's rule:
for strict sized `ds` agreeing with `{}` on the lock and the counter words. -/
theorem swp_counter_envG_runner_noFault [layout : _root_.Layout]
    [Executable.ValidLayout (layout swpWorker)] {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat)
    (l c : BitVec 64) (hag : ds.AgreesOnA (casS l c)) :
    NoFaultRule (swpRule_envGC_declsA hsz P tid l c) :=
  noFaultRule_ofSafelyEnvGRCMAD_rootD _ _ _ _ _ _ _ _ _ swpWorker_noFault hag

/-! ## Program level -/

section Prog

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]

/-- The SWP worker's address run as a value specification at `G = ⊤`. -/
def swpSpecA (l c : BitVec 64) : ValSpecA fun _ _ => True :=
  .ofAddr (casS l c) (layout swpWorker) (layout swpWorker)
    ((layout swpWorker).addrOf swpWorker.length) swpWorker_noPairs (MaskOf.refl _)
    swpWorker_rmwLive swpWorker_noFault (rootOnlyDA_of_phase1TreeR swpWorker_phase1R)

theorem swpSpecA_holdsD {ds : Decls} {l c : BitVec 64} {s : isa.State}
    (hst : WithDeclsD ds (StartState l c) s) : (swpSpecA l c).HoldsD ds s := by
  letI : CodeEnv := ⟨layout swpWorker⟩
  obtain ⟨hds, hst⟩ := hst
  exact holdsD_ofAddr (st := s) hst.exe hds hst.endPc
    (addrSafeA_of_partialTripleEnv (swpWorker_addr l c).uncount rfl hst.pc ⟨0, hst.x0, hst.x1, hst.dl, hst.dc⟩)

/-- **No reachable configuration of SWP spinlock workers with the runner's
declarations has a faulting step**, under any architecture (promises
included), for strict sized `ds` agreeing on the lock and the counter
words. -/
theorem swp_counter_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (l c : BitVec 64) (hag : ds.AgreesOnA (casS l c)) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  a64_faultFree_of_addrSpecs (fun _ => swpSpecA l c) (fun _ => ds) (fun _ => hsz) (fun _ => hag)
    (init_threads_ofA fun _ s hs => swpSpecA_holdsD (hst s (List.mem_of_getElem? hs)))

end Prog

end Kraken.Promising.SLR.EnvG.SwpEnvG

namespace Kraken.Promising.SLR.EnvG.A64SwpRunner

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG.SwpEnvG
open Kraken.Promising.SLR.EnvG.CasSmoke (casS)
open Kraken.Promising.SLR.SwpConcrete (swpLayout swpValid lockAddr counterAddr worker0 initMem2)
open Kraken.Promising.SLR.EnvG.A64Whole (withDeclsD_of)

/-- The runner's declarations agree with `{}` on the lock and the counter. -/
theorem swpDeclsD_agreesA : swpDeclsD.AgreesOnA (casS lockAddr counterAddr) := by
  decls_agrees_on_a

/-- **No fault at the runner's declarations**, concrete: the SWP worker's
rule at `SwpConcrete.swpLayout` and `swpDeclsD`. -/
theorem swp_counter_envG_runner_noFault_concrete (P : SpinCommon.Sys) (tid : Nat) :
    NoFaultRule (swpRule_envGC_declsA (layout := swpLayout) swpDeclsD_sized P tid lockAddr counterAddr) :=
  swp_counter_envG_runner_noFault (layout := swpLayout) swpDeclsD_sized P tid _ _ swpDeclsD_agreesA

/-- **`spinlock_swp2.kl` (`N = 2`) and `spinlock_swp3.kl` (`N = 3`) never
fault**, from the runner's exact configuration (`N` workers `swpWorkerD0`,
initial memory `SwpConcrete.initMem2`), under any architecture. -/
theorem swp_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N swpWorkerD0) initMem2) :=
  swp_counter_envG_runner_faultFree (layout := swpLayout) swpDeclsD_sized _ _ swpDeclsD_agreesA
    fun _ hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl SwpPublic.worker0_start

end Kraken.Promising.SLR.EnvG.A64SwpRunner

#print axioms Kraken.Promising.SLR.EnvG.SwpEnvG.swpInv_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_noFault_concrete
#print axioms Kraken.Promising.SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_faultFree_concreteN
