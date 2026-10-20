/-
**No fault at the runner's declarations for the AArch64 lock counters**
`spinlock_cas2/3.kl`, `spinlock_swpl2/3.kl`,
`ticketlock{2,3}.kl`, `ticketlock_al{2,3}.kl`.

Per program: the worker's **address run** in `SharedEnv.invTop S` (`vcgen`
with a register-only table: the address registers (`X0`/`X1`, and `X2` for
the ticket workers) hold the shared words, the private memory maps none),
giving `AddrSafeA` at the start; the worker's rule with the address run
(`…MAD`, `EnvG/A64NoFaultD.lean`; same `B` as the existing `…_decls` rule); its
initial invariant at the
runner's start (`…Inv_init_declsA`); and the rule's no-fault at `decls = ds`
for declarations agreeing on the shared words (`…_runner_noFault`), with a
concrete instance at the runner's declarations.
-/
import Kraken.Promising.SLR.EnvG.A64NoFaultD
import Kraken.Promising.SLR.EnvG.A64CasRunner
import Kraken.Promising.SLR.EnvG.A64SwplRunner
import Kraken.Promising.SLR.EnvG.A64TicketRunner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP

/-! ## `spinlock_cas2/3.kl` -/

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The worker's layout: the lock and the counter, 4-byte words. -/
abbrev casS (l c : BitVec 64) : SharedEnv.Layout := [(l, 4), (c, 4)]

section Addr

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)]

local instance casAddr.env : CodeEnv := ⟨layout casTtasWorker⟩

/-- The address table: `X0`, `X1` hold the lock and the counter, unmapped. -/
abbrev casAddrTable (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.invTop (casS l c))).State → Prop :=
  fun _ s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
    Mem.loadInt s.dmem c 4 = none

/-- **The worker's address run**: every access is the lock or the counter
word. -/
theorem casWorker_addr (l c : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.invTop (casS l c)))
      (fun s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
        Mem.loadInt s.dmem c 4 = none)
      casTtasWorker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (casAddrTable l c) (hP := by funext s g; simp [casAddrTable])
  cfg_cases_env [casTtasWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdl, hdc⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

end Addr

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)]

/-- **The CAS worker's rule with the address run** (`casRule_envG_decls`
through `ofSafelyEnvGMAD` on the lock and the counter). -/
noncomputable def casRule_envG_declsA {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat)
    (l c : BitVec 64) : ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGMAD (post := postCas P) (casS l c) hsz casTtasWorker_noPairs (MaskOf.refl _)
    (lockPlan_valid P tid) casTtasWorker_rmwLive casTtasWorker_phase1 postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_cas P tid)

/-- **The worker's initial invariant with the address run**
(`casInv_init_decls`). -/
theorem casInv_init_declsA {ds : Decls} (hsz : ds.StrictSized) {N : Nat} {l c : BitVec 64} (hlc : l ≠ c)
    (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hs : states[tid]? = some s) (hst : WithDeclsD ds (StartState l c) s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (casRule_envG_declsA hsz (ghostSys N l c) tid l c).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout casTtasWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  obtain ⟨hds, hst⟩ := hst
  refine invGMAD_init hs rfl ⟨QA64MD.of_noDecls hds (qa64_of_partialTripleEnv
    (casWorker_envG (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid,
      threadRes_C hL htid, by simp [σInit, Views.getFwd], threadRes_lkZero hLk0⟩),
    addrSafeA_of_partialTripleEnv (casWorker_addr l c).uncount rfl hst.pc ⟨0, hst.x0, hst.x1, hst.dl, hst.dc⟩⟩

end Rule

/-- **No fault at the runner's declarations** for the CAS worker's rule:
declarations agreeing on the lock and the counter words. -/
theorem cas_counter_envG_runner_noFault [layout : _root_.Layout]
    [Executable.ValidLayout (layout casTtasWorker)] {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat)
    (l c : BitVec 64) (hag : ds.AgreesOnA (casS l c)) :
    NoFaultRule (casRule_envG_declsA hsz P tid l c) :=
  noFaultRule_ofSafelyEnvGMAD_rootD _ _ _ _ _ _ _ _ _ casTtasWorker_noFault hag

end Kraken.Promising.SLR.EnvG.CasSmoke

namespace Kraken.Promising.SLR.EnvG.ConcreteCas

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG.CasSmoke

/-- The runner's declarations agree with `{}` on the lock and the counter. -/
theorem casDeclsD_agreesA : casDeclsD.AgreesOnA (casS lockAddr counterAddr) := by
  decls_agrees_on_a

/-- **No fault at the runner's declarations**, concrete: the CAS worker's
rule at `casLayout` and `casDeclsD`. -/
theorem cas_counter_envG_runner_noFault_concrete (P : SpinCommon.Sys) (tid : Nat) :
    NoFaultRule (casRule_envG_declsA (layout := casLayout) casDeclsD_sized P tid lockAddr counterAddr) :=
  cas_counter_envG_runner_noFault (layout := casLayout) casDeclsD_sized P tid _ _ casDeclsD_agreesA

end Kraken.Promising.SLR.EnvG.ConcreteCas

#print axioms Kraken.Promising.SLR.EnvG.CasSmoke.casInv_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.ConcreteCas.cas_counter_envG_runner_noFault_concrete

/-! ## `spinlock_swpl2/3.kl` -/

namespace Kraken.Promising.SLR.EnvG.SwplLock

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.EnvG.X64Spin (xlockPlan xlockPlan_valid)
open Kraken.Promising.SLR.EnvG.CasSmoke (ghostSys ghostSys_spinLocs world_spinGhost' threadRes_fresh' casS)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

set_option mvcgen.warning false
set_option experimental.vcgen true

section Addr

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]

local instance swplAddr.env : CodeEnv := ⟨layout swplWorker⟩

/-- The address table: `X0`, `X1` hold the lock and the counter, unmapped. -/
abbrev swplAddrTable (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.invTop (casS l c))).State → Prop :=
  fun _ s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
    Mem.loadInt s.dmem c 4 = none

/-- **The worker's address run**: every access is the lock or the counter
word. -/
theorem swplWorker_addr (l c : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.invTop (casS l c)))
      (fun s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
        Mem.loadInt s.dmem c 4 = none)
      swplWorker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (swplAddrTable l c) (hP := by funext s g; simp [swplAddrTable])
  cfg_cases_env [swplWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdl, hdc⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

end Addr

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swplWorker)]

/-- **The `swpl` worker's rule with the address run** (`swplRule_envGC_decls`
through `ofSafelyEnvGRCMAD` on the lock and the counter). -/
noncomputable def swplRule_envGC_declsA {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat)
    (l c : BitVec 64) : ThreadRuleRX (I := isa) Arch.armv8 (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.ofSafelyEnvGRCMAD (post := postSwpl P) (casS l c) hsz swplWorker_noPairs (MaskOf.refl _)
    (xlockPlan_valid P tid) swplWorker_rmwLive swplWorker_phase1R postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_swpl P tid)

/-- **The worker's initial invariant with the address run**
(`swplInv_init_decls`). -/
theorem swplInv_init_declsA {ds : Decls} (hsz : ds.StrictSized) {N : Nat} {l c : BitVec 64} (hlc : l ≠ c)
    (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N) {states : List isa.State} {initMem : List (Loc × Val)}
    {s : isa.State} (hs : states[tid]? = some s) (hst : WithDeclsD ds (StartState l c) s)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (swplRule_envGC_declsA hsz (ghostSys N l c) tid l c).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout swplWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  obtain ⟨hds, hst⟩ := hst
  refine invGRCMAD_init hs rfl ⟨QA64MD.of_noDecls hds (qa64C_of_partialTripleEnv
    (swplWorker_envGC (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_,
      threadRes_lkLe hLk0 _⟩),
    addrSafeA_of_partialTripleEnv (swplWorker_addr l c).uncount rfl hst.pc ⟨0, hst.x0, hst.x1, hst.dl, hst.dc⟩⟩
  intro f hf
  simp [σInit, Views.getFwd] at hf

end Rule

/-- **No fault at the runner's declarations** for the `swpl` worker's rule:
declarations agreeing on the lock and the counter words. -/
theorem swpl_counter_envG_runner_noFault [layout : _root_.Layout]
    [Executable.ValidLayout (layout swplWorker)] {ds : Decls} (hsz : ds.StrictSized) (P : Sys) (tid : Nat)
    (l c : BitVec 64) (hag : ds.AgreesOnA (casS l c)) :
    NoFaultRule (swplRule_envGC_declsA hsz P tid l c) :=
  noFaultRule_ofSafelyEnvGRCMAD_rootD _ _ _ _ _ _ _ _ _ swplWorker_noFault hag

end Kraken.Promising.SLR.EnvG.SwplLock

namespace Kraken.Promising.SLR.EnvG.ConcreteSwpl

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG.SwplLock
open Kraken.Promising.SLR.EnvG.CasSmoke (casS)

/-- The runner's declarations agree with `{}` on the lock and the counter. -/
theorem swplDeclsD_agreesA : swplDeclsD.AgreesOnA (casS lockAddr counterAddr) := by
  decls_agrees_on_a

/-- **No fault at the runner's declarations**, concrete: the `swpl` worker's
rule at `swplLayout` and `swplDeclsD`. -/
theorem swpl_counter_envG_runner_noFault_concrete (P : SpinCommon.Sys) (tid : Nat) :
    NoFaultRule (swplRule_envGC_declsA (layout := swplLayout) swplDeclsD_sized P tid lockAddr counterAddr) :=
  swpl_counter_envG_runner_noFault (layout := swplLayout) swplDeclsD_sized P tid _ _ swplDeclsD_agreesA

end Kraken.Promising.SLR.EnvG.ConcreteSwpl

#print axioms Kraken.Promising.SLR.EnvG.SwplLock.swplInv_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.ConcreteSwpl.swpl_counter_envG_runner_noFault_concrete

/-! ## `ticketlock{2,3}.kl` and `ticketlock_al{2,3}.kl` -/

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The worker's layout: `next`, `owner` and the counter, 4-byte words. -/
abbrev tkS (x o c : BitVec 64) : SharedEnv.Layout := [(x, 4), (o, 4), (c, 4)]

/-- The ticket workers' address precondition: `X0`, `X1`, `X2` hold `next`,
`owner` and the counter, unmapped. -/
abbrev tkAddrPre (x o c : BitVec 64) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = x ∧ s.regs.X1.toBitVec = o ∧ s.regs.X2.toBitVec = c ∧
    Mem.loadInt s.dmem x 4 = none ∧ Mem.loadInt s.dmem o 4 = none ∧ Mem.loadInt s.dmem c 4 = none

section Addr

variable [layout : _root_.Layout]

/-- **The `ldadda` worker's address run**: every access is `next`, `owner`
or the counter word. -/
theorem tkWorker_addr [Executable.ValidLayout (layout tkWorker)] (x o c : BitVec 64) :
    letI : CodeEnv := ⟨layout tkWorker⟩
    PartialTripleEnv (SharedEnv.counted (SharedEnv.invTop (tkS x o c))) (fun s _ => tkAddrPre x o c s)
      tkWorker (fun _ _ => True) (fun _ _ _ => False) := by
  letI : CodeEnv := ⟨layout tkWorker⟩
  apply MachineWP.cfgEnv_partial
    (fun (_ : Label) s (_ : (SharedEnv.counted (SharedEnv.invTop (tkS x o c))).State) => tkAddrPre x o c s)
    (hP := rfl)
  cfg_cases_env [tkWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hx2, hdx, hdo, hdc⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

/-- **The `ldaddal` worker's address run.** -/
theorem tkWorkerAl_addr [Executable.ValidLayout (layout tkWorkerAl)] (x o c : BitVec 64) :
    letI : CodeEnv := ⟨layout tkWorkerAl⟩
    PartialTripleEnv (SharedEnv.counted (SharedEnv.invTop (tkS x o c))) (fun s _ => tkAddrPre x o c s)
      tkWorkerAl (fun _ _ => True) (fun _ _ _ => False) := by
  letI : CodeEnv := ⟨layout tkWorkerAl⟩
  apply MachineWP.cfgEnv_partial
    (fun (_ : Label) s (_ : (SharedEnv.counted (SharedEnv.invTop (tkS x o c))).State) => tkAddrPre x o c s)
    (hP := rfl)
  cfg_cases_env [tkWorkerAl]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hx2, hdx, hdo, hdc⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.inv, Reg64s.setXReg]

end Addr

section Rule

variable [layout : _root_.Layout]

/-- **The `ldadda` worker's rule with declarations and the address run**
(`npSafeP_of_safelyEnvGTDMD`'s rule through `ofSafelyEnvGTDMAD` on `next`,
`owner` and the counter). -/
noncomputable def tkRule_envGTD_declsA [Executable.ValidLayout (layout tkWorker)] {ds : Decls}
    (hsz : ds.StrictSized) (P : Sys) (hL : Locs P) (tid : Nat) (x o c : BitVec 64) :
    ThreadRuleRXGSXE (I := isa) G₀ (disp P hL.xo).TX Arch.armv8 (fun c r _ => TPost P c r) tid :=
  ThreadRuleRXGSXE.ofSafelyEnvGTDMAD (post := postTk P tid) (tkS x o c) hsz tkWorker_noPairs (MaskOf.refl _)
    (tkPlan_valid P) tkWorker_rmwLive tkWorker_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_tk P tid)

/-- **The `ldadda` worker's initial invariant with the address run**
(`tkInv_init_decls`). -/
theorem tkInv_init_declsA [Executable.ValidLayout (layout tkWorker)] {ds : Decls} (hsz : ds.StrictSized)
    {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) {tid : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : WithDeclsD ds (StartState x o c) s) :
    (tkRule_envGTD_declsA hsz (tkSys N x o c) hL tid x o c).Inv True (Config.init states initMem)
      (thRes (Config.init states initMem).mem (tkSys N x o c) tid)
      (tkGhost (Config.init states initMem).mem (tkSys N x o c)) := by
  letI : CodeEnv := ⟨layout tkWorker⟩
  obtain ⟨hds, hst⟩ := hst
  exact invGTDMAD_init hs rfl ⟨QA64MD.of_noDecls hds (qa64TD_of_partialTripleEnv
    (tkWorker_envGTD N x o c hL tid).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc, start_init hL _ tid _⟩),
    addrSafeA_of_partialTripleEnv (tkWorker_addr x o c).uncount rfl hst.pc
      ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc⟩⟩

/-- **No fault at the runner's declarations** for the `ldadda` worker's
rule: declarations agreeing on `next`, `owner` and the counter. -/
theorem ticket_counter_envG_runner_noFault [Executable.ValidLayout (layout tkWorker)] {ds : Decls}
    (hsz : ds.StrictSized) (P : Sys) (hL : Locs P) (tid : Nat) (x o c : BitVec 64)
    (hag : ds.AgreesOnA (tkS x o c)) :
    NoFaultRuleSXE (tkRule_envGTD_declsA hsz P hL tid x o c) :=
  noFaultRule_ofSafelyEnvGTDMAD_rootD _ _ _ _ _ _ _ _ _ tkWorker_noFault hag

/-- **The `ldaddal` worker's rule with declarations and the address run**
(through `ofSafelyEnvGTDRMAD`). -/
noncomputable def tkAlRule_envGTDR_declsA [Executable.ValidLayout (layout tkWorkerAl)] {ds : Decls}
    (hsz : ds.StrictSized) (P : Sys) (hL : Locs P) (tid : Nat) (x o c : BitVec 64) :
    ThreadRuleRXGSXE (I := isa) G₀ (disp P hL.xo).TX Arch.armv8 (fun c r _ => TPost P c r) tid :=
  ThreadRuleRXGSXE.ofSafelyEnvGTDRMAD (post := postTkAl P tid) (tkS x o c) hsz tkWorkerAl_noPairs
    (MaskOf.refl _) (tkPlan_valid P) tkWorkerAl_rmwLive tkWorkerAl_phase1R postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_tkAl P tid)

/-- **The `ldaddal` worker's initial invariant with the address run**
(`tkAlInv_init_decls`). -/
theorem tkAlInv_init_declsA [Executable.ValidLayout (layout tkWorkerAl)] {ds : Decls} (hsz : ds.StrictSized)
    {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) {tid : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : WithDeclsD ds (StartStateAl x o c) s) :
    (tkAlRule_envGTDR_declsA hsz (tkSys N x o c) hL tid x o c).Inv True (Config.init states initMem)
      (thRes (Config.init states initMem).mem (tkSys N x o c) tid)
      (tkGhost (Config.init states initMem).mem (tkSys N x o c)) := by
  letI : CodeEnv := ⟨layout tkWorkerAl⟩
  obtain ⟨hds, hst⟩ := hst
  exact invGTDRMAD_init hs rfl ⟨QA64MD.of_noDecls hds (qa64TDR_of_partialTripleEnv
    (tkWorkerAl_envGTDR N x o c hL tid).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc, start_init hL _ tid _⟩),
    addrSafeA_of_partialTripleEnv (tkWorkerAl_addr x o c).uncount rfl hst.pc
      ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc⟩⟩

/-- **No fault at the runner's declarations** for the `ldaddal` worker's
rule. -/
theorem ticket_al_counter_envG_runner_noFault [Executable.ValidLayout (layout tkWorkerAl)] {ds : Decls}
    (hsz : ds.StrictSized) (P : Sys) (hL : Locs P) (tid : Nat) (x o c : BitVec 64)
    (hag : ds.AgreesOnA (tkS x o c)) :
    NoFaultRuleSXE (tkAlRule_envGTDR_declsA hsz P hL tid x o c) :=
  noFaultRule_ofSafelyEnvGTDRMAD_rootD _ _ _ _ _ _ _ _ _ tkWorkerAl_noFault hag

end Rule

end Kraken.Promising.SLR.EnvG.TicketLock

namespace Kraken.Promising.SLR.EnvG.ConcreteTicketD

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.SLR.EnvG.ConcreteTicketAl (nextAddr ownerAddr counterAddr tkAlLayout)

/-- The runner's declarations agree with `{}` on `next`, `owner` and the
counter. -/
theorem tkDeclsD_agreesA : tkDeclsD.AgreesOnA (tkS nextAddr ownerAddr counterAddr) := by
  decls_agrees_on_a

/-- **No fault at the runner's declarations**, concrete: the `ldadda`
worker's rule at `tkLayoutD` and `tkDeclsD`. -/
theorem ticket_counter_envG_runner_noFault_concrete (P : Sys) (hL : Locs P) (tid : Nat) :
    NoFaultRuleSXE (tkRule_envGTD_declsA (layout := tkLayoutD) tkDeclsD_sized P hL tid nextAddr ownerAddr
      counterAddr) :=
  ticket_counter_envG_runner_noFault (layout := tkLayoutD) tkDeclsD_sized P hL tid _ _ _ tkDeclsD_agreesA

/-- **No fault at the runner's declarations**, concrete: the `ldaddal`
worker's rule at `tkAlLayout` and `tkDeclsD`. -/
theorem ticket_al_counter_envG_runner_noFault_concrete (P : Sys) (hL : Locs P) (tid : Nat) :
    NoFaultRuleSXE (tkAlRule_envGTDR_declsA (layout := tkAlLayout) tkDeclsD_sized P hL tid nextAddr ownerAddr
      counterAddr) :=
  ticket_al_counter_envG_runner_noFault (layout := tkAlLayout) tkDeclsD_sized P hL tid _ _ _ tkDeclsD_agreesA

end Kraken.Promising.SLR.EnvG.ConcreteTicketD

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkInv_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkAlInv_init_declsA
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketD.ticket_counter_envG_runner_noFault_concrete
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketD.ticket_al_counter_envG_runner_noFault_concrete
