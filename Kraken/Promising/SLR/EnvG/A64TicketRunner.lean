/-
**`ticketlock{2,3}.kl` and `ticketlock_al{2,3}.kl` for AArch64 from the
runner's exact configuration**:
`ticket_counter_envG_runner` and `ticket_al_counter_envG_runner`,
`TicketLock.ticket_counter_envG` / `ticket_al_counter_envG` for threads that
carry the `.kl` runner's declarations (the typed header `uint32_t next,
owner, counter`: strict sized, `Decls.StrictSized`), and their concrete
instances (`A64Whole.runnerIsD`: declarations and initial memory included).

- **Purity and phases with declarations**: `DispSpec.HoldsD` (`DispSpec.Holds`
  with `decls = ds`), `DispSpec.holdsD_of_noDecls`, `dispSpec_stepD`
  (`dispSpec_step` through `exec_treeJ_of_reresolve`); they moved
  beside `DispSpec` in `EnvG/DispenserPureA64.lean`.
- **Assembly**: `ticket_counter_ofD`, the existing `ticket_counter_of` at
  `DispSpec.HoldsD` (the existing one is stated at `DispSpec.Holds`, i.e.
  `decls = {}`; it is unchanged). Both are instances of the generic
  `ticket_counter_core` (`EnvG/TicketCounterCore.lean`).
- **Rules**: the D forms of `EnvG/A64DeclsLinkMore.lean`,
  `npSafeP_of_safelyEnvGTDMD` (`ldadda`) and `npSafeP_of_safelyEnvGTDRMD`
  (`ldaddal`), with `MaskOf.refl`; starts `tkInv_init_decls`,
  `tkAlInv_init_decls` (`invGTDMD_init`/`invGTDRMD_init`).
- **Concrete**: `ConcreteTicketD` (new: the existing files have no concrete
  instance for the `ldadda` worker `tkWorker`) and `ConcreteTicketAl`
  (`tkAlWorker0` with the runner's declarations).

The start states are the verbatim `StartState`/`StartStateAl` with
declarations (`A64Whole.WithDeclsD`). The old theorems are unchanged. Faults
are not covered (see `EnvG/A64DeclsBridge.lean`); `tkRule_noFault` and
`tkRuleAl_noFault` stay at `decls = {}`.
-/
import Kraken.Promising.SLR.EnvG.ConcreteTicketAl
import Kraken.Promising.SLR.EnvG.A64DeclsRunner
import Kraken.Promising.SLR.EnvG.A64DeclsLinkMore

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
open Kraken.Promising.SLR.EnvG.CasSmoke (reachable_nil')
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

-- `DispSpec.HoldsD`, `DispSpec.holdsD_of_noDecls` and `dispSpec_stepD` are in
-- `EnvG/DispenserPureA64.lean` (moved, same names).

/-! ## The assembly with declarations -/

/-- **The ticket lock's assembly with declarations** (`ticket_counter_of`
at `DispSpec.HoldsD`; an instance of `ticket_counter_core`): from a purity-and-phase specification `DS` whose code
has no `LDXP`/`STXP`, holding with strict sized declarations `ds` at every
start state, and each thread's `NPSafeP` at the initial configuration,
`counter = N` at every final reachable configuration. -/
theorem ticket_counter_ofD {fuel : Nat}
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)} (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (DS : ∀ Q : Loc → Val → Prop, DispSpec Arch.armv8 Q ⟨x, 4⟩ (N + 1)) {ds : Decls} (hsz : ds.StrictSized)
    (hnp : ∀ Q, Kraken.Executable.noPairs (DS Q).e = true)
    (hDS : ∀ Q : Loc → Val → Prop, (∀ v, Q ⟨x, 4⟩ v) → (∀ v, Q ⟨c, 4⟩ v) → ∀ s ∈ states,
      (DS Q).HoldsD ds false s)
    (hsafe : ∀ (hL : Locs (tkSys N x o c)) tid s, states[tid]? = some s → ∀ n m,
      NPSafeP (modelX isa (disp (tkSys N x o c) hL.xo).TX) Arch.armv8 (fun cf r _ => TPost (tkSys N x o c) cf r) tid
        G₀ (K2Scope (model isa) AllocIds) n m True (Config.init states initMem)
        (thRes (Config.init states initMem).mem (tkSys N x o c) tid) (tkGhost (Config.init states initMem).mem
          (tkSys N x o c)))
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  ticket_counter_core Arch.armv8 N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 (fun _ b s => (DS _).HoldsD ds b s)
    (fun _ hc' => Config.ntFree_armv8 hc') (fun _ _ _ _ _ h hex => dispSpec_stepD _ hsz (hnp _) h _ hex)
    (fun hL _ s hs => hDS _ (tkGhost_pure_x hL _) (tkGhost_pure_c hL _) s (List.mem_of_getElem? hs)) hsafe hc hf

/-! ## The `ldadda` worker (`ticketlock{2,3}.kl`) -/

section Tk

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]

omit [Executable.ValidLayout (layout tkWorker)] in
/-- The worker has no `LDXP`/`STXP`. -/
theorem tkWorker_noPairs : Kraken.Executable.noPairs (layout tkWorker) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The worker's initial invariant with declarations** (`tkInv_init`). -/
theorem tkInv_init_decls {ds : Decls} {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) {tid : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : WithDeclsD ds (StartState x o c) s) :
    InvGTD (I := isa) Arch.armv8 tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo)
      (QA64MD ds (EnvGTDA Arch.armv8 tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo)) (layout tkWorker)
        (layout tkWorker) ((layout tkWorker).addrOf tkWorker.length) (postTk (tkSys N x o c) tid))
      True (Config.init states initMem) (thRes (Config.init states initMem).mem (tkSys N x o c) tid)
      (tkGhost (Config.init states initMem).mem (tkSys N x o c)) := by
  letI : CodeEnv := ⟨layout tkWorker⟩
  obtain ⟨hds, hst⟩ := hst
  exact invGTDMD_init hs rfl (QA64MD.of_noDecls hds (qa64TD_of_partialTripleEnv
    (tkWorker_envGTD N x o c hL tid).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc, start_init hL _ tid _⟩))

end Tk

/-- **`counter = N` for the AArch64 ticket lock workers, with the runner's
declarations**: `ticket_counter_envG` for threads whose declarations are
strict sized (`ds.StrictSized`: the `.kl` runner's, from the typed header)
and which otherwise start as there (`StartState` of the thread with its
declarations dropped). -/
theorem ticket_counter_envG_runner [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)]
    {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartState x o c) s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  have hxo' : x ≠ o := by rintro rfl; simp [Decls.overlaps] at hxo
  have hxc' : x ≠ c := by rintro rfl; simp [Decls.overlaps] at hxc
  exact ticket_counter_ofD N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 (tkDispSpec · N x) hsz
    (fun _ => tkWorker_noPairs)
    (fun _ hQx hQc s hs => DispSpec.holdsD_of_noDecls (hst s hs).1
      (tkDispSpec_holds hN32 hxo' hxc' hQx hQc (hst s hs).2))
    (fun hL tid s hs n m => npSafeP_of_safelyEnvGTDMD hsz tkWorker_noPairs (MaskOf.refl _) (tkPlan_valid _)
      tkWorker_rmwLive tkWorker_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_tk _ tid) n m
      (tkInv_init_decls hL hs (hst s (List.mem_of_getElem? hs))))
    hc hf

/-! ## The `ldaddal` worker (`ticketlock_al{2,3}.kl`) -/

section TkAl

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]

omit [Executable.ValidLayout (layout tkWorkerAl)] in
/-- The worker has no `LDXP`/`STXP`. -/
theorem tkWorkerAl_noPairs : Kraken.Executable.noPairs (layout tkWorkerAl) = true := by
  rw [Layout.apply_noPairs]; decide

/-- **The worker's initial invariant with declarations** (`tkAlInv_init`). -/
theorem tkAlInv_init_decls {ds : Decls} {N : Nat} {x o c : BitVec 64} (hL : Locs (tkSys N x o c)) {tid : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : WithDeclsD ds (StartStateAl x o c) s) :
    InvGTDR (I := isa) tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo)
      (QA64MD ds (EnvGTDRA Arch.armv8 tid (tkPlan (tkSys N x o c)) (disp (tkSys N x o c) hL.xo))
        (layout tkWorkerAl) (layout tkWorkerAl) ((layout tkWorkerAl).addrOf tkWorkerAl.length)
        (postTkAl (tkSys N x o c) tid))
      True (Config.init states initMem) (thRes (Config.init states initMem).mem (tkSys N x o c) tid)
      (tkGhost (Config.init states initMem).mem (tkSys N x o c)) := by
  letI : CodeEnv := ⟨layout tkWorkerAl⟩
  obtain ⟨hds, hst⟩ := hst
  exact invGTDRMD_init hs rfl (QA64MD.of_noDecls hds (qa64TDR_of_partialTripleEnv
    (tkWorkerAl_envGTDR N x o c hL tid).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.x2, hst.dx, hst.dO, hst.dc, start_init hL _ tid _⟩))

end TkAl

/-- **`counter = N` for the AArch64 `ldaddal` ticket lock workers, with the
runner's declarations**: `ticket_al_counter_envG` for threads whose
declarations are strict sized (`ds.StrictSized`: the `.kl` runner's, from
the typed header) and which otherwise start as there (`StartStateAl` of the
thread with its declarations dropped). -/
theorem ticket_al_counter_envG_runner [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorkerAl)]
    {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (N : Nat) (x o c : BitVec 64) (hxo : Decls.overlaps x 4 o 4 = false) (hxc : Decls.overlaps x 4 c 4 = false)
    (hoc : Decls.overlaps o 4 c 4 = false) (hN32 : N + 1 < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, WithDeclsD ds (StartStateAl x o c) s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  have hxo' : x ≠ o := by rintro rfl; simp [Decls.overlaps] at hxo
  have hxc' : x ≠ c := by rintro rfl; simp [Decls.overlaps] at hxc
  exact ticket_counter_ofD N x o c hxo hxc hoc hN32 hN hX0 hO0 hC0 (tkAlDispSpec · N x) hsz
    (fun _ => tkWorkerAl_noPairs)
    (fun _ hQx hQc s hs => DispSpec.holdsD_of_noDecls (hst s hs).1
      (tkAlDispSpec_holds hN32 hxo' hxc' hQx hQc (hst s hs).2))
    (fun hL tid s hs n m => npSafeP_of_safelyEnvGTDRMD hsz tkWorkerAl_noPairs (MaskOf.refl _) (tkPlan_valid _)
      tkWorkerAl_rmwLive tkWorkerAl_phase1R postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_tkAl _ tid) n m
      (tkAlInv_init_decls hL hs (hst s (List.mem_of_getElem? hs))))
    hc hf

end Kraken.Promising.SLR.EnvG.TicketLock

/-! ## The runner's configurations -/

/-! ### `ticketlock{2,3}.kl` (`ldadda`) -/

namespace Kraken.Promising.SLR.EnvG.ConcreteTicketD

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)
open Kraken.Promising.SLR.EnvG.A64WholeCounters (ticket2Kl ticket3Kl)
open Kraken.Promising.SLR.EnvG.ConcreteTicketAl (nextAddr ownerAddr counterAddr)

/-- The worker's layout: text at `0x100000`, each directive its `fakeSize`
(the runner's layout). -/
@[reducible] def tkLayoutD : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize tkWorker

instance tkValidD : Executable.ValidLayout (tkLayoutD tkWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- A worker's initial state without declarations: `X0 = next`,
`X1 = owner`, `X2 = counter`, at the start label `worker`, halting at `done`
(the end of the text, `0x100000 + 44`); empty private memory. -/
def tkWorker0 : AArch64.State where
  exe := tkLayoutD tkWorker
  endPc := 0x100000 + 44
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X2 := 0x1200 } }, 0x100000)

section
attribute [local instance] tkLayoutD

theorem tkWorker0_start : StartState nextAddr ownerAddr counterAddr tkWorker0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
    simp [tkWorker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, nextAddr, ownerAddr,
      counterAddr]

end

/-- The runner's declarations for the typed `ticketlock{2,3}.kl` and
`ticketlock_al{2,3}.kl`: `next`, `owner`, `counter` 4-byte words (strict). -/
def tkDeclsD : Decls :=
  { locs := [⟨nextAddr, 4⟩, ⟨ownerAddr, 4⟩, ⟨counterAddr, 4⟩], unsizedDefault := false }

theorem tkDeclsD_sized : tkDeclsD.StrictSized := ⟨rfl, by decide⟩

/-- A worker as the runner prepares it, declarations included. -/
def tkWorkerD0 : AArch64.State := { tkWorker0 with decls := tkDeclsD }

/-- The runner's configurations are `Config.init [tkWorkerD0, …]
tkAlInitMem` (two and three workers) in everything the theorem reads
(declarations and initial memory included: the typed header's initial
memory is the existing `ConcreteTicketAl.tkAlInitMem`). -/
def runnerMatchesDTk : Bool :=
  A64Whole.runnerIsD ticket2Kl (List.replicate 2 tkWorkerD0) ConcreteTicketAl.tkAlInitMem &&
    A64Whole.runnerIsD ticket3Kl (List.replicate 3 tkWorkerD0) ConcreteTicketAl.tkAlInitMem

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDTk

/-- **`counter = N`** for `N + 1 < 2 ^ 32` `ldadda` ticket-lock workers
carrying the runner's declarations, concrete instance of
`ticket_counter_envG_runner`. -/
theorem ticket_counter_envG_runner_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate N tkWorkerD0) ConcreteTicketAl.tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N :=
  ticket_counter_envG_runner (layout := tkLayoutD) tkDeclsD_sized N nextAddr ownerAddr counterAddr
    ConcreteTicketAl.tkAl_disj_xo ConcreteTicketAl.tkAl_disj_xc ConcreteTicketAl.tkAl_disj_oc hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl tkWorker0_start) List.length_replicate
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)
    hc hf

/-- **`counter = 2`** for `ticketlock2.kl` under `Arch.armv8`, from the
runner's exact configuration (the whole `code` block at `0x100000`, the
typed header's declarations and initial memory). -/
theorem ticket_counter_envG_runner_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 2 tkWorkerD0) ConcreteTicketAl.tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 2 :=
  ticket_counter_envG_runner_concreteN 2 (by decide) hc hf

/-- **`counter = 3`** for `ticketlock3.kl`, from the runner's exact
configuration. -/
theorem ticket_counter_envG_runner_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 3 tkWorkerD0) ConcreteTicketAl.tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 3 :=
  ticket_counter_envG_runner_concreteN 3 (by decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteTicketD

/-! ### `ticketlock_al{2,3}.kl` (`ldaddal`) -/

namespace Kraken.Promising.SLR.EnvG.ConcreteTicketAl

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)
open Kraken.Promising.SLR.EnvG.ConcreteTicketD (tkDeclsD tkDeclsD_sized)

/-- A worker as the runner prepares it, declarations included. -/
def tkAlWorkerD0 : AArch64.State := { tkAlWorker0 with decls := tkDeclsD }

/-- The runner's configurations are `Config.init [tkAlWorkerD0, …]
tkAlInitMem` (two and three workers) in everything the theorem reads
(declarations and initial memory included). -/
def runnerMatchesDTkAl : Bool :=
  A64Whole.runnerIsD tkAl2Kl (List.replicate 2 tkAlWorkerD0) tkAlInitMem &&
    A64Whole.runnerIsD tkAl3Kl (List.replicate 3 tkAlWorkerD0) tkAlInitMem

/-- info: true -/
#guard_msgs in
#eval runnerMatchesDTkAl

/-- **`counter = N`** for `N + 1 < 2 ^ 32` `ldaddal` ticket-lock workers
carrying the runner's declarations, concrete instance of
`ticket_al_counter_envG_runner`. -/
theorem ticket_al_counter_envG_runner_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate N tkAlWorkerD0) tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N :=
  ticket_al_counter_envG_runner (layout := tkAlLayout) tkDeclsD_sized N nextAddr ownerAddr counterAddr tkAl_disj_xo
    tkAl_disj_xc tkAl_disj_oc hN32 (fun s hs => (List.eq_of_mem_replicate hs) ▸ withDeclsD_of rfl tkAlWorker0_start)
    List.length_replicate (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)
    (by simp only [Config.init]; decide) hc hf

/-- **`counter = 2`** for `ticketlock_al2.kl` under `Arch.armv8`, from the
runner's exact configuration. -/
theorem ticket_al_counter_envG_runner_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 2 tkAlWorkerD0) tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 2 :=
  ticket_al_counter_envG_runner_concreteN 2 (by decide) hc hf

/-- **`counter = 3`** for `ticketlock_al3.kl`, from the runner's exact
configuration. -/
theorem ticket_al_counter_envG_runner_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate 3 tkAlWorkerD0) tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 3 :=
  ticket_al_counter_envG_runner_concreteN 3 (by decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteTicketAl

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.dispSpec_stepD
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_counter_ofD
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_counter_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_al_counter_envG_runner
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketD.ticket_counter_envG_runner_concrete2
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketD.ticket_counter_envG_runner_concrete3
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketAl.ticket_al_counter_envG_runner_concrete2
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketAl.ticket_al_counter_envG_runner_concrete3
