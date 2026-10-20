/-
**Liveness of the AArch64 SWP spinlocks (`spinlock_swp{2,3}.kl`,
`spinlock_swpl{2,3}.kl`) in the runner's declarations form.**

`Live.SpinSwpFam.spin_swp(l)_live_pf` (deadlock-freedom) and
`spin_swp(l)_live_oneShot_pf` (per-thread, one-shot workers) are stated for
threads with no declarations (`SpinSwp.SwpStartG`: `SwpPublic.StartState` /
`SwplLock.StartState`, `decls = {}`). The `.kl` runner's threads carry the
typed header's declarations (`swpDeclsD`, `swplDeclsD`: the two 4-byte
words, strict). As for the ticket lock (`LiveRunnerA64Ticket`), generically
in the program (`SpinSwpTrees.SwpCode P`):

- `SSwp P l c`: `SpinSwpInv.Static P` and the pc at one of the worker's
  positions (`swPcs`); `stepOK_swp` from the `SwpCode` cell trees (accesses
  only at `⟨l, 4⟩`, `⟨c, 4⟩`; the release is a store or an RMW at `l`);
- `SwpStartGD ds Start`: `SwpStartG Start` with `WithDeclsD ds (Start l c)`
  (the start states of `swp(l)_counter_envG_runner`) and `ds.AgreesAt l 4`,
  `ds.AgreesAt c 4`;
- `swp_live_pf_runner_gen` / `swp_live_oneShot_pf_runner_gen`: any
  `SwpLiveUnderG` / `SwpOneShotUnderG` statement at `decls = {}` transfers
  (`progressFrom_transfer` / `liveFrom_transfer`, `execSimA`);
- **`spin_swp_live_pf_runner`**, **`spin_swpl_live_pf_runner`** and the
  one-shot forms, with `_runner_concrete` (the runner's layouts) and
  `_runnerN` (`N` copies of `swpWorkerD0` / `swplWorkerD0`, the runner's
  initial memory; no hypothesis left).

Promise-free fragment only, as for the theorems transferred.
-/
import Kraken.Promising.LiveRunnerA64
import Kraken.Promising.LiveSpinSwpFam
import Kraken.Promising.SLR.EnvG.A64SwpRunner
import Kraken.Promising.SLR.EnvG.A64SwplRunner

namespace Kraken.Promising.Live.RunnerA64Swp

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.RunnerA64 Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.SpinSwp
open Kraken.Promising.Live.SpinSwpInv (Static)
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD)

section Generic

variable [layout : _root_.Layout] {P : Program} [hv : Executable.ValidLayout (layout P)]

set_option hygiene false in
local notation "pcA" => (layout P).addrOf

/-- **The bridge's invariant for an SWP-spinlock worker** (states without
declarations): `Static` and the pc at one of the worker's positions. -/
def SSwp (P : Program) (l c : BitVec 64) (s : State) : Prop :=
  Static P l c s ∧ ∃ i ∈ swPcs, s.st.2 = (layout P).addrOf i

/-- **Every tree of an `SSwp` state agrees with `ds` and stays in `SSwp`.** -/
theorem stepOK_swp (hC : SwpCode P) {ds : Decls} {l c : BitVec 64} (hl : ds.AgreesAt l 4)
    (hc : ds.AgreesAt c 4) : StepOK ds (layout P) (SSwp P l c) where
  exe _ h := h.1.exe
  decls _ h := h.1.decls
  ok s h t hex := by
    obtain ⟨hS, i, hi, hpc⟩ := h
    have hat : ∀ {j}, j ∈ swPcs → j ≠ 16 → s.st.2 = pcA j → AtG P s j :=
      fun hj h16 hp => SpinSwpInv.Static.at hC hS hj h16 hp
    have lf : ∀ md j, md.regs.X0 = s.st.1.regs.X0 → md.regs.X1 = s.st.1.regs.X1 → md.dmem = s.st.1.dmem →
        j ∈ swPcs → SSwp P l c (SLR.SwpTrees.goto s md (pcA j)) :=
      fun md j h0 h1 hd hj => ⟨hS.goto md _ h0 h1 hd, j, hj, rfl⟩
    simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hC.mov _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 3 rfl rfl rfl (by decide)
    · rw [hC.swpa _ _ (hat (by decide) (by decide) hpc) hS.x0 hS.dl] at hex; cases hex
      exact ⟨hl, fun _ => lf _ 4 rfl rfl rfl (by decide)⟩
    · rw [hC.cbz _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      by_cases hz : BitVec.setWidth 32 s.st.1.regs.X2.toBitVec = 0#32
      · simp only [hz, ite_true]; exact lf _ 10 rfl rfl rfl (by decide)
      · simp only [hz, ite_false]; exact lf _ 6 rfl rfl rfl (by decide)
    · rw [hC.ldr _ _ (hat (by decide) (by decide) hpc) hS.x0 hS.dl] at hex; cases hex
      exact ⟨hl, fun _ => lf _ 7 rfl rfl rfl (by decide)⟩
    · rw [hC.cbnz _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      by_cases hz : BitVec.setWidth 32 s.st.1.regs.X2.toBitVec = 0#32
      · simp only [hz, ite_true]; exact lf _ 8 rfl rfl rfl (by decide)
      · simp only [hz, ite_false]; exact lf _ 6 rfl rfl rfl (by decide)
    · rw [hC.btry _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 3 rfl rfl rfl (by decide)
    · rw [hC.ldrc _ _ (hat (by decide) (by decide) hpc) hS.x1 hS.dc] at hex; cases hex
      exact ⟨hc, fun _ => lf _ 11 rfl rfl rfl (by decide)⟩
    · rw [hC.add _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 12 rfl rfl rfl (by decide)
    · rw [hC.strc _ _ (hat (by decide) (by decide) hpc) hS.x1 hS.dc] at hex; cases hex
      exact ⟨hc, fun _ => lf _ 13 rfl rfl rfl (by decide)⟩
    · rcases hC.rel _ _ (hat (by decide) (by decide) hpc) hS.x0 hS.dl with h' | ⟨k, h'⟩ <;>
        rw [h'] at hex <;> cases hex
      · exact ⟨hl, fun _ => lf _ 14 rfl rfl rfl (by decide)⟩
      · exact ⟨hl, fun _ => lf _ 14 rfl rfl rfl (by decide)⟩
    · rw [hC.bdone _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 16 rfl rfl rfl (by decide)
    · have hn : isa.exec s = none := by
        show AArch64.exec s = none
        unfold AArch64.exec
        rw [hpc, hS.endPc]
        simp
      rw [hn] at hex; cases hex

omit hv in
/-- A start state is in the invariant. -/
theorem sSwp_of_start (hC : SwpCode P) {l c : BitVec 64} {s : State} (h : StartG P l c s) : SSwp P l c s :=
  ⟨⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.dl, h.dc⟩, 1, by decide, h.pc.trans hC.a0⟩

/-! ## The statements with declarations -/

/-- **The start configurations with declarations `ds`**: `SwpStartG Start`
with the workers at `WithDeclsD ds (Start l c)`, where `ds` resolves the two
4-byte words to themselves. -/
structure SwpStartGD (ds : Decls) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (l c : BitVec 64)
    (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  agL : ds.AgreesAt l 4
  agC : ds.AgreesAt c 4
  hlc : Decls.overlaps l 4 c 4 = false
  hst : ∀ s ∈ states, WithDeclsD ds (Start l c) s
  hL0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0

/-- `SwpLiveUnderG` (promise-free) at `SwpStartGD ds`. -/
def SwpLiveUnderGD (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (ds : Decls) (fuel : Nat) :
    Prop :=
  ∀ l c states initMem, SwpStartGD ds Start l c states initMem →
    Spin.ProgressFrom Arch.armv8 fuel (Config.init states initMem) (FairPF fuel) (SwpWaitingG P) (SwpDoneG P)

/-- `SwpOneShotUnderG` (promise-free) at `SwpStartGD ds`. -/
def SwpOneShotUnderGD (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (ds : Decls) (fuel : Nat) :
    Prop :=
  ∀ l c states initMem, SwpStartGD ds Start l c states initMem →
    LiveFrom Arch.armv8 fuel (Config.init states initMem) (FairPF fuel) (SwpWaitingG P) (SwpDoneG P)

omit layout hv in
theorem swpStart_noDecls {ds : Decls} {Start : BitVec 64 → BitVec 64 → isa.State → Prop} {l c : BitVec 64}
    {states : List isa.State} {initMem : List (Loc × Val)} (hs : SwpStartGD ds Start l c states initMem) :
    SwpStartG Start l c (states.map State.noDecls) initMem :=
  ⟨hs.hlc, fun s h => by
    obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
    exact (hs.hst s' h').2, hs.hL0⟩

/-- **Generic transfer, deadlock-freedom**: for an SWP-spinlock program `P`
without `LDXP`/`STXP` whose start states are `StartG` states, a promise-free
`SwpLiveUnderG` statement at `decls = {}` holds at every `ds` agreeing at the
two words. -/
theorem swp_live_pf_runner_gen (hC : SwpCode P) (hnp : Kraken.Executable.noPairs (layout P) = true)
    {Start : BitVec 64 → BitVec 64 → isa.State → Prop} (hStart : ∀ l c s, Start l c s → StartG P l c s)
    {fuel : Nat} (h : SwpLiveUnderG P Start fuel (FairPF fuel)) (ds : Decls) : SwpLiveUnderGD P Start ds fuel := by
  intro l c states initMem hs
  refine progressFrom_transfer (execSimA hnp (stepOK_swp hC hs.agL hs.agC))
    (goodC_initA initMem fun s h' => ⟨(hs.hst s h').1, sSwp_of_start hC (hStart _ _ _ (hs.hst s h').2)⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact h l c _ initMem (swpStart_noDecls hs)

/-- **Generic transfer, one-shot per-thread liveness.** -/
theorem swp_live_oneShot_pf_runner_gen (hC : SwpCode P) (hnp : Kraken.Executable.noPairs (layout P) = true)
    {Start : BitVec 64 → BitVec 64 → isa.State → Prop} (hStart : ∀ l c s, Start l c s → StartG P l c s)
    {fuel : Nat} (h : SwpOneShotUnderG P Start fuel (FairPF fuel)) (ds : Decls) :
    SwpOneShotUnderGD P Start ds fuel := by
  intro l c states initMem hs
  refine liveFrom_transfer (execSimA hnp (stepOK_swp hC hs.agL hs.agC))
    (goodC_initA initMem fun s h' => ⟨(hs.hst s h').1, sSwp_of_start hC (hStart _ _ _ (hs.hst s h').2)⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact h l c _ initMem (swpStart_noDecls hs)

end Generic

/-! ## The two locks -/

section Locks

variable [layout : _root_.Layout]

/-- **Promise-free deadlock-freedom of the SWP spinlock (`SWPA`/`STLR`)
with the runner's declarations** (Stage 3, promise-free fragment): on a
valid layout of `swpWorker`, for every `ds` that resolves the lock and
counter words to themselves, on every promise-free stuttering trace from a
`SwpStartGD ds SwpPublic.StartState` configuration under weak fairness and
memory fairness, if a thread waits in its try/spin loop, then some thread
not yet past its release later is. `spin_swp_live_pf` transferred along
`State.noDecls`. -/
theorem spin_swp_live_pf_runner [Executable.ValidLayout (layout swpWorker)] (ds : Decls) (fuel : Nat) :
    SwpLiveUnderGD swpWorker SLR.SwpPublic.StartState ds fuel :=
  swp_live_pf_runner_gen swpCode SLR.EnvG.SwpEnvG.swpWorker_noPairs (fun _ _ _ => SpinSwpFam.startG_swp)
    (SpinSwpFam.spin_swp_live_pf fuel) ds

/-- One-shot per-thread liveness of the SWP workers with the runner's
declarations (promise-free fragment; not starvation-freedom of the lock). -/
theorem spin_swp_live_oneShot_pf_runner [Executable.ValidLayout (layout swpWorker)] (ds : Decls) (fuel : Nat) :
    SwpOneShotUnderGD swpWorker SLR.SwpPublic.StartState ds fuel :=
  swp_live_oneShot_pf_runner_gen swpCode SLR.EnvG.SwpEnvG.swpWorker_noPairs (fun _ _ _ => SpinSwpFam.startG_swp)
    (SpinSwpFam.spin_swp_live_oneShot_pf fuel) ds

/-- **Promise-free deadlock-freedom of the SWPL spinlock (`SWPA`/`SWPL`)
with the runner's declarations** (Stage 3, promise-free fragment), on a
valid layout of `swplWorker`, for every `ds` agreeing at the two words.
`spin_swpl_live_pf` transferred along `State.noDecls`. -/
theorem spin_swpl_live_pf_runner [Executable.ValidLayout (layout swplWorker)] (ds : Decls) (fuel : Nat) :
    SwpLiveUnderGD swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  swp_live_pf_runner_gen swplCode SLR.EnvG.SwplLock.swplWorker_noPairs (fun _ _ _ => SpinSwpFam.startG_swpl)
    (SpinSwpFam.spin_swpl_live_pf fuel) ds

/-- One-shot per-thread liveness of the SWPL workers with the runner's
declarations (promise-free fragment; not starvation-freedom of the lock). -/
theorem spin_swpl_live_oneShot_pf_runner [Executable.ValidLayout (layout swplWorker)] (ds : Decls) (fuel : Nat) :
    SwpOneShotUnderGD swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  swp_live_oneShot_pf_runner_gen swplCode SLR.EnvG.SwplLock.swplWorker_noPairs
    (fun _ _ _ => SpinSwpFam.startG_swpl) (SpinSwpFam.spin_swpl_live_oneShot_pf fuel) ds

end Locks

/-! ## The runner's configurations -/

section ConcreteSwp

open Kraken.Promising.SLR.SwpConcrete (swpLayout swpValid lockAddr counterAddr initMem2)
open Kraken.Promising.SLR.EnvG.A64SwpRunner (swpDeclsD swpWorkerD0 swp_disjD)
attribute [local instance] swpLayout

/-- `spin_swp_live_pf_runner` at the runner's layout `SwpConcrete.swpLayout`.
No hypothesis left. -/
theorem spin_swp_live_pf_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpLiveUnderGD swpLayout swpWorker SLR.SwpPublic.StartState ds fuel :=
  @spin_swp_live_pf_runner swpLayout swpValid ds fuel

/-- `spin_swp_live_oneShot_pf_runner` at the runner's layout. -/
theorem spin_swp_live_oneShot_pf_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpOneShotUnderGD swpLayout swpWorker SLR.SwpPublic.StartState ds fuel :=
  @spin_swp_live_oneShot_pf_runner swpLayout swpValid ds fuel

theorem swpStartGD_runner (N : Nat) :
    SwpStartGD swpDeclsD SLR.SwpPublic.StartState lockAddr counterAddr (List.replicate N swpWorkerD0) initMem2 :=
  ⟨rfl, rfl, swp_disjD,
    fun s hs => (List.eq_of_mem_replicate hs) ▸
      Kraken.Promising.SLR.EnvG.A64Whole.withDeclsD_of rfl SLR.SwpPublic.worker0_start,
    by simp only [Config.init]; decide⟩

/-- **The runner's own configuration, `N` workers** (`spinlock_swp2.kl`:
`N = 2`, `spinlock_swp3.kl`: `N = 3`): `N` copies of `swpWorkerD0`
(declarations `swpDeclsD` included), the runner's initial memory, at its
layout. No hypothesis left. -/
theorem spin_swp_live_pf_runnerN (fuel N : Nat) :
    Spin.ProgressFrom Arch.armv8 fuel (Config.init (List.replicate N swpWorkerD0) initMem2) (FairPF fuel)
      (@SwpWaitingG swpLayout swpWorker) (@SwpDoneG swpLayout swpWorker) :=
  spin_swp_live_pf_runner_concrete swpDeclsD fuel _ _ _ _ (swpStartGD_runner N)

/-- The one-shot per-thread form at the runner's configuration. -/
theorem spin_swp_live_oneShot_pf_runnerN (fuel N : Nat) :
    LiveFrom Arch.armv8 fuel (Config.init (List.replicate N swpWorkerD0) initMem2) (FairPF fuel)
      (@SwpWaitingG swpLayout swpWorker) (@SwpDoneG swpLayout swpWorker) :=
  spin_swp_live_oneShot_pf_runner_concrete swpDeclsD fuel _ _ _ _ (swpStartGD_runner N)

end ConcreteSwp

section ConcreteSwpl

open Kraken.Promising.SLR.EnvG.ConcreteSwpl (swplLayout swplValid lockAddr counterAddr swplInitMem
  swplWorker0_start swpl_disj swplDeclsD swplWorkerD0)
attribute [local instance] swplLayout

/-- `spin_swpl_live_pf_runner` at the runner's layout
`ConcreteSwpl.swplLayout`. No hypothesis left. -/
theorem spin_swpl_live_pf_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpLiveUnderGD swplLayout swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  @spin_swpl_live_pf_runner swplLayout swplValid ds fuel

/-- `spin_swpl_live_oneShot_pf_runner` at the runner's layout. -/
theorem spin_swpl_live_oneShot_pf_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpOneShotUnderGD swplLayout swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  @spin_swpl_live_oneShot_pf_runner swplLayout swplValid ds fuel

theorem swplStartGD_runner (N : Nat) :
    SwpStartGD swplDeclsD SLR.EnvG.SwplLock.StartState lockAddr counterAddr (List.replicate N swplWorkerD0)
      swplInitMem :=
  ⟨rfl, rfl, swpl_disj,
    fun s hs => (List.eq_of_mem_replicate hs) ▸
      Kraken.Promising.SLR.EnvG.A64Whole.withDeclsD_of rfl swplWorker0_start,
    by simp only [Config.init]; decide⟩

/-- **The runner's own configuration, `N` workers** (`spinlock_swpl2.kl`:
`N = 2`, `spinlock_swpl3.kl`: `N = 3`): `N` copies of `swplWorkerD0`
(declarations `swplDeclsD` included), the runner's initial memory, at its
layout. No hypothesis left. -/
theorem spin_swpl_live_pf_runnerN (fuel N : Nat) :
    Spin.ProgressFrom Arch.armv8 fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem) (FairPF fuel)
      (@SwpWaitingG swplLayout swplWorker) (@SwpDoneG swplLayout swplWorker) :=
  spin_swpl_live_pf_runner_concrete swplDeclsD fuel _ _ _ _ (swplStartGD_runner N)

/-- The one-shot per-thread form at the runner's configuration. -/
theorem spin_swpl_live_oneShot_pf_runnerN (fuel N : Nat) :
    LiveFrom Arch.armv8 fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem) (FairPF fuel)
      (@SwpWaitingG swplLayout swplWorker) (@SwpDoneG swplLayout swplWorker) :=
  spin_swpl_live_oneShot_pf_runner_concrete swplDeclsD fuel _ _ _ _ (swplStartGD_runner N)

end ConcreteSwpl

end Kraken.Promising.Live.RunnerA64Swp

#print axioms Kraken.Promising.Live.RunnerA64Swp.spin_swp_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerA64Swp.spin_swpl_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerA64Swp.spin_swp_live_pf_runnerN
#print axioms Kraken.Promising.Live.RunnerA64Swp.spin_swp_live_oneShot_pf_runnerN
#print axioms Kraken.Promising.Live.RunnerA64Swp.spin_swpl_live_pf_runnerN
#print axioms Kraken.Promising.Live.RunnerA64Swp.spin_swpl_live_oneShot_pf_runnerN
