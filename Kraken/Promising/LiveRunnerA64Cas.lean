/-
**Liveness of the AArch64 CAS spinlock (`spinlock_cas{2,3}.kl`) in the
runner's declarations form.**

`Live.SpinCasPF.spin_cas_live_pf` (deadlock-freedom) and
`spin_cas_live_oneShot_pf` (per-thread, one-shot workers) are stated for
threads with no declarations (`Spin.CasStart`: `CasSmoke.StartState l c`,
`decls = {}`). The `.kl` runner's threads carry the typed header's
declarations (`ConcreteCas.casDeclsD`: the two 4-byte words, strict). As for
the ticket lock (`LiveRunnerA64Ticket`):

- `SCas l c`: `SpinCasInv.Static` and the pc at one of the worker's
  positions (`SpinCasTrees.spPcs`); `stepOK_cas` from the existing
  `SpinCasTrees.exec_*` (accesses only at `⟨l, 4⟩`, `⟨c, 4⟩`);
- `CasStartD ds`: `Spin.CasStart` with `WithDeclsD ds (StartState l c)` (the
  start states of `cas_counter_envG_runner`) and `ds.AgreesAt l 4`,
  `ds.AgreesAt c 4` (the no-fault side's `casDeclsD_agreesA` facts);
- **`spin_cas_live_pf_runner`** (`progressFrom_transfer`) and
  `spin_cas_live_oneShot_pf_runner` (`liveFrom_transfer`), with
  `_runner_concrete` (the runner's layout) and `_runnerN` (`N` copies of
  `casWorkerD0`, the runner's initial memory; no hypothesis left).

Promise-free fragment only, as for the theorems transferred.
-/
import Kraken.Promising.LiveRunnerA64
import Kraken.Promising.LiveSpinCasPF
import Kraken.Promising.SLR.EnvG.A64CasRunner

namespace Kraken.Promising.Live.RunnerA64Cas

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.RunnerA64 Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.SpinCasInv
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker StartState casTtasWorker_noPairs)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD)

section Generic

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

/-- **The bridge's invariant for the CAS worker** (states without
declarations): `Static` and the pc at one of the worker's positions. -/
def SCas (l c : BitVec 64) (s : State) : Prop := Static l c s ∧ ∃ i ∈ spPcs, s.st.2 = pcA i

/-- **Every tree of an `SCas` state agrees with `ds` and stays in `SCas`.** -/
theorem stepOK_cas {ds : Decls} {l c : BitVec 64} (hl : ds.AgreesAt l 4) (hc : ds.AgreesAt c 4) :
    StepOK ds (layout casTtasWorker) (SCas l c) where
  exe _ h := h.1.exe
  decls _ h := h.1.decls
  ok s h t hex := by
    obtain ⟨hS, i, hi, hpc⟩ := h
    have hat : ∀ {j}, j ∈ spPcs → j ≠ 17 → s.st.2 = pcA j → At s j := fun hj h17 hp => hS.at hj h17 hp
    have lf : ∀ md j, md.regs.X0 = s.st.1.regs.X0 → md.regs.X1 = s.st.1.regs.X1 → md.dmem = s.st.1.dmem →
        j ∈ spPcs → SCas l c (SpinCasTrees.goto s md (pcA j)) :=
      fun md j h0 h1 hd hj => ⟨hS.goto md _ h0 h1 hd, j, hj, rfl⟩
    simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [exec_mov3 _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 3 rfl rfl rfl (by decide)
    · rw [exec_mov2 _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 4 rfl rfl rfl (by decide)
    · rw [exec_casa _ (hat (by decide) (by decide) hpc) hS.x0 hS.dl] at hex; cases hex
      exact ⟨hl, fun _ => lf _ 5 rfl rfl rfl (by decide)⟩
    · rw [exec_cbz _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      by_cases hz : w32 s.st.1.regs.X2 = 0#32
      · simp only [hz, ite_true]; exact lf _ 11 rfl rfl rfl (by decide)
      · simp only [hz, ite_false]; exact lf _ 7 rfl rfl rfl (by decide)
    · rw [exec_ldr_l _ (hat (by decide) (by decide) hpc) hS.x0 hS.dl] at hex; cases hex
      exact ⟨hl, fun _ => lf _ 8 rfl rfl rfl (by decide)⟩
    · rw [exec_cbnz _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      by_cases hz : w32 s.st.1.regs.X2 = 0#32
      · simp only [hz, ite_true]; exact lf _ 9 rfl rfl rfl (by decide)
      · simp only [hz, ite_false]; exact lf _ 7 rfl rfl rfl (by decide)
    · rw [exec_b_try _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 3 rfl rfl rfl (by decide)
    · rw [exec_ldr_c _ (hat (by decide) (by decide) hpc) hS.x1 hS.dc] at hex; cases hex
      exact ⟨hc, fun _ => lf _ 12 rfl rfl rfl (by decide)⟩
    · rw [exec_add5 _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 13 rfl rfl rfl (by decide)
    · rw [exec_str_c _ (hat (by decide) (by decide) hpc) hS.x1 hS.dc] at hex; cases hex
      exact ⟨hc, fun _ => lf _ 14 rfl rfl rfl (by decide)⟩
    · rw [exec_stlr _ (hat (by decide) (by decide) hpc) hS.x0 hS.dl] at hex; cases hex
      exact ⟨hl, fun _ => lf _ 15 rfl rfl rfl (by decide)⟩
    · rw [exec_b_done _ (hat (by decide) (by decide) hpc)] at hex; cases hex
      exact lf _ 17 rfl rfl rfl (by decide)
    · have hn : isa.exec s = none := by
        show AArch64.exec s = none
        unfold AArch64.exec
        rw [hpc, hS.endPc]
        simp
      rw [hn] at hex; cases hex

/-- A start state is in the invariant. -/
theorem sCas_of_start {l c : BitVec 64} {s : State} (h : StartState l c s) : SCas l c s :=
  ⟨⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.dl, h.dc⟩, 1, by decide, h.pc.trans addrOf_0⟩

/-! ## The statements with declarations -/

/-- **The start configurations with declarations `ds`**: `Spin.CasStart`
with the workers at `WithDeclsD ds (StartState l c)`, where `ds` resolves
the two 4-byte words to themselves. -/
structure CasStartD (ds : Decls) (l c : BitVec 64) (states : List isa.State) (initMem : List (Loc × Val)) :
    Prop where
  agL : ds.AgreesAt l 4
  agC : ds.AgreesAt c 4
  hlc : Decls.overlaps l 4 c 4 = false
  hst : ∀ s ∈ states, WithDeclsD ds (StartState l c) s
  hL0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0

/-- **Promise-free CAS-spinlock deadlock-freedom with declarations `ds`**
(`Spin.CasSpinLivePF` at `CasStartD ds`). -/
def CasSpinLivePFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ l c states initMem, CasStartD ds l c states initMem →
    Spin.ProgressFrom Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      Spin.CasWaiting Spin.CasDone

/-- **Per-thread liveness of the one-shot CAS workers with declarations
`ds`** (`Spin.CasSpinLiveOneShotPF` at `CasStartD ds`). -/
def CasSpinLiveOneShotPFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ l c states initMem, CasStartD ds l c states initMem →
    LiveFrom Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      Spin.CasWaiting Spin.CasDone

omit hv in
theorem casStart_noDecls {ds : Decls} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : CasStartD ds l c states initMem) : Spin.CasStart l c (states.map State.noDecls) initMem :=
  ⟨hs.hlc, fun s h => by
    obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
    exact (hs.hst s' h').2, hs.hL0⟩

/-- **Promise-free deadlock-freedom of the AArch64 CAS spinlock with the
runner's declarations** (Stage 3, promise-free fragment): on a valid layout
of `casTtasWorker`, for every `ds` that resolves the lock and counter words
to themselves, on every promise-free stuttering `Arch.armv8` trace from a
`CasStartD ds` configuration under weak fairness and memory fairness, if a
thread waits in its try/spin loop, then some thread not yet past its release
later is. `spin_cas_live_pf` transferred along `State.noDecls`
(`progressFrom_transfer`, `execSimA`). -/
theorem spin_cas_live_pf_runner (ds : Decls) (fuel : Nat) : CasSpinLivePFD ds fuel := by
  intro l c states initMem hs
  refine progressFrom_transfer (execSimA casTtasWorker_noPairs (stepOK_cas hs.agL hs.agC))
    (goodC_initA initMem fun s h => ⟨(hs.hst s h).1, sCas_of_start (hs.hst s h).2⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact SpinCasPF.spin_cas_live_pf fuel l c _ initMem (casStart_noDecls hs)

/-- **Per-thread liveness of the one-shot CAS workers with the runner's
declarations** (promise-free fragment; one-shot workers, not
starvation-freedom of the lock): `spin_cas_live_oneShot_pf` transferred
along `State.noDecls` (`liveFrom_transfer`). -/
theorem spin_cas_live_oneShot_pf_runner (ds : Decls) (fuel : Nat) : CasSpinLiveOneShotPFD ds fuel := by
  intro l c states initMem hs
  refine liveFrom_transfer (execSimA casTtasWorker_noPairs (stepOK_cas hs.agL hs.agC))
    (goodC_initA initMem fun s h => ⟨(hs.hst s h).1, sCas_of_start (hs.hst s h).2⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact SpinCasPF.spin_cas_live_oneShot_pf fuel l c _ initMem (casStart_noDecls hs)

end Generic

/-! ## The runner's configuration -/

section Concrete

open Kraken.Promising.SLR.EnvG.ConcreteCas (casLayout casValid lockAddr counterAddr casInitMem casWorker0_start
  cas_disj casDeclsD casWorkerD0)
attribute [local instance] casLayout

/-- `spin_cas_live_pf_runner` at the runner's layout `ConcreteCas.casLayout`.
No hypothesis left. -/
theorem spin_cas_live_pf_runner_concrete (ds : Decls) (fuel : Nat) : @CasSpinLivePFD casLayout ds fuel :=
  @spin_cas_live_pf_runner casLayout casValid ds fuel

/-- `spin_cas_live_oneShot_pf_runner` at the runner's layout. -/
theorem spin_cas_live_oneShot_pf_runner_concrete (ds : Decls) (fuel : Nat) :
    @CasSpinLiveOneShotPFD casLayout ds fuel :=
  @spin_cas_live_oneShot_pf_runner casLayout casValid ds fuel

theorem casStartD_runner (N : Nat) :
    CasStartD casDeclsD lockAddr counterAddr (List.replicate N casWorkerD0) casInitMem :=
  ⟨rfl, rfl, cas_disj,
    fun s hs => (List.eq_of_mem_replicate hs) ▸ Kraken.Promising.SLR.EnvG.A64Whole.withDeclsD_of rfl casWorker0_start,
    by simp only [Config.init]; decide⟩

/-- **The runner's own configuration, `N` workers** (`spinlock_cas2.kl`:
`N = 2`, `spinlock_cas3.kl`: `N = 3`): `N` copies of the runner's prepared
worker `casWorkerD0` (declarations `casDeclsD` included), the runner's
initial memory, at its layout, under `WeakFair ∧ MemFair ∧ PromiseFree`.
No hypothesis left. -/
theorem spin_cas_live_pf_runnerN (fuel N : Nat) :
    Spin.ProgressFrom Arch.armv8 fuel (Config.init (List.replicate N casWorkerD0) casInitMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      (@Spin.CasWaiting casLayout) (@Spin.CasDone casLayout) :=
  spin_cas_live_pf_runner_concrete casDeclsD fuel _ _ _ _ (casStartD_runner N)

/-- The one-shot per-thread form at the runner's configuration. No
hypothesis left. -/
theorem spin_cas_live_oneShot_pf_runnerN (fuel N : Nat) :
    LiveFrom Arch.armv8 fuel (Config.init (List.replicate N casWorkerD0) casInitMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      (@Spin.CasWaiting casLayout) (@Spin.CasDone casLayout) :=
  spin_cas_live_oneShot_pf_runner_concrete casDeclsD fuel _ _ _ _ (casStartD_runner N)

end Concrete

end Kraken.Promising.Live.RunnerA64Cas

#print axioms Kraken.Promising.Live.RunnerA64Cas.spin_cas_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerA64Cas.spin_cas_live_pf_runnerN
#print axioms Kraken.Promising.Live.RunnerA64Cas.spin_cas_live_oneShot_pf_runnerN
