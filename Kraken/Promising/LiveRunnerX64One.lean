/-
**Per-thread liveness of the one-shot x64 spinlock workers in the runner's
declarations form.**

`spin_cmpx_live_oneShot_pf` and `spin_xchg_live_oneShot_pf` (every waiting
thread is eventually past its release; a property of these one-shot
programs, not starvation-freedom of the lock) are stated for workers with no
declarations (`StartStateCV`, `StartStateV`: `decls = {}`). Here they are
lifted to the runner's declarations, with the same start structures and
hypotheses as the x64 spinlock runner theorems
(`RunnerX64Spin.CmpxStartD ds`, `RunnerX64Spin.XchgStartD ds`):

- **`spin_cmpx_live_oneShot_pf_runner`**, **`spin_xchg_live_oneShot_pf_runner`**:
  `LiveFrom` under `WeakFair ∧ MemFair ∧ PromiseFree`, by `liveFrom_transfer`
  (`LiveRunnerSim`) along `State.noDecls`, with the same simulation
  (`execSimD` of `…ImageV_cellsDeclsAgree`) as the deadlock-freedom forms;
  the waiting/done predicates depend on the pc only (`exists_mapC`);
- `…_runner_concrete` (the runner's layout and declarations) and
  `…_runnerN` (`N` copies of the runner's prepared worker `cmpxWorkerD0` /
  `spinWorkerD0`, declarations included, with its initial memory): no
  hypothesis left.

Promise-free fragment only, as for the theorems transferred. The A64 twins
are `spin_{cas,swp,swpl}_live_oneShot_pf_runner{,_concrete,N}`.
-/
import Kraken.Promising.LiveRunnerX64Spin

namespace Kraken.Promising.Live.RunnerX64One

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.RunnerX64 Kraken.Promising.Live.RunnerX64Spin

/-! ## `lock cmpxchg` -/

section Cmpx

variable [layout : _root_.Layout]

open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV)

/-- **Per-thread liveness of the one-shot `lock cmpxchg` workers with
declarations `ds`** (`SpinX64.CmpxSpinLiveOneShotPF` at `CmpxStartD ds`). -/
def CmpxSpinLiveOneShotPFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, CmpxStartD ds states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64.CmpxWaiting SpinX64.CmpxDone

/-- **Per-thread liveness of the one-shot x64 `lock cmpxchg` workers with
the runner's declarations** (promise-free fragment; one-shot workers, not
starvation-freedom of the lock): on a valid layout of `cmpxImageV`, for every
`ds` resolving `lock` and `counter` (4 bytes) to themselves.
`spin_cmpx_live_oneShot_pf` transferred along `State.noDecls`
(`liveFrom_transfer`). -/
theorem spin_cmpx_live_oneShot_pf_runner [Executable.ValidLayout (layout cmpxImageV)] (ds : Decls)
    (fuel : Nat) : CmpxSpinLiveOneShotPFD ds fuel := by
  intro states initMem hs
  refine liveFrom_transfer (execSimD (cmpxImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64CmpxPF.spin_cmpx_live_oneShot_pf fuel _ initMem
    ⟨hs.hlc, fun s h => by
      obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
      have h'' := hs.hst s' h'
      exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩, hs.hL0⟩

end Cmpx

section CmpxConcrete

open Kraken.Promising.X64.EnvG.CmpxAbs (symC)
open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete
attribute [local instance] cmpxLayoutV

/-- `spin_cmpx_live_oneShot_pf_runner` at the runner's layout and
declarations `cmpxDeclsD`. No hypothesis left. -/
theorem spin_cmpx_live_oneShot_pf_runner_concrete (fuel : Nat) : CmpxSpinLiveOneShotPFD cmpxDeclsD fuel :=
  spin_cmpx_live_oneShot_pf_runner cmpxDeclsD fuel

/-- The one-shot per-thread form at the runner's own configuration
(`spinlock_cmpxchg2/3.kl`: `N = 2, 3`): `N` copies of `cmpxWorkerD0`
(declarations `cmpxDeclsD` included), the runner's initial memory, at its
layout. No hypothesis left. -/
theorem spin_cmpx_live_oneShot_pf_runnerN (fuel N : Nat) :
    LiveFrom Arch.tso fuel (Config.init (List.replicate N cmpxWorkerD0) cmpxInitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64.CmpxWaiting SpinX64.CmpxDone :=
  spin_cmpx_live_oneShot_pf_runner_concrete fuel _ _
    ⟨by show cmpxDeclsD.resolve _ 4 = _; rw [symC_lock]; rfl,
     by show cmpxDeclsD.resolve _ 4 = _; rw [symC_counter]; rfl,
     by rw [symC_lock, symC_counter]; decide,
     fun s hs => (List.eq_of_mem_replicate hs) ▸ cmpxWorkerD0_start,
     by rw [symC_lock]; simp only [Config.init_mem]; decide⟩

end CmpxConcrete

/-! ## `xchg` -/

section Xchg

variable [layout : _root_.Layout]

open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV)

/-- **Per-thread liveness of the one-shot `xchg` workers with declarations
`ds`** (`SpinX64Xchg.XchgSpinLiveOneShotPF` at `XchgStartD ds`). -/
def XchgSpinLiveOneShotPFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, XchgStartD ds states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone

/-- **Per-thread liveness of the one-shot x64 `xchg` workers with the
runner's declarations** (promise-free fragment; one-shot workers, not
starvation-freedom of the lock): on a valid layout of `spinImageV`, for every
`ds` resolving `lock` and `counter` (4 bytes) to themselves.
`spin_xchg_live_oneShot_pf` transferred along `State.noDecls`
(`liveFrom_transfer`). -/
theorem spin_xchg_live_oneShot_pf_runner [Executable.ValidLayout (layout spinImageV)] (ds : Decls)
    (fuel : Nat) : XchgSpinLiveOneShotPFD ds fuel := by
  intro states initMem hs
  refine liveFrom_transfer (execSimD (spinImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64XchgPF.spin_xchg_live_oneShot_pf fuel _ initMem
    ⟨hs.hlc, fun s h => by
      obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
      have h'' := hs.hst s' h'
      exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩, hs.hL0⟩

end Xchg

section XchgConcrete

open Kraken.Promising.X64.EnvG.SpinAbs (symV)
open Kraken.Promising.X64.EnvG.SpinAbs.Concrete
attribute [local instance] spinLayoutV

/-- `spin_xchg_live_oneShot_pf_runner` at the runner's layout and
declarations `spinDeclsD`. No hypothesis left. -/
theorem spin_xchg_live_oneShot_pf_runner_concrete (fuel : Nat) : XchgSpinLiveOneShotPFD spinDeclsD fuel :=
  spin_xchg_live_oneShot_pf_runner spinDeclsD fuel

/-- The one-shot per-thread form at the runner's own configuration
(`spinlock2/3.kl`: `N = 2, 3`): `N` copies of `spinWorkerD0` (declarations
`spinDeclsD` included), the runner's initial memory, at its layout. No
hypothesis left. -/
theorem spin_xchg_live_oneShot_pf_runnerN (fuel N : Nat) :
    LiveFrom Arch.tso fuel (Config.init (List.replicate N spinWorkerD0) spinInitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone :=
  spin_xchg_live_oneShot_pf_runner_concrete fuel _ _
    ⟨by show spinDeclsD.resolve _ 4 = _; rw [symV_lock]; rfl,
     by show spinDeclsD.resolve _ 4 = _; rw [symV_counter]; rfl,
     by rw [symV_lock, symV_counter]; decide,
     fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorkerD0_start,
     by rw [symV_lock]; simp only [Config.init_mem]; decide⟩

end XchgConcrete

end Kraken.Promising.Live.RunnerX64One

#print axioms Kraken.Promising.Live.RunnerX64One.spin_cmpx_live_oneShot_pf_runner
#print axioms Kraken.Promising.Live.RunnerX64One.spin_cmpx_live_oneShot_pf_runnerN
#print axioms Kraken.Promising.Live.RunnerX64One.spin_xchg_live_oneShot_pf_runner
#print axioms Kraken.Promising.Live.RunnerX64One.spin_xchg_live_oneShot_pf_runnerN
