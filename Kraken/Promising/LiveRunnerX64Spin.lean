/-
**Deadlock-freedom of the x64 spinlocks in the runner's declarations form
.**

`spin_cmpx_live_pf` (`lock cmpxchg`, `spinlock_cmpxchg2/3.kl`) and
`spin_xchg_live_pf` (`xchg`, `spinlock2/3.kl`) are stated for workers with no
declarations (`StartStateCV`, `StartStateV`: `decls = {}`). The `.kl`
runner's workers carry the typed header's declarations (`cmpxDeclsD`,
`spinDeclsD`: the two 4-byte words, strict). For each lock:

- `…ImageV_cellsDeclsAgree`: every cell of the image accesses only `(lock)`
  and `(counter)`, 4 bytes, so it agrees with any `ds` under which those
  resolve to themselves (`Decls.AgreesAt`; weaker than the safety side's
  `ds.Sized` here: nothing is assumed about other declarations);
- `CmpxStartD ds` / `XchgStartD ds`: the existing start structure with the
  runner's `StartStateCVD ds` / `StartStateVD ds` and the two `AgreesAt`
  facts;
- **`spin_cmpx_live_pf_runner`**, **`spin_xchg_live_pf_runner`**: promise-free
  deadlock-freedom (`ProgressFromN`, under `WeakFair ∧ MemFair ∧
  PromiseFree`) from every such configuration, by `progressFrom_transfer`
  (`LiveRunnerSim`) along `State.noDecls`;
- `…_runner_concrete` (the runner's layout and declarations) and
  `…_runnerN` (`N` copies of the runner's prepared worker `cmpxWorkerD0` /
  `spinWorkerD0`, declarations included, with its initial memory): no
  hypothesis left.

Promise-free fragment only, as for the theorems transferred.

**Short-name clash** (documented, not renamed): `spin_cmpx_live_pf_runnerN`
and `spin_xchg_live_pf_runnerN` here (declarations `ds` = the runner's) have
the same short names as the existing `Live.SpinX64CmpxPF.spin_cmpx_live_pf_runnerN`
and `Live.SpinX64XchgPF.spin_xchg_live_pf_runnerN` (`decls = {}`). With both
namespaces open, write them qualified (`RunnerX64Spin.…` / `SpinX64CmpxPF.…`,
`SpinX64XchgPF.…`).
-/
import Kraken.Promising.LiveRunnerX64
import Kraken.Promising.LiveSpinX64CmpxPF
import Kraken.Promising.LiveSpinX64XchgPF
import Kraken.Promising.SLR.EnvG.X64CmpxAbsRunner
import Kraken.Promising.SLR.EnvG.X64SpinAbsRunner

namespace Kraken.Promising.Live.RunnerX64Spin

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.RunnerX64 Kraken.Promising.Live.SpinX64Step

/-! ## `lock cmpxchg` -/

section Cmpx

open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV cmpxWorkerV symC StartStateCV StartStateCVD)
open Kraken.Promising.X64.EnvG.SpinAbs (spinDataV)

variable [layout : _root_.Layout]

/-- The address an absolute operand `(x)` computes in the image. -/
theorem addrC (x : Label) (regs : Reg64s) (rng : Std.Rco Int64) :
    @AddrExpr.interp (_root_.Executable.labels (layout cmpxImageV)) ⟨.W64⟩ ⟨none, none, .label x⟩ regs rng =
      symC x := by
  have := @AddrExpr.zeroExtend_interp_abs_label (_root_.Executable.labels (layout cmpxImageV)) x regs rng
  simpa using this

/-- Every cell of `cmpxImageV` accesses only `(lock)` and `(counter)`, 4
bytes. -/
theorem cmpxImageV_cellsDeclsAgree {ds : Decls} (hl : ds.AgreesAt (symC "lock") 4)
    (hc : ds.AgreesAt (symC "counter") 4) : CellsDeclsAgree ds (layout cmpxImageV) := by
  refine cellsDeclsAgree_layoutL ?_
  intro d hd' s rng next jmp hn hj
  simp only [cmpxImageV, cmpxWorkerV, spinDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd'
  repeat' (rcases hd' with rfl | hd')
  all_goals simp [Directive.interp, Instr.interp, Effects.DeclsAgree, Operation.interp, hn, hj,
    RelRegOrMem.interp, RegOrMem.interp, Operand.interp, MachineData.load, MachineData.store, MachineData.rmwK,
    RegOrMem.rmw, MachineData.set, addrC]
  all_goals (repeat' (first | (intro x) | split | simp [Effects.DeclsAgree, hn, hj, hl, hc]))

/-- **The start configurations with declarations `ds`**: `CmpxStart` with
the workers at `StartStateCVD ds`, where `ds` resolves the two 4-byte words
to themselves (`Decls.AgreesAt`; weaker than `ds.Sized` here). -/
structure CmpxStartD (ds : Decls) (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  agL : ds.AgreesAt (symC "lock") 4
  agC : ds.AgreesAt (symC "counter") 4
  hlc : Decls.overlaps (symC "lock") 4 (symC "counter") 4 = false
  hst : ∀ s ∈ states, StartStateCVD ds s
  hL0 : (Config.init states initMem).mem.initVal ⟨symC "lock", 4⟩ = 0

/-- **Promise-free `lock cmpxchg` spinlock deadlock-freedom with
declarations `ds`** (`SpinX64.CmpxSpinLivePF` at `CmpxStartD ds`). -/
def CmpxSpinLivePFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, CmpxStartD ds states initMem →
    ProgressFromN Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64.CmpxWaiting SpinX64.CmpxDone

/-- **Promise-free deadlock-freedom of the x64 `lock cmpxchg` spinlock with
the runner's declarations** (`spinlock_cmpxchg2/3.kl` verbatim): on a valid
layout of `cmpxImageV`, for every `ds` resolving `lock` and `counter` (4
bytes) to themselves. `spin_cmpx_live_pf` transferred along
`State.noDecls` (`progressFrom_transfer`). -/
theorem spin_cmpx_live_pf_runner [Executable.ValidLayout (layout cmpxImageV)] (ds : Decls) (fuel : Nat) :
    CmpxSpinLivePFD ds fuel := by
  intro states initMem hs
  refine progressFrom_transfer (execSimD (cmpxImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64CmpxPF.spin_cmpx_live_pf fuel _ initMem
    ⟨hs.hlc, fun s h => by
      obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
      have h'' := hs.hst s' h'
      exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩, hs.hL0⟩

end Cmpx

section CmpxConcrete

open Kraken.Promising.X64.EnvG.CmpxAbs (symC)
open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete
attribute [local instance] cmpxLayoutV

/-- `spin_cmpx_live_pf_runner` at the runner's layout and declarations
`cmpxDeclsD`. No hypothesis left. -/
theorem spin_cmpx_live_pf_runner_concrete (fuel : Nat) : CmpxSpinLivePFD cmpxDeclsD fuel :=
  spin_cmpx_live_pf_runner cmpxDeclsD fuel

/-- **The runner's own configuration, `N` workers** (`spinlock_cmpxchg2.kl`
for `N = 2`, `spinlock_cmpxchg3.kl` for `N = 3`): `N` copies of the runner's
prepared worker `cmpxWorkerD0` (declarations `cmpxDeclsD` included), the
runner's initial memory, at its layout. No hypothesis left. -/
theorem spin_cmpx_live_pf_runnerN (fuel N : Nat) :
    ProgressFromN Arch.tso fuel (Config.init (List.replicate N cmpxWorkerD0) cmpxInitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64.CmpxWaiting SpinX64.CmpxDone :=
  spin_cmpx_live_pf_runner_concrete fuel _ _
    ⟨by show cmpxDeclsD.resolve _ 4 = _; rw [symC_lock]; rfl,
     by show cmpxDeclsD.resolve _ 4 = _; rw [symC_counter]; rfl,
     by rw [symC_lock, symC_counter]; decide,
     fun s hs => (List.eq_of_mem_replicate hs) ▸ cmpxWorkerD0_start,
     by rw [symC_lock]; simp only [Config.init_mem]; decide⟩

end CmpxConcrete

/-! ## `xchg` -/

section Xchg

open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV spinWorkerV spinDataV symV StartStateV StartStateVD)

variable [layout : _root_.Layout]

/-- The address an absolute operand `(x)` computes in the image. -/
theorem addrV (x : Label) (regs : Reg64s) (rng : Std.Rco Int64) :
    @AddrExpr.interp (_root_.Executable.labels (layout spinImageV)) ⟨.W64⟩ ⟨none, none, .label x⟩ regs rng =
      symV x := by
  have := @AddrExpr.zeroExtend_interp_abs_label (_root_.Executable.labels (layout spinImageV)) x regs rng
  simpa using this

/-- Every cell of `spinImageV` accesses only `(lock)` and `(counter)`, 4
bytes. -/
theorem spinImageV_cellsDeclsAgree {ds : Decls} (hl : ds.AgreesAt (symV "lock") 4)
    (hc : ds.AgreesAt (symV "counter") 4) : CellsDeclsAgree ds (layout spinImageV) := by
  refine cellsDeclsAgree_layoutL ?_
  intro d hd' s rng next jmp hn hj
  simp only [spinImageV, spinWorkerV, spinDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd'
  repeat' (rcases hd' with rfl | hd')
  all_goals simp [Directive.interp, Instr.interp, Effects.DeclsAgree, Operation.interp, hn, hj,
    RelRegOrMem.interp, RegOrMem.interp, Operand.interp, MachineData.load, MachineData.store, MachineData.rmwK,
    RegOrMem.rmw, MachineData.set, addrV]
  all_goals (repeat' (first | (intro x) | split | simp [Effects.DeclsAgree, hn, hj, hl, hc]))

/-- **The start configurations with declarations `ds`**: `XchgStart` with
the workers at `StartStateVD ds`, where `ds` resolves the two 4-byte words
to themselves (`Decls.AgreesAt`; weaker than `ds.Sized` here). -/
structure XchgStartD (ds : Decls) (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  agL : ds.AgreesAt (symV "lock") 4
  agC : ds.AgreesAt (symV "counter") 4
  hlc : Decls.overlaps (symV "lock") 4 (symV "counter") 4 = false
  hst : ∀ s ∈ states, StartStateVD ds s
  hL0 : (Config.init states initMem).mem.initVal ⟨symV "lock", 4⟩ = 0

/-- **Promise-free `xchg` spinlock deadlock-freedom with declarations
`ds`** (`SpinX64Xchg.XchgSpinLivePF` at `XchgStartD ds`). -/
def XchgSpinLivePFD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, XchgStartD ds states initMem →
    ProgressFromN Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone

/-- **Promise-free deadlock-freedom of the x64 `xchg` spinlock with the
runner's declarations** (`spinlock2/3.kl` verbatim): on a valid layout of
`spinImageV`, for every `ds` resolving `lock` and `counter` (4 bytes) to
themselves. `spin_xchg_live_pf` transferred along `State.noDecls`
(`progressFrom_transfer`). -/
theorem spin_xchg_live_pf_runner [Executable.ValidLayout (layout spinImageV)] (ds : Decls) (fuel : Nat) :
    XchgSpinLivePFD ds fuel := by
  intro states initMem hs
  refine progressFrom_transfer (execSimD (spinImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64XchgPF.spin_xchg_live_pf fuel _ initMem
    ⟨hs.hlc, fun s h => by
      obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
      have h'' := hs.hst s' h'
      exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩, hs.hL0⟩

end Xchg

section XchgConcrete

open Kraken.Promising.X64.EnvG.SpinAbs (symV)
open Kraken.Promising.X64.EnvG.SpinAbs.Concrete
attribute [local instance] spinLayoutV

/-- `spin_xchg_live_pf_runner` at the runner's layout and declarations
`spinDeclsD`. No hypothesis left. -/
theorem spin_xchg_live_pf_runner_concrete (fuel : Nat) : XchgSpinLivePFD spinDeclsD fuel :=
  spin_xchg_live_pf_runner spinDeclsD fuel

/-- **The runner's own configuration, `N` workers** (`spinlock2.kl` for
`N = 2`, `spinlock3.kl` for `N = 3`): `N` copies of the runner's prepared
worker `spinWorkerD0` (declarations `spinDeclsD` included), the runner's
initial memory, at its layout. No hypothesis left. -/
theorem spin_xchg_live_pf_runnerN (fuel N : Nat) :
    ProgressFromN Arch.tso fuel (Config.init (List.replicate N spinWorkerD0) spinInitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone :=
  spin_xchg_live_pf_runner_concrete fuel _ _
    ⟨by show spinDeclsD.resolve _ 4 = _; rw [symV_lock]; rfl,
     by show spinDeclsD.resolve _ 4 = _; rw [symV_counter]; rfl,
     by rw [symV_lock, symV_counter]; decide,
     fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorkerD0_start,
     by rw [symV_lock]; simp only [Config.init_mem]; decide⟩

end XchgConcrete

end Kraken.Promising.Live.RunnerX64Spin

#print axioms Kraken.Promising.Live.RunnerX64Spin.spin_cmpx_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerX64Spin.spin_cmpx_live_pf_runnerN
#print axioms Kraken.Promising.Live.RunnerX64Spin.spin_xchg_live_pf_runner
#print axioms Kraken.Promising.Live.RunnerX64Spin.spin_xchg_live_pf_runnerN
