/-
**No stuck configurations (N1), an AArch64 instance: the CAS spinlock's stuck
configurations have a dead promise.**

For the AArch64 CAS spinlock worker `casTtasWorker` (`spinlock_cas2`/`3`, the
`spin_cas_live_sem` family), `OkStepsPF` holds in every configuration
reachable on the semantic `Arch.armv8` machine from a start configuration
(from the semantic invariant `SpinSemInv.InvS`, kept by every step, and the
worker's `instrEnabledSem_of`). So N1 (`stuckHasDeadPromise`) applies with no
hypothesis left: every reachable stuck configuration has a thread with an
outstanding promise that it cannot fulfil alone within `fuel`. (Stuck
configurations are reachable for this one-shot client on AArch64: see
`LiveNoStuck.lean`; the liveness theorems are silent on those runs.)

- `cas_okStepsPF`, `cas_invS_reach`.
- `spin_cas_stuckHasDeadPromise`, `spin_cas_stuckHasDeadPromise_concrete`.
-/
import Kraken.Promising.LiveNoStuck
import Kraken.Promising.LiveSpinSemCas

namespace Kraken.Promising.Live.NoStuck

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
  Kraken.Promising.Live.Bridge

section Cas

open Kraken.Promising.Live.SpinSemSolo Kraken.Promising.Live.SpinSemInv
open Kraken.Promising.Live.SpinCasInv (stepOne_end)
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

/-- Every running promise-free CAS worker has a successful outcome, under the
semantic invariant. -/
theorem cas_okStepsPF {fuel : Nat} {l c : BitVec 64} {cfg : Config isa} (h : InvS fuel l c cfg) :
    OkStepsPF Arch.armv8 cfg := by
  intro tid t ht hh hp
  have hT := h.thr tid t ht
  have h17 : t.st.st.2 ≠ pcA 17 := fun e => by
    rw [halted_of_stepOne_none (stepOne_end hT.sinv.st e Arch.armv8 tid cfg.mem)] at hh; cases hh
  obtain ⟨c', t', outs, o, ht', hs, ho, -, -⟩ :=
    instrEnabledSem_of (fuel := fuel) ht hT.sinv h17 (h.bnd tid t ht) (.inl hp)
  rw [ht] at ht'; cases ht'
  exact ⟨outs, o, hs, ho⟩

/-- The semantic invariant along every semantic run from a start
configuration. -/
theorem cas_invS_reach {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) {cfg : Config isa}
    (hr : ReachableSem Arch.armv8 fuel (Config.init states initMem) cfg) : InvS fuel l c cfg := by
  refine reachableSem_inv (InvS fuel l c) (fun tid c0 c1 hc hst => ?_) hr (inv_init hs)
  obtain ⟨t, ht⟩ : ∃ t, c0.threads[tid]? = some t := by
    rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
  exact inv_step hc ht hst

/-- **N1 for the AArch64 CAS spinlock**: every stuck configuration reachable
on the semantic `Arch.armv8` machine from a start configuration has a thread
with an outstanding promise that it cannot fulfil alone within `fuel`. -/
theorem spin_cas_stuckHasDeadPromise (fuel : Nat) (l c : BitVec 64) (states : List isa.State)
    (initMem : List (Loc × Val)) (hs : Spin.CasStart l c states initMem) (cfg : Config isa)
    (hr : ReachableSem Arch.armv8 fuel (Config.init states initMem) cfg) (hst : StuckSem Arch.armv8 fuel cfg) :
    ∃ tid t, cfg.threads[tid]? = some t ∧ t.prom ≠ [] ∧ ¬ CertOkN Arch.armv8 tid t cfg.mem fuel :=
  stuckHasDeadPromise Arch.armv8 isa fuel cfg hst (cas_okStepsPF (cas_invS_reach hs hr))

end Cas

open Kraken.Promising.Live.SpinCasPF in
/-- `spin_cas_stuckHasDeadPromise` at the concrete layout
`SpinCasPF.casLayout`. -/
theorem spin_cas_stuckHasDeadPromise_concrete (fuel : Nat) (l c : BitVec 64) (states : List isa.State)
    (initMem : List (Loc × Val)) (hs : @Spin.CasStart casLayout l c states initMem) (cfg : Config isa)
    (hr : ReachableSem Arch.armv8 fuel (Config.init states initMem) cfg) (hst : StuckSem Arch.armv8 fuel cfg) :
    ∃ tid t, cfg.threads[tid]? = some t ∧ t.prom ≠ [] ∧ ¬ CertOkN Arch.armv8 tid t cfg.mem fuel :=
  @spin_cas_stuckHasDeadPromise casLayout casValid fuel l c states initMem hs cfg hr hst

end Kraken.Promising.Live.NoStuck
