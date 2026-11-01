/-
**hello.w's `wc_main` obligations past the box's store: conjunction and the clone's pc** (AArch64): the generic part
of `Spike/Lib/A64WakeWcMidW.lean` at hello's `WcMidWH` (`A64HelloWcMid`).

- `WcResWH.and`, `WcSp3WH.and`, `WcSp4WH.and`, `WcSp6W.and`, `WcMidWH.and`: two facts at the segments' states
  combine at the first's outside move (wake's `nodeW_and`, `blkW_and`, `reserveW_and`, `tcbWG_and`);
- `wcNSH_cloneAt`, `wcNSH_clonePc`: a state at the clone's `svc` is at `cloneAtH pfxM exe`, `pcOf s = clonePcH L`.

Deferred (B8, the instance): wake's `wcMidW_wcG` (the obligations inside `SFactsSt2` at `ownG`, `tcbWG_c0`,
`stackM_nil`) fixes wake's W instance; hello's twin waits for hello's W.
-/
import Spike.Lib.A64HelloWcMid
import Spike.Lib.A64HelloWcInv
import Spike.Lib.A64WakeWcMidW

namespace Spike.Lib.A64.Flow.HelloWc

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.HelloPh.WcSp6 (wcNSH WcSp6W)
open Spike.Lib.A64.Flow.WakeWc (nodeW_and blkW_and reserveW_and tcbWG_and)
open Spike.Lib.HelloPreA (pfxM cloneAtH clonePcH)

/-! ## Conjunction -/

section And

variable {W₁ W₂ : Frag isaLSE2} {K K₂ : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **From the fence to `.sp3`**: two facts combine. -/
theorem WcResWH.and {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcResWH W₁ K exe endPc R F ms J1 S Q) (h₂ : WcResWH W₂ K₂ exe endPc R F ms J1 S Q) :
    WcResWH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F ms J1 S Q :=
  ⟨nodeW_and h₁.f h₂.f, blkW_and h₁.bl h₂.bl, fun g hg i => reserveW_and (h₁.res g hg i) (h₂.res g hg i)⟩

/-- **From `.sp3` to `.sp4`**: two facts combine. -/
theorem WcSp3WH.and {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp3WH W₁ K exe endPc R F c0 sl me cA fr) (h₂ : WcSp3WH W₂ K₂ exe endPc R F c0 sl me cA fr) :
    WcSp3WH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 sl me cA fr :=
  ⟨blkW_and h₁.blk h₂.blk, fun g hg i => tcbWG_and (h₁.tcb g hg i) (h₂.tcb g hg i)⟩

/-- **From `.sp4` to the call of `scc_rt_thread_init`**: two facts combine. -/
theorem WcSp4WH.and {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp4WH W₁ K exe endPc R F c0 t sl me cA fr) (h₂ : WcSp4WH W₂ K₂ exe endPc R F c0 t sl me cA fr) :
    WcSp4WH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 t sl me cA fr :=
  ⟨blkW_and h₁.n4 h₂.n4, nodeW_and h₁.n4s h₂.n4s, blkW_and h₁.n5 h₂.n5⟩

/-- **From `.sp6` to the `svc`**: two facts combine. -/
theorem WcSp6W.and {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp6W W₁ K exe endPc R F c0 t k sl me cA fr) (h₂ : WcSp6W W₂ K₂ exe endPc R F c0 t k sl me cA fr) :
    WcSp6W (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 t k sl me cA fr :=
  ⟨blkW_and h₁.n6 h₂.n6, nodeW_and h₁.n6f h₂.n6f, blkW_and h₁.n6a h₂.n6a⟩

/-- **From the box's store to the `svc`**: two facts combine at the first's outside move. -/
theorem WcMidWH.and {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcMidWH W₁ K exe endPc R F F₂ ms J1 S Q) (h₂ : WcMidWH W₂ K₂ exe endPc R F F₂ ms J1 S Q) :
    WcMidWH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F F₂ ms J1 S Q :=
  ⟨WcResWH.and h₁.res h₂.res,
    fun c0 sl me cA fr hM => WcSp3WH.and (h₁.sp3 c0 sl me cA fr hM) (h₂.sp3 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp4WH.and (h₁.sp4 c0 sl me cA fr hM) (h₂.sp4 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp6W.and (h₁.sp6 c0 sl me cA fr hM) (h₂.sp6 c0 sl me cA fr hM)⟩

end And

/-! ## The clone's pc -/

/-- **A state at the clone's `svc` is at `cloneAtH pfxM exe`.** -/
theorem wcNSH_cloneAt {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr) s c) :
    s.st.2 = cloneAtH pfxM exe :=
  h.2.2.2.1

/-- **A state at the clone's `svc` has `pcOf s = clonePcH L`**, in `L`'s executable. -/
theorem wcNSH_clonePc {L : Spike.Lib.A64.Rt.RuntimeLayout} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At L.exe endPc R F (wcNSH (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c) :
    Scc.Sem.A64.pcOf s = clonePcH L := by
  unfold Scc.Sem.A64.pcOf clonePcH
  rw [wcNSH_cloneAt h]

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcMidWH.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcMidWH.and

/-- info: 'Spike.Lib.A64.Flow.HelloWc.wcNSH_clonePc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.wcNSH_clonePc
