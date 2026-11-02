/-
**hello.w's `wc_main` obligations past the box's store: conjunction and the clone's pc** (x86-64; the twin of
`Spike/Lib/A64HelloWcMidW.lean`): the generic part of `Spike/Lib/X64WakeWcMidW.lean` at hello's `WcMidWH`
(`X64HelloWcMid`).

- `WcResWH.and`, `WcSp3WH.and`, `WcSp4WH.and`, `WcSp6W.and`, `WcSp6PW.and`, `WcMidWH.and`: two facts at the
  pieces' states combine at the first's outside move (wake's `nodeW_and`, `blkW_and`, `reserveW_and`, `tcbWG_and`);
- `wcNSH_cloneAt`, `wcNSH_clonePc`: a state at the clone's `syscall` is at `cloneAtH exe`, `pcOf s = clonePcH L`.

## Differences from the AArch64 version

- x86-64's `WcResWH` has no fence node (`bl`, `res`; AArch64 also `f`), and `WcMidWH` no `S` parameter
  (`X64HelloWcMid`).
- x86-64's `WcSp6W` has six nodes (`n6`, `n6f`, `n6a`, `nd`, `n10`, `nr`: the clone's argument load, two `xorl`
  rows and the call number's block), so its conjunction has six components (AArch64: three); `WcSp6PW.and` is
  the same at `X64HelloWcPub`'s published nodes, which `WcMidWH`'s `sp6` uses.
- The clone's pc has no prefix argument (`cloneAtH exe`, AArch64 `cloneAtH pfxM exe`), as wake's x86-64
  `wcNS_cloneAt`.
-/
import Spike.Lib.X64HelloWcMid
import Spike.Lib.X64HelloWcInv
import Spike.Lib.X64WakeWcMidW

namespace Spike.Lib.X64.Flow.HelloWc

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH WcSp6W WcSp6PW)
open Spike.Lib.X64.Flow.WakeWc (nodeW_and blkW_and reserveW_and tcbWG_and)
open Spike.Lib.X64HelloPreA (cloneAtH clonePcH)

/-! ## Conjunction -/

section And

variable {W₁ W₂ : Frag isa} {K K₂ : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **From the call block to `.x23`**: two facts combine. -/
theorem WcResWH.and {ms : MemSide isa} {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcResWH W₁ K exe endPc R F ms J1 Q) (h₂ : WcResWH W₂ K₂ exe endPc R F ms J1 Q) :
    WcResWH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F ms J1 Q :=
  ⟨blkW_and h₁.bl h₂.bl, fun g hg i => reserveW_and (h₁.res g hg i) (h₂.res g hg i)⟩

/-- **From `.x23` to `.x24`**: two facts combine. -/
theorem WcSp3WH.and {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp3WH W₁ K exe endPc R F c0 sl me cA fr) (h₂ : WcSp3WH W₂ K₂ exe endPc R F c0 sl me cA fr) :
    WcSp3WH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 sl me cA fr :=
  ⟨blkW_and h₁.blk h₂.blk, fun g hg i => tcbWG_and (h₁.tcb g hg i) (h₂.tcb g hg i)⟩

/-- **From `.x24` to the call of `scc_rt_thread_init`**: two facts combine. -/
theorem WcSp4WH.and {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp4WH W₁ K exe endPc R F c0 t sl me cA fr) (h₂ : WcSp4WH W₂ K₂ exe endPc R F c0 t sl me cA fr) :
    WcSp4WH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 t sl me cA fr :=
  ⟨blkW_and h₁.n4 h₂.n4, nodeW_and h₁.n4s h₂.n4s, blkW_and h₁.n5 h₂.n5⟩

/-- **From `.x25` to the `syscall`**: two facts combine. -/
theorem WcSp6W.and {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp6W W₁ K exe endPc R F c0 t k sl me cA fr) (h₂ : WcSp6W W₂ K₂ exe endPc R F c0 t k sl me cA fr) :
    WcSp6W (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 t k sl me cA fr :=
  ⟨blkW_and h₁.n6 h₂.n6, nodeW_and h₁.n6f h₂.n6f, blkW_and h₁.n6a h₂.n6a, nodeW_and h₁.nd h₂.nd,
    nodeW_and h₁.n10 h₂.n10, blkW_and h₁.nr h₂.nr⟩

/-- **From `.x25` to the `syscall`, publishing at the `mfence`**: two facts combine. -/
theorem WcSp6PW.and {c0 c1 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp6PW W₁ K exe endPc R F c0 c1 t k sl me cA fr) (h₂ : WcSp6PW W₂ K₂ exe endPc R F c0 c1 t k sl me cA fr) :
    WcSp6PW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 c1 t k sl me cA fr :=
  ⟨blkW_and h₁.n6 h₂.n6, nodeW_and h₁.n6f h₂.n6f, blkW_and h₁.n6a h₂.n6a, nodeW_and h₁.nd h₂.nd,
    nodeW_and h₁.n10 h₂.n10, blkW_and h₁.nr h₂.nr⟩

/-- **From the box's store to the `syscall`**: two facts combine at the first's outside move. -/
theorem WcMidWH.and {F₂ : MachineData → Prop} {ms : MemSide isa} {J1 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcMidWH W₁ K exe endPc R F F₂ ms J1 Q) (h₂ : WcMidWH W₂ K₂ exe endPc R F F₂ ms J1 Q) :
    WcMidWH (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F F₂ ms J1 Q :=
  ⟨WcResWH.and h₁.res h₂.res,
    fun c0 sl me cA fr hM => WcSp3WH.and (h₁.sp3 c0 sl me cA fr hM) (h₂.sp3 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp4WH.and (h₁.sp4 c0 sl me cA fr hM) (h₂.sp4 c0 sl me cA fr hM),
    fun c0 ty l sl me cA fr hM => WcSp6PW.and (h₁.sp6 c0 ty l sl me cA fr hM) (h₂.sp6 c0 ty l sl me cA fr hM)⟩

end And

/-! ## The clone's pc -/

/-- **A state at the clone's `syscall` is at `cloneAtH exe`.** -/
theorem wcNSH_cloneAt {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr) s c) :
    s.st.2 = cloneAtH exe :=
  h.2.2.2.1

/-- **A state at the clone's `syscall` has `pcOf s = clonePcH L`**, in `L`'s executable. -/
theorem wcNSH_clonePc {L : Spike.Lib.X64.Rt.RuntimeLayout} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At L.exe endPc R F (wcNSH (_root_.Executable.labels L.exe).label c0 t k sl me cA fr) s c) :
    Scc.Sem.X64.pcOf s = clonePcH L := by
  unfold Scc.Sem.X64.pcOf clonePcH
  rw [wcNSH_cloneAt h]

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcMidWH.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcMidWH.and

/-- info: 'Spike.Lib.X64.Flow.HelloWc.wcNSH_clonePc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.wcNSH_clonePc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcSp6PW.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcSp6PW.and
