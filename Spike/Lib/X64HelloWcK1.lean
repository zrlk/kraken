/-
**hello.w's `wc_main` obligations past the box's store at `h1`'s outside move** (x86-64; the twin of
`Spike/Lib/A64HelloWcK1.lean`, wake's x86-64 `Spike/Lib/X64WakeWcK1.lean` at hello's `WcMidWH`, frame 128): node
obligations under a pointwise change of the predicate and the outside move, and `WcMidWH`'s states off the clone's
and the take site's pcs.

- `nodeW_mapWK` … `tcbWG_mapWK` (wake's, generic) reused; `WcResWH.mapWK`, `WcSp3WH.mapWK`, `WcSp4WH.mapWK`,
  `WcSp6W.mapWK`, `WcSp6PW.mapWK`, `WcMidWH.mapWK`: node obligations under a pointwise change of the predicate
  and the outside move.
- `ckRunsH`, `ckInH`, `ckInBH`, `ckH_chk`, `ckH_ne`: the byte runs of `WcMidWH`'s nodes (`wc_main` from
  `.x22 + 18` to the clone's `syscall`, `scc_rt_thread_reserve`, `scc_rt_alloc_tcb`, `scc_rt_thread_init`'s entry),
  none the clone's pc (`cloneAtH exe`, `.x25 + 94`) nor the take site's (`scc_rt_take_site`), decided on
  `helloCells`.
- `OffCH`, `nodeW_offCH`, `nodeW_offCH0`, `blkW_offCH`, `blkW_offCH0`, `wcMidW_offCH`: `WcMidWH`'s states off both
  pcs.

No absolute address appears in this file.

## Differences from the AArch64 version

- `WcMidWH` has x86-64's nodes: the reserve's call block (no fence node `f`), `.x24`'s three and `.x25`'s six
  nodes; there is no source parameter `S`.
- Instructions have byte sizes: a node's pc is `label l + k` bytes, a block's `j`-th instruction at
  `+ cellOff blk j`; the runs are byte ranges (`X64RunsOff.runsNeChk`), each from its label up to the next of the
  two points, and a block's bytes are its cells' sizes. So there is a new `ckInBH` (a block's bytes in the runs,
  every cell of positive size: wake's `ckInB`), which `blkW_offCH` asks in place of `ckInH l k blk.length`.
- The clone's pc has no prefix argument (`cloneAtH exe`).
- Only the live constants are twinned: `wcMidW_k1H`, `wcMidW_k1SH` are not.
-/
import Spike.Lib.X64HelloWcMidW
import Spike.Lib.X64WakeWcK1

namespace Spike.Lib.X64.Flow.HelloWc

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (TcbGG TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResG ReserveW)
open Spike.Lib.X64.Flow.WakeWc (nodeW_mapWK blkW_mapWK reserveW_mapWK tcbWG_mapWK cellOff_lt)
open Spike.Lib.X64.HelloPh.WcSp6 (WcSp6W WcSp6PW)
open Spike.Lib.X64HelloPreA (cloneAtH)
open Scc.Cert.Rt.X64 (Lays)

/-! ## A pointwise change of the predicate and the outside move -/

section Map

variable {W W' : Frag isa} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}
  (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s')
include hf

/-- **From the call block to `.x23`** under a pointwise change. -/
theorem WcResWH.mapWK {ms : MemSide isa} {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResWH W K exe endPc R F ms J1 Q) : WcResWH W' K' exe endPc R F ms J1 Q :=
  ⟨blkW_mapWK hf h.bl, fun g hg i => reserveW_mapWK hf (h.res g hg i)⟩

/-- **From `.x23` to `.x24`** under a pointwise change. -/
theorem WcSp3WH.mapWK {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (h : WcSp3WH W K exe endPc R F c0 sl me cA fr) :
    WcSp3WH W' K' exe endPc R F c0 sl me cA fr :=
  ⟨blkW_mapWK hf h.blk, fun g hg i => tcbWG_mapWK hf (h.tcb g hg i)⟩

/-- **From `.x24` to the call** under a pointwise change. -/
theorem WcSp4WH.mapWK {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp4WH W K exe endPc R F c0 t sl me cA fr) :
    WcSp4WH W' K' exe endPc R F c0 t sl me cA fr :=
  ⟨blkW_mapWK hf h.n4, nodeW_mapWK hf h.n4s, blkW_mapWK hf h.n5⟩

/-- **From `.x25` to the `syscall`** under a pointwise change. -/
theorem WcSp6W.mapWK {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp6W W K exe endPc R F c0 t k sl me cA fr) :
    WcSp6W W' K' exe endPc R F c0 t k sl me cA fr :=
  ⟨blkW_mapWK hf h.n6, nodeW_mapWK hf h.n6f, blkW_mapWK hf h.n6a, nodeW_mapWK hf h.nd, nodeW_mapWK hf h.n10,
    blkW_mapWK hf h.nr⟩

/-- **From `.x25` to the `syscall`, publishing at the `mfence`,** under a pointwise change. -/
theorem WcSp6PW.mapWK {c0 c1 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp6PW W K exe endPc R F c0 c1 t k sl me cA fr) :
    WcSp6PW W' K' exe endPc R F c0 c1 t k sl me cA fr :=
  ⟨blkW_mapWK hf h.n6, nodeW_mapWK hf h.n6f, blkW_mapWK hf h.n6a, nodeW_mapWK hf h.nd, nodeW_mapWK hf h.n10,
    blkW_mapWK hf h.nr⟩

/-- **From the box's store to the `syscall`** under a pointwise change of the predicate and the outside move. -/
theorem WcMidWH.mapWK {F₂ : MachineData → Prop} {ms : MemSide isa} {J1 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidWH W K exe endPc R F F₂ ms J1 Q) :
    WcMidWH W' K' exe endPc R F F₂ ms J1 Q :=
  ⟨WcResWH.mapWK hf h.res, fun c0 sl me cA fr hM => WcSp3WH.mapWK hf (h.sp3 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp4WH.mapWK hf (h.sp4 c0 sl me cA fr hM),
    fun c0 ty l sl me cA fr hM => WcSp6PW.mapWK hf (h.sp6 c0 ty l sl me cA fr hM)⟩

end Map

/-! ## The nodes' pcs off the clone's -/

/-- **The byte runs of `WcMidWH`'s nodes**: `wc_main` from `.x22 + 18` (the reserve's call block) through `.x23`,
`.x24` and `.x25` up to the clone's `syscall` (`.x25 + 94`), and `scc_rt_thread_reserve`'s, `scc_rt_alloc_tcb`'s
and `scc_rt_thread_init`'s labels, each up to the take site, in hello's cells. -/
def ckRunsH : List (Label × Nat × Nat) :=
  [(".Lwc_main.x0", 18, 165), (".Lwc_main.x1", 0, 142), (".Lwc_main.x2", 0, 119), (".Lwc_main.x3", 0, 94),
   (Flow.Reserve.fnL, 0, 830), (Flow.Reserve.entryL, 0, 822), (Flow.Reserve.okL, 0, 741),
   (Ret0.AllocTcb.fnL, 0, 1285), (Ret0.AllocTcb.entryL, 0, 1266), (Ret0.AllocTcb.lenL, 0, 1244),
   (Ret0.AllocTcb.okL, 0, 1030), (Ret0.ThreadInit.fnL, 0, 732)]

/-- **The runs' pcs are neither the clone's** (`.x25 + 94`) **nor the take site's** (`scc_rt_take_site`), on
hello's cells. -/
theorem ckH_chk : Spike.Lib.X64.RunsOff.runsNeChk SccCode.helloCells ckRunsH
    [(".Lwc_main.x3", 94), (Ret0.StackTake.siteL, 0)] = true := by
  decide +kernel

/-- **`n` bytes from `l + k` lie in one of the runs.** -/
def ckInH (l : Label) (k n : Nat) : Bool :=
  ckRunsH.any fun r => r.1 == l && decide (r.2.1 ≤ k) && decide (k + n ≤ r.2.2)

/-- **A block's bytes from `l + k` lie in one of the runs**, every cell of the block of positive size. -/
def ckInBH (l : Label) (k : Nat) (blk : List (Directive × Nat)) : Bool :=
  ckInH l k (blk.map (·.2)).sum && blk.all fun c => decide (0 < c.2)

section Off

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) {endPc : Int64} {R : Region} {F : MachineData → Prop}
include hp

/-- **A pc of the runs is neither the clone's nor the take site's.** -/
theorem ckH_ne {l : Label} {k n : Nat} (h : ckInH l k n = true) {j : Nat} (hj : j < n) :
    (_root_.Executable.labels exe).label l + Int64.ofNat (k + j) ≠ cloneAtH exe ∧
      (_root_.Executable.labels exe).label l + Int64.ofNat (k + j) ≠
        (_root_.Executable.labels exe).label Ret0.StackTake.siteL := by
  obtain ⟨⟨l', lo, hi⟩, hr, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
  have hn := Spike.Lib.X64.RunsOff.runsNe_of_chk hp ckH_chk _ hr (k + j) (by show lo ≤ k + j; omega)
    (by show k + j < hi; omega)
  exact ⟨hn _ List.mem_cons_self, by
    simpa [Spike.Lib.X64.Flow.ofNat_zero'] using hn _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- **Off the clone's pc and the take site's.** -/
def OffCH (exe : _root_.Executable) : Frag isa := fun s _ =>
  s.st.2 ≠ cloneAtH exe ∧ s.st.2 ≠ (_root_.Executable.labels exe).label Ret0.StackTake.siteL

/-- A node at `l + k` in the runs is off the clone's pc. -/
theorem nodeW_offCH {n : ND} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat k) (h : ckInH l k 1 = true) :
    NodeW (OffCH exe) (fun _ _ => False) exe endPc R F n :=
  fun _ _ ⟨_, _, _, hpc, _⟩ => ⟨by
    show _ ∧ _
    rw [hpc, he]
    simpa using ckH_ne hp h (j := 0) (by decide), fun _ h => h⟩

/-- A node at a label in the runs is off the clone's pc. -/
theorem nodeW_offCH0 {n : ND} {l : Label} (he : n.pc = (_root_.Executable.labels exe).label l)
    (h : ckInH l 0 1 = true) : NodeW (OffCH exe) (fun _ _ => False) exe endPc R F n :=
  nodeW_offCH hp (k := 0) (by rw [he, Spike.Lib.X64.Flow.ofNat_zero']) h

/-- A block node at `l + k` whose bytes are in the runs is off the clone's pc. -/
theorem blkW_offCH {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat k) (h : ckInBH l k blk = true) :
    BlkW (OffCH exe) (fun _ _ => False) exe endPc R F n blk := by
  simp only [ckInBH, Bool.and_eq_true] at h
  exact fun _ _ _ _ _ _ _ _ _ _ j hj _ _ _ => ⟨by
    show _ ∧ _
    rw [he, Int64.add_assoc, ← Int64.ofNat_add]
    exact ckH_ne hp h.1 (cellOff_lt h.2 hj), fun _ h => h⟩

/-- A block node at a label whose bytes are in the runs is off the clone's pc. -/
theorem blkW_offCH0 {n : ND} {blk : List (Directive × Nat)} {l : Label}
    (he : n.pc = (_root_.Executable.labels exe).label l) (h : ckInBH l 0 blk = true) :
    BlkW (OffCH exe) (fun _ _ => False) exe endPc R F n blk :=
  blkW_offCH hp (k := 0) (by rw [he, Spike.Lib.X64.Flow.ofNat_zero']) h

/-- One node or block of `WcMidWH` off the clone's pc. -/
local macro "offch" : tactic =>
  `(tactic| first
    | exact nodeW_offCH hp rfl (by decide +kernel)
    | exact nodeW_offCH0 hp rfl (by decide +kernel)
    | exact blkW_offCH hp rfl (by decide +kernel)
    | exact blkW_offCH0 hp rfl (by decide +kernel))

/-- **`WcMidWH`'s states are off the clone's pc and the take site's**, with no outside moves: every node of
`wc_main` from `.x22 + 18` to the clone's `syscall` and of its callees is at a pc of `ckRunsH`. -/
theorem wcMidW_offCH {F₂ : MachineData → Prop} {ms : MemSide isa} {J1 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidWH (OffCH exe) (fun _ _ => False) exe endPc R F F₂ ms J1 Q := by
  refine ⟨⟨?_, fun g _ i => ?_⟩, fun c0 sl me cA fr _ => ⟨?_, fun g _ i => ?_⟩,
    fun c0 sl me cA fr _ => ⟨?_, ?_, ?_⟩, fun c0 ty l sl me cA fr _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  case refine_2 => cases i <;> dsimp only [ReserveW] <;> offch
  case refine_4 => cases i <;> dsimp only [TcbWG] <;> offch
  all_goals offch

end Off

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcMidWH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcMidWH.mapWK

/-- info: 'Spike.Lib.X64.Flow.HelloWc.ckH_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.ckH_ne

/-- info: 'Spike.Lib.X64.Flow.HelloWc.wcMidW_offCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.wcMidW_offCH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcResWH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcResWH.mapWK

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcSp3WH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcSp3WH.mapWK

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcSp4WH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcSp4WH.mapWK

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcSp6W.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcSp6W.mapWK

/-- info: 'Spike.Lib.X64.Flow.HelloWc.ckH_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.ckH_chk

/-- info: 'Spike.Lib.X64.Flow.HelloWc.nodeW_offCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.nodeW_offCH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.nodeW_offCH0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.nodeW_offCH0

/-- info: 'Spike.Lib.X64.Flow.HelloWc.blkW_offCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.blkW_offCH

/-- info: 'Spike.Lib.X64.Flow.HelloWc.blkW_offCH0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.blkW_offCH0

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcSp6PW.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcSp6PW.mapWK
