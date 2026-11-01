/-
**hello.w's `wc_main` obligations past the box's store at `h1`'s outside
move** (AArch64 tier, `HelloHMid`'s prerequisite;
the twin of `Spike/Lib/A64WakeWcK1.lean` at hello's `WcMidWH`, frame 144):
from `WcMidWH` at a stack take at `a` to `WcMidWH` at the take of the site's
range or a `clone` refusal (`TakeCKS a Cl`, `Cl` only at the clone's pc),
the states off the clone's and the take's pcs.

- `nodeW_mapWK` … `tcbWG_mapWK` (wake's, generic) reused; `WcResWH.mapWK`,
  `WcSp3WH.mapWK`, `WcSp4WH.mapWK`, `WcSp6W.mapWK`, `WcMidWH.mapWK`: node
  obligations under a pointwise change of the predicate and the outside move.
- `ckRunsH`, `ckInH`, `ckH_chk`, `ckH_ne`: the pcs of `WcMidWH`'s nodes
  (`wc_main` from `.sp0 + 16` to the `svc`, `scc_rt_thread_reserve`,
  `scc_rt_alloc_tcb`, `scc_rt_thread_init`'s entry), none the clone's
  (`cloneAtH pfxM exe`, `.sp6 + 100`) nor the take site's
  (`scc_rt_take_site`), decided on helloProg's listing.
- `OffCH`, `wcMidW_offCH`: `WcMidWH`'s states off both pcs.
- `wcMidW_k1H`, `wcMidW_k1SH`: `WcMidWH` at `TakeCKS a Cl` with both pcs
  avoided (wake's `takeK_pc`, `takeCKS_none`, `pcOf_ne` reused).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloWcMidW
import Spike.Lib.A64WakeWcK1

namespace Spike.Lib.A64.Flow.HelloWc

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.A64.Flow (ND BlkW NodeW At AS)
open Spike.Lib.A64.Rt (TcbGG TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResG ReserveW)
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.A64ConsumerA (TakeKS TakeCKS)
open Spike.Lib.A64.Flow.WakeWc (nodeW_mapWK blkW_mapWK reserveW_mapWK tcbWG_mapWK takeK_pc takeCKS_none pcOf_ne)
open Spike.Lib.A64.HelloPh.WcSp6 (WcSp6W)
open Spike.Lib.HelloPreA (pfxM cloneAtH)
open Scc.Cert.Rt.A64 (Lays)
open Scc.Sem.A64 (pcOf)

/-! ## A pointwise change of the predicate and the outside move -/

section Map

variable {W W' : Frag isaLSE2} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}
  (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s')
include hf

/-- **From the fence to `.sp3`** under a pointwise change. -/
theorem WcResWH.mapWK {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResWH W K exe endPc R F ms J1 S Q) : WcResWH W' K' exe endPc R F ms J1 S Q :=
  ⟨nodeW_mapWK hf h.f, blkW_mapWK hf h.bl, fun g hg i => reserveW_mapWK hf (h.res g hg i)⟩

/-- **From `.sp3` to `.sp4`** under a pointwise change. -/
theorem WcSp3WH.mapWK {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (h : WcSp3WH W K exe endPc R F c0 sl me cA fr) :
    WcSp3WH W' K' exe endPc R F c0 sl me cA fr :=
  ⟨blkW_mapWK hf h.blk, fun g hg i => tcbWG_mapWK hf (h.tcb g hg i)⟩

/-- **From `.sp4` to the call** under a pointwise change. -/
theorem WcSp4WH.mapWK {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp4WH W K exe endPc R F c0 t sl me cA fr) :
    WcSp4WH W' K' exe endPc R F c0 t sl me cA fr :=
  ⟨blkW_mapWK hf h.n4, nodeW_mapWK hf h.n4s, blkW_mapWK hf h.n5⟩

/-- **From `.sp6` to the `svc`** under a pointwise change. -/
theorem WcSp6W.mapWK {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp6W W K exe endPc R F c0 t k sl me cA fr) :
    WcSp6W W' K' exe endPc R F c0 t k sl me cA fr :=
  ⟨blkW_mapWK hf h.n6, nodeW_mapWK hf h.n6f, blkW_mapWK hf h.n6a⟩

/-- **From the box's store to the `svc`** under a pointwise change of the
predicate and the outside move. -/
theorem WcMidWH.mapWK {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidWH W K exe endPc R F F₂ ms J1 S Q) :
    WcMidWH W' K' exe endPc R F F₂ ms J1 S Q :=
  ⟨WcResWH.mapWK hf h.res, fun c0 sl me cA fr hM => WcSp3WH.mapWK hf (h.sp3 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp4WH.mapWK hf (h.sp4 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp6W.mapWK hf (h.sp6 c0 sl me cA fr hM)⟩

end Map

/-! ## The nodes' pcs off the clone's -/

/-- **The runs of `WcMidWH`'s nodes**: `wc_main` from `.sp0 + 16` to the
last instruction before the `svc` (`.sp6 + 4·25`), `scc_rt_thread_reserve`,
`scc_rt_alloc_tcb` and `scc_rt_thread_init`'s entry. -/
def ckRunsH : List (Label × Nat × Nat) :=
  [(".L22_wc_main.sp0", 4, 6), (".L22_wc_main.sp3", 0, 5), (".L22_wc_main.sp4", 0, 6),
   ("scc_rt_thread_init", 0, 1), (".L22_wc_main.sp6", 0, 25),
   (Flow.Reserve.fnL, 0, 4), (Flow.Reserve.entryL, 0, 16), (Flow.Reserve.okL, 0, 5),
   (Ret0.AllocTcb.fnL, 0, 6), (Ret0.AllocTcb.entryL, 0, 5), (Ret0.AllocTcb.lenL, 0, 48),
   (Ret0.AllocTcb.okL, 0, 43)]

/-- **The runs' pcs are neither the clone's** (`.sp6 + 4·25`) **nor the take
site's** (`scc_rt_take_site`), on helloProg's listing. -/
theorem ckH_chk : Spike.Lib.A64.RunsOff.runsNeChk SccCode.helloProg ckRunsH
    [(pfxM ++ ".sp6", 25), (Ret0.StackTake.siteL, 0)] = true := by
  decide +kernel

/-- **`n` instructions from `l + 4k` lie in one of the runs.** -/
def ckInH (l : Label) (k n : Nat) : Bool :=
  ckRunsH.any fun r => r.1 == l && decide (r.2.1 ≤ k) && decide (k + n ≤ r.2.2)

section Off

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe SccCode.helloProg kp) {endPc : Int64} {R : Region} {F : MachineData → Prop}
include hp

/-- **A pc of the runs is neither the clone's nor the take site's.** -/
theorem ckH_ne {l : Label} {k n : Nat} (h : ckInH l k n = true) {j : Nat} (hj : j < n) :
    (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + j)) ≠ cloneAtH pfxM exe ∧
      (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + j)) ≠
        (_root_.Executable.labels exe).label Ret0.StackTake.siteL := by
  obtain ⟨⟨l', lo, hi⟩, hr, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
  have hn := Spike.Lib.A64.RunsOff.runsNe_of_chk hp ckH_chk _ hr (k + j) (by show lo ≤ k + j; omega)
    (by show k + j < hi; omega)
  exact ⟨hn _ (List.mem_cons_self ..), by
    simpa [Spike.Lib.A64.Flow.ofNat4_zero] using hn _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- **Off the clone's pc and the take site's.** -/
def OffCH (exe : _root_.Executable) : Frag isaLSE2 := fun s _ =>
  s.st.2 ≠ cloneAtH pfxM exe ∧ s.st.2 ≠ (_root_.Executable.labels exe).label Ret0.StackTake.siteL

/-- A node at `l + 4k` in the runs is off the clone's pc. -/
theorem nodeW_offCH {n : ND} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) (h : ckInH l k 1 = true) :
    NodeW (OffCH exe) (fun _ _ => False) exe endPc R F n :=
  fun _ _ ⟨_, _, _, hpc, _⟩ => ⟨by
    show _ ∧ _
    rw [hpc, he]
    simpa using ckH_ne hp h (j := 0) (by decide), fun _ h => h⟩

/-- A node at a label in the runs is off the clone's pc. -/
theorem nodeW_offCH0 {n : ND} {l : Label} (he : n.pc = (_root_.Executable.labels exe).label l)
    (h : ckInH l 0 1 = true) : NodeW (OffCH exe) (fun _ _ => False) exe endPc R F n :=
  nodeW_offCH hp (k := 0) (by rw [he, Spike.Lib.A64.Flow.ofNat4_zero]) h

/-- A block node at `l + 4k` whose instructions are in the runs is off the
clone's pc. -/
theorem blkW_offCH {n : ND} {blk : List Directive} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) (h : ckInH l k blk.length = true) :
    BlkW (OffCH exe) (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ j hj _ _ _ => ⟨by
    show _ ∧ _
    rw [he, Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add]
    exact ckH_ne hp h hj, fun _ h => h⟩

/-- A block node at a label whose instructions are in the runs is off the
clone's pc. -/
theorem blkW_offCH0 {n : ND} {blk : List Directive} {l : Label} (he : n.pc = (_root_.Executable.labels exe).label l)
    (h : ckInH l 0 blk.length = true) : BlkW (OffCH exe) (fun _ _ => False) exe endPc R F n blk :=
  blkW_offCH hp (k := 0) (by rw [he, Spike.Lib.A64.Flow.ofNat4_zero]) h

/-- One node or block of `WcMidWH` off the clone's pc. -/
local macro "offch" : tactic =>
  `(tactic| first
    | exact nodeW_offCH hp rfl (by decide +kernel)
    | exact nodeW_offCH0 hp rfl (by decide +kernel)
    | exact blkW_offCH hp rfl (by decide +kernel)
    | exact blkW_offCH0 hp rfl (by decide +kernel))

/-- **`WcMidWH`'s states are off the clone's pc and the take site's**, with
no outside moves: every node of `wc_main` from `.sp0 + 16` to the `svc` and
of its callees is at a pc of `ckRunsH`. -/
theorem wcMidW_offCH {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidWH (OffCH exe) (fun _ _ => False) exe endPc R F F₂ ms J1 S Q := by
  refine ⟨⟨?_, ?_, fun g _ i => ?_⟩, fun c0 sl me cA fr _ => ⟨?_, fun g _ i => ?_⟩,
    fun c0 sl me cA fr _ => ⟨?_, ?_, ?_⟩, fun c0 sl me cA fr _ => ⟨?_, ?_, ?_⟩⟩
  case refine_3 => cases i <;> dsimp only [ReserveW] <;> offch
  case refine_5 => cases i <;> dsimp only [TcbWG] <;> offch
  all_goals offch

end Off

/-! ## `h1`'s outside move -/

/-- **`WcMidWH` at the take of the site's range or a refusal**, the states
off the clone's pc and the take's pc `a`, from `WcMidWH` at a take at `a`:
no take at `a` moves a state, so it is off `a`; every state is off the
clone's pc (`wcMidW_offCH`), where only the refusal `Cl` is (`hCl`). -/
theorem wcMidW_k1H {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp) {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {W : Frag isaLSE2}
    {a : Int64} {rK : Scc.Sem.Range} {Cl : State → Prop}
    (hCl : ∀ s, Cl s → pcOf s = (cloneAtH pfxM exe).toBitVec.toNat)
    (h : WcMidWH W (TakeK a rK) exe endPc R F F₂ ms J1 S Q) :
    WcMidWH (fun s c => W s c ∧ pcOf s ≠ (cloneAtH pfxM exe).toBitVec.toNat ∧ pcOf s ≠ a.toBitVec.toNat)
      (TakeCKS a Cl) exe endPc R F F₂ ms J1 S Q :=
  WcMidWH.mapWK (fun _ _ ⟨hW, hc, _⟩ hk =>
      ⟨⟨hW, pcOf_ne hc, pcOf_ne (takeK_pc hk)⟩, takeCKS_none hCl (takeK_pc hk) (pcOf_ne hc)⟩)
    (WcMidWH.and h (wcMidW_offCH hp))

/-- **`WcMidWH` at the take of the site's range or a refusal**, the states
off the clone's pc and the take site's (`wcMidW_offCH`): only a refusal at
`Cl` (`hCl`, at the clone's pc) or a take at the site moves a state. -/
theorem wcMidW_k1SH {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp) {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    {Cl : State → Prop} (hCl : ∀ s, Cl s → pcOf s = (cloneAtH pfxM exe).toBitVec.toNat) :
    WcMidWH (fun s _ => pcOf s ≠ (cloneAtH pfxM exe).toBitVec.toNat ∧
        pcOf s ≠ ((_root_.Executable.labels exe).label Ret0.StackTake.siteL).toBitVec.toNat)
      (TakeCKS ((_root_.Executable.labels exe).label Ret0.StackTake.siteL) Cl) exe endPc R F F₂ ms J1 S Q :=
  WcMidWH.mapWK (fun _ _ ⟨hc, ha⟩ _ => ⟨⟨pcOf_ne hc, pcOf_ne ha⟩, takeCKS_none hCl ha (pcOf_ne hc)⟩)
    (wcMidW_offCH hp)

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcMidWH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcMidWH.mapWK

/-- info: 'Spike.Lib.A64.Flow.HelloWc.ckH_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.ckH_ne

/-- info: 'Spike.Lib.A64.Flow.HelloWc.wcMidW_offCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.wcMidW_offCH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.wcMidW_k1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.wcMidW_k1H

/-- info: 'Spike.Lib.A64.Flow.HelloWc.wcMidW_k1SH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.wcMidW_k1SH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcResWH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcResWH.mapWK

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcSp3WH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcSp3WH.mapWK

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcSp4WH.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcSp4WH.mapWK

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcSp6W.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcSp6W.mapWK

/-- info: 'Spike.Lib.A64.Flow.HelloWc.ckH_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.ckH_chk

/-- info: 'Spike.Lib.A64.Flow.HelloWc.nodeW_offCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.nodeW_offCH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.nodeW_offCH0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.nodeW_offCH0

/-- info: 'Spike.Lib.A64.Flow.HelloWc.blkW_offCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.blkW_offCH

/-- info: 'Spike.Lib.A64.Flow.HelloWc.blkW_offCH0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.blkW_offCH0
