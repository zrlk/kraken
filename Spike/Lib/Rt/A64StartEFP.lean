/-
**The start's prefix with an extra entry fact `P` in the frame** (AArch64):
`scc_rt_start` from `_start` to `.sp2`'s call of `scc_rt_thread_init`,
run at the frame `F ∧ P`, where `P` is stable for the start's region
(`FStable R P`). The prefix asks no closure under `K` of its frame (its
nodes and blocks are moved by no `K`, the call of `scc_rt_alloc_tcb` is at
`KC := False`), so `P` rides there from `_start` with no other premise; at
the thread init's call it is the callee's entry fact (`call_nd_FWP`).

- `Sp0W.monoF`: `scc_rt_start`'s obligations up to `.sp2` at a stronger
  frame condition;
- `entry_sp2_segWP`: `entry_segW'` then `startSp2_segWA`, at `F ∧ P`.
-/
import Spike.Lib.Rt.A64StartE

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_start`'s obligations up to `.sp2` at a stronger frame
condition.** -/
theorem Sp0W.monoF {W : Frag isaLSE2} {K : State → State → Prop} {F' : MachineData → Prop} {n0 : BitVec 64}
    {c0 : Ctl} (h : Sp0W W K exe endPc R F n0 c0) (hFF : ∀ m, F' m → F m) : Sp0W W K exe endPc R F' n0 c0 :=
  ⟨⟨blkW_mono h.start.w0 hFF, nodeW_mono h.start.w1 hFF, nodeW_mono h.start.w2 hFF, blkW_mono h.start.w3 hFF,
      nodeW_mono h.start.w4 hFF⟩, blkW_mono h.blk hFF, fun g hg i => (h.tcb g hg i).mono hFF⟩

/-- **From `_start` to `.sp2`'s node with `P` in the frame**: `entry_segW'`
then `startSp2_segWA` at `F ∧ P`, the obligations and word facts at `F`
(`blkW_mono`, `Sp0W.monoF`, `StOk.mono`, `TcbOkA.mono`). -/
theorem entry_sp2_segWP {W : Frag isaLSE2} {K : State → State → Prop} {P : MachineData → Prop}
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hc : RtCodeIn0 prog) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hP : FStable R P) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkA ms F exe endPc (R.callee (-48) (-192) 0) F ⟨g, n0, c0⟩)
    (he : BlkW W K exe endPc R F (entryN (_root_.Executable.labels exe).label c0) entryB)
    (hs1 : Sp0W W K exe endPc R F n0 c0) :
    SegW W K p lbl ms (At exe endPc R (fun m => F m ∧ P m) (entryN (_root_.Executable.labels exe).label c0))
      (At exe endPc R (fun m => F m ∧ P m) (Ret0.startN2 (_root_.Executable.labels exe).label n0 c0)) :=
  have hFP : FStable R (fun m => F m ∧ P m) := fun m m' h hd => ⟨hF m m' h.1 hd, hP m m' h.2 hd⟩
  (entry_segW' hp hend hc.entry hFP hR hal (by omega) hhi c0 (blkW_mono he fun _ h => h.1)).seq
    (startSp2_segWA hp hend hc.call hc.start hc.tcb hK hFP hR hal (by omega) hhi n0 c0 hn
      (hhdr.mono fun _ h => h.1)
      (fun g => ⟨(htcb g).next.mono fun _ h => h.1, ((htcb g).mono fun _ h => h.1).own⟩)
      (Sp0W.monoF hs1 fun _ h => h.1))

end Spike.Lib.A64.Rt

/-- info: 'Spike.Lib.A64.Rt.Sp0W.monoF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.Sp0W.monoF

/-- info: 'Spike.Lib.A64.Rt.entry_sp2_segWP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.entry_sp2_segWP
