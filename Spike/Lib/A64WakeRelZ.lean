/-
**wake.w's worker writes at most once per instruction, a release write**
(AArch64): `RelZ` (`Spike/Lib/A64RelW1Nodes.lean`) at every
node's states of the spawned child's run (`ThrZA`, `NodeZA` at the stub),
`wakeZX`'s `RelW1` conjunct. Every block is covered (it runs to `.done`:
its stack accesses hit the private memory), the prologues' limit loads are
loads, the writes are the `stlr` to the flag and to the thread's exit word
and `scc_rt_unpark`'s `swpal`, the `svc`s fault. The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `thrZA_rel`: `ThrZA RelZ` of the thread worker in a region covering its
  frames.
- `cZA_rel`: at the child's stub.
-/
import Spike.Lib.A64RelW1Nodes
import Spike.Lib.A64WakeChildNNA

namespace Spike.Lib.A64.Flow.Worker.Wake.RelZW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZA thrJ thrJE wcJE wkCode unpkCode thrCode thECode wake_wcPro
  wake_thrPro)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cN childN cBlk pfxM wake_stubIn stubIn cb chB cb_ok chB_ok)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.RelZ

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

omit [Kraken.Executable.ValidLayout exe] in
/-- A node with no instruction (a call). -/
theorem nodeZA_nil {Z : Frag isaLSE2} {R : Region} {F : MachineData → Prop} {n : ND} :
    NodeZA Z exe endPc R F n [] :=
  fun _ _ _ _ _ _ _ _ _ _ k hk => absurd hk (by simp)

variable (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
include hp hend

set_option hygiene false in
/-- A covered block's node: its `okBlk`, its code. -/
local macro "rb " ok:term:max cd:term:max : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => relZ_of_done h) $ok hR hal hlo hhi $cd)

/-- **`RelZ` at `scc_rt_unpark`'s nodes.** -/
theorem unpk_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c2 c3 : Ctl} {B x29 ra tp : BitVec 64} (i : Unpark.PN) :
    NodeZA RelZ exe endPc R F (Unpark.N (_root_.Executable.labels exe).label c2 c3 B x29 ra tp i)
      (Unpark.blkN i) := by
  have hc := unpkCode hp hend (c0 := c2) (c1 := c3) (B := B) (x29 := x29) (ra := ra) (tp := tp)
  cases i
  · rb Unpark.b0_ok hc.e
  · rb Unpark.b1_ok hc.n1
  · exact nodeZA_cell hc.swp fun _ _ hc hd => relZ_swpal hc hd
  · rb Unpark.b2_ok hc.n2
  · rb Unpark.b3_ok hc.n3
  · rb Unpark.b4_ok hc.wake
  · exact nodeZA_cell hc.svc fun _ _ hc _ => relZ_svc hc
  · rb Unpark.b5_ok hc.n5
  · rb Unpark.b6_ok hc.done

/-- **`RelZ` at `wc_worker`'s nodes.** -/
theorem wk_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi) {c1 c2 c3 : Ctl} {A B x29 ra tp : BitVec 64} (i : WkTailW.PN) :
    NodeZA RelZ exe endPc R F (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c1 c2 c3 A B x29 ra tp i)
      (WkTailW.blkN i) := by
  have hc := wkCode hp hend (c0 := c1) (c1 := c2) (c2 := c3) (A := A) (B := B) (x29 := x29) (ra := ra) (tp := tp)
  cases i
  · rb WkTailW.b0_ok hc.e
  · exact nodeZA_cell hc.st fun _ _ hc hd => relZ_stlr hc hd
  · rb WkTailW.b1_ok hc.n3
  · rb WkTailW.b2_ok hc.bl
  · exact nodeZA_nil
  · rb WkTailW.b3_ok hc.sp1

/-- **`RelZ` at `scc_rt_thr_worker`'s tail.** -/
theorem tail_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c3 : Ctl} {tp : BitVec 64} (i : ThrTailW.PN) :
    NodeZA RelZ exe endPc R F (ThrTailW.N ThrTailW.pfx0 (_root_.Executable.labels exe).label c3 tp i)
      (ThrTailW.blkN i) := by
  have hc := thrCode hp hend (c0 := c3) (tp := tp)
  cases i
  · rb ThrTailW.b0_ok hc.sp0
  · exact nodeZA_cell hc.ex fun _ _ hc hd => relZ_stlr hc hd
  · rb ThrTailW.b1_ok hc.n2
  · exact nodeZA_cell hc.svc fun _ _ hc _ => relZ_svc hc

/-- **`RelZ` at `scc_rt_thr_worker`'s head.** -/
theorem head_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : ThrHeadW.TN) :
    NodeZA RelZ exe endPc R F (ThrHeadW.tN ThrTailW.pfx0 (_root_.Executable.labels exe).label J L i)
      (ThrHeadW.blkN i) := by
  cases i
  · rb ThrHeadW.thE_ok (thECode hp hend)
  · exact nodeZA_nil

/-- **`RelZ` at every node's states of the thread worker's run**, in a
region covering its frames. -/
theorem thrZA_rel {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) {c0 c1 c2 c3 : Ctl}
    {A B tp sp0 : BitVec 64} : ThrZA RelZ exe endPc R F ms c0 c1 c2 c3 A B tp sp0 where
  pro := proW_relZ hp hend wake_thrPro (by decide) (by decide) hR hal (Int.le_trans hlo (by decide)) hhi
    (by decide)
  head := head_rel hp hend hR hal hlo hhi
  wpro _ _ hC _ _ := proW_relZ hp hend wake_wcPro (by decide) (by decide) hC.ok hC.al
    (Int.le_trans hC.lo (by decide)) hC.hi (by decide)
  wk _ _ hC _ _ := wk_rel hp hend hC.ok hC.al (Int.le_trans hC.lo (by decide)) hC.hi
  unpk _ _ _ _ _ _ _ hC _ _ := unpk_rel hp hend hC.ok hC.al hC.lo hC.hi
  tail := tail_rel hp hend hR hal (Int.le_trans hlo (by decide)) hhi

/-- **`RelZ` at the child's stub.** -/
theorem cZA_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) {cW : Ctl} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZA RelZ exe endPc R F (cN pfxM (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i) := by
  have hin := wake_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  intro i
  cases i
  · rb cb_ok (code_of hp hend hcb (by simp only [cN, childN, ofNat4_succ, ofNat4_zero]))
  · rb chB_ok (code_of hp hend hch (ofNat4_zero _))

end Spike.Lib.A64.Flow.Worker.Wake.RelZW
