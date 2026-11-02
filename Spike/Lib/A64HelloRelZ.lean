/-
**hello.w's worker writes at most once per instruction, a release write**
(AArch64): `RelZ`
(`Spike/Lib/A64RelW1Nodes.lean`) at every node's states of hello's worker
segments, in the `NodeZA`/`NodeW`/`ProW` form the segment lemmas take
(`A64HelloWkTailNN`, `A64HelloThrNN`, `A64HelloChildNN`, `A64HelloPrintNN`,
`A64HelloWorkerTCS`). Every block is covered (it runs to `.done`: its stack
accesses hit the private memory), the prologues' limit loads are loads, the
writes are the `stlr`s to the store's flag and the thread's exit word and
`scc_rt_unpark`'s `swpal`, `print`'s `dmb ish` is a fence, the `svc`s
fault. (`print` loads nothing from the shared buffer: its loads are its own
stack slots; the `write`'s bytes are the kernel's.) The abort path's
`RelZ` is `A64HelloAbortX`'s own.

- `NodeZA.toW0`: a node's fact at its first instruction.
- `unpk_relH`, `tail_relH`: `scc_rt_unpark`'s and `wc_worker`'s tail nodes.
- `thrTail_relH`, `thrHead_relH`, `child_relH`: the thread worker's tail
  and head, the child's stub.
- `wcPro_relH`, `thrPro_relH`: the two stack-checked prologues.
- `wE_relH`, `wCall_relH`: `wc_worker`'s `.0_entry` block and its call
  node (`scc_rt_print`'s first instruction, in the worker's region).
- `print_relH`: `scc_rt_print`'s nodes.
-/
import Spike.Lib.A64HelloWorkerTCS
import Spike.Lib.A64HelloChildNN
import Spike.Lib.A64WakeRelZ

namespace Spike.Lib.A64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)
open Spike.Lib.A64.Flow.RelZ
open Spike.Lib.A64.Flow.Worker.Wake.RelZW (nodeZA_nil)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE thrJE thrJ cN childN cBlk pfxM stubIn hello_stubIn cb chB
  cb_ok chB_ok)

/-- **A node's fact at its first instruction** (`NodeZA.toW` for a longer
block). -/
theorem NodeZA.toW0 {Z : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {d : Directive} {ds : List Directive}
    (h : NodeZA Z exe endPc R F n (d :: ds)) : NodeW Z (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => by
    have h0 := (h s σ c he hn hdc hpc hA hD hJ 0 (by simp) s.st.1 hA (DFrame.refl _ _)).1
    rw [Spike.Lib.A64.Flow.ofNat4_zero, ← hpc] at h0
    exact ⟨h0, fun _ h => h⟩

/-- `blkZA_done` with the code at the state's ghost control. -/
theorem blkZA_doneC {Z : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {lo hi : Int} {blk : List Directive}
    (hZ : ∀ s c s', isaLSE2.exec s = some (.done s') → Z s c)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) (hcode : ∀ _ : Ctl, ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) :
    NodeZA Z exe endPc R F n blk :=
  fun s σ c => blkZA_done hZ hok hR hal hlo hhi (hcode c) s σ c

/-- `nodeZA_cell` with the code at the state's ghost control. -/
theorem nodeZA_cellC {Z : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {d : Directive}
    (hcode : ∀ _ : Ctl, ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (h : ∀ s c, CellAt s d 4 → s.decls = {} → Z s c) : NodeZA Z exe endPc R F n [d] :=
  fun s σ c => nodeZA_cell (hcode c) h s σ c

/-- `scc_rt_print`'s entry block at the worker's call (`sp` at `-96`) is
covered in the worker's region. -/
theorem b0_okW : okBlk (-192) 0 ⟨-96, []⟩ A64.Print.b0 = true := by decide

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

variable (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
include hp hend

set_option hygiene false in
/-- A covered block's node: its `okBlk`, its code. -/
local macro "rb " ok:term:max cd:term:max : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => relZ_of_done h) $ok hR hal hlo hhi $cd)

set_option hygiene false in
/-- A covered block of `print`'s, its code at the state's control. -/
local macro "rp " ok:term:max f:ident : tactic =>
  `(tactic| exact blkZA_doneC (fun _ _ _ h => relZ_of_done h) $ok hR hal hlo hhi
    (fun c s he hn => (hc c).$f s he hn))

/-- **`RelZ` at `scc_rt_unpark`'s nodes.** -/
theorem unpk_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c1 c2 : Ctl} {B x29 ra tp : BitVec 64} (i : Unpark.PN) :
    NodeZA RelZ exe endPc R F (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp i)
      (Unpark.blkN i) := by
  have hc := Labels.unpkCode hp hend (c0 := c1) (c1 := c2) (B := B) (x29 := x29) (ra := ra) (tp := tp)
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

/-- **`RelZ` at `wc_worker`'s tail nodes.** -/
theorem tail_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) {c0 c1 c2 : Ctl} {A B x29 ra tp : BitVec 64} (i : HelloTail.PN) :
    NodeZA RelZ exe endPc R F (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i)
      (HelloTail.blkN i) := by
  have hc := tailCode hp hend (c0 := c0) (c1 := c1) (c2 := c2) (A := A) (B := B) (x29 := x29) (ra := ra) (tp := tp)
  cases i
  · rb HelloTail.b0_ok hc.sp4
  · exact nodeZA_cell hc.st fun _ _ hc hd => relZ_stlr hc hd
  · rb HelloTail.b1_ok hc.n3
  · rb HelloTail.b2_ok hc.bl
  · exact nodeZA_nil
  · rb HelloTail.b3_ok hc.sp6

/-- **`RelZ` at `scc_rt_thr_worker`'s tail.** -/
theorem thrTail_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {c3 : Ctl} {tp : BitVec 64} (i : HThrTail.PN) :
    NodeZA RelZ exe endPc R F (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp i)
      (HThrTail.blkN i) := by
  have hc := thrCode hp hend (c0 := c3) (tp := tp)
  cases i
  · rb HThrTail.b0_ok hc.sp0
  · exact nodeZA_cell hc.ex fun _ _ hc hd => relZ_stlr hc hd
  · rb HThrTail.b1_ok hc.n2
  · exact nodeZA_cell hc.svc fun _ _ hc _ => relZ_svc hc

/-- **`RelZ` at `scc_rt_thr_worker`'s head.** -/
theorem thrHead_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : HThrHead.TN) :
    NodeZA RelZ exe endPc R F (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label J L i)
      (HThrHead.blkN i) := by
  cases i
  · rb HThrHead.thE_ok (thECode hp hend)
  · exact nodeZA_nil

/-- **`RelZ` at the child's stub.** -/
theorem child_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {cW : Ctl} {w : Words} {tp sp0 : BitVec 64} (i : Child.CN) :
    NodeZA RelZ exe endPc R F (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i) := by
  have hin := hello_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  cases i
  · rb cb_ok (code_of hp hend hcb (by simp only [cN, childN, ofNat4_succ, ofNat4_zero]))
  · rb chB_ok (code_of hp hend hch (ofNat4_zero _))

/-- **`RelZ` at `wc_worker`'s prologue.** -/
theorem wcPro_relH {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    ProW RelZ (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker") 96 8
      ".L20_wc_worker.stack_grow" wcPs J :=
  proW_relZ hp hend hello_wcPro (by decide) (by decide) hR hal hlo hhi (by decide)

/-- **`RelZ` at `scc_rt_thr_worker`'s prologue.** -/
theorem thrPro_relH {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    ProW RelZ (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8
      (HThrTail.pfx0 ++ ".stack_grow") thrPs J :=
  proW_relZ hp hend hello_thrPro (by decide) (by decide) hR hal hlo hhi (by decide)

/-- **`RelZ` at `wc_worker`'s `.0_entry` block.** -/
theorem wE_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} :
    NodeZA RelZ exe endPc R F (Body.wN (_root_.Executable.labels exe).label J Pr .e) Body.wkE := by
  rb Body.wkE_ok (wkECode hp hend)

/-- **`RelZ` at `wc_worker`'s call node** (`scc_rt_print`'s first
instruction, `sp` at `-96`). -/
theorem wCall_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) {J Kc : AS → Ctl → Prop} :
    NodeW RelZ (fun _ _ => False) exe endPc R F (Body.wCall (_root_.Executable.labels exe).label J Kc) :=
  fun s c hs => by
    have h : NodeZA RelZ exe endPc R F (Body.wCall (_root_.Executable.labels exe).label J Kc) A64.Print.b0 :=
      blkZA_done (fun _ _ _ h => relZ_of_done h) b0_okW hR hal hlo hhi
        (fun s he hn => (printCode hp hend (c0 := c) (x29 := 0) (ra := 0)).e s he hn)
    exact NodeZA.toW0 h s c hs

/-- **`RelZ` at `scc_rt_print`'s nodes**, at any call state. -/
theorem print_relH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {Pc Qc : AS → Nat → Ctl → Prop} {σC : AS} (i : PrintF.PN) :
    NodeZA RelZ exe endPc R F (PrintF.cN (_root_.Executable.labels exe).label Pc Qc σC i) (PrintF.FA.blkN i) := by
  have hc : ∀ c0 : Ctl, PrintF.Code c0 σC.regs.X29.toBitVec σC.regs.X30.toBitVec exe endPc := fun c0 =>
    printCode hp hend
  cases i
  · rp A64.Print.b0_ok e
  · rp A64.Print.b1_ok n1
  · rp A64.Print.b2_ok loop
  · rp A64.Print.b3_ok n3
  · exact nodeZA_cellC (fun c s he hn => (hc c).fence s he hn) (fun _ _ hc _ e he => by
      rw [exec_dmb hc] at he; cases he; exact .noW (.fence fun _ => .done _))
  · rp A64.Print.b4_ok write
  · exact nodeZA_cellC (fun c s he hn => (hc c).svc s he hn) (fun _ _ hc _ => relZ_svc hc)
  · rp A64.Print.b5_ok n5
  · rp A64.Print.b6_ok n6
  · rp A64.Print.b7_ok n7
  · rp A64.Print.b8_ok chk2
  · rp A64.Print.b9_ok n9
  · rp A64.Print.b10_ok n10
  · rp A64.Print.b11_ok chk3
  · rp A64.Print.b12_ok n12
  · rp A64.Print.b13_ok adv
  · rp A64.Print.b14_ok fail
  · rp A64.Print.b16_ok done

end Spike.Lib.A64.Flow.Worker.Hello.Wk
