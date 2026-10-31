/-
**wake.w on x86-64: the code facts of the worker's functions** (the x64
twin of `Spike/Lib/A64WakeWorkerLabels.lean`), decided on wake's cells
(`SccCode.wakeCells`, `Spike/Lib/X64WakeCode.lean`) by `decide +kernel` on
`blockAtB`/`labelGapB`/`prologueIn` (`Scc/Cert/Rt/CodeX64.lean`,
`Spike/Lib/X64CodeSegs.lean`), for any valid layout `exe` that lays the
cells out (`Lays exe SccCode.wakeCells kp`).

- `wkCode`, `thrCode`, `unpkCode`: `WkTailW.Code`, `ThrTailW.Code`,
  `Unpark.Code`; `thECode`: the `.entry` block of `scc_rt_thr_worker`.
- `hx14` (`.Lwc_worker.x14` right after `wc_worker`'s `call`), `hx12`
  (`.Lscc_rt_thr_worker.x12` right after `scc_rt_thr_worker`'s `call`),
  `hpentry` (`scc_rt_unpark`'s frame set-up falls through to `.entry`).
- `wc_prologue_seg`, `thr_prologue_seg`: the stack-checked prologues of
  `wc_worker` (frame 16) and `scc_rt_thr_worker` (frame 32), `%rdi`/`%rsi`
  stored at `-8(%rbp)`/`-16(%rbp)`, `prologue_seg_of` lifted to the thread
  rows.
- `seg_wcWorker` (`seg_wcWorkerX`, with an extra entry fact): `wc_worker`
  from its label (`wcJE`) to its return, the prologue then
  `WkTailW.seg_wkTailWU`, all code facts discharged here.
- `seg_thrWorker`: the worker thread from `scc_rt_thr_worker`'s label
  (`thrJE`: `%rdi`/`%rsi` the worker's two words, the thread pointer,
  `%rsp`) to its `exit`: the prologue, `ThrHeadW.seg_thrHeadW` with
  `seg_wcWorkerX` as the callee (the source's `split` across the `.entry`
  block), then `ThrTailW.seg_thrTailW`.

**Unlike AArch64** (forced by the x64 shape):

- the checks take the cells (`wkIn cells`, …; `wake_wkIn` at
  `SccCode.wakeCells`), as `X64WaitLoop.waitIn`; the labels carry no
  numbered prefix.
- the stack limit is read through `%fs:8`: `hlim` is `Ret0.LimOk` at
  `tp + 8`, one for each prologue (`hlim` for `scc_rt_thr_worker`'s room
  below `sp0 - 8 - 32`, `hlimW` for `wc_worker`'s below
  `sp0 - 48 - 8 - 16`; AArch64 states both rooms in one `hlim`).
- the entry's `%rsp` is a register fact of the entry node's offsets
  (`At.rspAt`): `wc_worker`'s frame is at the region's base, and
  `seg_thrWorker`'s entry `sp0` is the region's base on every state of its
  pre-fragment (other `sp0`s make it empty).
- the return address of `wc_worker` is in its entry cell `0` (`wcJE`'s
  `ra`, AArch64: `x30`), its caller's frame pointer in `%rbp`.
- `scc_rt_thr_worker`'s tail carries `ThrTailW.seg_thrTailW`'s premises:
  the thread pointer's load from the TCB's self word (`hT`, `hown`).
-/
import Spike.Lib.X64WakeWorker

namespace Spike.Lib.X64.Flow.Worker.Wake.Labels

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk LimOk)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `wc_worker`'s blocks. -/
def wkIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_worker.entry" 0 WkTailW.b0 &&
  blockAtB cells ".Lwc_worker.entry" 11 [(stDir .rcx 0 .rax, 3)] &&
  blockAtB cells ".Lwc_worker.entry" 14 WkTailW.b1 &&
  blockAtB cells ".Lwc_worker.x14" 0 WkTailW.b2 &&
  labelGapB cells ".Lwc_worker.entry" ".Lwc_worker.x14" 23

/-- `scc_rt_thr_worker`'s blocks. -/
def thrIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lscc_rt_thr_worker.entry" 0 ThrHeadW.thE &&
  labelGapB cells ".Lscc_rt_thr_worker.entry" ".Lscc_rt_thr_worker.x12" 13 &&
  blockAtB cells ".Lscc_rt_thr_worker.x12" 0 [(fsDir .rax 0, 9)] &&
  blockAtB cells ".Lscc_rt_thr_worker.x12" 9 ThrTailW.b0 &&
  blockAtB cells ".Lscc_rt_thr_worker.x12" 24 [(stDir .rcx 24 .rax, 4)] &&
  blockAtB cells ".Lscc_rt_thr_worker.x12" 28 ThrTailW.b1 &&
  blockAtB cells ".Lscc_rt_thr_worker.x12" 40 [(op64 .syscall, 2)]

/-- `scc_rt_unpark`'s blocks. -/
def unpkIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells "scc_rt_unpark" 0 Unpark.b0 &&
  labelGapB cells "scc_rt_unpark" ".Lscc_rt_unpark.entry" 12 &&
  blockAtB cells ".Lscc_rt_unpark.entry" 0 Unpark.b1 &&
  blockAtB cells ".Lscc_rt_unpark.entry" 11 [(xchgDir .rcx 16 .rax, 4)] &&
  blockAtB cells ".Lscc_rt_unpark.entry" 15 Unpark.b2 &&
  blockAtB cells ".Lscc_rt_unpark.entry" 35 Unpark.b3 &&
  blockAtB cells ".Lscc_rt_unpark.wake" 0 Unpark.b4 &&
  blockAtB cells ".Lscc_rt_unpark.wake" 62 [(op64 .syscall, 2)] &&
  blockAtB cells ".Lscc_rt_unpark.wake" 64 Unpark.b5 &&
  blockAtB cells ".Lscc_rt_unpark.done" 0 Unpark.b6

/-- `wc_worker`'s prologue: frame 16, `c` and `j` at `-8(%rbp)`, `-16(%rbp)`. -/
def wcPro (cells : List (Directive × Nat)) : Bool :=
  prologueIn cells "wc_worker" ".Lwc_worker.chk" ".Lwc_worker.entry" 16 8 ".Lwc_worker.stk" 5 9 3 2 4
    [(.rdi, -8, 4), (.rsi, -16, 4)]

/-- `scc_rt_thr_worker`'s prologue: frame 32, its two arguments at
`-8(%rbp)`, `-16(%rbp)`. -/
def thrPro (cells : List (Directive × Nat)) : Bool :=
  prologueIn cells "scc_rt_thr_worker" ".Lscc_rt_thr_worker.chk" ".Lscc_rt_thr_worker.entry" 32 8
    ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 [(.rdi, -8, 4), (.rsi, -16, 4)]

theorem wake_wkIn : wkIn SccCode.wakeCells = true := by decide +kernel
theorem wake_thrIn : thrIn SccCode.wakeCells = true := by decide +kernel
theorem wake_unpkIn : unpkIn SccCode.wakeCells = true := by decide +kernel
theorem wake_wcPro : wcPro SccCode.wakeCells = true := by decide +kernel
theorem wake_thrPro : thrPro SccCode.wakeCells = true := by decide +kernel

/-! ## The code facts -/

section Code

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
include hp hend

/-- **`wc_worker`'s code**, any ghosts. -/
theorem wkCode {c0 c1 c2 : Ctl} {A B rbp0 ra tp sp : BitVec 64} :
    WkTailW.Code c0 c1 c2 A B rbp0 ra tp sp exe endPc := by
  have h := wake_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, -⟩ := h
  exact ⟨code_field hp hend h0 (ofNat_zero' _), code_field hp hend h1 rfl, code_field hp hend h2 rfl,
    code_field hp hend h3 (ofNat_zero' _)⟩

/-- **`scc_rt_thr_worker`'s tail code**, any ghosts. -/
theorem thrCode {c0 : Ctl} {tp sp : BitVec 64} : ThrTailW.Code c0 tp sp exe endPc := by
  have h := wake_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, h0, h1, h2, h3, h4⟩ := h
  exact ⟨code_field hp hend h0 (ofNat_zero' _), code_field hp hend h1 rfl, code_field hp hend h2 rfl,
    code_field hp hend h3 rfl, code_field hp hend h4 rfl⟩

/-- **`scc_rt_thr_worker`'s `.entry` block.** -/
theorem thECode : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry") ThrHeadW.thE := by
  have h := wake_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  exact code_field hp hend h.1 (ofNat_zero' _)

/-- **`scc_rt_unpark`'s code**, any ghosts. -/
theorem unpkCode {c0 c1 : Ctl} {B rbp0 ra tp : BitVec 64} : Unpark.Code c0 c1 B rbp0 ra tp exe endPc := by
  have h := wake_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨code_field hp hend h0 (ofNat_zero' _), code_field hp hend h1 (ofNat_zero' _), code_field hp hend h2 rfl,
    code_field hp hend h3 rfl, code_field hp hend h4 rfl, code_field hp hend h5 (ofNat_zero' _),
    code_field hp hend h6 rfl, code_field hp hend h7 rfl, code_field hp hend h8 (ofNat_zero' _)⟩

omit hend in
/-- **`.x14` right after `wc_worker`'s `call`.** -/
theorem hx14 : (_root_.Executable.labels exe).label ".Lwc_worker.x14" =
    (_root_.Executable.labels exe).label ".Lwc_worker.entry" + 14 + 9 := by
  have h := wake_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.2.2.2, Int64.add_assoc]; rfl

omit hend in
/-- **`.x12` right after `scc_rt_thr_worker`'s `call`.** -/
theorem hx12 : (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12" =
    (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry" + 13 := by
  have h := wake_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.1]; rfl

omit hend in
/-- **`scc_rt_unpark`'s frame set-up falls through to `.entry`.** -/
theorem hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
    (_root_.Executable.labels exe).label "scc_rt_unpark" + 12 := by
  have h := wake_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGapB hp h.2.1]; rfl

end Code

/-! ## The prologues -/

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Region} {F : MachineData → Prop}

omit [Executable.ValidLayout exe] in
/-- **`%rsp` at a node's offsets**: a node's states have `%rsp` at the
region's address of the offsets' `sp`. -/
theorem At.rspAt {pc : Int64} {k : Int} {rs : List (Reg64 × Int)} {J : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, ⟨k, rs⟩, J⟩ s c) :
    At exe endPc R F ⟨pc, ⟨k, rs⟩, fun σ c => J σ c ∧ σ.regs.rsp.toBitVec = R.addr k⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hA.so .rsp k (SO.get_rsp _)⟩

/-- **`wc_worker`'s prologue** in any valid layout of wake's cells, with the
thread rows. -/
theorem wc_prologue_seg (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lwc_worker.entry")
    (ho : SO.le nb.o (oF 16) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 16 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4), (.rsi, -16, 4)] (xS1 σ).slot → nb.J σ' c) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_of hp hend wake_wcPro (by decide) hF hR
    (by have : (16 : Int64).toInt = 16 := by decide
        omega) hhi (by decide) hpc ho hedge).toT

/-- **`scc_rt_thr_worker`'s prologue** in any valid layout of wake's cells,
with the thread rows. -/
theorem thr_prologue_seg (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry")
    (ho : SO.le nb.o (oF 32) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 32 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4), (.rsi, -16, 4)] (xS1 σ).slot → nb.J σ' c) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_of hp hend wake_thrPro (by decide) hF hR
    (by have : (32 : Int64).toInt = 32 := by decide
        omega) hhi (by decide) hpc ho hedge).toT

/-- **`wc_worker`'s entry**: the source at `c0`, `c`'s address `A` in
`%rdi`, `j`'s tid `B` in `%rsi`, the caller's `%rbp` `rbp0`, the return
address `ra` in the entry cell `0`, the thread pointer `tp`. -/
def wcJE (c0 : Ctl) (A B rbp0 ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.rdi.toBitVec = A ∧ σ.regs.rsi.toBitVec = B ∧ σ.regs.rbp.toBitVec = rbp0 ∧
    σ.slot 0 = ra ∧ σ.regs.fsBase.toBitVec = tp

/-- **`wc_worker` is one segment with the thread rows** in any valid layout
of wake's cells, from its label (`wcJE`, and any further fact `X` of the
entry state) to its return (`WkTailW.E`): the stack-checked prologue, the
source's `store rel c 1` at the `movq`, its `unpark j` at
`scc_rt_unpark`'s `xchgq`, the epilogue. The region holds the frame and
`scc_rt_unpark`'s below it (`hlo`). Left to the caller: the stack limit's
facts at entry (`hlim`, which may use `X`), the source's facts of the store
and the `unpark` (as `WkTailW.seg_wkTailWU`), the permit word's (`hS`,
`htp4`), the kernel model (`hK`). -/
theorem seg_wcWorkerX (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {c0 c1 c2 : Ctl} {A B rbp0 ra tp : BitVec 64} {X : AS → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 A B rbp0 ra tp σ c → X σ →
      LimOk ms F (tp + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 A B rbp0 ra tp σ c ∧ X σ⟩)
      (fun s c => ∃ x, At exe endPc R F (WkTailW.E c2 rbp0 ra tp x) s c) := by
  refine (SegT.seq (wc_prologue_seg hp hend hF hR (Int.le_trans hlo (by decide)) (by omega)
    (J := fun σ c => (wcJE c0 A B rbp0 ra tp σ c ∧ X σ) ∧ σ.regs.rsp.toBitVec = R.addr 0)
    (nb := WkTailW.N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e)
    rfl (by show SO.le WkTailW.oI (oF 16) = true; decide) fun σ c hJ => ?_)
    (WkTailW.seg_wkTailWU hF hR hlo hhi hdm ht hev hv htag hevb hvb hc1 (wkCode hp hend) hK hS htp4
      htu hhu hevu hvu hc2 (unpkCode hp hend (c0 := c0) (c1 := c1) (B := B) (rbp0 := rbp0) (ra := ra) (tp := tp))
      (hpentry hp) (hx14 hp))).mono_pre fun _ _ h => At.rspAt h
  obtain ⟨⟨hJ, hX⟩, hsp⟩ := hJ
  have hl := hlim σ c hJ hX
  obtain ⟨rfl, hdi, hsi, hbp, h0, htp⟩ := hJ
  rw [htp]
  refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ?_⟩⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; simp [xStSlots, xS1, upd_apply, hbp]
  · rw [hs]; simp [xStSlots, xS1, upd_apply, h0]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hsi]
  · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
  · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]

/-- **`wc_worker` is one segment with the thread rows** (`seg_wcWorkerX`
with no further entry fact). -/
theorem seg_wcWorker (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {c0 c1 c2 : Ctl} {A B rbp0 ra tp : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 A B rbp0 ra tp σ c →
      LimOk ms F (tp + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        wcJE c0 A B rbp0 ra tp⟩)
      (fun s c => ∃ x, At exe endPc R F (WkTailW.E c2 rbp0 ra tp x) s c) :=
  (seg_wcWorkerX (X := fun _ => True) hp hend hF hR hlo hhi (fun σ c h _ => hlim σ c h) hdm ht hev hv htag
    hevb hvb hc1 hK hS htp4 htu hhu hevu hvu hc2).mono_pre fun _ _ ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ =>
      ⟨he, hn, hd, hpc, σ, hA, hD, hJ, trivial⟩

/-- **`scc_rt_thr_worker`'s entry**: the source at `c0` (the worker's body),
`c`'s address `A` in `%rdi`, `j`'s tid `B` in `%rsi`, the thread pointer
`tp`, `%rsp` at `sp0`. -/
def thrJE (c0 : Ctl) (A B tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.rdi.toBitVec = A ∧ σ.regs.rsi.toBitVec = B ∧ σ.regs.fsBase.toBitVec = tp ∧
    σ.regs.rsp.toBitVec = sp0

/-- After `scc_rt_thr_worker`'s prologue: `A`, `B` in the frame's cells
`-16`, `-24`, the thread pointer, `%rbp` at the saved `%rbp`, `%rsp` the
frame's base. -/
def thrJ (c0 : Ctl) (A B tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-16) = A ∧ σ.slot (-24) = B ∧ σ.regs.fsBase.toBitVec = tp ∧
    σ.regs.rbp.toBitVec = sp0 - 8#64 ∧ σ.regs.rsp.toBitVec = sp0 - 40#64

/-- **The worker thread is one segment with the thread rows** in any valid
layout of wake's cells, from `scc_rt_thr_worker`'s label (`thrJE`) to any
fragment (the thread exits): the prologue, the call of `wc_worker`
(`seg_wcWorkerX`, the source's `split` of its argument across the
`.entry` block: `hsplit`), the `exited` store and the `exit`
(`ThrTailW.seg_thrTailW`). The source controls: `c0` (the worker's body),
`c1` (after the `split`), `c2` (after the store), `c3` (after the
`unpark`, at `ret`). The region holds the thread's frame, `wc_worker`'s and
`scc_rt_unpark`'s (`hlo`). Left to the caller: the stack limit's facts for
both prologues (`hlim`, `hlimW`), the facts of the store and the `unpark`,
the permit word's (`hS`, `htp4`), the thread pointer's load (`hT`, `hown`),
the `exited` word's (`hSx`), the kernel model. -/
theorem seg_thrWorker {Q : Frag isa} (hp : Lays exe SccCode.wakeCells kp)
    (hend : endPc = endOf exe SccCode.wakeCells kp)
    {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -120) (hhi : 8 ≤ R.hi)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) (sp0 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (tp + (8 : Int64).toBitVec) (sp0 - 48#64 - 8#64 - (16 : Int64).toBitVec))
    (hsplit : LocalRun p c0 c1)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c1.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c1.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c1.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc2 : c2 = ⟨e1, (d, .unit, []) :: c1.env, none⟩)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c2.term = .let_ x (.ext .unpark au) e) (hhu : c2.hold = none)
    (hevu : TermRun.evalAt c2.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc3 : c3 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c2.env, none⟩)
    {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12") tp tp)
    (hSx : StOk ms F (tp + 24#64) 1#64) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 A B tp sp0⟩) Q := by
  by_cases hsp : sp0 = R.addr 0
  case neg =>
    refine ⟨fun _ _ => False, fun s c h => ?_, fun _ _ h => h.elim⟩
    obtain ⟨-, -, -, -, σ, -, -, hJ, hr⟩ := At.rspAt h
    exact hsp (hJ.2.2.2.2.symm.trans hr)
  subst hsp
  let lab := (_root_.Executable.labels exe).label
  refine SegT.seq (thr_prologue_seg hp hend hF hR (Int.le_trans hlo (by decide)) (by omega)
    (nb := ThrHeadW.tN lab (thrJ c0 A B tp (R.addr 0)) (fun _ c => c = c1) .e)
    rfl (by show SO.le ThrHeadW.oI (oF 32) = true; decide) fun σ c hJ => ?_) ?_
  · obtain ⟨rfl, hdi, hsi, htp, hsp⟩ := hJ
    rw [htp]
    refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨by rw [hsp]; exact hlim.room v hv, fun σ' hr hs => ?_⟩⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hsi]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
      bv_omega
  refine SegT.seq (ThrHeadW.seg_thrHeadW (N := fun _ : Unit => ThrTailW.N lab c3 tp (R.addr 0) .x12)
    (E := (nofun : Empty → ND)) hF hR hlo hhi (fun σ c hJ => ⟨c1, by rw [hJ.1]; exact hsplit, rfl⟩)
    (thECode hp hend)
    (Ne := fun g : BitVec 64 × BitVec 64 => ⟨lab "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c1 A B g.1 g.2 tp σ c ∧ σ.regs.rsp.toBitVec = R.addr 0 - 48#64⟩)
    (Ex := fun g y => WkTailW.E c3 g.1 g.2 tp y)
    (fun R' F' hR' hlo' hhi' hF' hFF g =>
      seg_wcWorkerX hp hend hF' hR' hlo' hhi'
        (fun σ c _ hX => by rw [hX]; exact hlimW.mono hFF)
        (fun m hm => hdm m (hFF m hm)) ht hev hv htag hevb hvb hc2 hK (hS.mono hFF) htp4 htu hhu hevu hvu hc3)
    (fun _ => rfl) ?_ ?_) ?_
  · rintro σC c ⟨σ0, c0', ⟨-, h16, h24, htp, -, hsp⟩, hc, rfl⟩
    refine ⟨(_, _), rfl, ⟨hc, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩ <;>
      simp [enter, ThrHeadW.thE_run, Reg64s.set64, Reg64s.get64, h16, h24, htp, hsp]
    bv_omega
  · rintro ⟨rbp1, ra1⟩ ⟨⟩ σC c σx c' σR ⟨σ0, c0', ⟨-, -, -, -, hbp, -⟩, -, rfl⟩ ⟨⟨-, -, -, hrb, hra, -⟩, -⟩
      ⟨hc', hrb', htp'⟩ hreg - - -
    refine .inl ⟨(), ?_, by show SO.le ThrTailW.oP ⟨-48 - 0 + 8, []⟩ = true; decide, hc', ?_, ?_⟩
    · show (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12" = Int64.ofBitVec ra1
      have hra' : (enter (-48 - 0) (arun lab ThrHeadW.thE ⟨lab ".Lscc_rt_thr_worker.entry", ThrHeadW.oI, σ0⟩).σ).slot 0
        = ra1 := hra
      rw [← hra', hx12 hp]
      simp only [enter, ThrHeadW.thE_run, upd_apply]
      rfl
    · show σR.regs.fsBase.toBitVec = tp
      rw [hreg]; exact htp'
    · show σR.regs.rbp.toBitVec = _
      have h1 : σx.regs.get64 .rbp = rbp1 := hrb'
      have h2 : (enter (-48 - 0) (arun lab ThrHeadW.thE ⟨lab ".Lscc_rt_thr_worker.entry", ThrHeadW.oI, σ0⟩).σ).regs.rbp.toBitVec
        = rbp1 := hrb
      rw [hreg]; simp only [Reg64s.get64] at h1; rw [h1, ← h2]
      simp [enter, ThrHeadW.thE_run, Reg64s.set64, hbp]
  · exact (ThrTailW.seg_thrTailW hF hR (Int.le_trans hlo (by decide)) hhi hK hT hown hSx hret3
      (thrCode hp hend)).mono_pre fun s c h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim

end Pro

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Labels.seg_wcWorker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_wcWorker

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Labels.seg_thrWorker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_thrWorker

end Spike.Lib.X64.Flow.Worker.Wake.Labels
