/-
**wake.w on AArch64: the code facts of the worker's functions** (the worker's half), decided on the program the canonical loader
reads from the certificate's listing (`Spike.Lib.A64.WakeLabels.wakeProg`) by `decide +kernel` on `blockAt`/`labelGap`/
`prologueIn` (`Scc/Cert/Rt/LayoutA64.lean`, `Spike/Lib/A64CodeSegs.lean`),
for any valid layout `exe` that lays the program out (`Lays exe wakeProg
kp`; the canonical loader's thread is one: `Scc.Cert.Rt.A64.lays_threadAt`).

- `wkCode`, `thrCode`, `unpkCode`: `WkTailW.Code`, `ThrTailW.Code`,
  `Unpark.Code` at wake's prefixes (`.L19_wc_worker`,
  `.L18_scc_rt_thr_worker`, `.L11_scc_rt_unpark`); `thECode`: the
  `.0_entry` block of `scc_rt_thr_worker`.
- `hsp1` (`.sp1` right after `wc_worker`'s `bl`), `hsp0` (`.sp0` right after
  `scc_rt_thr_worker`'s `bl`), `hpentry` (`scc_rt_unpark`'s frame set-up
  falls through to `.0_entry`).
- `wc_prologue_seg`, `thr_prologue_seg`: the stack-checked prologues of
  `wc_worker` (frame 32, `x0`/`x1` at 0/8) and `scc_rt_thr_worker` (frame
  48, `x0`/`x1` at 0/8), `prologue_seg_of` lifted to the thread rows.
- `seg_wcWorker` (`seg_wcWorkerX`, with an extra entry fact): `wc_worker`
  from its label (`wcJE`) to its return, the prologue then
  `WkTailW.seg_wkTailWU`, all code facts discharged here.
- `seg_thrWorker`: the worker thread from `scc_rt_thr_worker`'s label
  (`thrJE`: `x0`/`x1` the worker's two words, the thread pointer, `sp`) to
  its `exit`: the prologue, `ThrHeadW.seg_thrHeadW` with `seg_wcWorkerX` as
  the callee (the source's `split` across the `.0_entry` block), then
  `ThrTailW.seg_thrTailW`.
-/
import Spike.Lib.A64WakeWorker
import Spike.Lib.A64WakeLabels
import Spike.Lib.A64CodeSegs

namespace Spike.Lib.A64.Flow.Worker.Wake.Labels

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Park (swpDir)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.WakeLabels (wakeProg)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

/-- `wc_worker`'s blocks at wake's prefix. -/
abbrev wkIn : Bool :=
  blockAt wakeProg (WkTailW.pfx0 ++ ".0_entry") 0 WkTailW.b0 &&
  blockAt wakeProg (WkTailW.pfx0 ++ ".0_entry") 2
    [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] &&
  blockAt wakeProg (WkTailW.pfx0 ++ ".0_entry") 3 WkTailW.b1 &&
  blockAt wakeProg (WkTailW.pfx0 ++ ".0_entry") 4 WkTailW.b2 &&
  blockAt wakeProg (WkTailW.pfx0 ++ ".sp1") 0 WkTailW.b3 &&
  labelGap wakeProg (WkTailW.pfx0 ++ ".0_entry") (WkTailW.pfx0 ++ ".sp1") 5

/-- `scc_rt_thr_worker`'s blocks at wake's prefix. -/
abbrev thrIn : Bool :=
  blockAt wakeProg (ThrTailW.pfx0 ++ ".0_entry") 0 ThrHeadW.thE &&
  labelGap wakeProg (ThrTailW.pfx0 ++ ".0_entry") (ThrTailW.pfx0 ++ ".sp0") 3 &&
  blockAt wakeProg (ThrTailW.pfx0 ++ ".sp0") 0 ThrTailW.b0 &&
  blockAt wakeProg (ThrTailW.pfx0 ++ ".sp0") 5
    [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] &&
  blockAt wakeProg (ThrTailW.pfx0 ++ ".sp0") 6 ThrTailW.b1 &&
  blockAt wakeProg (ThrTailW.pfx0 ++ ".sp0") 8 [svcDir]

/-- `scc_rt_unpark`'s blocks. -/
abbrev unpkIn : Bool :=
  blockAt wakeProg "scc_rt_unpark" 0 Unpark.b0 &&
  labelGap wakeProg "scc_rt_unpark" ".L11_scc_rt_unpark.0_entry" 5 &&
  blockAt wakeProg ".L11_scc_rt_unpark.0_entry" 0 Unpark.b1 &&
  blockAt wakeProg ".L11_scc_rt_unpark.0_entry" 3 [swpDir .acqRel .X9 .X11 .X10] &&
  blockAt wakeProg ".L11_scc_rt_unpark.0_entry" 4 Unpark.b2 &&
  blockAt wakeProg ".L11_scc_rt_unpark.0_entry" 9 Unpark.b3 &&
  blockAt wakeProg ".L11_scc_rt_unpark.1_wake" 0 Unpark.b4 &&
  blockAt wakeProg ".L11_scc_rt_unpark.1_wake" 11 [svcDir] &&
  blockAt wakeProg ".L11_scc_rt_unpark.1_wake" 12 Unpark.b5 &&
  blockAt wakeProg ".L11_scc_rt_unpark.2_done" 0 Unpark.b6

/-- `wc_worker`'s prologue: frame 32, `c` and `j` at 0 and 8. -/
abbrev wcPro : Bool := prologueIn wakeProg "wc_worker" (WkTailW.pfx0 ++ ".stack_check")
  (WkTailW.pfx0 ++ ".0_entry") 32 8 (WkTailW.pfx0 ++ ".stack_grow") [(.X0, 0), (.X1, 8)]

/-- `scc_rt_thr_worker`'s prologue: frame 48, its two arguments at 0 and 8. -/
abbrev thrPro : Bool := prologueIn wakeProg "scc_rt_thr_worker" (ThrTailW.pfx0 ++ ".stack_check")
  (ThrTailW.pfx0 ++ ".0_entry") 48 8 (ThrTailW.pfx0 ++ ".stack_grow") [(.X0, 0), (.X1, 8)]

theorem wake_wkIn : wkIn = true := by decide +kernel
theorem wake_thrIn : thrIn = true := by decide +kernel
theorem wake_unpkIn : unpkIn = true := by decide +kernel
theorem wake_wcPro : wcPro = true := by decide +kernel
theorem wake_thrPro : thrPro = true := by decide +kernel

/-! ## The code facts -/

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
include hp hend

/-- **`wc_worker`'s code** at wake's prefix, any ghosts. -/
theorem wkCode {c0 c1 c2 : Ctl} {A B x29 ra tp : BitVec 64} :
    WkTailW.Code WkTailW.pfx0 c0 c1 c2 A B x29 ra tp exe endPc := by
  have h := wake_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := h
  exact ⟨code_of hp hend h0 (by simp only [WkTailW.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h1 (by simp only [WkTailW.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h2 (by simp only [WkTailW.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h3 (by simp only [WkTailW.N, WkTailW.pcBl, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h4 (by simp only [WkTailW.N, ofNat4_succ, ofNat4_zero])⟩

/-- **`.sp1` right after `wc_worker`'s `bl`.** -/
theorem hsp1 : (_root_.Executable.labels exe).label (WkTailW.pfx0 ++ ".sp1") =
    WkTailW.pcBl WkTailW.pfx0 (_root_.Executable.labels exe).label + 4 := by
  have h := wake_wkIn
  simp only [wkIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGap hp h.2.2.2.2.2]
  simp only [WkTailW.pcBl, ofNat4_succ, ofNat4_zero]

/-- **`scc_rt_thr_worker`'s tail code** at wake's prefix, any ghosts. -/
theorem thrCode {c0 : Ctl} {tp : BitVec 64} : ThrTailW.Code ThrTailW.pfx0 c0 tp exe endPc := by
  have h := wake_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, h0, h1, h2, h3⟩ := h
  exact ⟨code_of hp hend h0 (by simp only [ThrTailW.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h1 (by simp only [ThrTailW.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h2 (by simp only [ThrTailW.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h3 (by simp only [ThrTailW.N, ofNat4_succ, ofNat4_zero])⟩

/-- **`scc_rt_thr_worker`'s `.0_entry` block.** -/
theorem thECode : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s ((_root_.Executable.labels exe).label (ThrTailW.pfx0 ++ ".0_entry")) ThrHeadW.thE := by
  have h := wake_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  exact code_of hp hend h.1 (ofNat4_zero _)

/-- **`.sp0` right after `scc_rt_thr_worker`'s `bl`.** -/
theorem hsp0 : (_root_.Executable.labels exe).label (ThrTailW.pfx0 ++ ".sp0") =
    (_root_.Executable.labels exe).label (ThrTailW.pfx0 ++ ".0_entry") + 4 + 4 + 4 := by
  have h := wake_thrIn
  simp only [thrIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGap hp h.2.1]
  simp only [ofNat4_succ, ofNat4_zero]

/-- **`scc_rt_unpark`'s code**, any ghosts. -/
theorem unpkCode {c0 c1 : Ctl} {B x29 ra tp : BitVec 64} : Unpark.Code c0 c1 B x29 ra tp exe endPc := by
  have h := wake_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨code_of hp hend h0 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h1 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h2 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h3 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h4 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h5 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h6 (by simp only [Unpark.N, Unpark.pcSvc, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h7 (by simp only [Unpark.N, Unpark.pcSvc, ofNat4_succ, ofNat4_zero]),
    code_of hp hend h8 (by simp only [Unpark.N, ofNat4_succ, ofNat4_zero])⟩

/-- **`scc_rt_unpark`'s frame set-up falls through to `.0_entry`.** -/
theorem hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
    (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4 := by
  have h := wake_unpkIn
  simp only [unpkIn, Bool.and_eq_true, and_assoc] at h
  rw [label_labelGap hp h.2.1]
  simp only [ofNat4_succ, ofNat4_zero]

end Code

/-! ## The prologues -/

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`wc_worker`'s prologue** in any valid layout of `wakeProg`, with the
thread rows. -/
theorem wc_prologue_seg (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label (WkTailW.pfx0 ++ ".0_entry"))
    (ho : SO.le nb.o (oFr 32) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 32 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 32 σ.regs }).regs →
          σ'.slot = stSlots (-(32 : Int64).toInt) σ'.regs [(.X0, 0), (.X1, 8)] (frSlot σ) → nb.J σ' c) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_of hp hend wake_wcPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge).toT

/-- **`scc_rt_thr_worker`'s prologue** in any valid layout of `wakeProg`,
with the thread rows. -/
theorem thr_prologue_seg (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label (ThrTailW.pfx0 ++ ".0_entry"))
    (ho : SO.le nb.o (oFr 48) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (48 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 48 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 48 σ.regs }).regs →
          σ'.slot = stSlots (-(48 : Int64).toInt) σ'.regs [(.X0, 0), (.X1, 8)] (frSlot σ) → nb.J σ' c) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_of hp hend wake_thrPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge).toT

/-- **`wc_worker`'s entry**: the source at `c0`, `c`'s address `A` in `x0`,
`j`'s tid `B` in `x1`, the caller's `x29`, the return address `ra` in
`x30`, the thread pointer `tp`. -/
def wcJE (c0 : Ctl) (A B x29 ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.X0.toBitVec = A ∧ σ.regs.X1.toBitVec = B ∧ σ.regs.X29.toBitVec = x29 ∧
    σ.regs.X30.toBitVec = ra ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- **`wc_worker` is one segment with the thread rows** in any valid layout
of `wakeProg`, from its label (`wcJE`, and any further fact `X` of the
entry state) to its return (`WkTailW.E`): the stack-checked prologue, the
source's `store rel c 1` at the `stlr`, its `unpark j` at
`scc_rt_unpark`'s `swpal`, the epilogue. The region holds the frame and
`scc_rt_unpark`'s below it (`hlo`). Left to the caller: the stack limit's
facts at entry (`hlim`, which may use `X`), the source's facts of the store
and the `unpark` (as `WkTailW.seg_wkTailWU`), the permit word's (`hS`,
`htp4`), the kernel model (`hK`). -/
theorem seg_wcWorkerX (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {c0 c1 c2 : Ctl} {A B x29 ra tp : BitVec 64} {X : AS → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 A B x29 ra tp σ c → X σ →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (32 : Int64).toBitVec).toNat)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 A B x29 ra tp σ c ∧ X σ⟩)
      (fun s c => ∃ x, At exe endPc R F (WkTailW.E c2 x29 ra tp x) s c) := by
  refine SegT.seq (wc_prologue_seg hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .e)
    rfl (by simp only [WkTailW.N]; decide) fun σ c hJ => ?_)
    (WkTailW.seg_wkTailWU hF hR hal hlo hhi hdm ht hev hv htag hevb hvb hc1 (wkCode hp hend) hK hS htp4
      htu hhu hevu hvu hc2 (unpkCode hp hend (c0 := c0) (c1 := c1) (B := B) (x29 := x29) (ra := ra) (tp := tp))
      (hpentry hp hend) (hsp1 hp hend))
  obtain ⟨hJ, hX⟩ := hJ
  obtain ⟨h1, h2, h3, h4⟩ := hlim σ c hJ hX
  refine ⟨h1, h2, h3, fun v hv => ⟨h4 v hv, fun σ' hreg hsl => ?_⟩⟩
  obtain ⟨rfl, h0, hx1, h29, h30, htp⟩ := hJ
  simp only [WkTailW.N, WkTailW.JI]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
      Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]

/-- **`wc_worker` is one segment with the thread rows** (`seg_wcWorkerX`
with no further entry fact). -/
theorem seg_wcWorker (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {c0 c1 c2 : Ctl} {A B x29 ra tp : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 A B x29 ra tp σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (32 : Int64).toBitVec).toNat)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        wcJE c0 A B x29 ra tp⟩)
      (fun s c => ∃ x, At exe endPc R F (WkTailW.E c2 x29 ra tp x) s c) :=
  (seg_wcWorkerX (X := fun _ => True) hp hend hF hR hal hlo hhi (fun σ c h _ => hlim σ c h) hdm ht hev hv htag
    hevb hvb hc1 hK hS htp4 htu hhu hevu hvu hc2).mono_pre fun _ _ ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ =>
      ⟨he, hn, hd, hpc, σ, hA, hD, hJ, trivial⟩

/-- **`scc_rt_thr_worker`'s entry**: the source at `c0` (the worker's body),
`c`'s address `A` in `x0`, `j`'s tid `B` in `x1`, the thread pointer `tp`,
`sp` at `sp0`. -/
def thrJE (c0 : Ctl) (A B tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.X0.toBitVec = A ∧ σ.regs.X1.toBitVec = B ∧ σ.regs.TPIDR_EL0.toBitVec = tp ∧
    σ.regs.SP.toBitVec = sp0

/-- After `scc_rt_thr_worker`'s prologue: `A`, `B` in the frame's first two
words, the thread pointer, `sp` the frame's base. -/
def thrJ (c0 : Ctl) (A B tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-48) = A ∧ σ.slot (-40) = B ∧ σ.regs.TPIDR_EL0.toBitVec = tp ∧
    σ.regs.SP.toBitVec = sp0 - (48 : Int64).toBitVec

/-- **The worker thread is one segment with the thread rows** in any valid
layout of `wakeProg`, from `scc_rt_thr_worker`'s label (`thrJE`) to any
fragment (the thread exits): the prologue, the call of `wc_worker`
(`seg_wcWorkerX`, the source's `split` of its argument across the
`.0_entry` block: `hsplit`), the `exited` release and the `exit`
(`ThrTailW.seg_thrTailW`). The source controls: `c0` (the worker's body),
`c1` (after the `split`), `c2` (after the store), `c3` (after the
`unpark`, at `ret`). The region holds the thread's frame, `wc_worker`'s and
`scc_rt_unpark`'s (`hlo`). Left to the caller: the stack limit's facts for
both prologues (`hlim`), the facts of the store and the `unpark`, the permit
word's (`hS`, `htp4`) and the `exited` word's (`hSx`), the kernel model. -/
theorem seg_thrWorker {Q : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hlim : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (sp0 - (48 : Int64).toBitVec).toNat ∧
        (v.setWidth 64).toNat ≤ (sp0 - (48 : Int64).toBitVec - (32 : Int64).toBitVec).toNat)
    (hsplit : LocalRun p c0 c1)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c1.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c1.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c1.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc2 : c2 = ⟨e1, (d, .unit, []) :: c1.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c2.term = .let_ x (.ext .unpark au) e) (hhu : c2.hold = none)
    (hevu : TermRun.evalAt c2.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc3 : c3 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c2.env, none⟩)
    {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hSx : StOk ms F exe endPc (tp + 24#64) 1#64) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 A B tp sp0⟩) Q := by
  let lab := (_root_.Executable.labels exe).label
  refine SegT.seq (thr_prologue_seg hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := ThrHeadW.tN ThrTailW.pfx0 lab (thrJ c0 A B tp sp0) (fun _ c => c = c1) .e)
    rfl (by simp only [ThrHeadW.tN]; decide) fun σ c hJ => ?_) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hlim σ.regs hJ.2.2.2.1
    refine ⟨h1, h2, h3, fun v hv => ⟨?_, fun σ' hreg hsl => ?_⟩⟩
    · rw [hJ.2.2.2.2]; exact (h4 v hv).1
    obtain ⟨rfl, h0, hx1, htp, hsp⟩ := hJ
    simp only [ThrHeadW.tN, thrJ]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  refine SegT.seq (ThrHeadW.seg_thrHeadW (N := fun _ : Unit => ThrTailW.N ThrTailW.pfx0 lab c3 tp .sp0)
    (E := (nofun : Empty → ND)) hF hR hal hlo hhi (fun σ c hJ => ⟨c1, hJ.1 ▸ hsplit, rfl⟩) (thECode hp hend)
    (Ne := fun g : BitVec 64 × BitVec 64 => ⟨lab "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c1 A B g.1 g.2 tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (48 : Int64).toBitVec⟩)
    (Ex := fun g y => WkTailW.E c3 g.1 g.2 tp y)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g =>
      seg_wcWorkerX hp hend hF' hR' hal' hlo' hhi'
        (fun σ c hJ hX => by
          obtain ⟨h1, h2, h3, h4⟩ := hlim σ.regs hJ.2.2.2.2.2
          exact ⟨h1, h2, fun m hm => h3 m (hFF m hm), fun v hv => by rw [hX]; exact (h4 v hv).2⟩)
        (fun m hm => hdm m (hFF m hm)) ht hev hv htag hevb hvb hc2 hK (hS.mono hFF) htp4 htu hhu hevu hvu hc3)
    (fun _ => rfl) ?_ ?_) ?_
  · rintro σC c ⟨σ0, c0', ⟨-, h48, h40, htp, hsp⟩, hc, rfl⟩
    refine ⟨(_, _), rfl, ⟨hc, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩ <;>
      simp only [enter, ThrHeadW.thE_run] <;> assumption
  · rintro ⟨x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨σ0, c0', -, -, rfl⟩ ⟨⟨-, -, -, -, h30, -⟩, -⟩ ⟨hc', -, -, htp'⟩ hreg - -
    refine .inl ⟨(), ?_, by simp only [ThrTailW.N, WkTailW.E]; decide, hc', ?_⟩
    · show (_root_.Executable.labels exe).label (ThrTailW.pfx0 ++ ".sp0") = Int64.ofBitVec ra'
      have h30' : ra' = _ := h30.symm
      rw [h30']
      simp only [enter, ThrHeadW.thE_run]
      rw [hsp0 hp hend, Ret0.ofInt_bmod, BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_add,
        Spike.Lib.int64_ofInt_toInt]; rfl
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'
  · exact (ThrTailW.seg_thrTailW hF hR hal (Int.le_trans hlo (by decide)) hhi hK hSx hret3 (thrCode hp hend)).mono_pre
      fun s c h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim

end Pro

end Spike.Lib.A64.Flow.Worker.Wake.Labels
