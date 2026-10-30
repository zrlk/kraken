/-
**wake.w's worker in its certificate, off the transfer sites, `Z` at the
nodes' states** (AArch64): the segments of
`Spike/Lib/A64WakeWorkerLabelsNN.lean` with `Z` at the states before each
instruction (`ProW` at the prologues, `NodeZA` per node), which know the
registers and the frame's cells, not only the pc and the control. The
listing is wake.w's certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `ThrZA`: `Z` at every node's states of `scc_rt_thr_worker`'s run, the
  callees' at the frame conditions seeing their call (`CallerF`);
  `ThrZ.toA`: a `ThrZ` (pc and control only) is one.
- `wc_prologue_segNNA`, `thr_prologue_segNNA`, `seg_wcWorkerXNNA`,
  `seg_thrWorkerNNA`: the `NN` segments at `ThrZA`/`ProW`/`NodeZA`.
-/
import Spike.Lib.A64WakeWorkerLabelsNN
import Spike.Lib.A64WakeWorkerNNA

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

/-- **`Z` at every node's states of `scc_rt_thr_worker`'s run** in the
region `R` with frame condition `F`: its prologue (`ProW`), its head, its
tail (`NodeZA`); `wc_worker`'s prologue and tail at every frame condition
seeing the head's call (`CallerF`) and every return frame; the unpark
callee at every frame condition seeing `wc_worker`'s call. -/
structure ThrZA (Z : Frag isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isaLSE2) (c0 c1 c2 c3 : Ctl) (A B tp sp0 : BitVec 64) : Prop where
  pro : ProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 48 8
    (ThrTailW.pfx0 ++ ".stack_grow") [(.X0, 0), (.X1, 8)] (thrJE c0 A B tp sp0)
  head : ∀ i, NodeZA Z exe endPc R F (ThrHeadW.tN ThrTailW.pfx0 (_root_.Executable.labels exe).label
    (thrJ c0 A B tp sp0) (fun _ c => c = c1) i) (ThrHeadW.blkN i)
  wpro : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F (ThrHeadW.tN ThrTailW.pfx0
      (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0) (fun _ c => c = c1) .call) (-80) 0 R' F' → ∀ x29 ra,
    ProW Z (fun _ _ => False) exe endPc R' F' ms ((_root_.Executable.labels exe).label "wc_worker") 32 8
      (WkTailW.pfx0 ++ ".stack_grow") [(.X0, 0), (.X1, 8)]
      fun σ c => wcJE c1 A B x29 ra tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (48 : Int64).toBitVec
  wk : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F (ThrHeadW.tN ThrTailW.pfx0
      (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0) (fun _ c => c = c1) .call) (-80) 0 R' F' → ∀ x29 ra i,
    NodeZA Z exe endPc R' F' (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c1 c2 c3 A B x29 ra tp i)
      (WkTailW.blkN i)
  unpk : ∀ (R' : Region) (F' : MachineData → Prop), CallerF R F (ThrHeadW.tN ThrTailW.pfx0
      (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0) (fun _ c => c = c1) .call) (-80) 0 R' F' → ∀ x29 ra,
    ∀ (R'' : Region) (F'' : MachineData → Prop),
      CallerF R' F' (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c1 c2 c3 A B x29 ra tp .unpk)
        (-48) 0 R'' F'' →
      ∀ x29' ra' i, NodeZA Z exe endPc R'' F'' (Unpark.N (_root_.Executable.labels exe).label c2 c3 B x29' ra' tp i)
        (Unpark.blkN i)
  tail : ∀ i, NodeZA Z exe endPc R F (ThrTailW.N ThrTailW.pfx0 (_root_.Executable.labels exe).label c3 tp i)
    (ThrTailW.blkN i)

/-- A fact of the pc and the control at every node (`ThrZ`) is one at every
node's states. -/
theorem ThrZ.toA {Z : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (h : ThrZ Z exe c0 c1 c2 c3 A B tp sp0) : ThrZA Z exe endPc R F ms c0 c1 c2 c3 A B tp sp0 where
  pro := ProW.ofPcs h.pro
  head i := NodeZ.toAOf (h.head i) (by cases i <;> rfl)
  wpro _ _ _ x29 ra := ProW.ofPcs fun s σ c k hk he hpc hJ => h.wpro x29 ra s σ c k hk he hpc hJ.1
  wk _ _ _ x29 ra i := NodeZ.toAOf (h.wk x29 ra i) (by cases i <;> rfl)
  unpk _ _ _ _ _ _ _ _ x29' ra' i := NodeZ.toAOf (h.unpk x29' ra' i) (by cases i <;> rfl)
  tail i := NodeZ.toAOf (h.tail i) (by cases i <;> rfl)

section ProNNA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : Frag isaLSE2}

/-- **`wc_prologue_segNN` with `Z` at the prologue's states** (`ProW`). -/
theorem wc_prologue_segNNA (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
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
          σ'.slot = stSlots (-(32 : Int64).toInt) σ'.regs [(.X0, 0), (.X1, 8)] (frSlot σ) → nb.J σ' c)
    (hz : ProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker") 32 8
      (WkTailW.pfx0 ++ ".stack_grow") [(.X0, 0), (.X1, 8)] J) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend wake_wcPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge hz

/-- **`thr_prologue_segNN` with `Z` at the prologue's states** (`ProW`). -/
theorem thr_prologue_segNNA (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
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
          σ'.slot = stSlots (-(48 : Int64).toInt) σ'.regs [(.X0, 0), (.X1, 8)] (frSlot σ) → nb.J σ' c)
    (hz : ProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 48 8
      (ThrTailW.pfx0 ++ ".stack_grow") [(.X0, 0), (.X1, 8)] J) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend wake_thrPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge hz

/-- **`seg_wcWorkerXNN` with `Z` at every node's states** (`ProW` at the
prologue, `NodeZA` per node; the unpark callee's at the frame conditions
seeing the call, `CallerF`). -/
theorem seg_wcWorkerXNNA (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
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
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    (hz : ProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker") 32 8
      (WkTailW.pfx0 ++ ".stack_grow") [(.X0, 0), (.X1, 8)] fun σ c => wcJE c0 A B x29 ra tp σ c ∧ X σ)
    (hZW : ∀ i, NodeZA Z exe endPc R F
      (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i) (WkTailW.blkN i))
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop),
      CallerF R F (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk) (-48) 0
        R' F' →
      ∀ x29' ra' i, NodeZA Z exe endPc R' F' (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29' ra' tp i)
        (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 A B x29 ra tp σ c ∧ X σ⟩)
      (fun s c => ∃ x, At exe endPc R F (WkTailW.E c2 x29 ra tp x) s c) := by
  refine SegTC.seq (wc_prologue_segNNA hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .e)
    rfl (by simp only [WkTailW.N]; decide) (fun σ c hJ => ?_) hz)
    (WkTailW.seg_wkTailWUNNA hF hR hal hlo hhi hdm ht hev hv htag hevb hvb hc1 (wkCode hp hend) hK hS htp4
      htu hhu hevu hvu hc2 (unpkCode hp hend (c0 := c0) (c1 := c1) (B := B) (x29 := x29) (ra := ra) (tp := tp))
      (hpentry hp hend) (hsp1 hp hend) hZW hZU)
  obtain ⟨hJ, hX⟩ := hJ
  obtain ⟨h1, h2, h3, h4⟩ := hlim σ c hJ hX
  refine ⟨h1, h2, h3, fun v hv => ⟨h4 v hv, fun σ' hreg hsl => ?_⟩⟩
  obtain ⟨rfl, h0, hx1, h29, h30, htp⟩ := hJ
  simp only [WkTailW.N, WkTailW.JI]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
      Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]

/-- **`seg_thrWorkerNNA` with `Z` at every node's states** (`ThrZA`). -/
theorem seg_thrWorkerNNA {Q : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
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
    (hSx : StOk ms F exe endPc (tp + 24#64) 1#64)
    (hZ : ThrZA Z exe endPc R F ms c0 c1 c2 c3 A B tp sp0) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 A B tp sp0⟩) Q := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTC.seq (thr_prologue_segNNA hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := ThrHeadW.tN ThrTailW.pfx0 lab (thrJ c0 A B tp sp0) (fun _ c => c = c1) .e)
    rfl (by simp only [ThrHeadW.tN]; decide) (fun σ c hJ => ?_) hZ.pro) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hlim σ.regs hJ.2.2.2.1
    refine ⟨h1, h2, h3, fun v hv => ⟨?_, fun σ' hreg hsl => ?_⟩⟩
    · rw [hJ.2.2.2.2]; exact (h4 v hv).1
    obtain ⟨rfl, h0, hx1, htp, hsp⟩ := hJ
    simp only [ThrHeadW.tN, thrJ]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  refine SegTC.seq (ThrHeadW.seg_thrHeadWNNA (N := fun _ : Unit => ThrTailW.N ThrTailW.pfx0 lab c3 tp .sp0)
    (E := (nofun : Empty → ND)) hF hR hal hlo hhi (fun σ c hJ => ⟨c1, hJ.1 ▸ hsplit, rfl⟩) (thECode hp hend)
    (Ne := fun g : BitVec 64 × BitVec 64 => ⟨lab "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c1 A B g.1 g.2 tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (48 : Int64).toBitVec⟩)
    (Ex := fun g y => WkTailW.E c3 g.1 g.2 tp y)
    (fun R' F' hC g =>
      seg_wcWorkerXNNA hp hend hC.stab hC.ok hC.al hC.lo hC.hi
        (fun σ c hJ hX => by
          obtain ⟨h1, h2, h3, h4⟩ := hlim σ.regs hJ.2.2.2.2.2
          exact ⟨h1, h2, fun m hm => h3 m (hC.sees m hm).1, fun v hv => by rw [hX]; exact (h4 v hv).2⟩)
        (fun m hm => hdm m (hC.sees m hm).1) ht hev hv htag hevb hvb hc2 hK (hS.mono fun m hm => (hC.sees m hm).1) htp4
        htu hhu hevu hvu hc3 (hZ.wpro R' F' hC g.1 g.2) (hZ.wk R' F' hC g.1 g.2) (hZ.unpk R' F' hC g.1 g.2))
    (fun _ => rfl) ?_ ?_ hZ.head) ?_
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
  · exact (ThrTailW.seg_thrTailWNNA hF hR hal (Int.le_trans hlo (by decide)) hhi hK hSx hret3
      (thrCode hp hend) hZ.tail).mono_pre fun s c h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim

end ProNNA

end Spike.Lib.A64.Flow.Worker.Wake.Labels
