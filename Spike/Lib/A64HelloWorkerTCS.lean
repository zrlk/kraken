/-
**hello.w's `wc_worker` at depth, `print` a source call** (AArch64): `A64HelloWorkerSegNN.seg_wcWorkerHANN` over
`Spike/Lib/HelloSegTCS.lean`'s `SegTCS`, the call of `scc_rt_print` taken
by the source as a call (`call print [q] sl`, the frame `fr` pushed:
`PrintF.printF_callTCS`) instead of a local run, `print`'s abort closed
inside the callee.

The worker's own nodes are at the frames `[]`: the prologue
(`wc_prologue_segNN`), the `.0_entry` block (`seg_ndNN`, the source's local
run to the call's control `Kc`: `hcall`), the call node `wCall` (at
`scc_rt_print`, `sp` at `-96`), the tail from `.sp4`
(`HelloTail.seg_wkTailUNN`), each lifted by `SegTCS.ofTC`. `print`'s nodes
are at `[fr]`. The fragment is `NNH ∧ Z` at every depth (`Z : FragS`),
the form hello's thread segment consumes (`hseg`), and at `[]` wake's
`SysSafe` (no `write` at all: the worker's own nodes are wake's `NN` leaves,
the call node's first instruction no `svc`), which the concrete `Z` keeps
for `ZStoreOk` (the store phase's `svc`s issue no `write(1, …)`; a pc/control
fact `NodeZ` could not see the registers).

The source facts at the call are asked of `Kc`: the call (`hcallI`,
`CallToI`), `print`'s predicate `Pr` at the callee's entry control
(`hP0`), the frame run from `print`'s end back to `[]` at the store's
control `cw` (`hdone`).

**The worker's region reaches `-192`** (`hlo`): `print`'s 48 bytes and the
abort dispatcher's 48 below the call's `sp` at `-96`; the flat version's
bound was the same (`seg_wcWorkerHANN`).

- `Body.wCall`: the call node, the source at the call's control `Kc`.
- `Hello.Wk.seg_wcWorkerS`: the worker from its label to the tail's exit
  at `[]`.
-/
import Spike.Lib.A64HelloPrintTCS
import Spike.Lib.A64HelloWorkerSegNN

set_option linter.unusedSimpArgs false

namespace Spike.Lib.A64.Flow.Worker.Body

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **The worker's call node**: at `scc_rt_print` with `sp` at `-96`,
after the `.0_entry` block from a state of `J`, the source at the call's
control (`Kc`). -/
def wCall (lab : Label → Int64) (J Kc : AS → Ctl → Prop) : ND :=
  ⟨lab "scc_rt_print", ⟨-96, []⟩, fun σ c => (∃ σ0 c0, J σ0 c0 ∧ σ = wkC lab σ0) ∧ Kc σ c⟩

end Spike.Lib.A64.Flow.Worker.Body

namespace Spike.Lib.A64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)
open Spike.Lib.A64.PcRuns (PcIn)

section WorkerTCS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : FragS isaLSE2}

open Classical in
/-- **`wc_worker` at depth inside `NNH ∧ Z`**: from its label at `[]` to
the tail's exit at `[]`, `print` a source call at `[fr]`
(`PrintF.printF_callTCS`, its abort closed inside). The worker's
hypotheses are `seg_wcWorkerHANN`'s with `ms []` and `Z · · []`; at the
call node the source's facts on `Kc` (`hcallI`, `hP0`, `hdone`) and `Z`
(`hZC`); `print`'s at `[fr]` (`hsvc`, `hZP`, `hZA`, `habt`, `hZu`; `hsvc`,
`hZP` and `hZA` given their frame condition's landing at the call node,
`PrintF.CallFC`; `hZA` an `AbortObl` in any dispatcher region). The
`unpark` callee's nodes (`hZU`) are asked only at the return address
`.sp6`. -/
theorem seg_wcWorkerS (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 cw c1 c2 : Ctl} {w : Words} {x29 ra tp : BitVec 64} {X : AS → Prop}
    {Pr Qa : AS → Nat → Ctl → Prop} {Kc : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 w x29 ra tp σ c → X σ →
      (ms []).rt (tcbA σ.regs 8).toNat ∧ (ms []).mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, (ms []).G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat)
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ, wkJ c0 w x29 ra tp σ c0 →
      ∃ c', LocalRun p c0 c' ∧ Kc (Body.wkC (_root_.Executable.labels exe).label σ) c')
    (hcallI : ∀ σ c, Kc σ c → ∃ cE fr, CallToI p c cE fr)
    (hP0 : ∀ σ c cE fr, Kc σ c → CallToI p c cE fr → Pr σ 0 cE)
    (hdone : ∀ σ0 c cE fr c', wkJ c0 w x29 ra tp σ0 c0 →
      Kc (Body.wkC (_root_.Executable.labels exe).label σ0) c → CallToI p c cE fr →
      Pr (Body.wkC (_root_.Executable.labels exe).label σ0)
        (Body.wkC (_root_.Executable.labels exe).label σ0).regs.X1.toBitVec.toNat c' →
      FrameRun p (c', [fr]) (cw, []))
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (hsvc : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Kc) F' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Kc).J σC c → CallToI p c cE fr →
      SegTC (NNZP SysW1 exe endPc (fun s c => Z s c [fr])) p lbl (ms [fr])
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (ht : cw.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt cw.env a = some (ty, [wa]))
    (hv : ValRep lbl wa.val w.w4.toNat) (htag : ∃ sa, wa.val = .loc sa 0)
    (hevb : TermRun.evalAt cw.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: cw.env, none⟩)
    (hS : StOk (ms []) F exe endPc (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val w.w5.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    (hz : ProW (fun s c => Z s c []) (fun _ _ => False) exe endPc R F (ms [])
      ((_root_.Executable.labels exe).label "wc_worker") 96 8 ".L20_wc_worker.stack_grow" wcPs
      (fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ))
    (hZE : NodeZA (fun s c => Z s c []) exe endPc R F
      (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .e) Body.wkE)
    (hZC : NodeW (fun s c => Z s c []) (fun _ _ => False) exe endPc R F
      (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Kc))
    (hZP : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -96 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Kc) F' → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Kc).J σC c → CallToI p c cE fr →
      ∀ i, NodeZA (fun s c => Z s c [fr]) exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC i)
        (PrintF.FA.blkN i))
    (hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.base.toNat % 16 = 0 → RA.lo ≤ -48 →
      0 ≤ RA.hi → FStable RA FA → (∀ m, FA m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Kc) FA → ∀ σC c cE,
      (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Kc).J σC c →
      CallToI p c cE fr → ∀ k c', Qa σC k c' → AbortObl (fun s c => Z s c [fr]) exe endPc RA FA c')
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms [fr]).abortAt s)
    (hZu : ∀ fr s c, Z s c [fr] → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hZW : ∀ i, NodeZA (fun s c => Z s c []) exe endPc R F
      (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp i) (HelloTail.blkN i))
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ x29' ra',
      Int64.ofBitVec ra' = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" →
      ∀ i, NodeZA (fun s c => Z s c []) exe endPc R' F'
        (Unpark.N (_root_.Executable.labels exe).label c1 c2 w.w5 x29' ra' tp i) (Unpark.blkN i)) :
    SegTCS (fun s c fs => NNH exe endPc s ∧ Z s c fs ∧ (fs = [] → SysSafe s)) p lbl ms
      ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩).at [])
      (Frag.at (fun s c => ∃ y, At exe endPc R F (Wake.WkTailW.E c2 x29 ra tp y) s c) []) := by
  let lab := (_root_.Executable.labels exe).label
  let nE := Body.wN lab (wkJ c0 w x29 ra tp) Pr .e
  let nC := Body.wCall lab (wkJ c0 w x29 ra tp) Kc
  let nT := HelloTail.N lab cw c1 c2 w.w4 w.w5 x29 ra tp .sp4
  -- the prologue, at `[]`
  have h1 : SegTCS (fun s c fs => NNH exe endPc s ∧ Z s c fs ∧ (fs = [] → SysSafe s)) p lbl ms
      ((At exe endPc R F ⟨lab "wc_worker", ⟨0, []⟩, fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩).at [])
      ((At exe endPc R F nE).at []) := by
    refine SegTCS.ofTC (wc_prologue_segNN (Z := fun s c => Z s c []) (ms := ms []) hp hend hF hR hal
      (Int.le_trans hlo (by decide)) hhi (nb := nE) rfl (by simp only [nE, Body.wN]; decide)
      (fun σ c hJ => ?_) hz) fun _ _ h => ⟨h.1.toH, h.2, fun _ => h.1.2.2.2⟩
    obtain ⟨hJ, hX⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := hlim σ c hJ hX
    refine ⟨h1, h2, h3, fun v hv => ⟨h4 v hv, fun σ' hreg hsl => ?_⟩⟩
    obtain ⟨rfl, h0, hx1, hx2, hx3, hx4, hx5, h29, h30, htp⟩ := hJ
    simp only [nE, Body.wN, wkJ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  -- the `.0_entry` block to the call node, at `[]`
  have h2 : SegTCS (fun s c fs => NNH exe endPc s ∧ Z s c fs ∧ (fs = [] → SysSafe s)) p lbl ms
      ((At exe endPc R F nE).at []) ((At exe endPc R F nC).at []) := by
    refine (SegTCS.ofTC (seg_ndNNA (ms := ms []) (Z := fun s c => Z s c [])
      (N := fun _ : Unit => nC) (E := fun y : Empty => y.elim) (by simp [Body.wkE]) Body.wkE_ok
      (by simp [Body.wkE, notNop]) hF hR hal (Int.le_trans hlo (by decide)) hhi (wkECode hp hend)
      (fun σ c hJ => ?_) hZE) fun _ _ h => ⟨h.1.toH, h.2, fun _ => h.1.2.2.2⟩).mono_post ?_
    · obtain rfl := hJ.1
      obtain ⟨c', hr, hK'⟩ := hcall σ hJ
      refine ⟨c', hr, .inl ⟨(), ?_, ?_, ⟨⟨σ, c, hJ, (Body.wkC_eq _ _).symm⟩, ?_⟩⟩⟩
      · simp only [nC, nE, Body.wCall, Body.wN]; rw [Body.wkE_run]
      · simp only [nC, nE, Body.wCall, Body.wN]; rw [Body.wkE_run]; rfl
      · show Kc (arun lab Body.wkE ⟨lab ".L20_wc_worker.0_entry", ⟨-96, []⟩, σ⟩).σ c'
        rw [← Body.wkC_eq]; exact hK'
    · rintro s c fs ⟨(⟨_, h⟩ | ⟨⟨⟩, -⟩), rfl⟩
      exact ⟨h, rfl⟩
  -- the call, `print` at `[fr]`, back to `.sp4` at `[]`
  have h3 : SegTCS (fun s c fs => NNH exe endPc s ∧ Z s c fs ∧ (fs = [] → SysSafe s)) p lbl ms
      ((At exe endPc R F nC).at []) ((At exe endPc R F nT).at []) := by
    refine (PrintF.printF_callTCS (nC := nC) (Pc := Pr) (Qc := Qa) (Zc := fun fr s c => Z s c [fr])
      (N' := fun _ : Unit => nT) (E' := fun y : Empty => y.elim) hp hend SccCode.hello_abort hR hal hF
      (by show R.lo ≤ -96 + -96; omega) (by show (-96 : Int) < R.hi; omega) (by show (-96 : Int) % 16 = 0; decide)
      (printCode hp hend (c0 := c0) (x29 := x29) (ra := ra)) (printEntry hp) rfl (fun fr => hK _)
      (fun σ c ⟨⟨σ0, c0', hJ0, hσ⟩, _⟩ => hσ ▸ Body.wkC_x1_lt lab σ0 (by rw [hJ0.2.2.2.1]; exact hm))
      (fun s c hA => ?_) (fun _ _ _ h1 h2 => ⟨h1, h2, fun h => absurd h (List.cons_ne_nil _ _)⟩) hZu (fun σ c hJ => hcallI σ c hJ.2)
      (fun σ c cE fr hJ hCT => hP0 σ c cE fr hJ.2 hCT) hsvc hZP hZA habt ?_).mono_post ?_
    · obtain ⟨hn, hz'⟩ := nodeW_nnzPA (Sy := SysW1) (Z := fun s c => Z s c []) (R := R) (F := F) (n := nC)
        (fun s he hn => (printCode hp hend (c0 := c0) (x29 := x29) (ra := ra)).e s he hn) (by decide) hZC s c hA
        |>.1
      have hss : SysSafe s := (nodeW_nnzPA (Sy := fun call => call = .exit ∨
          ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)) (Z := fun s c => Z s c [])
        (R := R) (F := F) (n := nC)
        (fun s he hn => (printCode hp hend (c0 := c0) (x29 := x29) (ra := ra)).e s he hn) (by decide) hZC s c hA
        |>.1).1.2.2.2
      exact ⟨hn.toH fun _ h => .inr (.inl h), hz', fun _ => hss⟩
    · rintro σC c cE fr σR c' ⟨⟨σ0, c0', hJ0, rfl⟩, hKc⟩ hCT - h30 htp hP hsl
      obtain rfl := hJ0.1
      refine ⟨cw, hdone σ0 c cE fr c' hJ0 hKc hCT hP, .inl ⟨(), ?_, ?_, ?_⟩⟩
      · show lab ".L20_wc_worker.sp4" = Int64.ofBitVec (Body.wkC lab σ0).regs.X30.toBitVec
        rw [Body.wkC_eq, Body.wkE_X30, ← hgap hp, int64_ofBitVec_toBitVec]
      · rfl
      · obtain ⟨-, -, -, -, -, h64, h56, h16, h8, htp0⟩ := hJ0
        obtain ⟨k16, k8, k64, k56⟩ := Body.wkSl_keep σ0
        have hk : ∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = Body.wkSl σ0 k := fun k h1 h2 h3 => by
          rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, nC, Body.wCall]; omega),
            Body.wkC_eq, Body.wkSl_eq]
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk _ (by decide) (by decide) (by decide), k16, h16]
        · rw [hk _ (by decide) (by decide) (by decide), k8, h8]
        · rw [hk _ (by decide) (by decide) (by decide), k64, h64]
        · rw [hk _ (by decide) (by decide) (by decide), k56, h56]
        · rw [htp, Body.wkC_tp, htp0]
    · rintro s c fs ⟨(⟨_, h⟩ | ⟨⟨⟩, -⟩), rfl⟩
      exact ⟨h, rfl⟩
  -- the tail, at `[]`
  have h4 : SegTCS (fun s c fs => NNH exe endPc s ∧ Z s c fs ∧ (fs = [] → SysSafe s)) p lbl ms
      ((At exe endPc R F nT).at []) (Frag.at (fun s c => ∃ y, At exe endPc R F (HelloTail.E c2 x29 ra tp y) s c) []) :=
    SegTCS.ofTC (HelloTail.seg_wkTailUNN (Z := fun s c => Z s c []) (ms := ms []) hF hR hal
      (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 (tailCode hp hend) (hK _) hS htp4 htu hhu
      hevu hvu hc2 (Labels.unpkCode hp hend (c0 := cw) (c1 := c1) (B := w.w5) (x29 := x29) (ra := ra) (tp := tp))
      (Labels.hpentry hp) (hsp6 hp) hZW hZU) fun _ _ h => ⟨h.1.toH, h.2, fun _ => h.1.2.2.2⟩
  refine (((h1.seq h2).seq h3).seq h4).mono_post ?_
  rintro s c fs ⟨⟨y, hy⟩, rfl⟩
  cases y
  exact ⟨⟨.ret, tailE_eq c2 x29 ra tp ▸ hy⟩, rfl⟩

end WorkerTCS

end Spike.Lib.A64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerS
