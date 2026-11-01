/-
**hello.w on AArch64: `wc_worker` as one segment** (B5 check-in 3,
part 3b): in any valid layout of `SccCode.helloProg`, from `wc_worker`'s
label (`Child.wcJE`: the six words in `x0..x5`) to its return
(`HelloTail.E`, equal to `Wake.WkTailW.E`: `tailE_eq`) or `print`'s abort
exit (`Body.wX … .abort`, left open): the stack-checked prologue
(`Wk.wc_prologue_seg`), the head (`Body.seg_wkT`: the `.0_entry` block and
the fenced `print`), the tail (`HelloTail.seg_wkTailU`: the source's
`store rel c 1` and `unpark j`), every code fact discharged
(`A64HelloWorker`).

- `wkJ`: the invariant at `.0_entry`: the six words in the frame's cells
  `-96..-56`, the caller's `x29`/return address at `-16`/`-8`, the thread
  pointer;
- `tailE_eq`: `HelloTail.E … .ret = Wake.WkTailW.E … .ret` (the hello copy's exit is
  wake's);
- `seg_wcWorkerH`: the segment. The tail's `c`/`j` are the words `w4`/`w5`
  (cells `-64`/`-56`), `print`'s slice the words `w0..w3`.

- `seg_wcWorkerHA`: `seg_wcWorkerH` with `print`'s abort exit closed by
  `Abort.seg_jabort4T` (`scc_rt_abort` 48 bytes below it, `sp` at `-144`:
  the region reaches `-192`), to the return alone.
-/
import Spike.Lib.A64HelloWorker
import Spike.Lib.A64HelloChild
import Spike.Lib.A64AbortJT

namespace Spike.Lib.A64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-- **`wc_worker`'s invariant at `.0_entry`**: the source at `c0`, the six
words in the cells `-96..-56`, the caller's `x29` and the return address
at `-16`/`-8`, the thread pointer `tp`. -/
def wkJ (c0 : Ctl) (w : Words) (x29 ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-96) = w.w0 ∧ σ.slot (-88) = w.w1 ∧ σ.slot (-80) = w.w2 ∧ σ.slot (-72) = w.w3 ∧
    σ.slot (-64) = w.w4 ∧ σ.slot (-56) = w.w5 ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧
    σ.regs.TPIDR_EL0.toBitVec = tp

/-- **The hello copy's exit is wake's.** -/
theorem tailE_eq (c2 : Ctl) (x29 ra tp : BitVec 64) :
    HelloTail.E c2 x29 ra tp .ret = Wake.WkTailW.E c2 x29 ra tp .ret := rfl

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`wc_worker` is one segment with the thread rows** in any valid layout
of `helloProg`, from its label (`wcJE c0 w x29 ra tp`, and any further
entry fact `X`) to its return (`Wake.WkTailW.E c2`) or `print`'s abort
exit. Left to the caller: the stack limit (`hlim`), `print`'s source side
(`hcall`: the local run into `print`'s predicate `Pr`; `hdone`: `Pr` with
all bytes out is at `cw`; `hm`: the slice's word count; `hsvc`: `print`'s
`write`), the store's and the `unpark`'s source facts (at `cw` and `c1`,
`c`'s address `w.w4`, `j`'s tid `w.w5`), the permit word's (`hS`, `htp4`),
the kernel model. -/
theorem seg_wcWorkerH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 cw c1 c2 : Ctl} {w : Words} {x29 ra tp : BitVec 64} {X : AS → Prop}
    {Pr Qa : AS → Nat → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 w x29 ra tp σ c → X σ →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat)
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ, wkJ c0 w x29 ra tp σ c0 →
      ∃ c', LocalRun p c0 c' ∧ Pr (Body.wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hdone : ∀ σ, wkJ c0 w x29 ra tp σ c0 → ∀ c',
      Pr (Body.wkC (_root_.Executable.labels exe).label σ)
        (Body.wkC (_root_.Executable.labels exe).label σ).regs.X1.toBitVec.toNat c' → c' = cw)
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .call).J σC c →
      SegT p lbl ms (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (ht : cw.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt cw.env a = some (ty, [wa]))
    (hv : ValRep lbl wa.val w.w4.toNat) (htag : ∃ sa, wa.val = .loc sa 0)
    (hevb : TermRun.evalAt cw.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: cw.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val w.w5.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩)
      (fun s c => (∃ y, At exe endPc R F (Wake.WkTailW.E c2 x29 ra tp y) s c) ∨
        At exe endPc R F (Body.wX (_root_.Executable.labels exe).label Qa
          (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort) s c) := by
  refine SegT.mono_post (Q := fun s c => (∃ y, At exe endPc R F (HelloTail.E c2 x29 ra tp y) s c) ∨
      At exe endPc R F (Body.wX (_root_.Executable.labels exe).label Qa
        (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort) s c) ?_
    fun s c h => h.imp_left fun ⟨y, hy⟩ => by cases y; exact ⟨.ret, tailE_eq c2 x29 ra tp ▸ hy⟩
  refine SegT.seq (wc_prologue_seg hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .e)
    rfl (by simp only [Body.wN]; decide) fun σ c hJ => ?_) ?_
  · obtain ⟨hJ, hX⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := hlim σ c hJ hX
    refine ⟨h1, h2, h3, fun v hv => ⟨h4 v hv, fun σ' hreg hsl => ?_⟩⟩
    obtain ⟨rfl, h0, hx1, hx2, hx3, hx4, hx5, h29, h30, htp⟩ := hJ
    simp only [Body.wN, wkJ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  refine Body.seg_wkT hF hR hal hlo hhi (wkECode hp hend) (hgap hp) (printCode hp hend (c0 := c0) (x29 := x29)
    (ra := ra)) (printEntry hp) ?_ ?_ hsvc ?_
    (HelloTail.seg_wkTailU hF hR hal hlo hhi hdm ht hev hv htag hevb hvb hc1 (tailCode hp hend) hK hS htp4
      htu hhu hevu hvu hc2 (Labels.unpkCode hp hend (c0 := cw) (c1 := c1) (B := w.w5) (x29 := x29) (ra := ra)
        (tp := tp)) (Labels.hpentry hp) (hsp6 hp))
  · rintro σ c ⟨-, -, -, h80, -⟩
    rw [h80]; exact hm
  · rintro σ c hJ
    obtain rfl := hJ.1
    exact hcall σ hJ
  · rintro σ0 c0' hJ
    obtain rfl := hJ.1
    exact ⟨hJ.2.2.2.2.2.2.2.1, hJ.2.2.2.2.2.2.2.2.1, hJ.2.2.2.2.2.1, hJ.2.2.2.2.2.2.1,
      hJ.2.2.2.2.2.2.2.2.2, hdone σ0 hJ⟩

/-- **`wc_worker` is one segment with the thread rows, its `print` abort
closed** (`seg_wcWorkerH`, then `Abort.seg_jabort4T` at `print`'s abort
exit, `sp` at `-144`, the dispatcher below to `-192`: `hlo`): from its
label to its return alone. `hstub`: the write abort path's obligations
there (`Abort.StubWW.triv`). -/
theorem seg_wcWorkerHA (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 cw c1 c2 : Ctl} {w : Words} {x29 ra tp : BitVec 64} {X : AS → Prop}
    {Pr Qa : AS → Nat → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 w x29 ra tp σ c → X σ →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat)
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ, wkJ c0 w x29 ra tp σ c0 →
      ∃ c', LocalRun p c0 c' ∧ Pr (Body.wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hdone : ∀ σ, wkJ c0 w x29 ra tp σ c0 → ∀ c',
      Pr (Body.wkC (_root_.Executable.labels exe).label σ)
        (Body.wkC (_root_.Executable.labels exe).label σ).regs.X1.toBitVec.toNat c' → c' = cw)
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .call).J σC c →
      SegT p lbl ms (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (ht : cw.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt cw.env a = some (ty, [wa]))
    (hv : ValRep lbl wa.val w.w4.toNat) (htag : ∃ sa, wa.val = .loc sa 0)
    (hevb : TermRun.evalAt cw.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: cw.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val w.w5.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    (hstub : ∀ m0 σC c0',
      (Body.wX (_root_.Executable.labels exe).label Qa
        (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort).J σC c0' →
      Abort.Disp.StubWW (fun _ _ => True) (fun _ _ => False) p lbl ms exe endPc (R.callee (-144) (-48) 0)
        (fun m => F m ∧ CKept R (-144) (-48) 0 m0 m ∧ Abs R ⟨-144, []⟩ m0 σC) c0') :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩)
      (fun s c => ∃ y, At exe endPc R F (Wake.WkTailW.E c2 x29 ra tp y) s c) :=
  ((seg_wcWorkerH hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi hlim hm hcall hdone hsvc hdm ht hev hv htag
    hevb hvb hc1 hK hS htp4 htu hhu hevu hvu hc2).mono_post fun _ _ h => h.symm).seq_or
    (Abort.seg_jabort4T (Q := fun s c => ∃ y, At exe endPc R F (Wake.WkTailW.E c2 x29 ra tp y) s c)
      (nC := Body.wX (_root_.Executable.labels exe).label Qa
        (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort)
      rfl (fun σ _ h => by rw [h.1]; rfl) hF hR hal (by show R.lo ≤ -144 - 48; omega)
      (by show (-144 : Int) < R.hi; omega) (by show (-144 : Int) % 16 = 0; decide) hK hstub) |>.mono_post fun _ _ h => h.elim id id

end Seg

end Spike.Lib.A64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerH

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerHA
