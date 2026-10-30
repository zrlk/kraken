/-
**wake.w on AArch64: the child's stub** (the spawn's
child half): after main's `clone` (`Spike.Lib.WakePreA.cloneAt`, the `svc`
at `wc_main`'s `.sp6` plus 13 instructions), the child thread
(`Spike.Lib.Handover.childAfter`: `x0 = 0`, `sp` the handed stack's top,
`TPIDR_EL0` its TCB, the other registers the parent's, the pc past the
`svc`: `Spike.Lib.A64Handover.child_st`) runs

    cbz x0, .L21_wc_main.child9          -- the child's branch
    .child9: x0 = x9; x1 = x10           -- the worker's two words
             x29 = 0
             bl scc_rt_thr_worker        -- never returns: the thread exits

so its whole run is one segment with the thread rows from the `cbz` to any
fragment: the stub's two blocks (the source stutters) then
`Spike.Lib.A64.Flow.Worker.Wake.Labels.seg_thrWorker` at
`scc_rt_thr_worker`'s label, in the same region (`sp` does not move
before the callee's prologue; no return is needed, so no `call_ndT`).

The `cbz` names a local label of `wc_main`, so the block is taken at
`wc_main`'s label prefix `pfx` (`.L21_wc_main` in wake.w: `pfxM`) as
`Spike.Lib.A64Relabel`'s blocks are (`cbzD`, `dstep_cbz`).

- `childN pfx lab cW A B tp sp0`: the child's node at the `cbz` (offset 0).
- `seg_childStub`: the child, from `childN` to any fragment, in any valid
  layout of `wakeProg`, all code facts decided here.
-/
import Spike.Lib.A64WakeWorkerLabels
import Spike.Lib.A64Relabel

namespace Spike.Lib.A64.Flow.Worker.Wake.Child

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.WakeLabels (wakeProg)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- A `cbz` to a label. -/
def cbzD (t : XReg) (L : Label) : Directive := .instr ⟨.W64, .CBZ (.low (.reg t) .W64) (.label L)⟩

theorem dstep_cbz (lab : Label → Int64) (t : XReg) (L0 L1 : Label) (am : AM) :
    dstep lab am (cbzD t L1) = dstep (rl lab L0 L1) am (cbzD t L0) := by
  simp only [dstep, cbzD, classify, AI.tgt, AI.so, AI.step, rl_self]

/-- The `cbz`'s template, at the placeholder prefix `pfx`. -/
def cbT : List Directive := parseAArch64("cbz x0, pfx.child9")

theorem cbT_eq : cbT = [] ++ [cbzD .X0 "pfx.child9"] := by decide

/-- The `cbz` at prefix `pfx`. -/
def cb (pfx : String) : List Directive := [] ++ [cbzD .X0 (pfx ++ ".child9")]

/-- The stub's call block. -/
def chB : List Directive := parseAArch64("orr x0, xzr, x9
orr x1, xzr, x10
movz x29, #0
bl scc_rt_thr_worker")

block_spec cbT (-128) 0 (⟨0, []⟩ : SO) cbT
block_spec chB (-128) 0 (⟨0, []⟩ : SO) chB

theorem cb_ok {pfx : String} : okBlk (-128) 0 ⟨0, []⟩ (cb pfx) = true := by
  rw [cb, okBlk_snoc (t := cbzD .X0 (pfx ++ ".child9")) (t' := cbzD .X0 "pfx.child9") (fun _ => rfl), ← cbT_eq]
  exact cbT_ok

theorem cb_run {pfx : String} (lab : Label → Int64) (am : AM) :
    arun lab (cb pfx) am = arun (rl lab "pfx.child9" (pfx ++ ".child9")) cbT am := by
  rw [cbT_eq]; exact arun_snoc (by decide) (dstep_cbz _ _ _ _) am

/-! ## The nodes -/

/-- The child's invariant: the source at `cW` (it stutters through the
stub), `x0 = 0`, `x9`/`x10` the worker's two words `A`/`B`, the thread
pointer `tp`, `sp` at `sp0`. -/
def childJ (cW : Ctl) (A B tp sp0 : BitVec 64) (x0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = cW ∧ σ.regs.X0.toBitVec = x0 ∧ σ.regs.X9.toBitVec = A ∧ σ.regs.X10.toBitVec = B ∧
    σ.regs.TPIDR_EL0.toBitVec = tp ∧ σ.regs.SP.toBitVec = sp0

/-- **The child's node** past the `clone`'s `svc` (`cloneAt pfx + 4`), at
the `cbz`: `x0 = 0`. -/
def childN (pfx : String) (lab : Label → Int64) (cW : Ctl) (A B tp sp0 : BitVec 64) : ND :=
  ⟨lab (pfx ++ ".sp6") + Int64.ofNat (4 * 13) + 4, ⟨0, []⟩, childJ cW A B tp sp0 0⟩

/-- The stub's internal nodes. -/
inductive CN where
  | cb | ch

/-- The stub's nodes. -/
def cN (pfx : String) (lab : Label → Int64) (cW : Ctl) (A B tp sp0 : BitVec 64) : CN → ND
  | .cb => childN pfx lab cW A B tp sp0
  | .ch => ⟨lab (pfx ++ ".child9"), ⟨0, []⟩, fun σ c => ∃ x0, childJ cW A B tp sp0 x0 σ c⟩

/-- `wc_main`'s label prefix in wake's certificate. -/
abbrev pfxM : String := ".L21_wc_main"

/-- The stub's blocks in wake's program. -/
abbrev stubIn : Bool :=
  blockAt wakeProg (pfxM ++ ".sp6") 14 (cb pfxM) && blockAt wakeProg (pfxM ++ ".child9") 0 chB

theorem wake_stubIn : stubIn = true := by decide +kernel

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The child's run is one segment with the thread rows** in any valid
layout of `wakeProg`, from its node past the `clone` (`childN`) to any
fragment: the `cbz` (taken, `x0 = 0`), the stub's call block, then the
worker thread (`seg_thrWorker`, whose hypotheses are this one's but for
`hsplit`, `hlim`, which take the stub's `cW` and `sp0`). -/
theorem seg_childStub {Q : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {cW c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hlim : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (sp0 - (48 : Int64).toBitVec).toNat ∧
        (v.setWidth 64).toNat ≤ (sp0 - (48 : Int64).toBitVec - (32 : Int64).toBitVec).toNat)
    (hsplit : LocalRun p cW c1)
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
    SegT p lbl ms (At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label cW A B tp sp0)) Q := by
  have hin := wake_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  let nT : ND := ⟨lab "scc_rt_thr_worker", ⟨0, []⟩, thrJE cW A B tp sp0⟩
  refine SegT.seq (Q := At exe endPc R F nT) ?_
    (seg_thrWorker hp hend hF hR hal hlo hhi hlim hsplit hdm ht hev hv htag hevb hvb hc2 hK hS htp4
      htu hhu hevu hvu hc3 hret3 hSx)
  refine ((fn_segT (N := cN pfxM lab cW A B tp sp0) (E := fun _ : Unit => nT) (fun i => ?_) CN.cb).mono_post
    fun _ _ ⟨_, h⟩ => h)
  cases i
  case cb =>
    refine (seg_nd (by simp [cb]) cb_ok hF hR hal hlo hhi
      (code_of hp hend hcb (by simp only [cN, childN, ofNat4_succ, ofNat4_zero]; rfl)) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT
    obtain ⟨rfl, h0, h9, h10, htp, hsp⟩ := hJ
    rw [cN, childN, cb_run, cbT_run]
    refine .inl ⟨CN.ch, ?_, rfl, ⟨_, rfl, rfl, h9, h10, htp, hsp⟩⟩
    simp only [cN, rl, Reg64s.getRegOrZr] at h0 ⊢
    simp [h0, Reg64s.getRegOrZr, Reg64s.getXReg]
    all_goals rfl
  case ch =>
    refine (seg_nd (by simp [chB]) chB_ok hF hR hal hlo hhi
      (code_of hp hend hch (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT
    obtain ⟨x0, rfl, -, h9, h10, htp, hsp⟩ := hJ
    rw [cN, chB_run]
    refine .inr ⟨(), rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all

end Seg

end Spike.Lib.A64.Flow.Worker.Wake.Child
