/-
**hello.w on AArch64: the child's stub** (B4a, the spawn's
child half): after main's `clone` (the `svc` at `wc_main`'s `.sp6` plus 25
instructions in hello.w's listing, `SccCode.helloProg`), the child thread
(`x0 = 0`, `sp` the handed stack's top, `TPIDR_EL0` its TCB, the other
registers the parent's) runs

    cbz x0, .L22_wc_main.child13          -- the child's branch
    .child13: x0..x5 = x9..x14            -- the worker's six words
              x29 = 0
              bl scc_rt_thr_worker        -- never returns: the thread exits

so its run is one segment with the thread rows from the `cbz` to any
fragment: the stub's two blocks (the source stutters), then the worker
thread from `scc_rt_thr_worker`'s label (`thrJE`), given (`hthr`). wake.w's
(`Spike/Lib/A64WakeChild.lean`) with hello's packet of six registers: the
slice's four words, the cell and the waiter (the spawn's `x9..x14`).

The `cbz` names a local label of `wc_main`, so the block is taken at
`wc_main`'s label prefix (`.L22_wc_main` in hello.w: `pfxM`) as
`Spike.Lib.A64Relabel`'s blocks are (`Wake.Child.cbzD`, `dstep_cbz`).

- `thrJE`: `scc_rt_thr_worker`'s entry, the six words in `x0..x5`.
- `childJ`, `childN pfx lab cW w tp sp0`: the child's node at the `cbz`.
- `stubIn`, `hello_stubIn`: the stub's blocks decided on `helloProg`.
- `seg_childStub`: the child, from `childN` to any fragment `Q`, given the
  worker thread's segment to `Q` (`hthr`; B5's `wc_worker` inside).
-/
import Spike.Lib.A64HelloThr
import Spike.Lib.A64WakeChild

namespace Spike.Lib.A64.Flow.Worker.Hello.Child

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake.Child (cbzD dstep_cbz)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The `cbz`'s template, at the placeholder prefix `pfx`. -/
def cbT : List Directive := parseAArch64("cbz x0, pfx.child13")

theorem cbT_eq : cbT = [] ++ [cbzD .X0 "pfx.child13"] := by decide

/-- The `cbz` at prefix `pfx`. -/
def cb (pfx : String) : List Directive := [] ++ [cbzD .X0 (pfx ++ ".child13")]

/-- The stub's call block. -/
def chB : List Directive := parseAArch64("orr x0, xzr, x9
orr x1, xzr, x10
orr x2, xzr, x11
orr x3, xzr, x12
orr x4, xzr, x13
orr x5, xzr, x14
movz x29, #0
bl scc_rt_thr_worker")

block_spec cbT (-224) 0 (⟨0, []⟩ : SO) cbT
block_spec chB (-224) 0 (⟨0, []⟩ : SO) chB

theorem cb_ok {pfx : String} : okBlk (-224) 0 ⟨0, []⟩ (cb pfx) = true := by
  rw [cb, okBlk_snoc (t := cbzD .X0 (pfx ++ ".child13")) (t' := cbzD .X0 "pfx.child13") (fun _ => rfl),
    ← cbT_eq]
  exact cbT_ok

theorem cb_run {pfx : String} (lab : Label → Int64) (am : AM) :
    arun lab (cb pfx) am = arun (rl lab "pfx.child13" (pfx ++ ".child13")) cbT am := by
  rw [cbT_eq]; exact arun_snoc (by decide) (dstep_cbz _ _ _ _) am

/-! ## The nodes -/

/-- The worker's six words: the slice's four, the cell, the waiter. -/
structure Words where
  (w0 w1 w2 w3 w4 w5 : BitVec 64)

/-- **`scc_rt_thr_worker`'s entry**: the source at `c0` (the worker's
body), the six words in `x0..x5`, the thread pointer `tp`, `sp` at `sp0`. -/
def thrJE (c0 : Ctl) (w : Words) (tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.X0.toBitVec = w.w0 ∧ σ.regs.X1.toBitVec = w.w1 ∧ σ.regs.X2.toBitVec = w.w2 ∧
    σ.regs.X3.toBitVec = w.w3 ∧ σ.regs.X4.toBitVec = w.w4 ∧ σ.regs.X5.toBitVec = w.w5 ∧
    σ.regs.TPIDR_EL0.toBitVec = tp ∧ σ.regs.SP.toBitVec = sp0

/-- The child's invariant: the source at `cW` (it stutters through the
stub), `x0 = x0'`, `x9..x14` the worker's six words, the thread pointer
`tp`, `sp` at `sp0`. -/
def childJ (cW : Ctl) (w : Words) (tp sp0 : BitVec 64) (x0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = cW ∧ σ.regs.X0.toBitVec = x0 ∧ σ.regs.X9.toBitVec = w.w0 ∧ σ.regs.X10.toBitVec = w.w1 ∧
    σ.regs.X11.toBitVec = w.w2 ∧ σ.regs.X12.toBitVec = w.w3 ∧ σ.regs.X13.toBitVec = w.w4 ∧
    σ.regs.X14.toBitVec = w.w5 ∧ σ.regs.TPIDR_EL0.toBitVec = tp ∧ σ.regs.SP.toBitVec = sp0

/-- **The child's node** past the `clone`'s `svc` (`.sp6` plus 25
instructions, plus 4), at the `cbz`: `x0 = 0`. -/
def childN (pfx : String) (lab : Label → Int64) (cW : Ctl) (w : Words) (tp sp0 : BitVec 64) : ND :=
  ⟨lab (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4, ⟨0, []⟩, childJ cW w tp sp0 0⟩

/-- The stub's internal nodes. -/
inductive CN where
  | cb | ch

/-- The stub's nodes. -/
def cN (pfx : String) (lab : Label → Int64) (cW : Ctl) (w : Words) (tp sp0 : BitVec 64) : CN → ND
  | .cb => childN pfx lab cW w tp sp0
  | .ch => ⟨lab (pfx ++ ".child13"), ⟨0, []⟩, fun σ c => ∃ x0, childJ cW w tp sp0 x0 σ c⟩

/-- `wc_main`'s label prefix in hello's listing. -/
abbrev pfxM : String := ".L22_wc_main"

/-- The stub's blocks in hello's program. -/
abbrev stubIn : Bool :=
  blockAt helloProg (pfxM ++ ".sp6") 26 (cb pfxM) && blockAt helloProg (pfxM ++ ".child13") 0 chB

theorem hello_stubIn : stubIn = true := by decide +kernel

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The child's run is one segment with the thread rows** in any valid
layout of `helloProg`, from its node past the `clone` (`childN`) to any
fragment `Q`: the `cbz` (taken, `x0 = 0`), the stub's call block, then the
worker thread from `scc_rt_thr_worker`'s label at `thrJE` (`hthr`, in the
same region: `sp` does not move before the callee's prologue). -/
theorem seg_childStub {Q : Frag isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {cW : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi)
    (hthr : SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
      thrJE cW w tp sp0⟩) Q) :
    SegT p lbl ms (At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label cW w tp sp0)) Q := by
  have hin := hello_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  let nT : ND := ⟨lab "scc_rt_thr_worker", ⟨0, []⟩, thrJE cW w tp sp0⟩
  refine SegT.seq (Q := At exe endPc R F nT) ?_ hthr
  refine ((fn_segT (N := cN pfxM lab cW w tp sp0) (E := fun _ : Unit => nT) (fun i => ?_) CN.cb).mono_post
    fun _ _ ⟨_, h⟩ => h)
  cases i
  case cb =>
    refine (seg_nd (by simp [cb]) cb_ok hF hR hal hlo hhi
      (code_of hp hend hcb (by simp only [cN, childN, ofNat4_succ, ofNat4_zero]; rfl))
      fun σ c hJ => ⟨c, .refl c, ?_⟩).toT
    obtain ⟨rfl, h0, h9, h10, h11, h12, h13, h14, htp, hsp⟩ := hJ
    rw [cN, childN, cb_run, cbT_run]
    refine .inl ⟨CN.ch, ?_, rfl, ⟨_, rfl, rfl, h9, h10, h11, h12, h13, h14, htp, hsp⟩⟩
    simp only [cN, rl, Reg64s.getRegOrZr] at h0 ⊢
    simp [h0, Reg64s.getRegOrZr, Reg64s.getXReg]
    all_goals rfl
  case ch =>
    refine (seg_nd (by simp [chB]) chB_ok hF hR hal hlo hhi
      (code_of hp hend hch (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT
    obtain ⟨x0, rfl, -, h9, h10, h11, h12, h13, h14, htp, hsp⟩ := hJ
    rw [cN, chB_run]
    refine .inr ⟨(), rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

end Seg

end Spike.Lib.A64.Flow.Worker.Hello.Child

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Child.seg_childStub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Child.seg_childStub

namespace Spike.Lib.A64.Flow.Worker.Hello.Child

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Hello
open Spike.Lib.A64.Flow.Ret0 (StOk)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-! ## The worker thread, `wc_worker` given -/

/-- **`wc_worker`'s entry**: the source at `c0`, the six words in `x0..x5`,
the caller's `x29`, the return address `ra` in `x30`, the thread pointer
`tp`. -/
def wcJE (c0 : Ctl) (w : Words) (x29 ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.X0.toBitVec = w.w0 ∧ σ.regs.X1.toBitVec = w.w1 ∧ σ.regs.X2.toBitVec = w.w2 ∧
    σ.regs.X3.toBitVec = w.w3 ∧ σ.regs.X4.toBitVec = w.w4 ∧ σ.regs.X5.toBitVec = w.w5 ∧
    σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- After `scc_rt_thr_worker`'s prologue: the six words in the frame's
first six cells, the thread pointer, `sp` the frame's base. -/
def thrJ (c0 : Ctl) (w : Words) (tp sp0 : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-80) = w.w0 ∧ σ.slot (-72) = w.w1 ∧ σ.slot (-64) = w.w2 ∧ σ.slot (-56) = w.w3 ∧
    σ.slot (-48) = w.w4 ∧ σ.slot (-40) = w.w5 ∧ σ.regs.TPIDR_EL0.toBitVec = tp ∧
    σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The worker thread is one segment with the thread rows** in any valid
layout of `helloProg`, from `scc_rt_thr_worker`'s label (`thrJE`) to any
fragment (the thread exits): the prologue (frame 80), the call of
`wc_worker` (the source's split of its argument across the `.0_entry`
block: `hsplit`), the `exited` release and the `exit`
(`HThrTail.seg_thrTail`). **`wc_worker` is given** (`hwk`, B5): in every
region `[-192, 0)` below the frame (`print`'s abort exit included),
from its label (`wcJE` at `c1`, `sp` the frame's base) to its return (`Wake.WkTailW.E` at `c3`), for every
caller's `x29` and return address. Left to the caller: the stack limit's
facts for the prologue (`hlim`), the `exited` word's (`hSx`), the kernel
model. -/
theorem seg_thrWorker {Q : Frag isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 c1 c3 : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi)
    (hlim : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v → (v.setWidth 64).toNat ≤ (sp0 - (80 : Int64).toBitVec).toNat)
    (hsplit : LocalRun p c0 c1)
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -192 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ x29 ra : BitVec 64,
        SegT p lbl ms (At exe endPc R' F' ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
            fun σ c => wcJE c1 w x29 ra tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec⟩)
          (fun s c => ∃ x, At exe endPc R' F' (Wake.WkTailW.E c3 x29 ra tp x) s c))
    (hK : ms.K = some Scc.Sem.A64.abi) {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hSx : StOk ms F exe endPc (tp + 24#64) 1#64) :
    SegT p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 w tp sp0⟩) Q := by
  let lab := (_root_.Executable.labels exe).label
  refine SegT.seq (thr_prologue_seg hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := HThrHead.tN HThrTail.pfx0 lab (thrJ c0 w tp sp0) (fun _ c => c = c1) .e)
    rfl (by simp only [HThrHead.tN]; decide) fun σ c hJ => ?_) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hlim σ.regs hJ.2.2.2.2.2.2.2.1
    refine ⟨h1, h2, h3, fun v hv => ⟨?_, fun σ' hreg hsl => ?_⟩⟩
    · rw [hJ.2.2.2.2.2.2.2.2]; exact h4 v hv
    obtain ⟨rfl, h0, hx1, hx2, hx3, hx4, hx5, htp, hsp⟩ := hJ
    simp only [HThrHead.tN, thrJ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  refine SegT.seq (HThrHead.seg_thrHead (N := fun _ : Unit => HThrTail.N HThrTail.pfx0 lab c3 tp .sp0)
    (E := (nofun : Empty → ND)) hF hR hal hlo hhi (fun σ c hJ => ⟨c1, hJ.1 ▸ hsplit, rfl⟩) (thECode hp hend)
    (Ne := fun g : BitVec 64 × BitVec 64 => ⟨lab "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c1 w g.1 g.2 tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec⟩)
    (Ex := fun g y => Wake.WkTailW.E c3 g.1 g.2 tp y)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g => hwk R' F' hR' hal' hlo' hhi' hF' hFF g.1 g.2)
    (fun _ => rfl) ?_ ?_) ?_
  · rintro σC c ⟨σ0, c0', ⟨-, h0, h1, h2, h3, h4, h5, htp, hsp⟩, hc, rfl⟩
    refine ⟨(_, _), rfl, ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩ <;>
      simp only [enter, HThrHead.thE_run] <;> assumption
  · rintro ⟨x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨σ0, c0', -, -, rfl⟩ ⟨⟨-, -, -, -, -, -, -, -, h30, -⟩, -⟩
      ⟨hc', -, -, htp'⟩ hreg - -
    refine .inl ⟨(), ?_, by simp only [HThrTail.N, Wake.WkTailW.E]; decide, hc', ?_⟩
    · show (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") = Int64.ofBitVec ra'
      have h30' : ra' = _ := h30.symm
      rw [h30']
      simp only [enter, HThrHead.thE_run]
      rw [hsp0 hp, Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'
  · exact (HThrTail.seg_thrTail hF hR hal (Int.le_trans hlo (by decide)) hhi hK hSx hret3
      (thrCode hp hend)).mono_pre fun s c h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim

end Seg

end Spike.Lib.A64.Flow.Worker.Hello.Child

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Child.seg_thrWorker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Child.seg_thrWorker
