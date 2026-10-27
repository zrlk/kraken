/-
**A lowered `Accepted1` function with calls is one segment at fixed frames**
(AArch64, H7a calls): the prologue (`prologue_seg_ofW`) lifted at the frames
`fs`, then the body: a body segment from the body's entry node to its exits
`ExitC` (`bodyC_segS` with plain calls, or any other provider). The
twin of `Spike/Lib/LowerX64/FnC.lean`.

- `ParamSpill`: the prologue's parameter spill (`spills`' result `ps`) for
  the parameter registers `prs`: none, or `x0`'s store at the parameter's
  cell, below the saved pair; `paramSpill_of_spills` from `spills` at an
  `Accepted1` code block's parameter registers.
- `prologue_body_segTP`: the prologue with its spill at a node with the
  thread pointer: the prologue keeps `TPIDR_EL0` (`tp_frRegs`), so the
  body's entry node has it (`ND.withTp`), and the parameter's cell holds the
  entry's `x0`.
- `fnC_segB`: from the function's label at `fs` (`sp` at 0, the entry
  invariant `J` pinning the thread pointer to `tp`) to the body's exits,
  given the body's segment (`hbody`).
-/
import Spike.Lib.LowerA64.ProIn
import Spike.Lib.LowerA64.BodyC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Form (SEnv)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lowerC Res1)

set_option linter.unusedSimpArgs false

/-- **The prologue's parameter spill** `ps` for the parameter registers
`prs` of a function with frame `cx`: no parameter and no store, or one
parameter `pr` stored from `x0` at offset `o` from the new `sp`, its cell
`-frame + o` (`rsOf cx pr`), below the saved pair. -/
def ParamSpill (cx : FnCtx) (ps : List (XReg × Int64)) (prs : List Scc.IR.Reg) : Prop :=
  (ps = [] ∧ prs = []) ∨ ∃ pr o, ps = [(.X0, o)] ∧ prs = [pr] ∧
    (∀ k, rsOf cx pr = some k → k = -(cx.frame : Int) + o.toInt) ∧ -(cx.frame : Int) + o.toInt ≤ -24 ∧
    offOk (-(cx.frame : Int)) 0 (-(cx.frame : Int) + o.toInt) = true

/-- **An `Accepted1` code block's spill is a `ParamSpill`**: `spills` at its
parameter registers `params1R d`. -/
theorem paramSpill_of_spills {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {d : Decl} {ps : List (XReg × Int64)}
    (h : Scc.Cert.Code1A64.spills cx (Scc.Lower.Inv.params1R d) = some ps) :
    ParamSpill cx ps (Scc.Lower.Inv.params1R d) := by
  unfold Scc.Lower.Inv.params1R at h ⊢
  generalize s!"{d.arg}.{0}" = pr at h ⊢
  split
  · next hi =>
    simp only [hi, ite_true] at h
    refine .inr ?_
    unfold Scc.Cert.Code1A64.spills at h
    split at h
    · cases ho : cx.slotOff pr with
      | error e => simp [argRegs, xregs, ho, Except.toOption] at h
      | ok o =>
        simp [argRegs, xregs, ho, Except.toOption] at h
        subst h
        obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
        have hoo : (Int64.ofInt o).toInt = o := toInt_ofInt_small (by omega) (by omega)
        refine ⟨pr, Int64.ofInt o, rfl, rfl, fun k hk => ?_, by omega, ?_⟩
        · simp only [rsOf, ho, Option.some.injEq] at hk
          rw [hoo]; omega
        · rw [hoo]; simp only [offOk, decide_eq_true_eq]; omega
    · cases h
  · next hi =>
    simp only [Bool.not_eq_true] at hi
    simp only [hi, Bool.false_eq_true, ite_false] at h
    refine .inl ⟨?_, rfl⟩
    unfold Scc.Cert.Code1A64.spills at h
    split at h
    · simpa using h.symm
    · cases h

/-- **A `ParamSpill`'s stores are cells of the frame** (`proW_bodyS`'s and
`prologue_seg_ofW`'s `hps`). -/
theorem ParamSpill.hps {cx : FnCtx} (h1 : cx.frame ≤ 4095) {ps : List (XReg × Int64)} {prs : List Scc.IR.Reg}
    (h : ParamSpill cx ps prs) :
    ∀ q ∈ ps, offOk (-(Int64.ofInt cx.frame).toInt) 0 (-(Int64.ofInt cx.frame).toInt + q.2.toInt) = true := by
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  rw [hF64]
  rcases h with ⟨rfl, -⟩ | ⟨pr, o, rfl, -, -, -, hok⟩
  · intro q hq; cases hq
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact hok

/-- The prologue keeps the thread pointer. -/
theorem tp_frRegs (Z : Int64) (v : BitVec 64) (σ : AS) :
    (frRegs Z (ldStep .X10 v { σ with regs := chkRegs Z σ.regs }).regs).TPIDR_EL0 = σ.regs.TPIDR_EL0 := by
  simp [frRegs, ldStep, chkRegs, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Ret0.setXReg_TPIDR]

/-- The prologue keeps `x0`. -/
theorem x0_frRegs (Z : Int64) (v : BitVec 64) (σ : AS) :
    (frRegs Z (ldStep .X10 v { σ with regs := chkRegs Z σ.regs }).regs).X0 = σ.regs.X0 := by
  simp [frRegs, ldStep, chkRegs, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}

/-- **The prologue with its parameter spill at a node with the thread
pointer** (`prologue_seg_ofW` at the frame `cx.frame`, the limit at
`Tcb.stackLimit`): every entry state's thread pointer `tp` (`htp`) is kept,
and the parameter registers' cells (`prs`, `ParamSpill`) hold the entry's
`x0`, so the source relation `NJ` is needed only at cells with it
(`hedge`). -/
theorem prologue_body_segTP {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {fn entry : Label}
    {ps : List (XReg × Int64)} {prs : List Scc.IR.Reg}
    (hin : prologueIn prog fn (cx.local "stack_check") entry (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps = true)
    (hsp : ParamSpill cx ps prs)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl} {t : Expr} {s : SEnv} {tp : UInt64}
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps J)
    (htp : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = tp)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        ms.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, ms.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧
      (∀ sl, (∀ pr ∈ prs, ∀ k, rsOf cx pr = some k → sl k = σ.regs.X0.toBitVec) → NJ p lbl (rsOf cx) t s sl c) ∧
      LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F ((bodyN p lbl cx fp ra c0 ((_root_.Executable.labels exe).label entry) t s).withTp tp)) := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  refine prologue_seg_ofW hp hend hin (by rw [hF64]; omega) (by rw [hF64]; omega) hF hR hal
    (by rw [hF64]; exact hlo) hhi (hsp.hps h1) rfl (oF_le_oFr cx hF64) hW fun σ c hJ => ?_
  obtain ⟨⟨hrt, hmp, hld, hG⟩, h29, h30, hN, hc0⟩ := hedge σ c hJ
  refine ⟨hrt, hmp, hld, fun v hv => ⟨hG v hv, fun σ' hr hsl => ⟨⟨hN _ ?_, ?_, hc0⟩, ?_⟩⟩⟩
  · rcases hsp with ⟨rfl, rfl⟩ | ⟨pr, o, rfl, rfl, hpr, -, -⟩
    · intro pr hpr; cases hpr
    · intro pr' hpr' k hk
      simp only [List.mem_singleton] at hpr'
      subst hpr'
      rw [hpr k hk, hsl]
      simp only [stSlots, hF64, upd_apply, ite_true]
      rw [hr]
      simp [Reg64s.getXReg, x0_frRegs]
  · rcases hsp with ⟨rfl, -⟩ | ⟨pr, o, rfl, -, -, ho, -⟩
    · simp only [stSlots] at hsl
      rw [hsl, ← h29, ← h30]
      exact frJ_frSlot σ
    · simp only [stSlots, hF64] at hsl
      have e16 : (-16 : Int) ≠ -(cx.frame : Int) + o.toInt := by omega
      have e8 : (-8 : Int) ≠ -(cx.frame : Int) + o.toInt := by omega
      rw [hsl, ← h29, ← h30]
      constructor <;> simp [upd_apply, e16, e8, frSlot]
  · rw [hr, tp_frRegs]; exact htp σ c hJ

end Pro

section FnC

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A lowered `Accepted1` function with calls is one segment at the
frames `fs`, from its body's segment**: from the function's label (`sp` at
0, the entry invariant `J` with the thread pointer `tp`, `htp`) through the
prologue (`hpro`, its spill `hsp`, its states inside `W₀`, `hWpro`, its
limit facts and the entry's ghosts, `hedge`) and the body (`hbody`, e.g.
`bodyC_segS` with plain calls) to the body's exits (`ExitC`): the
return's exit at `fs` after the source's frame run from the ghost `c0`, or
an abort `Ab`. -/
theorem fnC_segB {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {fn entry : Label}
    {ps : List (XReg × Int64)} {prs : List Scc.IR.Reg}
    (hpro : prologueIn prog fn (cx.local "stack_check") entry (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps = true)
    (hsp : ParamSpill cx ps prs)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {fs : List TermRun.Frame} {W₀ : Frag isaLSE2}
    (hW₀ : ∀ s c, W₀ s c → W s c fs) {tp : UInt64} {Ab : FragS isaLSE2} {e : Expr} {env : Scc.Lower.Env}
    {c0 : Ctl}
    (hbody : SegWS W K p lbl ms
      ((At exe endPc R F ((bodyN p lbl cx fp ra c0 ((_root_.Executable.labels exe).label entry) e
        (ofEnv env)).withTp tp)).at fs)
      (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab))
    {J : AS → Ctl → Prop}
    (hWpro : ProW W₀ K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label fn) (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) ps J)
    (htp : ∀ σ c, J σ c → σ.regs.TPIDR_EL0 = tp)
    (hedge : ∀ σ c, J σ c →
      ((ms fs).rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        (ms fs).mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, (ms fs).G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧
      (∀ sl, (∀ pr ∈ prs, ∀ k, rsOf cx pr = some k → sl k = σ.regs.X0.toBitVec) →
        NJ p lbl (rsOf cx) e (ofEnv env) sl c) ∧
      LocalRun p c0 c) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC p lbl exe endPc R F fp ra tp c0 fs Ab) :=
  (SegWS.liftS fs (prologue_body_segTP hf h1 h16 hp hend hpro hsp hF hR hal hlo hhi hWpro htp hedge) hW₀).seq
    hbody

end FnC

end Spike.Lib.LowerA64
