/-
**A lowered parameterless function is one segment** (AArch64), symbolic
in the frame.

`fn0_seg`: `prologue_body_seg_of` (the emitted prologue, `proInC`) then
`body_seg` (the lowered body, its code from `bodyIn` by `bodyCode_of`),
from the function's label (`sp` at 0) to the return's exit at the saved
return address or the overflow abort label. The source's body `e` is
lowered by `lower0` from the environment `env` (fresh above `n`); the
prologue's edge gives the body's node invariant at its entry.
-/
import Spike.Lib.LowerA64.ProIn
import Spike.Lib.LowerA64.BodyIn

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Form (NodeJ SEnv)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 Res)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A lowered parameterless function is one segment** in any valid
layout of a program with its prologue (`proInC`) and its body (`bodyIn`
after `entry`): from `fn` to `retN` or `abortN` (at a table `i` holding
the lowering's environments' immediates, `hImm`), given the prologue's
states inside `W` (`hWp`) and the body's blocks' (`InBody`) at its nodes
(`hWb`) and pending stores (`hWs`). -/
theorem fn0_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hp : Lays exe prog) (hend : endPc = endOf exe prog) {fn entry : Label}
    (hpro : proInC prog cx fn entry = true)
    {e : Expr} {env : Scc.Lower.Env} {n : Nat} {r : Res} (hr : lower0 env n e = some r) (hfr : Fresh env n)
    (hbody : bodyIn prog cx entry 0 r.insts r.ret = true)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (hImm : ∀ q ∈ lowerEnvs env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl}
    (hWp : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) [] J)
    (hWb : ∀ pc t s blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label cx entry r.insts r.ret pc blk →
      BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc t s) blk)
    (hWs : ∀ pc t s k blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label cx entry r.insts r.ret pc blk →
      BlkW W K exe endPc R F (pendN p lbl cx fp ra c0 pc t s k) blk)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        ms.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, ms.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧
      (∀ sl, NJ p lbl (rsOf cx) e (ofEnv env) sl c) ∧ LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
        At exe endPc R F (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c) := by
  have hcode := bodyCode_inBody (cx := cx) hp hend hbody
  exact (prologue_body_seg_of hf h1 h16 hp hend hpro hF hR hal hlo hhi hWp hedge).seq
    (body_seg hf h1 h16 hF hR hal hlo hhi (fun _ _ h => h.1) (fun pc t s blk h => hWb pc t s blk h.1 h.2)
      (fun pc t s k blk h => hWs pc t s k blk h.1 h.2) e env n r _ hr hfr hcode hImm)

end Fn

end Spike.Lib.LowerA64
