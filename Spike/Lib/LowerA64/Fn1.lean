/-
**A lowered call-free `Accepted1` function is one segment** (AArch64),
symbolic in the frame: the twin of `fn0_seg` (`Spike/Lib/LowerA64/Fn.lean`).

`fn1_seg`: `prologue_body_seg_of` (the emitted prologue, `proInC`) then
`body1_seg` (the lowered body's blocks at a code predicate `Cd`: the open
block's code at the entry's label, `Code1`, and the later blocks',
`BlocksCode`), from the function's label (`sp` at 0) to the return's exit
at the saved return address or the overflow abort label.
-/
import Spike.Lib.LowerA64.ProIn
import Spike.Lib.LowerA64.Body1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Form (NodeJ SEnv)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower1 Res1)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A lowered call-free `Accepted1` function is one segment** in any
valid layout of a program with its prologue (`proInC`): from `fn` to `retN`
or `abortN` (at a table `i` holding the lowering's environments'
immediates, `hImm`), given the body's code at a code predicate `Cd` in the
code (`hCd`; the open block at the entry's label, `hcode`, the later
blocks at theirs, `hbl`), the prologue's states inside `W` (`hWp`) and the
body's blocks' at its nodes (`hWb`) and pending stores (`hWs`). -/
theorem fn1_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {fn entry : Label}
    (hpro : proInC prog cx fn entry = true)
    {e : Expr} {env : Scc.Lower.Env} {n : Nat} {r : Res1} (hr : lower1 env n e = some r) (hfr : Fresh env n)
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hcode : Code1 cx Cd ((_root_.Executable.labels exe).label entry) r.insts r.term)
    (hbl : BlocksCode cx Cd (_root_.Executable.labels exe).label r.blocks)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (hImm : ∀ q ∈ lowerEnvs1 env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl}
    (hWp : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) [] J)
    (hWb : ∀ pc t s blk, Cd pc blk → BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc t s) blk)
    (hWs : ∀ pc t s k blk, Cd pc blk → BlkW W K exe endPc R F (pendN p lbl cx fp ra c0 pc t s k) blk)
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
        At exe endPc R F (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c) :=
  (prologue_body_seg_of hf h1 h16 hp hend hpro hF hR hal hlo hhi hWp hedge).seq
    (body1_seg hf h1 h16 hF hR hal hlo hhi hCd hWb hWs e env n r _ hr hfr hcode hbl hImm)

end Fn

end Spike.Lib.LowerA64
