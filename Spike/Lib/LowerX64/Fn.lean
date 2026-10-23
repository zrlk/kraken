/-
**A lowered parameterless function is one segment** (x86-64), symbolic in
the frame; the twin of `Spike/Lib/LowerA64/Fn.lean`.

`fn0_seg`: `prologue_body_seg_of` (the emitted prologue, `proInC`) then
`body_seg` (the lowered body, its code from `bodyIn` by `bodyCode_of`),
from the function's label (`%rsp` at 0) to the return's exit at the saved
return address or the overflow abort label. The source's body `e` is
lowered by `lower0` from the environment `env` (fresh above `n`); the
prologue's edge gives the body's node invariant at its entry.

Where x86-64 differs from AArch64: the entry is in the region `R` based at
the entry `%rsp`, the body and its exits in `rbR R` (based at the frame
record, `8` lower; the exit's `%rsp` at `16` there is `8` in `R`, past the
return address); the return address is the entry's top cell (`σ.slot 0`);
the prologue's cells' sizes are parameters.
-/
import Spike.Lib.LowerX64.ProIn
import Spike.Lib.LowerX64.BodyIn

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW ofNat_zero')
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.Form (SEnv)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 Res)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}

/-- **A lowered parameterless function is one segment** in any valid
layout of cells with its prologue (`proInC`) and its body (`bodyIn` after
`entry`): from `fn` to `retN` or `abortN` (at a table `i` holding the
lowering's environments' immediates, `hImm`), given the prologue's
states inside `W` (`hWp`) and the body's blocks' (`InBody`) at its nodes
(`hWb`) and pending stores (`hWs`). -/
theorem fn0_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hp : Lays exe cells) (hend : endPc = endOf exe cells) {fn entry : String} {zl zf z1 z2 zs : Nat}
    (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true)
    {e : Expr} {env : Scc.Lower.Env} {n : Nat} {r : Res} (hr : lower0 env n e = some r) (hfr : Fresh env n)
    (hbody : bodyIn cells fr entry 0 r.insts r.ret = true)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (hImm : ∀ q ∈ lowerEnvs env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl}
    (hWp : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [] J)
    (hWb : ∀ pc t s blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label cells fr entry r.insts r.ret pc blk →
      BlkW W K exe endPc (rbR R) F (bodyN p lbl fr fp ra c0 pc t s) blk)
    (hWs : ∀ pc t s k blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label cells fr entry r.insts r.ret pc blk →
      BlkW W K exe endPc (rbR R) F (pendN p lbl fr fp ra c0 pc t s k) blk)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        ms.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧
      (∀ sl, NJ p lbl (rsOf fr) e (ofEnv env) sl c) ∧ LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc (rbR R) F (retN p lbl fp ra c0) s c ∨
        At exe endPc (rbR R) F (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c) := by
  have hcode := bodyCode_inBody (fr := fr) hp hend hbody
  exact (prologue_body_seg_of h1 hp hend hpro hF hR hlo hhi hWp hedge).seq
    (body_seg hf h1 (rbR_fstable hR (by omega) (by omega) hF) (rbR_ok hR (by omega) (by omega))
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
      (fun _ _ h => h.1) (fun pc t s blk h => hWb pc t s blk h.1 h.2)
      (fun pc t s k blk h => hWs pc t s k blk h.1 h.2) e env n r _ hr hfr hcode hImm)

end Fn

end Spike.Lib.LowerX64
