/-
**The emitted prologue's placement, from the function's context** (AArch64).

`proInC prog c fn entry`: `prologueIn` with every label and constant taken
from the emitter's context `c` (`emitFunc`'s `alloc`/`save` for a function
with `checkStack` and no parameters): the stack check at `c.local
"stack_check"`, the frame `c.frame`, the thread's limit at
`Scc.IR.Tcb.stackLimit`, the branch to `c.local "stack_grow"` (a program with
growth) or `c.local "abort_stack"`. `prologue_body_seg_of` is
`prologue_body_seg` from it. The check is a closed Boolean, discharged per
program by `decide +kernel`.

The stack check's label is emitted only under `c.maps`; without it
`prologueIn`'s first gap (function label, then check label) cannot hold and
`proInC` is false.
-/
import Spike.Lib.LowerA64.Prologue
import Spike.Lib.LowerA64.Checks

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Form (NodeJ SEnv)
open Spike.Lib.LowerNode

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}

/-- `prologue_body_seg` from `proInC`. -/
theorem prologue_body_seg_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    (h16 : cx.frame % 16 = 0) {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {fn entry : Label}
    (hin : proInC prog cx fn entry = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl} {t : Expr} {s : SEnv}
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt cx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) [] J)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        ms.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, ms.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt cx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧ (∀ sl, NJ p lbl (rsOf cx) t s sl c) ∧
      LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F (bodyN p lbl cx fp ra c0 ((_root_.Executable.labels exe).label entry) t s)) :=
  prologue_body_seg hf h1 h16 hp hend hin hF hR hal hlo hhi hW hedge

end Pro

end Spike.Lib.LowerA64
