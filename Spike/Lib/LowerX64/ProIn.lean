/-
**The emitted prologue's placement, from the function's frame** (x86-64);
the twin of `Spike/Lib/LowerA64/ProIn.lean`.

`proInC cells fr fn entry zl zf z1 z2 zs`: `prologueIn` with every label and
constant taken from the emitter's frame `fr` (`emitFunc` for a function with
`checkStack` and no parameters): the stack check at `labelOf fr.fn "chk"`,
the frame `fr.size`, the thread's limit at `Scc.IR.Tcb.stackLimit`, the
branch to `labelOf fr.fn "stk"` (the grow stub with growth, the abort
without: one label either way, `proL`). `prologue_body_seg_of` is
`prologue_body_seg` from it. The check is a closed Boolean, discharged per
program by `decide +kernel`.

Where x86-64 differs from AArch64:
- the prologue's cells' sizes (`zl` the `lea`, `zf` the limit's load, `z1`
  `z2` the compare and branch, `zs` the `sub`) are parameters of the check,
  read off the listing;
- the stack check's label is emitted only with growth (`fr.maps`), and the
  `sub` only for a frame of positive size; without either `prologueIn`
  cannot hold and `proInC` is false.
-/
import Spike.Lib.LowerX64.Prologue

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (prologueIn XProW)
open Scc.Emit.X64 (labelOf)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.Form (SEnv)
open Spike.Lib.LowerNode

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}

/-- `prologue_body_seg` from `proInC`. -/
theorem prologue_body_seg_of {fr : Scc.Emit.X64.Frame} (h1 : fr.size ≤ 2 ^ 31)
    (hp : Lays exe cells) (hend : endPc = endOf exe cells) {fn entry : String} {zl zf z1 z2 zs : Nat}
    (hin : proInC cells fr fn entry zl zf z1 z2 zs = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl} {t : Expr} {s : SEnv}
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [] J)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        ms.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ (∀ sl, NJ p lbl (rsOf fr) t s sl c) ∧ LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc (rbR R) F (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s)) :=
  prologue_body_seg h1 hp hend hin hF hR hlo hhi hW hedge

end Pro

end Spike.Lib.LowerX64
