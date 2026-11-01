/-
**A jump to `scc_rt_abort(4)` with the thread rows** (AArch64; B5, for
`print`'s abort exit under `wc_worker`): `Disp.seg_jabort4W` at the
trivial `W` (no outside moves), forgotten to `Seg` (`SegW.toSeg`) and lifted
to the thread rows (`Seg.toT`). `seg_jabort4W` is not changed.

- `StubWW.triv`: the write abort path's obligations at the trivial `W`
  from the code (dispatcher and stub), the stub's `write` call as a `Seg`
  and its exit at an abort site (`BlkW.triv`, `NodeW.triv`,
  `SegW.ofSeg`);
- `seg_jabort4T`: from a node `nC` at `scc_rt_abort` with `x0 = 4`, a
  `SegT` segment to any fragment, the dispatcher in the region below
  `nC.o.sp` (`R.lo ≤ nC.o.sp - 48`).
-/
import Spike.Lib.A64AbortWriteW
import Spike.Lib.SegThr

namespace Spike.Lib.A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **The write abort path's obligations at the trivial `W`**: the
dispatcher's and the stub's code, the stub's `write` call as a segment, its
exit at an abort site. -/
theorem StubWW.triv (dcode : Disp.Code c0 exe endPc) (scode : Abort.Code write c0 b1Write exe endPc)
    (svc : Seg p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .svc))
      (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .n5)))
    (ab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label write c0 .ex) s c → ms.abortAt s) :
    Disp.StubWW (fun _ _ => True) (fun _ _ => False) p lbl ms exe endPc R F c0 :=
  ⟨dcode, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    scode, BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv, BlkW.triv, NodeW.triv, SegW.ofSeg svc, ab⟩

/-- **A jump to `scc_rt_abort` with `x0 = 4` does not return, with the
thread rows**: `Disp.seg_jabort4W` at the trivial `W`, as a `SegT`
segment to any fragment, given the write abort path's obligations
(`StubWW.triv`) for each caller's state `m0`, `σC` and source control. -/
theorem seg_jabort4T [Kraken.Executable.ValidLayout exe] {Q : Frag isaLSE2} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 4)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 →
      Disp.StubWW (fun _ _ => True) (fun _ _ => False) p lbl ms exe endPc (R.callee nC.o.sp (-48) 0)
        (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) c0) :
    SegT p lbl ms (At exe endPc R F nC) Q :=
  Seg.toT (Disp.seg_jabort4W hpc hX0 hF hR hal hlo hkc h16 hK hstub).toSeg

end Spike.Lib.A64.Abort

/-- info: 'Spike.Lib.A64.Abort.seg_jabort4T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Abort.seg_jabort4T
