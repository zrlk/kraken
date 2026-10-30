/-
**wake.w's heap abort from `wc_main`'s allocation** (AArch64): the
allocator's full exit `wX .abort` (`Spike/Lib/A64WakeWcPre.lean`) jumps to
`scc_rt_abort` with `x0 = 2` at `-240` in `wc_main`'s region `R`; the
dispatcher and `scc_rt_abort_heap` run in the region below it
(`Abort.Disp.seg_jabort2RW`), and do not return.

- `WcHAbStub`: the heap abort path's obligations below `-240` for every
  source control of the node.
- `wc_heapAb_segWS`: the heap abort does not return, at any frames, into
  any fragment.
-/
import Spike.Lib.A64WakeWcPre
import Spike.Lib.A64AbortHeapS
import Spike.Lib.A64AbortHeapRW

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow

section Tail

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The heap abort's obligations** in `wc_main`'s region `R` under `F`,
at the frames `fs`: the heap abort path's below `-240` (`wX .abort`'s
offset) for every caller's state and source control of the node. -/
def WcHAbStub (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (J0 : AS → Ctl → Prop) : Prop :=
  ∀ m0 σC c0, (wX (ms fs) (_root_.Executable.labels exe).label J0 .abort).J σC c0 →
    Abort.Disp.StubHRW (fun s c => W s c fs) K p lbl (ms fs) exe endPc (R.callee (-240) (-48) 0)
      (fun m => F m ∧ CKept R (-240) (-48) 0 m0 m ∧ Flow.Abs R ⟨-240, []⟩ m0 σC) c0
      ((_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full" + 8).toBitVec

/-- **The heap abort does not return**: from `wX .abort` in `wc_main`'s
region at the frames `fs`, into any fragment (`seg_jabort2RW` at `-240`; the
return address `x30` is `wX .abort`'s). -/
theorem wc_heapAb_segWS {W : FragS isaLSE2} {K : State → State → Prop} {fs : List TermRun.Frame}
    {J0 : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : (ms fs).K = some Scc.Sem.A64.abi) (hstub : WcHAbStub W K p lbl ms exe endPc R F fs J0)
    (Q : FragS isaLSE2) :
    SegWS W K p lbl ms ((At exe endPc R F (wX (ms fs) (_root_.Executable.labels exe).label J0 .abort)).at fs) Q :=
  SegWS.liftS_noret fs (Abort.Disp.seg_jabort2RW (Q := fun _ _ => False)
    (nC := wX (ms fs) (_root_.Executable.labels exe).label J0 .abort) rfl
    (fun σ c h => by show σ.regs.X0.toBitVec.toNat = 2; rw [h.1]; rfl) (fun σ c h => h.2.1)
    hF hR hal (by show R.lo ≤ -240 - 48; omega) (by show (-240 : Int) < R.hi; omega)
    (by show (-240 : Int) % 16 = 0; decide) hK hstub) (fun _ _ h => h) Q

end Tail

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wc_heapAb_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wc_heapAb_segWS

end Spike.Lib.A64.Flow.WakeWc
