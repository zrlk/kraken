/-
**The heap abort path on AArch64 at any call depth**: `seg_heapW`,
`Disp.seg_disp2W`, `Disp.seg_abort2W` and `Disp.seg_jabort2W`
(`Spike/Lib/A64AbortHeapW.lean`) as segments with the source thread's
frames (`SegWS`, `Spike/Lib/SegS.lean`), at any fixed frames `frs`: the same
premises, under the memory side at `frs` (`msS frs = ms`), inside any `W'`
that contains `W` at `frs`. Each is `SegWS.liftS` of the one-frame rule; the
paths that do not return (`SegWS.liftS_noret`) end in any fragment with
frames.
-/
import Spike.Lib.A64AbortHeapW
import Spike.Lib.SegS

namespace Spike.Lib

namespace SegWS

open CoreTerm Kraken Kraken.Promising

variable {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {ms : List TermRun.Frame → MemSide I}

/-- **A segment that does not return, at fixed frames**: a one-frame
segment into no pair is, at frames `fs`, a segment into any fragment with
frames. -/
theorem liftS_noret {W₀ : Frag I} {P₀ : Frag I} (fs : List TermRun.Frame)
    (h : SegW W₀ K p lbl (ms fs) P₀ (fun _ _ => False)) (hW : ∀ s c, W₀ s c → W s c fs) (Q : FragS I) :
    SegWS W K p lbl ms (P₀.at fs) Q :=
  (liftS fs h hW).mono_post fun _ _ _ h => h.1.elim

end SegWS

namespace A64.Abort

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **`seg_heapW` at any call depth.** -/
theorem seg_heapWS {W : Frag isaLSE2} {W' : FragS isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code heap c0 b1Heap exe endPc) (hK : ms.K = some Scc.Sem.A64.abi)
    (hWe : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .e) b0)
    (hWn1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n1))
    (hWn1b : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n1b))
    (hWn2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n2) b1Heap)
    (hWn5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n5) b2)
    (hWex : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .ex))
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .ex) s c →
      ms.abortAt s)
    (msS : List TermRun.Frame → MemSide isaLSE2) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) (Q : FragS isaLSE2) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .e)) frs) Q := by
  have h := seg_heapW (p := p) (Q := fun _ _ => False) hF hR hal hlo hhi hcode hK hWe hWn1 hWn1b hWn2 hWn5 hWex
    hsvc hab
  subst hms
  exact SegWS.liftS_noret frs h hWS' Q

namespace Disp

/-- **`seg_disp2W` at any call depth.** -/
theorem seg_disp2WS {W : Frag isaLSE2} {W' : FragS isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t1) t1)
    (hWj1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .j1) j1)
    (hWt2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t2) t2)
    (hWg2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .g2) g2)
    (msS : List TermRun.Frame → MemSide isaLSE2) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e)) frs)
      (Frag.at (At exe endPc R F (DX.nd (_root_.Executable.labels exe).label c0 .heap)) frs) := by
  have h := seg_disp2W (p := p) (lbl := lbl) (ms := ms) hF hR hal hlo hhi hcode hWe hWt1 hWj1 hWt2 hWg2
  subst hms
  exact SegWS.liftS frs h hWS'

/-- **`seg_abort2W` at any call depth**: into any fragment with frames. -/
theorem seg_abort2WS {W : Frag isaLSE2} {W' : FragS isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi) (hs : StubHW W K p lbl ms exe endPc R F c0)
    (msS : List TermRun.Frame → MemSide isaLSE2) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) (Q : FragS isaLSE2) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e)) frs) Q := by
  have h := seg_abort2W (Q := fun _ _ => False) hF hR hal hlo hhi hK hs
  subst hms
  exact SegWS.liftS_noret frs h hWS' Q

/-- **`seg_jabort2W` at any call depth**: from a node `nC` at
`scc_rt_abort` with `x0 = 2`, into any fragment with frames. -/
theorem seg_jabort2WS {W : Frag isaLSE2} {W' : FragS isaLSE2} {K : State → State → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat = 2)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ nC.o.sp - 48)
    (hkc : nC.o.sp < R.hi) (h16 : nC.o.sp % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubHW W K p lbl ms exe endPc (R.callee nC.o.sp (-48) 0)
      (fun m => F m ∧ CKept R nC.o.sp (-48) 0 m0 m ∧ Abs R nC.o m0 σC) c0)
    (msS : List TermRun.Frame → MemSide isaLSE2) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) (Q : FragS isaLSE2) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F nC) frs) Q := by
  have h := seg_jabort2W (Q := fun _ _ => False) hpc hX0 hF hR hal hlo hkc h16 hK hstub
  subst hms
  exact SegWS.liftS_noret frs h hWS' Q

end Disp

end A64.Abort

end Spike.Lib
