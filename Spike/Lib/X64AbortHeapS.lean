/-
**The heap abort path on x64 at any call depth**: `seg_heapW`,
`Disp.seg_disp2W`, `Disp.seg_abort2W` and `Disp.seg_jabort2W`
(`Spike/Lib/X64AbortHeapW.lean`) as segments with the source thread's
frames (`SegWS`, `Spike/Lib/SegS.lean`), at any fixed frames `frs`: the same
premises, under the memory side at `frs` (`msS frs = ms`), inside any `W'`
that contains `W` at `frs`. Each is `SegWS.liftS` of the one-frame rule; the
paths that do not return end in any fragment with frames.
-/
import Spike.Lib.X64AbortHeapW
import Spike.Lib.SegS

namespace Spike.Lib.X64.Abort

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64 Spike.Lib.X64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **`seg_heapW` at any call depth**: into any fragment with frames. -/
theorem seg_heapWS {W : Frag isa} {W' : FragS isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code heap c0 x1Heap exe endPc) (hK : ms.K = some Scc.Sem.X64.abi)
    (hWe : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .e) x0)
    (hWn1 : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n1))
    (hWn2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n2) x1Heap)
    (hWn5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n5) x2)
    (hWex : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .ex))
    (hsys : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .n5)))
    (hab : ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .ex) s c →
      ms.abortAt s)
    (msS : List TermRun.Frame → MemSide isa) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) (Q : FragS isa) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F (N (_root_.Executable.labels exe).label heap c0 .e)) frs) Q := by
  have h := seg_heapW (p := p) (Q := fun _ _ => False) hF hR hlo hhi hcode hK hWe hWn1 hWn2 hWn5 hWex hsys hab
  subst hms
  exact (SegWS.liftS frs h hWS').mono_post fun _ _ _ h => h.1.elim

namespace Disp

/-- **`seg_disp2W` at any call depth.** -/
theorem seg_disp2WS {W : Frag isa} {W' : FragS isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hcode : Code c0 exe endPc)
    (hWe : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e) d0)
    (hWt1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t1) t1)
    (hWj1 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .j1) j1)
    (hWt2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .t2) t2)
    (hWg2 : BlkW W K exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .g2) g2)
    (msS : List TermRun.Frame → MemSide isa) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e)) frs)
      (Frag.at (At exe endPc R F (DX.nd (_root_.Executable.labels exe).label c0 .heap)) frs) := by
  have h := seg_disp2W (p := p) (lbl := lbl) (ms := ms) hF hR hlo hhi hcode hWe hWt1 hWj1 hWt2 hWg2
  subst hms
  exact SegWS.liftS frs h hWS'

/-- **`seg_abort2W` at any call depth**: into any fragment with frames. -/
theorem seg_abort2WS {W : Frag isa} {W' : FragS isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hs : StubHW W K p lbl ms exe endPc R F c0)
    (msS : List TermRun.Frame → MemSide isa) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) (Q : FragS isa) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F (DN.nd2 (_root_.Executable.labels exe).label c0 .e)) frs) Q := by
  have h := seg_abort2W (Q := fun _ _ => False) hF hR hlo hhi hK hs
  subst hms
  exact (SegWS.liftS frs h hWS').mono_post fun _ _ _ h => h.1.elim

/-- **`seg_jabort2W` at any call depth**: from a node `nC` at
`scc_rt_abort` with `%rdi = 2`, into any fragment with frames. -/
theorem seg_jabort2WS {W : Frag isa} {W' : FragS isa} {K : State → State → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hrdi : ∀ σ c, nC.J σ c → σ.regs.get64 .rdi = 2#64)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ nC.o.sp - 32) (hhi : nC.o.sp + 8 ≤ R.hi)
    (h8 : nC.o.sp % 8 = 0) (hK : ms.K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, nC.J σC c0 → StubHW W K p lbl ms exe endPc (R.callee (nC.o.sp - 8) (-24) 16)
      (fun m => F m ∧ CKept R (nC.o.sp - 8) (-24) 16 m0 m ∧ Abs R nC.o m0 σC) c0)
    (msS : List TermRun.Frame → MemSide isa) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) (Q : FragS isa) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F nC) frs) Q := by
  have h := seg_jabort2W (Q := fun _ _ => False) hpc hrdi hF hR hlo hhi h8 hK hstub
  subst hms
  exact (SegWS.liftS frs h hWS').mono_post fun _ _ _ h => h.1.elim

end Disp

end Spike.Lib.X64.Abort
