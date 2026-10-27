/-
**The heap and write abort paths' obligations, their code and `write`
call** (AArch64): `Abort.Disp.StubHW` (`Spike/Lib/A64AbortHeapW.lean`) and
`Abort.Disp.StubWW` (`Spike/Lib/A64AbortWriteW.lean`) from the abort code
(`Scc.Cert.Rt.A64.Abort.abortIn`) in any valid layout, given only the
nodes' states inside `W` and the exit call at an abort site. The code
fields are `code_disp`/`code_stubs`; the stub's `write` call is
`StubW.seg_svcW` from its node's states inside `W`.

- `stubHW_of_code`, `stubWW_of_code`: the rule for the heap and the write
  path.
-/
import Spike.Lib.A64AbortHeapW
import Spike.Lib.A64AbortWriteW
import Spike.Lib.A64StubW

namespace Spike.Lib.A64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Rt.A64.Print (code_field add4 add0)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl} {W : Frag isaLSE2} {K : State → State → Prop}

/-- A stub's `write` call is a segment inside `W` given its node's states
there, for a program with the stub's code (`stubIn`). -/
theorem seg_svc_of_stubIn {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {st : Abort.Stub} {b1 : List Directive} (hst : Scc.Cert.Rt.A64.Abort.stubIn prog st b1 = true)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hW : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .svc)) :
    SegW W K p lbl ms (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .svc))
      (At exe endPc R F (Abort.N (_root_.Executable.labels exe).label st c0 .n5)) := by
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, -, hsvcIn, -⟩ := hst
  exact seg_svcW hK hF (code_field hp hend hsvcIn (by simp only [Abort.N, Abort.pcSvc, add4, add0])) hW

/-- **The heap abort path's obligations from the abort code**: `StubHW`
for a program with `abortIn`, given the dispatcher's and the heap stub's
nodes' states inside `W` (the stub's `write` call among them, `hsvc`) and
the exit call at an abort site (`hab`). -/
theorem stubHW_of_code {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (de : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .e) Abort.Disp.d0)
    (dt1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .t1) Abort.Disp.t1)
    (dj1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .j1) Abort.Disp.j1)
    (dt2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .t2) Abort.Disp.t2)
    (dg2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .g2) Abort.Disp.g2)
    (se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .e) Abort.b0)
    (sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n1))
    (sn1b : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n1b))
    (sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n2) Abort.b1Heap)
    (hsvc : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .svc))
    (sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n5) Abort.b2)
    (sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .ex))
    (hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubHW W K p lbl ms exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  exact ⟨Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2, de, dt1, dj1, dt2, dg2,
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .heap, se, sn1, sn1b, sn2, sn5, sex,
    seg_svc_of_stubIn hp hend hpr.1.1.1.1.2 hK hF hsvc, hab⟩

/-- **The write abort path's obligations from the abort code**: `StubWW`
for a program with `abortIn`, as `stubHW_of_code`. -/
theorem stubWW_of_code {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (de : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .e) Abort.Disp.d0)
    (dt1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t1) Abort.Disp.t1)
    (dj1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j1) Abort.Disp.j1)
    (dt2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t2) Abort.Disp.t2)
    (dj2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j2) Abort.Disp.j2)
    (dt3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t3) Abort.Disp.t3)
    (dj3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j3) Abort.Disp.j3)
    (dt4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t4) Abort.Disp.t4)
    (dg4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .g4) Abort.Disp.g4)
    (se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .e) Abort.b0)
    (sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n1))
    (sn1b : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n1b))
    (sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n2) Abort.b1Write)
    (hsvc : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .svc))
    (sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n5) Abort.b2)
    (sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex))
    (hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubWW W K p lbl ms exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  exact ⟨Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2, de, dt1, dj1, dt2, dj2, dt3, dj3, dt4, dg4,
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .write, se, sn1, sn1b, sn2, sn5, sex,
    seg_svc_of_stubIn hp hend hpr.1.1.2 hK hF hsvc, hab⟩

end Spike.Lib.A64.StubW
