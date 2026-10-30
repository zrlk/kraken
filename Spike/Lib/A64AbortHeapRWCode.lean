/-
**The heap abort path's obligations with the return address from the abort
code** (AArch64): `Abort.Disp.StubHRW` (`Spike/Lib/A64AbortHeapRW.lean`)
for a program with `Scc.Cert.Rt.A64.Abort.abortIn`, given the path's nodes
inside `W` (`Abort.Disp.HPathW`) and the exit call at an abort site; the
stub's `write` call is `StubW.seg_svcTW` over `Abort.NT`.

- `stubHRW_of_code`: `stubHW_of_code`'s twin over `DN.nd2R`/`NT ra`.
-/
import Spike.Lib.A64AbortHeapRW
import Spike.Lib.A64StubTAC

namespace Spike.Lib.A64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Rt.A64.Print (code_field add4 add0)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} {W : Frag isaLSE2} {K : State → State → Prop}

/-- **The heap abort path's obligations with the return address from the
abort code**: `StubHRW` for a program with `abortIn` (`stubHW_of_code` over
`DN.nd2R`/`NT ra`), given the path's nodes inside `W` (`HPathW`, the stub's
`write` call among them) and the exit call at an abort site (`hab`). -/
theorem stubHRW_of_code {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (h : Abort.Disp.HPathW W K exe endPc R F c0 ra)
    (hab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.heap c0 ra .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubHRW W K p lbl ms exe endPc R F c0 ra := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  have hst := hpr.1.1.1.1.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, -, hsvcIn, -⟩ := hst
  exact ⟨Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2, h.de, h.dt1, h.dj1, h.dt2, h.dg2,
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .heap, h.se, h.sn1, h.sn1b, h.sn2, h.sn5, h.sex,
    seg_svcTW hK hF (code_field hp hend hsvcIn (by simp only [Abort.NT, Abort.pcSvc, add4, add0])) h.ssvc, hab⟩

end Spike.Lib.A64.StubW

/-- info: 'Spike.Lib.A64.StubW.stubHRW_of_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.StubW.stubHRW_of_code
