/-
**The heap abort path's obligations with the return address from the abort
code** (x86-64; the twin of `Spike/Lib/A64AbortHeapRWCode.lean`):
`Abort.Disp.StubHRW` (`Spike/Lib/X64AbortHeapRW.lean`) for code cells with
`Scc.Cert.Rt.X64.Abort.abortIn`, given the path's nodes inside `W`
(`Abort.Disp.HPathW`) and the exit call at an abort site; the stub's
`write` call is `StubW.seg_svcTW` over `Abort.NT`.

- `stubHRW_of_code`: `stubHW_of_code`'s twin over `DN.nd2R`/`NT ra`.

Where x86-64 differs from AArch64: the program is a list of code cells
(`cells`, with byte sizes) rather than directives; the `write` call is the
`syscall` node `ssys` (A64's `svc`), its code `[(op64 .syscall, 2)]`
(`code_field … rfl`); there is no `sn1b` node.
-/
import Spike.Lib.X64AbortHeapRW
import Spike.Lib.X64StubTAC

namespace Spike.Lib.X64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf code_field)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} {W : Frag isa} {K : State → State → Prop}

/-- **The heap abort path's obligations with the return address from the
abort code**: `StubHRW` for code cells with `abortIn` (`stubHW_of_code` over
`DN.nd2R`/`NT ra`), given the path's nodes inside `W` (`HPathW`, the stub's
`write` call among them) and the exit call at an abort site (`hab`). -/
theorem stubHRW_of_code {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (h : Abort.Disp.HPathW W K exe endPc R F c0 ra)
    (hab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.heap c0 ra .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubHRW W K p lbl ms exe endPc R F c0 ra := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hpr
  have hst := hpr.1.1.1.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, hsysIn, -⟩ := hst
  exact ⟨Scc.Cert.Rt.X64.Abort.code_disp hp hend hpr.2, h.de, h.dt1, h.dj1, h.dt2, h.dg2,
    Scc.Cert.Rt.X64.Abort.code_stubs hp hend hprog .heap, h.se, h.sn1, h.sn2, h.sn5, h.sex,
    seg_svcTW hK hF (code_field hp hend hsysIn rfl) h.ssys, hab⟩

end Spike.Lib.X64.StubW

/-- info: 'Spike.Lib.X64.StubW.stubHRW_of_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.StubW.stubHRW_of_code
