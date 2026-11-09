/-
**hello.w's `wc_main` before the box's landing: the `NoSetFsW` lemmas** (x86-64; twin of the `NoMsrW` part of
`Spike/Lib/A64HelloWcWfS.lean`): `WcPreWH` and `WcSp0WH` in a layout of `helloCells` stay inside `NoSetFsW`,
generic in the level. The producers inside the start's level are `X64HelloWcWfSX`'s (at `ownGHXW`).

- `wcPreW_nsH`, `wcSp0W_nsH`: inside `NoSetFsW`.

## Unlike AArch64

- AArch64's `NoMsrW` lemmas (`wcPreW_nmH`, `wcSp0W_nmH`) become `NoSetFsW` lemmas (`wcPreW_nsH`, `wcSp0W_nsH`):
  the instruction x86-64 must avoid is the `%fs` base's write.
-/
import Spike.Lib.X64HelloWcWf
import Spike.Lib.X64HelloWcPreG
import Spike.Lib.X64HelloWcNoMsr
import Spike.Lib.X64HelloAllocWSTp
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64WakeWcWfS

namespace Spike.Lib.X64.HelloPh.WcWfS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.HelloWc (WcPreWH WcSp0WH)

/-! ## Inside `NoSetFsW` -/

section NoSetFs

variable {L : RuntimeLayout} {W : Spike.Lib.Frag isa} {K : State → State → Prop} {R : Spike.Lib.Region}
  {F : MachineData → Prop} {ms : Spike.Lib.MemSide isa}

/-- `WcPreWH` in `L`'s layout of helloCells is inside `NoSetFsW`. -/
theorem wcPreW_nsH (hp : L.prog = helloCells) {J0 J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (h : WcPreWH W K L.exe L.endPc R F ms J0 J1) :
    WcPreWH (Spike.Lib.X64.NoSetFsW W K) K L.exe L.endPc R F ms J0 J1 := by
  have hpS : Scc.Cert.Rt.X64.Lays L.exe helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = Scc.Cert.Rt.X64.endOf L.exe helloCells L.pfx := by
    show Scc.Cert.Rt.X64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact Spike.Lib.X64.Flow.HelloWc.WcPreWH.noSetFs hpS hendS h

/-- `WcSp0WH` in `L`'s layout of helloCells is inside `NoSetFsW`. -/
theorem wcSp0W_nsH (hp : L.prog = helloCells) {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (h : WcSp0WH W K L.exe L.endPc R F ms J1) :
    WcSp0WH (Spike.Lib.X64.NoSetFsW W K) K L.exe L.endPc R F ms J1 := by
  have hpS : Scc.Cert.Rt.X64.Lays L.exe helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = Scc.Cert.Rt.X64.endOf L.exe helloCells L.pfx := by
    show Scc.Cert.Rt.X64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact Spike.Lib.X64.Flow.HelloWc.WcSp0WH.noSetFs hpS hendS h

end NoSetFs

end Spike.Lib.X64.HelloPh.WcWfS

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.wcPreW_nsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.wcPreW_nsH

/-- info: 'Spike.Lib.X64.HelloPh.WcWfS.wcSp0W_nsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcWfS.wcSp0W_nsH
