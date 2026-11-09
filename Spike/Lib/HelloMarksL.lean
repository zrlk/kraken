/-
**`MarksL` at the placed layout** (row 5i-hab1, P5, AArch64): the loaded program's marks
(`PhRec.μ`, the canonical target's by `AbOffW.marks_target`) have their take, release and abort sites at
the layout's labels (`PlaceW.abortAt_eq`, `PlaceW.lab_toNat`; `A64AbOffL`'s argument), and the `writeErr`
exit is no other exit (`hlab_H`: hello's five exit calls are at distinct `codeOf` addresses).

- `marksL_H`: `MarksL (PhRec.μ (LH hp i)) (LH hp i).lab`.
- `marksL_HE`: `MarksL` at the canonical target's marks, of a text parsing to `helloProg`.
-/
import Spike.Lib.HelloOInit
import Spike.Lib.A64HelloAbObl
import Spike.Lib.A64WakeAbOffW
import Spike.Lib.HelloAssemblyI

namespace Spike.Lib.HelloAssemblyI

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Flow.Worker.Hello.AbObl (MarksL)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The loaded program's marks are at the layout's labels**, of an output whose program is `helloProg`
(`hpa`, `hhp`) placed at `lo` (`hlo`). -/
theorem marksL_H {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) :
    MarksL (Spike.Lib.A64.PhRec.μ (LH hp i)) (LH hp i).lab where
  take a ha := by
    change codeOf Λ0.code.lo o.prog "scc_rt_take_site" = some a at ha
    exact (PlaceW.lab_toNat hp i ha).symm
  release a ha := by
    change codeOf Λ0.code.lo o.prog "scc_rt_release_site" = some a at ha
    exact (PlaceW.lab_toNat hp i ha).symm
  abortAt k a ha := by
    rw [PlaceW.abortAt_eq hp i] at ha
    exact (PlaceW.lab_toNat hp i ha).symm
  wexit k hk := by
    have hl := Spike.Lib.HelloOInit.hlab_H hp i hpa hhp hlo
    rw [hl "scc_rt_abort_write_exit" 2168544 (by decide +kernel)]
    cases k
    · rw [hl _ 2168328 (by decide +kernel)]; decide
    · rw [hl _ 2168400 (by decide +kernel)]; decide
    · rw [hl _ 2168472 (by decide +kernel)]; decide
    · rw [hl _ 2168616 (by decide +kernel)]; decide
    · exact absurd rfl hk

/-- **`MarksL` at the canonical target's marks** (`μE` of `HelloAssemblyRS`/`RV`): they are `PhRec.μ`
(`AbOffW.marks_target`). -/
theorem marksL_HE {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} :
    MarksL ((target H E).marks asm (LH hp i).Λ) (LH hp i).lab := by
  rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (LH hp i) hpa]
  exact marksL_H hp i hpa hhp hlo

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.marksL_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.marksL_H

/-- info: 'Spike.Lib.HelloAssemblyI.marksL_HE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.marksL_HE
