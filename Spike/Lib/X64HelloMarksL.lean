/-
**`MarksL` at the placed layout** (x86-64; the twin of `Spike/Lib/HelloMarksL.lean`, same names): the loaded
program's marks (`PhRec.μ`, the canonical target's by `AbOffW.marks_target`) have their take, release and abort
sites at the layout's labels (`PlaceWX.abortAt_eq`, `PlaceWX.lab_toNat`; `X64AbOffL`'s argument), and the
`writeErr` exit is no other exit (`hlab_H`: hello's five exit calls are at distinct `codeLabel` addresses).

- `marksL_H`: `MarksL (PhRec.μ L) L.lab` at `L := RuntimeLayout.ofPlaceWX hp i`.
- `marksL_HE`: `MarksL` at the canonical target's marks, of an `Asm` whose cells are `helloCells`.

**Unlike AArch64**, the layout is `RuntimeLayout.ofPlaceWX hp i` of a `PlaceWX` (A64: `LH hp i` of a `PlaceW`;
`X64HelloAssemblyI.LH` is the same abbreviation, not imported here), the program comes from `cellsOf asm`
(A64: `textProgram asm`), the labels resolve by `codeLabel` (A64: `codeOf`), and the five exit calls are at
x86-64's byte addresses (`lo + 4292`, `+ 4360`, `+ 4428`, `+ 4496`, `+ 4564`).
-/
import Spike.Lib.X64HelloOInit
import Spike.Lib.X64HelloAbObl
import Spike.Lib.X64WakeAbOffW

namespace Spike.Lib.X64HelloAssemblyI

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Scc.Sem.X64 (codeLabel)
open Scc.Cert.Rt.X64 (codeT_eq)
open Spike.Lib.X64.Flow.Worker.Hello.AbObl (MarksL)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)
open SccCode (helloCells)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The loaded program's marks are at the layout's labels**, of an output whose cells are `helloCells`
(`hpa`, `hhp`) placed at `lo` (`hlo`). -/
theorem marksL_H {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = Spike.Lib.X64.HelloPh.lo) :
    MarksL (Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i)) (RuntimeLayout.ofPlaceWX hp i).lab where
  take a ha := by
    change codeLabel Λ0.code.lo o.prog "scc_rt_take_site" = some a at ha
    exact (PlaceWX.lab_toNat hp i ha).symm
  release a ha := by
    change codeLabel Λ0.code.lo o.prog "scc_rt_release_site" = some a at ha
    exact (PlaceWX.lab_toNat hp i ha).symm
  abortAt k a ha := by
    rw [PlaceWX.abortAt_eq hp i] at ha
    exact (PlaceWX.lab_toNat hp i ha).symm
  wexit k hk := by
    have hl := Spike.Lib.X64HelloOInit.hlab_H hp i hpa hhp hlo
    rw [hl "scc_rt_abort_write_exit" 4202896 (by rw [← codeT_eq]; decide +kernel)]
    cases k
    · rw [hl _ 4202692 (by rw [← codeT_eq]; decide +kernel)]; decide
    · rw [hl _ 4202760 (by rw [← codeT_eq]; decide +kernel)]; decide
    · rw [hl _ 4202828 (by rw [← codeT_eq]; decide +kernel)]; decide
    · rw [hl _ 4202964 (by rw [← codeT_eq]; decide +kernel)]; decide
    · exact absurd rfl hk

/-- **`MarksL` at the canonical target's marks** (`μE` of the assembly rows): they are `PhRec.μ`
(`AbOffW.marks_target`). -/
theorem marksL_HE {asm : Scc.Sem.X64.Asm} (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some helloCells) (hlo : Λ0.code.lo = Spike.Lib.X64.HelloPh.lo)
    {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} :
    MarksL ((Scc.Sem.X64.target H E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ)
      (RuntimeLayout.ofPlaceWX hp i).lab := by
  rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (RuntimeLayout.ofPlaceWX hp i) hpa]
  exact marksL_H hp i hpa hhp hlo

end Inst

end Spike.Lib.X64HelloAssemblyI

/-- info: 'Spike.Lib.X64HelloAssemblyI.marksL_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.marksL_H

/-- info: 'Spike.Lib.X64HelloAssemblyI.marksL_HE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.marksL_HE
