/-
**hello.w's worker segment at the placed instance** (row
5j-misc, AArch64): `HelloAssemblyI`'s root parameters `P`, `Z` and `hseg`
at the concrete fragment (`Z w := fun _ => ZHR`, `P w := childP` at the
record's placement and memory side), by `Hello.SegR.seg_childP`.

- `ZI`, `PI`: the root's `Z` and `P`.
- `hsegI`: the root's `hseg` at `ZI`, `PI` (from the loader's parses
  `hpa`, `hhp`: the placed output's program is hello's).
- `XI`, `hsegXI`: the root's landing fragment `X` (trivial) and `hsegI` as
  a `SegTCSX` segment landing in it (`SegTCSX.ofS`).
-/
import Spike.Lib.HelloAssemblyI
import Spike.Lib.A64HelloWorkerSegP

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.HelloMs (msH)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (childP seg_childP)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **The root's `Z`**: `ZHR` at the placed executable. -/
abbrev ZI : ιH hp i → FragS isaLSE2 := fun _ => ZHR (LH hp i).exe (LH hp i).pfx

/-- **The root's `P`**: `childP` at the record's placement and memory side. -/
abbrev PI : ιH hp i → FragS isaLSE2 := fun w =>
  childP (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)

/-- **The root's `hseg`** at `ZI`, `PI`. -/
theorem hsegI {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg) :
    ∀ w, SegTCS (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZI hp i w s c fs) helloSrc (SRH hp i w).lbl
      (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (PI hp i G0 w) (fun _ _ _ => False) := by
  haveI := (LH hp i).valid
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hl : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
  exact fun w => seg_childP hl rfl fun _ => HelloMs.K_H (LH hp i) (GH hp i G0) (SRH hp i) w

/-- **The root's landing fragment `X`**: trivial (`hsegI` lands in no fact). -/
abbrev XI : ιH hp i → FragS isaLSE2 := fun _ _ _ _ => True

/-- **The root's `hseg` as a `SegTCSX` segment** landing in `XI` (`hsegI` through `SegTCSX.ofS`). -/
theorem hsegXI {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg) :
    ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZI hp i w s c fs) (XI hp i w) helloSrc
      (SRH hp i w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (PI hp i G0 w)
      (fun _ _ _ => False) :=
  fun w => SegTCSX.ofS (hsegI hp i G0 hpa hhp w)

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.hsegI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hsegI

/-- info: 'Spike.Lib.HelloAssemblyI.hsegXI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hsegXI
