/-
**`hsegIP`'s `hX` at `X := AbX μ lab`, placed** (row 5i-hab1, P5): `zObl_abX` at
`HelloSegI`'s placement (`LH`, `endH`, `msWH`), the layout's labels `helloProg`'s at `lo` (`hlab_H`).

- `hX_abX`: `hsegIP`'s `hX` at `X := fun _ => AbX μ (LH hp i).lab`.
- `hsegIP_abX`: `hsegIP` at that `X`.
-/
import Spike.Lib.HelloSegIP
import Spike.Lib.HelloOInit
import Spike.Lib.A64HelloAbOblZ

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildD ChildPrem)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (ZObl)
open Spike.Lib.A64.Flow.Worker.Hello.AbObl (AbX MarksL zObl_abX)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **`hsegIP`'s `hX` at `AbX μ lab`**: every datum of the child's run keeps the worker's abort facts
(`zObl_abX`), at a layout placed at `lo` (`hlo`) whose marks are off the labels (`hμ`). -/
theorem hX_abX {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) {μ : Marks} (hμ : MarksL μ (LH hp i).lab) :
    ∀ w (d : ChildD), d.ok →
      ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
        (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
        d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m →
      ZObl (AbX μ (LH hp i).lab) (LH hp i).exe (endH hp i)
        (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
        d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m := by
  haveI := (LH hp i).valid
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hl : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
  intro w d ⟨_, hR, hal, hlo', hhi⟩ hP
  exact zObl_abX hl rfl (Spike.Lib.HelloOInit.hlab_H hp i hpa hhp hlo) hμ hR hal (by omega) hhi hP.hm

/-- **The root's `hseg` at `ZI ∧ AbX μ lab`, `PI`** (`hsegIP` at `hX_abX`). -/
theorem hsegIP_abX {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) {μ : Marks} (hμ : MarksL μ (LH hp i).lab) :
    ∀ w, SegTCS (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZI hp i w s c fs ∧ AbX μ (LH hp i).lab s c fs)
      helloSrc (SRH hp i w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
      (PI hp i G0 w) (fun _ _ _ => False) :=
  hsegIP hp i G0 hpa hhp (fun _ => AbX μ (LH hp i).lab) (hX_abX hp i G0 hpa hhp hlo hμ)

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.hX_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hX_abX

/-- info: 'Spike.Lib.HelloAssemblyI.hsegIP_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hsegIP_abX
