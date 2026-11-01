/-
**The root's `hseg` at `Z := ZHR ∧ X`, placed** (row
5i-ZObl): `SegRP.seg_childPP` at `HelloSegI`'s placement (`PI`, `msWH`),
once `X` holds at every node of the child's run at every datum of `PI`
(`ZObl`).

- `hsegIP`.
-/
import Spike.Lib.HelloSegI
import Spike.Lib.A64HelloWorkerSegRP

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildD ChildPrem)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (ZObl seg_childPP)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **The root's `hseg` at `ZI ∧ X`, `PI`**: `X w` at every node of the
child's run at every datum of `PI hp i G0 w` (`hX`). -/
theorem hsegIP {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (X : ιH hp i → FragS isaLSE2)
    (hX : ∀ w (d : ChildD), d.ok →
      ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
        (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
        d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m →
      ZObl (X w) (LH hp i).exe (endH hp i) (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
        d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m) :
    ∀ w, SegTCS (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZI hp i w s c fs ∧ X w s c fs) helloSrc
      (SRH hp i w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (PI hp i G0 w)
      (fun _ _ _ => False) := by
  haveI := (LH hp i).valid
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hl : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
  exact fun w => seg_childPP hl rfl (fun _ => HelloMs.K_H (LH hp i) (GH hp i G0) (SRH hp i) w) (hX w)

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.hsegIP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hsegIP
