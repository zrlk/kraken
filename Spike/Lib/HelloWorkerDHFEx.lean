/-
**The switch's worker side at the root's `μ`, `lab`: `hlab`, `hμ` discharged** (hello.w, row 5i-hab1; AArch64): a
gate that `HelloWorkerDHF`'s instance is not vacuous in its abort-fact arguments at the root: `hlab` is
`HelloOInit.hlab_H` (the layout placed at `lo`, from the loader's parses) and `hμ` is `HelloAssemblyI.marksL_HE` at
`μ := (target (kernel 2) E).marks asm (LH hp i).Λ` (the root's `μE`); `(LH hp i).lab` is the executable's labels
definitionally. The example is `DHF_ab` there (the root's `hab1W` at `AbH`'s labels).
-/
import Spike.Lib.HelloWorkerDHF
import Spike.Lib.HelloOInit
import Spike.Lib.HelloMarksL

namespace Spike.Lib.HelloWorkerDHFEx

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.HelloAssemblyI SccCode

example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)
  (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ) {asm : String}
  (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog) (hhp : Scc.Sem.A64.textProgram asm = .ok helloProg)
  (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (E : Scc.Sem.Entry) :
  ∀ w s c fs, (DH hp i G0 (HelloWorkerDHF.PF hp i G0)
      (HelloWorkerDHF.ZF hp i ((target (kernel 2) E).marks asm (LH hp i).Λ))
      (HelloWorkerDHF.XF hp i ((target (kernel 2) E).marks asm (LH hp i).Λ))
      (HelloWorkerDHF.hsegFH hp i G0 hI hpa hhp (HelloOInit.hlab_H hp i hpa hhp hlo)
        (marksL_HE hp i hpa hhp hlo))).Wi w s c fs →
    HelloPostAb.AbFacts ((target (kernel 2) E).marks asm (LH hp i).Λ)
      (Spike.Lib.A64.WriteAb.Ab (LH hp i).lab) s :=
  HelloWorkerDHF.DHF_ab hp i G0 hI hpa hhp (HelloOInit.hlab_H hp i hpa hhp hlo) (marksL_HE hp i hpa hhp hlo)

end Spike.Lib.HelloWorkerDHFEx
