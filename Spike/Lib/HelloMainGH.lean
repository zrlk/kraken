/-
**hello.w on AArch64: row 5j-segEnd at `HelloAssemblyI`'s main side**
(`hello_obligations_I`'s `hMainR`): `HelloMainG.hMainRH_ofG`'s conclusion at
the instance's `MH` (`helloM` at the target's marks `μH`, `HelloCompatI.hoffP`)
on `msH L (GH G0)`, rather than at `HelloMainG.helloMI` (`PhRec.μ L`,
`hoff_ofPlaceW`, `Gm`).

`HelloMainHRI.hMainRH_ofI` reads main's side only through its `Mi` (`hMi`),
and `helloM`'s `Mi` does not mention the marks or `hoff`, so the marks agree
without `AbOffW.marks_target`; `MH`'s `Mi` is `hMainRH_ofI`'s once the
records' value invariant below `wakeG` is hello's root one,
`G0 w = GOf2H L (m0Of L.Λ o.prog o.secs)` (`hG0`, what `Gm` is built from:
`HelloMainInstD.mainInstH_G` reads the permit and limit words' guarantee off
it), with the flag word `cT w := w.1.cT` (as `hello_obligations_I`).

- `hMainRH_ofGH`: `HMainRH` at `R1 ∧ VPriv L.Λ E`, `SRH`, `MH`; open only
  `hsub1` (the records' `r1` in the stack pool) and the segment end `hpc`,
  given the loader's parses and `hG0`.
-/
import Spike.Lib.HelloMainG
import Spike.Lib.HelloAssemblyI
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.HelloMainGH

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeT1
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Cert.Rt.A64 (endOf)
open SccCode (helloProg)
open Spike.Lib.HelloSrc (helloS)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH HMainRH)
open Spike.Lib.HelloMainHRD (MainSegH)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.HelloAssemblyI (ιH SRH MH)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {cS : ιH hp i → WeakMem.Address}
  {pT : ιH hp i → Loc} {Pa : ιH hp i → Inv2Params isaLSE2} {G : ιH hp i → Loc → Val → Prop}
  {passT : State → Prop} {D : WSideH (ιH hp i)} {r0 r1 : ιH hp i → Range} {asm : String} {E : Entry}
  {G0 : ιH hp i → Loc → Val → Prop}

/-- **`HMainRH` at `HelloAssemblyI`'s `MH`** (see the module doc): the
form `hello_obligations_I`'s `hMainR` takes, at `R1 ∧ VPriv`. -/
theorem hMainRH_ofGH {Fr : HelloSpawnR.FrP}
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    /- (instance; row root) the records' value invariant below `wakeG`
    is hello's root one -/
    (hG0 : ∀ w, G0 w = HelloGOf2H.GOf2H (RuntimeLayout.ofPlaceW hp i)
      (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs))
    /- row: 5j-hsub1 -/
    (hsub1 : ∀ w, (r1 w).Sub (RuntimeLayout.ofPlaceW hp i).Λ.stackPool)
    /- row: 5j-segEnd (the segment end, per clone) -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (Spike.Lib.HelloQ.helloQ arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (ιH hp i) (SRH hp i) (fun w => w.1.cT) cS pT Pa G passT (MH hp i G0 E hpa) D r0 r1)
        (RuntimeLayout.ofPlaceW hp i).Λ asm E 0
        d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) (SRH hp i) (fun w => w.1.cT) cS pT
        Pa G passT
        (MH hp i G0 E hpa) D r0 r1 (RuntimeLayout.ofPlaceW hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Fr lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH (RuntimeLayout.ofPlaceW hp i).exe
          (endOf (RuntimeLayout.ofPlaceW hp i).exe helloProg (RuntimeLayout.ofPlaceW hp i).pfx)
          th c Rm F₂ cA x29 ra tp ∧
        lbl l = some cA.toNat ∧ tp = (RuntimeLayout.ofPlaceW hp i).pinA + 0#64 + 8#64 ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat) :
    HMainRH arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) (SRH hp i) (fun w => w.1.cT) cS pT
      Pa G passT
      (MH hp i G0 E hpa) D r0 r1 (RuntimeLayout.ofPlaceW hp i).Λ asm E Fr :=
  HelloMainHRI.hMainRH_ofI hp i (HelloMainG.hprog_IH hpa hhp)
    (fun w => by
      show HelloMainInv.mainInvP _ _
          (HelloMs.helloMs _ (WakeG.wakeG (G0 w) w.1.cT) _ _) _ = _
      rw [hG0])
    (HelloMainG.hw_IH hp i) (HelloMainG.hpv_IH hp i) (HelloMainG.htop_IH hp i hsub1) hpc

end Inst

end Spike.Lib.HelloMainGH

/-- info: 'Spike.Lib.HelloMainGH.hMainRH_ofGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloMainGH.hMainRH_ofGH
