/-
**hello.w on AArch64: the placed assembly with main's invariant past the
clone discharged** (`HelloAssemblyI.hello_obligations_I` at hello's root
value invariant, its `hMainR` by `HelloMainGH.hMainRH_ofGH`).

`hMainRH_ofGH` proves `HMainRH` at the pre-spawn relation strengthened by
`VPriv` and at the records' value invariant `G0 w := GOf2H L (m0Of …)`
(hello's root one). So here `R1 ∧ VPriv` is the relation's pre-spawn half
(`HelloMainG.pre1T_privH` lifts `Pre1T` from `R1`), and `G0` is fixed to
`G0H`, making `hMainRH_ofGH`'s `hG0` `rfl`.

- `G0H`: hello's root value invariant at the placed output.
- `hello_obligations_IM`: `hello_obligations_I` at `R1 ∧ VPriv` and `G0H`;
  `hMainR` replaced by its open rows `hsub1` and `hpc` (the worker's
  progress rows `hhalt1`, `hmapW` passed through).
-/
import Spike.Lib.HelloMainGH
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.HelloAssemblyIM

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakePreTi Spike.Lib.Inv2Core Spike.Lib.WakeInst
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1Store (ZStoreOk)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH AbW)
open Spike.Lib.HelloMs (msH)
open Spike.Lib.HelloO (ODataH IH R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloPreA (ClonePreH)
open Spike.Lib.HelloSpawnR (PreRH HWiH)
open Spike.Lib.HelloMainHRD (MainSegH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.HelloAssembly (HelloRowsW)
open Spike.Lib.HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH hcwH hemH)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Cert.Rt.A64 (endOf)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **hello's root value invariant** at the placed output (what
`HelloMainInstD.mainInstH_G` reads the permit and limit words' guarantee
off). -/
abbrev G0H (_ : ιH hp i) : Loc → Val → Prop :=
  HelloGOf2H.GOf2H (LH hp i) (Spike.Lib.A64.PhRec.m0Of (LH hp i).Λ o.prog o.secs)

variable (P Z X : ιH hp i → FragS isaLSE2)
  /- row: 5j-misc (as `hello_obligations_I`'s `hseg`) -/
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w) (P w) (fun _ _ _ => False))

/-- **The assembly at the placed instance, `hMainR` discharged** (see the
module doc). -/
theorem hello_obligations_IM {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {passT : State → Prop} {Dd : ODataH} {r1c : Range}
    {Ab Ac : State → Prop} {Tw : Cfg → List Ev → Prop}
    /- the loader's parses (the trust boundary) -/
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hd : dataSections asm = some o.secs)
    /- row: 5j-start. The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- (row 1's `hbuf` in `R1`). The pre-spawn half. -/
    (O : Pre1T arch (LH hp i).Λ B asm E R1 Ab Ac helloSrc)
    /- `R1` is the pre-spawn relation with its source
    conjuncts. -/
    (hR1 : ∀ d s, R1 d s → R1OH arch (LH hp i).Λ (HelloAssemblyI.μH hp i E asm) Dd XH d s)
    /- row: 5j-hCl. The clone's facts at the pre-spawn segment's end. -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (fun d s => R1 d s ∧ VPriv (LH hp i).Λ E d) E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      A64Consumer.HeldOk2 (LH hp i).Λ Dd.r0 Dd.r1 th.st d.2.held → Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH ".L22_wc_main" (LH hp i).Λ Dd.r0 r1c X lbl d s)
    /- row: root. The data's guarantee is below every record's. -/
    (hG : ∀ w m, MemInv Dd.G m → MemInv (GH hp i (G0H hp i) w) m)
    /- (the record's park permit word at the clone; any) -/ (pT0 : Loc)
    /- row: 5j-k. The target store point (`WCompatH.pass`). -/
    (pass : HelloW1.PassH (DH hp i (G0H hp i) P Z X hseg) passT)
    /- row: 5j-ZS. The store phase's pc facts on the segment's `Z`. -/
    (hZ : ZStoreOk (LH hp i).exe Z)
    /- row: 5j-hsub1. The records' `r1` in the stack pool. -/
    (hsub1 : (r1c).Sub (LH hp i).Λ.stackPool)
    /- row: 5j-segEnd. The segment end, per clone (`hMainRH_ofGH`'s
    `hpc`). -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (fun d s => R1 d s ∧ VPriv (LH hp i).Λ E d) E hpa passT Dd r1c)
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (fun d s => R1 d s ∧ VPriv (LH hp i).Λ E d) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) P Z X hseg) (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize
        ts j own₀ l →
      HelloHPre.FrH Dd lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA x29 ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat)
    /- row: 5j-misc. The child in the worker side's invariant. -/
    (hWi : HWiH arch (fun d s => R1 d s ∧ VPriv (LH hp i).Λ E d) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
      (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
      (DH hp i (G0H hp i) P Z X hseg) (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E
      (HelloHPre.FrH Dd))
    /- (as `hello_obligations_I`'s `hhalt1`). -/
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = true →
      (isaLSE2.exec s).isSome)
    /- (as `hello_obligations_I`'s `hmapW`). -/
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = false → ∀ e,
      isaLSE2.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (A64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- 5i, 5j-wit; see
    `HelloRowsW`' fields. -/
    (R : HelloRowsW arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (fun d s => R1 d s ∧ VPriv (LH hp i).Λ E d) E hpa passT Dd r1c) E
      (DH hp i (G0H hp i) P Z X hseg) (MH hp i (G0H hp i) E hpa) (AbW (LH hp i).exe) (hcwH hp i (G0H hp i) P Z X hseg)
      (hemH hp i (G0H hp i) P Z X hseg hZ) Ab Ac Tw) :
    WakeObligationsR arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (fun d s => R1 d s ∧ VPriv (LH hp i).Λ E d) E hpa passT Dd r1c) E
      (fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) helloSrc :=
  HelloAssemblyI.hello_obligations_I hp i (G0H hp i) P Z X hseg hpa hhp hd hE (HelloMainG.pre1T_privH hp i hpa O)
    (fun d s h => hR1 d s h.1) hCl hG pT0 pass hZ
    (HelloMainGH.hMainRH_ofGH hp i hpa hhp (fun _ => rfl) (fun _ => hsub1) hpc) hWi hhalt1 hmapW R

end Inst

end Spike.Lib.HelloAssemblyIM

/-- info: 'Spike.Lib.HelloAssemblyIM.hello_obligations_IM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyIM.hello_obligations_IM
