/-
**hello.w on AArch64: the placed assembly at the root's pre-spawn data** (`HelloAssemblyIM.hello_obligations_IM`
at the certificate's listing, its `O` and `hR1` from the root: `Dd := HelloRootO.helloDR …`, the pre-spawn relation
`R1OH … helloDR … XH`, `O` by `HelloOLift.hello_O_X` of `HelloRootO.oPremH_R`, `hR1` by `id`).

The records' second stack `r1c` is the root's `r1W`, so `hello_obligations_IM`'s `hsub1` and `oPremH_R`'s are one
premise.

- `hello_obligations_R`: the statement; its premises are `hello_obligations_IM`'s other than `O`/`hR1` and
  `oPremH_R`'s (rows as there).
-/
import Spike.Lib.HelloAssemblyIM
import Spike.Lib.HelloRootO
import Spike.Lib.HelloOLift

namespace Spike.Lib.HelloAssemblyR

variable {asm : String}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakePreTi Spike.Lib.Inv2Core Spike.Lib.WakeInst
open Spike.Lib.WakeT1 (srcPo)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1Store (ZStoreOk)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH AbW)
open Spike.Lib.HelloO (ODataH IH R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloPreA (ClonePreH)
open Spike.Lib.HelloSpawnR (PreRH HWiH)
open Spike.Lib.HelloMainHRD (MainSegH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.HelloAssembly (HelloRowsW)
open Spike.Lib.HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH hcwH hemH μH)
open Spike.Lib.HelloAssemblyIM (G0H)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.A64.HelloPh.RootH0 (msBotH)
open Spike.Lib.HelloRootO (helloDR oPremH_R)
open Spike.Lib.A64.Rt (RuntimeLayout)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

variable (P Z X : ιH hp i → FragS isaLSE2)
  /- row: 5j-misc (as `hello_obligations_IM`'s `hseg`) -/
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w) (P w) (fun _ _ _ => False))

set_option hygiene false in
local notation "AX" => (LH hp i).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "D" => helloDR (asm := asm) hp i E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks asm (LH hp i).Λ

set_option hygiene false in
/-- The pre-spawn relation at the root's data, with `VPriv` (`hello_obligations_IM`'s `R1 ∧ VPriv`). -/
local notation "R1R" => fun d s => R1OH arch (LH hp i).Λ (μH hp i E asm) (D) XH d s ∧
  VPriv (LH hp i).Λ E d

set_option hygiene false in
local notation "r1R" => Spike.Lib.WakeOSide.r1W hp i

/-- **The assembly at the placed instance at the root's pre-spawn data** (see the module doc). -/
theorem hello_obligations_R {arch : WeakMem.Arch} {B : Budget} {E : Entry} {passT : State → Prop}
    {Ab Ac : State → Prop} {Tw : Cfg → List Ev → Prop}
    {Ctx : FragS isaLSE2} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    /- the loader's parses (the trust boundary) -/
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hd : dataSections asm = some o.secs)
    /- instance facts (as `HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (LH hp i).pinA.toNat + 168 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hnz : Spike.Lib.WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- row: 5j-start. The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- row: 5j-hsub1. The second stack in the stack pool. -/
    (hsub1 : (r1R).Sub (LH hp i).Λ.stackPool)
    /- rows: as `HelloRootO.oPremH_R`'s (the root's pre-spawn premises) -/
    (hst0 : SegWS (W0H (asm := asm) hp i E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (LH hp i))) helloSrc (L0T (LH hp i).Λ)
      (msBotH (asm := asm) hp i E (fun _ => True) ls inv1 inv2) (StartPH hp i E) (fun _ _ _ => False))
    (h2 : ∀ l b n l' b' n', (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      A64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      SegInvS ((D).W2 l b n l' b' n') (TakeCKS (D).a (D).Cl) helloSrc
        (A64ConsumerA.upd (A64ConsumerA.upd (D).L0 l b) l' b')
        (msOfA (LH hp i).Λ μE (D).rd (D).G (D).own (D).ar (fun _ _ _ _ _ => False)
          (A64ConsumerA.upd (A64ConsumerA.upd (D).L0 l b) l' b')
          (A64ConsumerA.updN (A64ConsumerA.updN (D).ls0 l n) l' n'))
        ((D).inv2 l b n l' b' n'))
    (h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS ((D).W1 l b n) (TakeCKS (D).a (D).Cl) helloSrc (A64ConsumerA.upd (D).L0 l b)
        (msOfA (LH hp i).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (A64ConsumerA.upd (D).L0 l b)
          (A64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n))
    (hW0 : ∀ s c fs, (D).inv0 s c fs → (D).W0 s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D)) (D).L0 (D).ls0 s c fs (D).Dt Ab (D).Cl
        Ac)
    (hW1 : ∀ l b n s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n → (D).W1 l b n s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (A64ConsumerA.upd (D).L0 l b) (A64ConsumerA.updN (D).ls0 l n) s c fs (D).Dt Ab (D).Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      A64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      (D).W2 l b n l' b' n' s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (A64ConsumerA.upd (A64ConsumerA.upd (D).L0 l b) l' b')
        (A64ConsumerA.updN (A64ConsumerA.updN (D).ls0 l n) l' n') s c fs (D).Dt Ab (D).Cl Ac)
    (h0t : Spike.Lib.HelloPreA.H0TakeH (LH hp i) (AX) (D).inv0)
    (h0o : Spike.Lib.HelloPreA.H0TakeOwnH (LH hp i) (AX) (D).inv0)
    (h1t : Spike.Lib.HelloPreA.Take1X.H1TakeXH (LH hp i) (AX) inv1)
    (h2t : Spike.Lib.HelloPreA.H2TakeH (LH hp i) (AX) inv2)
    (h2o : Spike.Lib.HelloPreA.H2TakeOwnH (LH hp i) (AX) inv2)
    (hP : HookOK (srcPo 2 arch helloSrc) helloSrc)
    (hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (IH (D)))
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm (LH hp i).Λ = some d → TIC Ab Ac [] d)
    /- rows: as `hello_obligations_IM`'s -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH (D) lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      A64Consumer.HeldOk2 (LH hp i).Λ (D).r0 (D).r1 th.st d.2.held →
      Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH ".L22_wc_main" (LH hp i).Λ (D).r0 (r1R) X lbl d s)
    (hG : ∀ w m, MemInv (D).G m → MemInv (GH hp i (G0H hp i) w) m)
    (pT0 : Loc)
    (pass : HelloW1.PassH (DH hp i (G0H hp i) P Z X hseg) passT)
    (hZ : ZStoreOk (LH hp i).exe Z)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) P Z X hseg) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s' s0 s1 lbl
        lsize ts j own₀ l →
      HelloHPre.FrH (D) lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA x29 ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat)
    (hWi : HWiH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
      (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
      (DH hp i (G0H hp i) P Z X hseg) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ asm E
      (HelloHPre.FrH (D)))
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = true →
      (isaLSE2.exec s).isSome)
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = false → ∀ e,
      isaLSE2.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (A64Consumer.K0 (LH hp i).Λ) w l = false) e)
    (R : HelloRowsW arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R)) E
      (DH hp i (G0H hp i) P Z X hseg) (MH hp i (G0H hp i) E hpa) (AbW (LH hp i).exe) (hcwH hp i (G0H hp i) P Z X hseg)
      (hemH hp i (G0H hp i) P Z X hseg hZ) Ab Ac Tw) :
    WakeObligationsR arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R)) E
      (fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) helloSrc :=
  HelloAssemblyIM.hello_obligations_IM hp i P Z X hseg hpa hhp hd hE
    (HelloOLift.hello_O_X (oPremH_R hp i hpa hhp hd hlo hstat hpin2 hsub1 hc hnz arch hB hE hst0 h2 h1 hW0 hW1 hW2
      h0t h0o h1t h2t h2o hP hsafe hti0))
    (fun _ _ h => h) hCl hG pT0 pass hZ hsub1 hpc hWi hhalt1 hmapW R

end Inst

end Spike.Lib.HelloAssemblyR

/-- info: 'Spike.Lib.HelloAssemblyR.hello_obligations_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyR.hello_obligations_R
