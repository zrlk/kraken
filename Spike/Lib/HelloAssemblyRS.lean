/-
**hello.w on AArch64: the placed assembly at the root, the worker's segment and the child's entry
instantiated** (independent part): `HelloAssemblyRV.hello_obligations_RV` at the root parameters
`P := HelloWorkerDHF.PF`, `Z := ZF μE`, `X := XF μE`, `hseg := hsegFH` (the DH := helloDRF switch; from the loader's
parses `hpa`, `hhp`, `hlo` and the immediates' `ImmsKid` `hI`), its `hWi` by `HelloWiI.hWiH_IG` (`PF` by
`cwvH`), whose handed-stack facts `htop`/`hal`/`hsz` are `HelloWiI.r1c_facts` at the records' second stack
`r1W = PreChild.r1Of (LH hp i).lab` and `hsub1`. The chain below (`hello_obligations_I` … `hello_obligations_RV`/`_RC`)
stays generic in `P`/`Z`/`hseg`/`hWi`; this file instantiates them once.

- `hello_obligations_RS`: the statement; its premises are `hello_obligations_RV`'s at `PF`/`ZF`/`XF`/`hsegFH`, with
  `hWi` replaced by `hWiH_IG`'s open rows `hX` (5j-misc-X) and `hCP` (`ChildPrem`).
- `hello_obligations_RSC`: `hello_obligations_RS` at `HelloAssemblyRC`'s choices (the root's immediate table
  `C0S.immsH Λ0 i0`, `Ctx := Land.CtxRH`, `frM := frH c0S.env`).
-/
import Spike.Lib.HelloAssemblyRC
import Spike.Lib.HelloWiI
import Spike.Lib.A64HelloLandRU
import Spike.Lib.HelloWorkerDHF
import Spike.Lib.HelloOInit
import Spike.Lib.HelloMarksL

namespace Spike.Lib.HelloAssemblyRS

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
open Spike.Lib.HelloAssemblyR (hello_obligations_R)
open Spike.Lib.HelloSrcOPrem (hello_hookOK hello_srcSafeS)
open Spike.Lib.HelloOAb (AbH AcH hti0_H)
open Spike.Lib.HelloAssemblyRP (hello_obligations_RP)
open Spike.Lib.HelloPostAb (TwH AbFacts)
open Spike.Lib.HelloAssemblyRV (hello_obligations_RV)
open Spike.Lib.HelloAssemblyI (PI ZI XI hsegI hsegXI hWiH_I hWiH_IG r1c_facts cwvH)
open Spike.Lib.HelloOkW (lBH)
open Spike.Lib.Handover (childAfter)
open Spike.Lib.WakeW1 (mainTidW)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildPrem)
open Spike.Lib.A64.HelloPh.Land (CtxRH)
open Spike.Lib.A64.HelloPh.C0S (c0S)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

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

set_option hygiene false in
/-- The root's worker fragment (`HelloWorkerDHF.PF`: `childPX` at the record's flag). -/
local notation "PS" => Spike.Lib.HelloWorkerDHF.PF hp i (G0H hp i)

set_option hygiene false in
/-- The root's store-phase fragment (`HelloWorkerDHF.ZF`: `ZHR ∧ XF`). -/
local notation "ZS" => Spike.Lib.HelloWorkerDHF.ZF hp i (μE)

set_option hygiene false in
/-- The root's landing fragment (`HelloWorkerDHF.XF`: `XHF ∧ AbX μE lab`). -/
local notation "XS" => Spike.Lib.HelloWorkerDHF.XF hp i (μE)

set_option hygiene false in
/-- The root's worker segment (`HelloWorkerDHF.hsegFH`: `helloDRF`'s, from the loader's parses, the immediates'
`ImmsKid` `hI`, the labels at `lo` and `μE`'s marks). -/
local notation "hS" => Spike.Lib.HelloWorkerDHF.hsegFH hp i (G0H hp i) hI hpa hhp
  (Spike.Lib.HelloOInit.hlab_H hp i hpa hhp hlo)
  (Spike.Lib.HelloAssemblyI.marksL_HE hp i hpa hhp hlo (H := kernel 2) (E := E))

set_option hygiene false in
local notation "QQ" => QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1R) E hpa passT (D) (r1R)

/-- **The assembly at the root, the worker's segment and the child's entry instantiated** (see the module
doc). -/
theorem hello_obligations_RS {arch : WeakMem.Arch} {B : Budget} {E : Entry} {passT : State → Prop}
    {AbT : State → Prop}
    {Ctx : FragS isaLSE2} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    /- the loader's parses (the trust boundary) -/
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hd : dataSections asm = some o.secs)
    /- instance facts (as `HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    /- row: switch-hI (`ImmsMe.kid_root`, `wcall_root`): no immediate at the child's and the worker call's
    controls (`HelloWorkerDHF.hsegFH`'s `hI`). -/
    (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ)
    (hstat : Λ0.static = fun _ => none)
    (hpin2 : (LH hp i).pinA.toNat + 200 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hnz : Spike.Lib.WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- row: 5j-start. The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- row: 5j-hsub1 (closed): A13's data part; the second stack in the pool is `StartPlaceLy.hsub1_W`. -/
    (hA13 : Scc.Cert.Spawn.A64.a13data (LH hp i).Λ o.prog o.secs = true)
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
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D)) (D).L0 (D).ls0 s c fs (D).Dt (AbH hp
          i) (D).Cl
        (AcH hp i))
    (hW1 : ∀ l b n s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n → (D).W1 l b n s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (A64ConsumerA.upd (D).L0 l b) (A64ConsumerA.updN (D).ls0 l n) s c fs (D).Dt (AbH hp i) (D).Cl (AcH hp i))
    (hW2 : ∀ l b n l' b' n' s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      A64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      (D).W2 l b n l' b' n' s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (A64ConsumerA.upd (A64ConsumerA.upd (D).L0 l b) l' b')
        (A64ConsumerA.updN (A64ConsumerA.updN (D).ls0 l n) l' n') s c fs (D).Dt (AbH hp i) (D).Cl (AcH hp i))
    (h0t : Spike.Lib.HelloPreA.H0TakeH (LH hp i) (AX) (D).inv0)
    (h0o : Spike.Lib.HelloPreA.H0TakeOwnH (LH hp i) (AX) (D).inv0)
    (h1t : Spike.Lib.HelloPreA.Take1X.H1TakeXH (LH hp i) (AX) inv1)
    (h2t : Spike.Lib.HelloPreA.H2TakeH (LH hp i) (AX) inv2)
    (h2o : Spike.Lib.HelloPreA.H2TakeOwnH (LH hp i) (AX) inv2)
    /- rows: as `hello_obligations_IM`'s -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH (D) lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      A64Consumer.HeldOk2 (LH hp i).Λ (D).r0 (D).r1 th.st d.2.held →
      Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH ".L22_wc_main" (LH hp i).Λ (D).r0 (r1R) X lbl d s)
    (hG : ∀ w m, MemInv (D).G m → MemInv (GH hp i (G0H hp i) w) m)
    (pT0 : Loc)
    (pass : HelloW1.PassH (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) passT)
    (hZ : ZStoreOk (LH hp i).exe (ZS))
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s' s0 s1
        lbl lsize ts j own₀ l →
      HelloHPre.FrH (D) lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA x29 ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat)
    /- row: 5j-misc-X. main's runtime facts at the clone (`HelloWiI.hWiH_I`'s `hX`). -/
    (hX : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s' s0 s1
        lbl lsize ts j own₀ l →
      HelloHPre.FrH (D) lbl lsize th s →
      th.st.exe = (LH hp i).exe ∧ th.st.endPc = endH hp i ∧ th.st.decls = {})
    /- rows: the child segment's (`Hello.SegR.ChildPrem`'s fields; `HelloWiI.hWiH_I`'s `hCP`)
    at the clone's data, given the packet. -/
    (hCP : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s' s0 s1
        lbl lsize ts j own₀ l →
      HelloHPre.FrH (D) lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
          (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w)
          (Spike.Lib.A64.Flow.DFrame (childR stack (-272)) (childAfter abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.X9.toBitVec, th.st.st.1.regs.X10.toBitVec, th.st.st.1.regs.X11.toBitVec,
            th.st.st.1.regs.X12.toBitVec, th.st.st.1.regs.X13.toBitVec, th.st.st.1.regs.X14.toBitVec⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2)
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → abi.atSys s = true →
      (isaLSE2.exec s).isSome)
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → abi.atSys s = false → ∀ e,
      isaLSE2.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (A64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- The worker's instructions are `RelW1`. -/
    (hRW1 : ∀ w s c fs e, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → isaLSE2.exec s = some e →
      EvTree.RelW1 Arch.armv8 e)
    /- row: 5i-hab1 (as `hello_obligations_RV`'s). -/
    (hab1W : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → AbFacts (μE) AbT s)
    /- row: 5i-hcl (as `hello_obligations_RV`'s). -/
    (hcl : ∀ d s tid th stack tls, (QQ).R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (Handover.childAfter abi d.2 tid th stack tls).st)
    /- row: 5j-wit-W (`HelloPostWit.post_wit_hello`'s `hplW`). The worker's invariant places every frame. -/
    (hplW : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs →
      A64ConsumerS.PlacedSE (LH hp i).Λ ((QQ).SR w).lbl s c fs)
    /- row: 5j-wit-E-call (`HelloPostWit.post_wit_hello`'s `hcall`; `HelloPlE.hplE_of`). From a `D.Wi` control
    on no frames, `print`'s call frame is placed. -/
    (hcall : ∀ w st c, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w st c [] → ∀ c', LocalRunS helloSrc c c' →
      c'.term = HelloSplit.workerCallH →
      A64ConsumerS.FramesPlaced (LH hp i).Λ ((QQ).SR w).lbl st [⟨"u", HelloSplit.workerRestH, c'.env, [], .unit⟩]) :
    WakeObligationsR arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1R) E hpa passT (D) (r1R)) E
      (fun t tr => TiPre (AbH hp i) (AcH hp i) t tr ∧ TwH (LH hp i).Λ E AbT t tr) helloSrc :=
  have ⟨htop, hal, hsz⟩ := r1c_facts (LH hp i) (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13) rfl
  hello_obligations_RV hp i (PS) (ZS) (XS) (hS) hpa hhp hd hlo hstat hpin2 hc hnz hB hE hA13 hst0 h2 h1 hW0 hW1 hW2 h0t
    h0o h1t h2t h2o hCl hG pT0 pass hZ hpc (hWiH_IG hp i (G0H hp i) hpa hhp htop hal hsz
        (fun w _ _ d h3 ho hc ha => ⟨rfl, d, ho, hc, h3 ▸ cwvH hp i w, ha⟩) hX hCP) hhalt1 hmapW hRW1 hab1W hcl hplW
    hcall

end Inst

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH0" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

/-- **`hello_obligations_RS` at `HelloAssemblyRC`'s choices** (`Ctx := CtxRH`, `frM := frH c0S.env`). -/
theorem hello_obligations_RSC {arch : WeakMem.Arch} {B : Scc.Sem.Budget} {E : Scc.Sem.Entry}
    {passT : State → Prop} {AbT} {ls : Lsize}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} :
    type_of% (@hello_obligations_RS asm pcfg o Λ0 hp (IH0) arch B E passT AbT
      (CtxRH (asm := asm) hp i0 E (fun _ => True) ls) ls (Spike.Lib.HelloRdCf.frH c0S.env) W1 inv1 W2 inv2) :=
  @hello_obligations_RS asm pcfg o Λ0 hp (IH0) arch B E passT AbT
    (CtxRH (asm := asm) hp i0 E (fun _ => True) ls) ls (Spike.Lib.HelloRdCf.frH c0S.env) W1 inv1 W2 inv2

/-- **`hello_obligations_RS` at the root's choices after the context switch** (`Ctx := LandRU.CtxRdU`: level 0's
context is rodata's counter add with the child's stack unmapped; `frM := frH c0S.env`). -/
theorem hello_obligations_RSU {arch : WeakMem.Arch} {B : Scc.Sem.Budget} {E : Scc.Sem.Entry}
    {passT : State → Prop} {AbT} {ls : Lsize}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} :
    type_of% (@hello_obligations_RS asm pcfg o Λ0 hp (IH0) arch B E passT AbT
      (Spike.Lib.A64.HelloPh.LandRU.CtxRdU (asm := asm) hp i0 E (fun _ => True) ls) ls
      (Spike.Lib.HelloRdCf.frH c0S.env) W1 inv1 W2 inv2) :=
  @hello_obligations_RS asm pcfg o Λ0 hp (IH0) arch B E passT AbT
    (Spike.Lib.A64.HelloPh.LandRU.CtxRdU (asm := asm) hp i0 E (fun _ => True) ls) ls
    (Spike.Lib.HelloRdCf.frH c0S.env) W1 inv1 W2 inv2

end Root

/-- info: 'Spike.Lib.HelloAssemblyRS.hello_obligations_RS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RS

/-- info: 'Spike.Lib.HelloAssemblyRS.hello_obligations_RSC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RSC

/-- info: 'Spike.Lib.HelloAssemblyRS.hello_obligations_RSU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RSU

end Spike.Lib.HelloAssemblyRS
