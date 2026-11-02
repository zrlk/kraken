/-
**hello.w on x86-64: the placed assembly at the root, the worker's segment and the child's entry
instantiated** (the twin of `Spike/Lib/HelloAssemblyRS.lean`): `X64HelloAssemblyRV.hello_obligations_RV` at the
root parameters `P := X64HelloWorkerDHF.PF`, `Z := ZF μE`, `X := XF μE`, `hseg := hsegFH` (the `DH := helloDRF`
switch; from the loader's parses `hpa`, `hhp`, `hlo` and the immediates' `ImmsKid` `hI`), its `hWi` by
`X64HelloAssemblyI.hWiH_IG` (`PF`'s word 3 by `cwvH`), whose handed-stack facts `htop`/`hsz` are
`X64HelloAssemblyI.r1c_facts` at the records' second stack `r1W = PreChild.r1Of (LH hp i).lab` and `hsub1`. The
chain below (`hello_obligations_I` … `hello_obligations_RV`) stays generic in `P`/`Z`/`hseg`/`hWi`; this file
instantiates them once.

- `hello_obligations_RS`: the statement; its premises are `hello_obligations_RV`'s at `PF`/`ZF`/`XF`/`hsegFH`,
  with `hWi` replaced by `hWiH_IG`'s open rows `hX` (main's runtime facts at the clone) and `hCP` (`ChildPrem`).
- `hello_obligations_RSU`: `hello_obligations_RS` at the root's choices after the context switch (the root's
  immediate table `HelloImms.immsH Λ0 i0`, `Ctx := LandRU.CtxRdU`, `frM := frH c0S.env`).
- `hello_obligations_RSg`, `hello_obligations_RSUg`: the same at an own map `own` (`helloDRg own`, over
  `hello_obligations_RVg`; the start segment at `W0Hg own` and `own`'s initial ownership `hown0`); at
  `own := ownGHXW …` the premise `hDd` is `rfl`.

## Unlike AArch64

- The worker's memory side is `X64HelloOwnLift.msWHX` (the worker owns its TCB self word `tcbWH`): `PF`,
  `hsegFH` and `hCP`'s `ChildPrem` are at it (AArch64 `HelloMsW.msWH`, no owned word).
- As `hello_obligations_RV`: the label offsets `hoffs`, `hpin2`, the store phase off the worker's self word
  (`hZW`), main's owned words at `ownGHXW` (`hDd`) and the spawned thread's executable (`hexe`) are further
  premises; the loader's parses are `cellsOf asm`'s; the segment end's bound is at `⟨Rm.base, -128, 40⟩`'s `fp 8`;
  the worker's `RelW1` is at `Arch.tso`.
- `hWiH_IG` asks no alignment of the handed stack (AArch64 `hal`); `hCP`'s words are `%r12`, `%rbx`, `%r13`,
  `%r14`, `%r15`, `%r9` (AArch64 `X9`–`X14`).
- AArch64's `hello_obligations_RSC` (at `HelloAssemblyRC`'s `Land.CtxRH`) has no twin: the root is at `CtxRdU`.
-/
import Spike.Lib.X64HelloAssemblyRV
import Spike.Lib.X64HelloWiI
import Spike.Lib.X64HelloLandRU
import Spike.Lib.X64HelloWorkerDHF
import Spike.Lib.X64HelloOInit
import Spike.Lib.X64HelloMarksL

namespace Spike.Lib.X64HelloAssemblyRS

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Inv2Core Spike.Lib.X64WakeInst
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1Store (ZStoreOk)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloPreA (ClonePreH)
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloMainHRD (MainSegH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakePrivR (VPriv)
open Spike.Lib.X64HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH μH hWiH_IG r1c_facts cwvH)
open Spike.Lib.X64HelloAssemblyIM (G0H)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.X64.HelloPh.RootH0 (msBotH)
open Spike.Lib.X64HelloRootO (helloDR)
open Spike.Lib.X64HelloOAb (AbH AcH)
open Spike.Lib.X64HelloPostAb (TwH AbFacts)
open Spike.Lib.X64HelloAssemblyRV (hello_obligations_RV)
open Spike.Lib.X64HelloOkW (lBH)
open Spike.Lib.Handover (childAfter)
open Spike.Lib.X64WakeW1 (mainTidW)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (ChildPrem)
open Spike.Lib.X64.HelloPh.C0S (c0S)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "AX" => (LH hp i).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "D" => helloDR (asm := asm) hp i E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks asm (LH hp i).Λ

set_option hygiene false in
/-- The pre-spawn relation at the root's data, with `VPriv` (`hello_obligations_IM`'s `R1 ∧ VPriv`). -/
local notation "R1R" => fun d s => R1OH arch (LH hp i).Λ (μH hp i E asm) (D) XH d s ∧
  VPriv (LH hp i).Λ E d

set_option hygiene false in
local notation "r1R" => Spike.Lib.X64WakeOSide.r1W hp i

set_option hygiene false in
/-- The root's worker fragment (`X64HelloWorkerDHF.PF`: `childPX` at the record's flag, at `msWHX`). -/
local notation "PS" => Spike.Lib.X64HelloWorkerDHF.PF hp i (G0H hp i)

set_option hygiene false in
/-- The root's store-phase fragment (`X64HelloWorkerDHF.ZF`). -/
local notation "ZS" => Spike.Lib.X64HelloWorkerDHF.ZF hp i (μE)

set_option hygiene false in
/-- The root's landing fragment (`X64HelloWorkerDHF.XF`: `XHF ∧ AbX μE lab`). -/
local notation "XS" => Spike.Lib.X64HelloWorkerDHF.XF hp i (μE)

set_option hygiene false in
/-- The root's worker segment (`X64HelloWorkerDHF.hsegFH`: `helloDRF`'s, from the loader's parses, the
immediates' `ImmsKid` `hI`, the labels at `lo` and `μE`'s marks). -/
local notation "hS" => Spike.Lib.X64HelloWorkerDHF.hsegFH hp i (G0H hp i) hI hpa hhp
  (Spike.Lib.X64HelloOInit.hlab_H hp i hpa hhp hlo)
  (Spike.Lib.X64HelloAssemblyI.marksL_HE hp i hpa hhp hlo (H := kernel 2) (E := E))

set_option hygiene false in
local notation "QQ" => QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1R) E hpa passT (D) (r1R)

/-- **The assembly at the root, the worker's segment and the child's entry instantiated** (see the module
doc). -/
theorem hello_obligations_RS {arch : WeakMem.Arch} {B : Budget} {E : Entry} {passT : State → Prop}
    {AbT : State → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the loader's parses (the trust boundary) -/
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts (as `X64HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    /- No immediate at the child's and the worker call's controls (`X64HelloWorkerDHF.hsegFH`'s `hI`). -/
    (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ)
    (hstat : Λ0.static = fun _ => none)
    (hpin2 : (LH hp i).pinA.toNat + 168 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- A13's data part (the second stack in the pool, `X64WakeStartPlaceLy.hsub1_W`). -/
    (hA13 : Scc.Cert.Spawn.X64.a13data (LH hp i).Λ o.prog o.secs = true)
    /- as `X64HelloRootO.oPremH_R`'s (the root's pre-spawn premises) -/
    (hst0 : SegWS (W0H (asm := asm) hp i E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (LH hp i))) helloSrc (L0T (LH hp i).Λ)
      (msBotH (asm := asm) hp i E (fun _ => True) ls inv1 inv2) (StartPH hp i E) (fun _ _ _ => False))
    (h2 : ∀ l b n l' b' n', (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      X64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      SegInvS ((D).W2 l b n l' b' n') (TakeCKS (D).a (D).Cl) helloSrc
        (X64ConsumerA.upd (X64ConsumerA.upd (D).L0 l b) l' b')
        (msOfA (LH hp i).Λ μE (D).rd (D).G (D).own (D).ar (fun _ _ _ _ _ => False)
          (X64ConsumerA.upd (X64ConsumerA.upd (D).L0 l b) l' b')
          (X64ConsumerA.updN (X64ConsumerA.updN (D).ls0 l n) l' n'))
        ((D).inv2 l b n l' b' n'))
    (h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      Spike.Lib.X64SegWPub.SegInvSP ((D).W1 l b n) (TakeCKS (D).a (D).Cl) helloSrc (X64ConsumerA.upd (D).L0 l b)
        (msOfA (LH hp i).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (X64ConsumerA.upd (D).L0 l b)
          (X64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n))
    (hW0 : ∀ s c fs, (D).inv0 s c fs → (D).W0 s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D)) (D).L0 (D).ls0 s c fs (D).Dt
        (AbH hp i) (D).Cl (AcH hp i))
    (hW1 : ∀ l b n s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n → (D).W1 l b n s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (X64ConsumerA.upd (D).L0 l b) (X64ConsumerA.updN (D).ls0 l n) s c fs (D).Dt (AbH hp i) (D).Cl (AcH hp i))
    (hW2 : ∀ l b n l' b' n' s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      X64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      (D).W2 l b n l' b' n' s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (X64ConsumerA.upd (X64ConsumerA.upd (D).L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN (D).ls0 l n) l' n') s c fs (D).Dt (AbH hp i) (D).Cl (AcH hp i))
    (h0t : Spike.Lib.X64HelloPreA.H0TakeH (LH hp i) (AX) (D).inv0)
    (h0o : Spike.Lib.X64HelloPreA.H0TakeOwnH (LH hp i) (AX) (D).inv0)
    (h1t : Spike.Lib.X64HelloPreA.Take1X.H1TakeXH (LH hp i) (AX) inv1)
    (h2t : Spike.Lib.X64HelloPreA.H2TakeH (LH hp i) (AX) inv2)
    (h2o : Spike.Lib.X64HelloPreA.H2TakeOwnH (LH hp i) (AX) inv2)
    /- as `hello_obligations_IM`'s -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QQ) (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH (D) lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      X64Consumer.HeldOk2 (LH hp i).Λ (D).r0 (D).r1 th.st d.2.held →
      Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH (LH hp i).Λ (D).r0 (r1R) X lbl d s)
    (hG : ∀ w m, MemInv (D).G m → MemInv (GH hp i (G0H hp i) w) m)
    (pT0 : Loc)
    (pass : X64HelloW1.PassH (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) passT)
    (hZ : ZStoreOk (LH hp i).exe (ZS))
    /- as `hello_obligations_RV`'s `hZW`, `hDd`, `hexe` -/
    (hZW : ∀ w s c, (ZS) w s c [] → c.hold = none → X64HelloW1Store.StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c)
    {a : BitVec 64} (hDd : ∀ s fs, (D).own s fs = Spike.Lib.X64.HelloPh.ownGHXW (LH hp i) a s)
    (hexe : ∀ d s th stack tls r, SpawnPrem (QQ) (LH hp i).Λ asm E 0 d s th stack tls r →
      th.st.exe = (LH hp i).exe)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QQ) (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s'
        s0 s1 lbl lsize ts j own₀ l →
      X64HelloHPre.FrH (D) lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    /- main's runtime facts at the clone (`hWiH_IG`'s `hX`) -/
    (hX : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QQ) (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s'
        s0 s1 lbl lsize ts j own₀ l →
      X64HelloHPre.FrH (D) lbl lsize th s →
      th.st.exe = (LH hp i).exe ∧ th.st.endPc = endH hp i ∧ th.st.decls = {})
    /- the child segment's premises (`Hello.SegR.ChildPrem`'s fields at `msWHX`; `hWiH_IG`'s `hCP`) at the clone's
    data, given the packet -/
    (hCP : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QQ) (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s'
        s0 s1 lbl lsize ts j own₀ l →
      X64HelloHPre.FrH (D) lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
          (fun _ => X64HelloOwnLift.msWHX (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w)
          (Spike.Lib.X64.DFrame (childR stack (-272)) (childAfter abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.get64 .r12, th.st.st.1.regs.get64 .rbx, th.st.st.1.regs.get64 .r13,
            th.st.st.1.regs.get64 .r14, th.st.st.1.regs.get64 .r15, th.st.st.1.regs.get64 .r9⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2)
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → abi.atSys s = true →
      (isa.exec s).isSome)
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → abi.atSys s = false → ∀ e,
      isa.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (X64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- The worker's instructions are `RelW1`. -/
    (hRW1 : ∀ w s c fs e, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → isa.exec s = some e →
      EvTree.RelW1 Arch.tso e)
    /- The worker's abort facts (as `hello_obligations_RV`'s). -/
    (hab1W : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → AbFacts (μE) AbT s)
    /- At `R1`'s `clone` one thread, the child out of `AbT` (as `hello_obligations_RV`'s). -/
    (hcl : ∀ d s tid th stack tls, (QQ).R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (Handover.childAfter abi d.2 tid th stack tls).st)
    /- The worker's invariant places every frame (`X64HelloPostWit.post_wit_hello`'s `hplW`). -/
    (hplW : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs →
      X64ConsumerS.PlacedSE (LH hp i).Λ ((QQ).SR w).lbl s c fs)
    /- From a `D.Wi` control on no frames, `print`'s call frame is placed (`X64HelloPostWit.post_wit_hello`'s
    `hcall`). -/
    (hcall : ∀ w st c, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w st c [] → ∀ c', LocalRunS helloSrc c c' →
      c'.term = X64HelloSplit.workerCallH →
      X64ConsumerS.FramesPlaced (LH hp i).Λ ((QQ).SR w).lbl st
        [⟨"u", X64HelloSplit.workerRestH, c'.env, [], .unit⟩]) :
    WakeObligationsR arch (LH hp i).Λ B asm (QQ) E
      (fun t tr => TiPre (AbH hp i) (AcH hp i) t tr ∧ TwH (LH hp i).Λ E AbT t tr) helloSrc :=
  have ⟨htop, hsz⟩ := r1c_facts (LH hp i) (Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13) rfl
  hello_obligations_RV hp i (PS) (ZS) (XS) (hS) hpa hhp hd hoffs hlo hstat hpin2 hc hnz hB hE hA13 hst0 h2 h1 hW0
    hW1 hW2 h0t h0o h1t h2t h2o hCl hG pT0 pass hZ hZW hDd hexe hpc
    (hWiH_IG hp i (G0H hp i) hpa hhp htop hsz
      (fun w _ _ d h3 ho hc ha => ⟨rfl, d, ho, hc, h3 ▸ cwvH hp i w, ha⟩) hX hCP)
    hhalt1 hmapW hRW1 hab1W hcl hplW hcall

set_option hygiene false in
local notation "DG" => Spike.Lib.X64HelloRootO.helloDRg (asm := asm) hp i own E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
/-- `R1R` at `helloDRg own`. -/
local notation "R1G" => fun d s => R1OH arch (LH hp i).Λ (μH hp i E asm) (DG) XH d s ∧
  VPriv (LH hp i).Λ E d

set_option hygiene false in
local notation "QG" => QH hp i (G0H hp i) (PS) (ZS) (XS) (hS) arch (R1G) E hpa passT (DG) (r1R)

/-- **The assembly at the root, the worker's segment and the child's entry instantiated** (see the module
doc).
At an own map `own` (`helloDRg own`, the start segment at `W0Hg own`, `own`'s initial ownership `hown0`). -/
theorem hello_obligations_RSg (own : State → List (Loc × Val)) {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {passT : State → Prop}
    {AbT : State → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the loader's parses (the trust boundary) -/
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts (as `X64HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    /- No immediate at the child's and the worker call's controls (`X64HelloWorkerDHF.hsegFH`'s `hI`). -/
    (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (LH hp i).Λ)
    (hstat : Λ0.static = fun _ => none)
    (hpin2 : (LH hp i).pinA.toNat + 168 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- A13's data part (the second stack in the pool, `X64WakeStartPlaceLy.hsub1_W`). -/
    (hA13 : Scc.Cert.Spawn.X64.a13data (LH hp i).Λ o.prog o.secs = true)
    /- as `X64HelloRootO.oPremH_R`'s (the root's pre-spawn premises) -/
    (hst0 : SegWS (Spike.Lib.X64.HelloPh.StartH0B.W0Hg (asm := asm) hp i own E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (LH hp i))) helloSrc (L0T (LH hp i).Λ)
      (Spike.Lib.X64.HelloPh.RootH0.msBotHg (asm := asm) hp i E (fun _ => True) ls inv1 inv2 own) (StartPH hp i E)
      (fun _ _ _ => False))
    /- `own` initially owned at the load (at `ownGH`: `X64HelloOInit.hown0_H`) -/
    (hown0 : ∀ t0, Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (LH hp i).Λ o.prog o.secs o.labelOffs = some t0 →
      Spike.Lib.Consumer1.OwnInit
        (own (Scc.Sem.X64.threadAt E (LH hp i).Λ.code.lo o.prog (Scc.Sem.loadSyms (LH hp i).Λ o.secs.rodata)))
        t0.1.mem)
    (h2 : ∀ l b n l' b' n', (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      X64ConsumerA.upd (DG).L0 l b l' = none → AllocLand (DG).ar.heap (DG).ar.cells b' n' →
      SegInvS ((DG).W2 l b n l' b' n') (TakeCKS (DG).a (DG).Cl) helloSrc
        (X64ConsumerA.upd (X64ConsumerA.upd (DG).L0 l b) l' b')
        (msOfA (LH hp i).Λ μE (DG).rd (DG).G (DG).own (DG).ar (fun _ _ _ _ _ => False)
          (X64ConsumerA.upd (X64ConsumerA.upd (DG).L0 l b) l' b')
          (X64ConsumerA.updN (X64ConsumerA.updN (DG).ls0 l n) l' n'))
        ((DG).inv2 l b n l' b' n'))
    (h1 : ∀ l b n, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      Spike.Lib.X64SegWPub.SegInvSP ((DG).W1 l b n) (TakeCKS (DG).a (DG).Cl) helloSrc (X64ConsumerA.upd (DG).L0 l b)
        (msOfA (LH hp i).Λ μE (DG).rd (DG).G (DG).own (DG).ar (IH (DG)) (X64ConsumerA.upd (DG).L0 l b)
          (X64ConsumerA.updN (DG).ls0 l n)) ((DG).inv1 l b n))
    (hW0 : ∀ s c fs, (DG).inv0 s c fs → (DG).W0 s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG)) (DG).L0 (DG).ls0 s c fs (DG).Dt
        (AbH hp i) (DG).Cl (AcH hp i))
    (hW1 : ∀ l b n s c fs, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n → (DG).W1 l b n s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG))
        (X64ConsumerA.upd (DG).L0 l b) (X64ConsumerA.updN (DG).ls0 l n) s c fs (DG).Dt (AbH hp i) (DG).Cl (AcH hp i))
    (hW2 : ∀ l b n l' b' n' s c fs, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      X64ConsumerA.upd (DG).L0 l b l' = none → AllocLand (DG).ar.heap (DG).ar.cells b' n' →
      (DG).W2 l b n l' b' n' s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG))
        (X64ConsumerA.upd (X64ConsumerA.upd (DG).L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN (DG).ls0 l n) l' n') s c fs (DG).Dt (AbH hp i) (DG).Cl (AcH hp i))
    (h0t : Spike.Lib.X64HelloPreA.H0TakeH (LH hp i) (AX) (DG).inv0)
    (h0o : Spike.Lib.X64HelloPreA.H0TakeOwnH (LH hp i) (AX) (DG).inv0)
    (h1t : Spike.Lib.X64HelloPreA.Take1X.H1TakeXH (LH hp i) (AX) inv1)
    (h2t : Spike.Lib.X64HelloPreA.H2TakeH (LH hp i) (AX) inv2)
    (h2o : Spike.Lib.X64HelloPreA.H2TakeOwnH (LH hp i) (AX) inv2)
    /- as `hello_obligations_IM`'s -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QG) (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH (DG) lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      X64Consumer.HeldOk2 (LH hp i).Λ (DG).r0 (DG).r1 th.st d.2.held →
      Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH (LH hp i).Λ (DG).r0 (r1R) X lbl d s)
    (hG : ∀ w m, MemInv (DG).G m → MemInv (GH hp i (G0H hp i) w) m)
    (pT0 : Loc)
    (pass : X64HelloW1.PassH (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) passT)
    (hZ : ZStoreOk (LH hp i).exe (ZS))
    /- as `hello_obligations_RV`'s `hZW`, `hDd`, `hexe` -/
    (hZW : ∀ w s c, (ZS) w s c [] → c.hold = none → X64HelloW1Store.StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c)
    {a : BitVec 64} (hDd : ∀ s fs, (DG).own s fs = Spike.Lib.X64.HelloPh.ownGHXW (LH hp i) a s)
    (hexe : ∀ d s th stack tls r, SpawnPrem (QG) (LH hp i).Λ asm E 0 d s th stack tls r →
      th.st.exe = (LH hp i).exe)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QG) (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1G) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (DG).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s'
        s0 s1 lbl lsize ts j own₀ l →
      X64HelloHPre.FrH (DG) lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    /- main's runtime facts at the clone (`hWiH_IG`'s `hX`) -/
    (hX : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QG) (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1G) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (DG).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s'
        s0 s1 lbl lsize ts j own₀ l →
      X64HelloHPre.FrH (DG) lbl lsize th s →
      th.st.exe = (LH hp i).exe ∧ th.st.endPc = endH hp i ∧ th.st.decls = {})
    /- the child segment's premises (`Hello.SegR.ChildPrem`'s fields at `msWHX`; `hWiH_IG`'s `hCP`) at the clone's
    data, given the packet -/
    (hCP : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QG) (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1G) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)) (fun _ => (DG).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s'
        s0 s1 lbl lsize ts j own₀ l →
      X64HelloHPre.FrH (DG) lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
          (fun _ => X64HelloOwnLift.msWHX (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w)
          (Spike.Lib.X64.DFrame (childR stack (-272)) (childAfter abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.get64 .r12, th.st.st.1.regs.get64 .rbx, th.st.st.1.regs.get64 .r13,
            th.st.st.1.regs.get64 .r14, th.st.st.1.regs.get64 .r15, th.st.st.1.regs.get64 .r9⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2)
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → abi.atSys s = true →
      (isa.exec s).isSome)
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → abi.atSys s = false → ∀ e,
      isa.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (X64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- The worker's instructions are `RelW1`. -/
    (hRW1 : ∀ w s c fs e, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → isa.exec s = some e →
      EvTree.RelW1 Arch.tso e)
    /- The worker's abort facts (as `hello_obligations_RV`'s). -/
    (hab1W : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs → AbFacts (μE) AbT s)
    /- At `R1`'s `clone` one thread, the child out of `AbT` (as `hello_obligations_RV`'s). -/
    (hcl : ∀ d s tid th stack tls, (QG).R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (Handover.childAfter abi d.2 tid th stack tls).st)
    /- The worker's invariant places every frame (`X64HelloPostWit.post_wit_hello`'s `hplW`). -/
    (hplW : ∀ w s c fs, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w s c fs →
      X64ConsumerS.PlacedSE (LH hp i).Λ ((QG).SR w).lbl s c fs)
    /- From a `D.Wi` control on no frames, `print`'s call frame is placed (`X64HelloPostWit.post_wit_hello`'s
    `hcall`). -/
    (hcall : ∀ w st c, (DH hp i (G0H hp i) (PS) (ZS) (XS) (hS)).Wi w st c [] → ∀ c', LocalRunS helloSrc c c' →
      c'.term = X64HelloSplit.workerCallH →
      X64ConsumerS.FramesPlaced (LH hp i).Λ ((QG).SR w).lbl st
        [⟨"u", X64HelloSplit.workerRestH, c'.env, [], .unit⟩]) :
    WakeObligationsR arch (LH hp i).Λ B asm (QG) E
      (fun t tr => TiPre (AbH hp i) (AcH hp i) t tr ∧ TwH (LH hp i).Λ E AbT t tr) helloSrc :=
  have ⟨htop, hsz⟩ := r1c_facts (LH hp i) (Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13) rfl
  X64HelloAssemblyRV.hello_obligations_RVg hp i (PS) (ZS) (XS) (hS) own hpa hhp hd hoffs hlo hstat hpin2 hc hnz hB hE
    hA13 hst0 hown0 h2 h1 hW0
    hW1 hW2 h0t h0o h1t h2t h2o hCl hG pT0 pass hZ hZW hDd hexe hpc
    (hWiH_IG hp i (G0H hp i) hpa hhp htop hsz
      (fun w _ _ d h3 ho hc ha => ⟨rfl, d, ho, hc, h3 ▸ cwvH hp i w, ha⟩) hX hCP)
    hhalt1 hmapW hRW1 hab1W hcl hplW hcall

end Inst

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH0" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

/-- **`hello_obligations_RS` at the root's choices after the context switch** (`Ctx := LandRU.CtxRdU`: level 0's
context is rodata's counter add with the child's stack unmapped; `frM := frH c0S.env`). -/
theorem hello_obligations_RSU {arch : WeakMem.Arch} {B : Scc.Sem.Budget} {E : Scc.Sem.Entry}
    {passT : State → Prop} {AbT} {ls : Lsize}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa} :
    type_of% (@hello_obligations_RS asm pcfg o Λ0 hp (IH0) arch B E passT AbT
      (Spike.Lib.X64.HelloPh.LandRU.CtxRdU (asm := asm) hp i0 E (fun _ => True) ls) ls
      (Spike.Lib.X64HelloRdCf.frH c0S.env) W1 inv1 W2 inv2) :=
  @hello_obligations_RS asm pcfg o Λ0 hp (IH0) arch B E passT AbT
    (Spike.Lib.X64.HelloPh.LandRU.CtxRdU (asm := asm) hp i0 E (fun _ => True) ls) ls
    (Spike.Lib.X64HelloRdCf.frH c0S.env) W1 inv1 W2 inv2

/-- **`hello_obligations_RSg` at the root's choices after the context switch** (as `hello_obligations_RSU`, at an
own map `own`). -/
theorem hello_obligations_RSUg (own : State → List (Loc × Val)) {arch : WeakMem.Arch} {B : Scc.Sem.Budget}
    {E : Scc.Sem.Entry} {passT : State → Prop} {AbT} {ls : Lsize}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa} :
    type_of% (@hello_obligations_RSg asm pcfg o Λ0 hp (IH0) own arch B E passT AbT
      (Spike.Lib.X64.HelloPh.LandRU.CtxRdU (asm := asm) hp i0 E (fun _ => True) ls) ls
      (Spike.Lib.X64HelloRdCf.frH c0S.env) W1 inv1 W2 inv2) :=
  @hello_obligations_RSg asm pcfg o Λ0 hp (IH0) own arch B E passT AbT
    (Spike.Lib.X64.HelloPh.LandRU.CtxRdU (asm := asm) hp i0 E (fun _ => True) ls) ls
    (Spike.Lib.X64HelloRdCf.frH c0S.env) W1 inv1 W2 inv2

end Root

/-- info: 'Spike.Lib.X64HelloAssemblyRS.hello_obligations_RS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RS

/-- info: 'Spike.Lib.X64HelloAssemblyRS.hello_obligations_RSU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RSU

/-- info: 'Spike.Lib.X64HelloAssemblyRS.hello_obligations_RSg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RSg

/-- info: 'Spike.Lib.X64HelloAssemblyRS.hello_obligations_RSUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_obligations_RSUg

end Spike.Lib.X64HelloAssemblyRS
