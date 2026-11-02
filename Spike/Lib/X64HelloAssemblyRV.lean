/-
**hello.w on x86-64: the placed assembly at the root, `hconv` wired** (the twin of
`Spike/Lib/HelloAssemblyRV.lean`: `X64HelloAssemblyRP.hello_obligations_RP` with its rows `R` from
`X64HelloRowsV.HelloRowsWV.toW`: `hconv` by `X64HelloConv1.hconvH` at the instance's `hwf`
(`X64WakeOSide.hwf_W`), `hms` (the worker's memory side does not read its frames, `rfl`), `hPT0`/`hKR` (`rfl`,
`X64HelloQ`), the worker's `RelW1` a premise, `hRW1`). `post_step1` wired too: the rows are
`X64HelloRowsV1.HelloRowsW1` (no `post_step1`), and `HelloRowsW1.toW` fills it by
`X64HelloStep1RI.post_step1RI` at the side facts of `X64HelloSideI` (`hml_I`, `hAbX_I` from the parses
`hpa`/`hhp`, `hfz_I`, `hES_I`; `hown` by `X64HelloOwn1.own1H_XW` at `X64HelloAssemblyI.own_QH`, the flag word
off `tcbWH` by `X64HelloSelfOK.cT_ne_tcbWH_placedH`; `hlbl`, `hbo` by `rfl`, `hNP` by
`WakeP.noProm_prom`) and the entry's
`hE`. The post-spawn aborts are wired by `X64HelloRowsV2.helloRowsW1_of`: at
`Tw := X64HelloPostAb.TwH (LH hp i).Λ E AbT`, `post_abort`, `tw_load`, `tw_step` by `X64HelloPostAbH`, the
program wide by `PlaceWX.wideIn_of_placeWX`; the open inputs are the premises `hab1W` and `hcl`. `post_wit` by
`X64HelloPostWit.post_wit_hello`, main's placement by `hplM_helloM`; its open inputs are the premises `hplW` and
`hcall`. The second stack in the pool is `X64WakeStartPlaceLy.hsub1_W` from A13's data part (`hA13`).

- `hello_obligations_RV`: the statement; its premises are `hello_obligations_RP`'s with `R` replaced by `hRW1`
  and the other rows, `hsub1` by `hA13`.
- `hello_obligations_RVg`: the same at `helloDRg own` (`hello_obligations_RPg`).

## Unlike AArch64

- As `hello_obligations_RP`: the label offsets `hoffs` and `hZW`, `hDd`, `hexe` are further premises, the
  loader's parses are `cellsOf asm`'s, and the segment end's bound is at `⟨Rm.base, -128, 40⟩`'s `fp 8`.
- The worker's `RelW1` (`hRW1`) is at `Arch.tso` (AArch64 `Arch.armv8`).
-/
import Spike.Lib.X64HelloAssemblyRP
import Spike.Lib.X64HelloRowsV
import Spike.Lib.X64HelloSideI
import Spike.Lib.X64HelloRowsV2
import Spike.Lib.X64HelloPostWit
import Spike.Lib.X64WakeStartPlaceLy

namespace Spike.Lib.X64HelloAssemblyRV

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Inv2Core Spike.Lib.X64WakeInst
open Spike.Lib.X64WakeT1 (srcPo)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1Store (ZStoreOk)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64.Flow.Worker (NNH AbW)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloPreA (ClonePreH)
open Spike.Lib.X64HelloSpawnR (PreRH HWiH)
open Spike.Lib.X64HelloMainHRD (MainSegH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakePrivR (VPriv)
open Spike.Lib.X64HelloAssembly (HelloRowsW)
open Spike.Lib.X64HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH hcwH hemH μH)
open Spike.Lib.X64HelloAssemblyIM (G0H)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.X64.HelloPh.RootH0 (msBotH)
open Spike.Lib.X64HelloRootO (helloDR oPremH_R)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloAssemblyR (hello_obligations_R)
open Spike.Lib.X64HelloSrcOPrem (hello_hookOK hello_srcSafeS)
open Spike.Lib.X64HelloOAb (AbH AcH hti0_H)
open Spike.Lib.X64HelloAssemblyRP (hello_obligations_RP)
open Spike.Lib.X64HelloRowsV1 (HelloRowsW1)
open Spike.Lib.X64HelloPostAb (TwH AbFacts)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

variable (P Z X : ιH hp i → FragS isa)
  /- the worker's segment at hello's memory side (as `hello_obligations_IM`'s `hseg`) -/
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w) (P w) (fun _ _ _ => False))

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
local notation "QQ" => QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R)

/-- **The assembly at the placed instance at the root, `hconv` wired** (see the module doc). -/
theorem hello_obligations_RV {arch : WeakMem.Arch} {B : Budget} {E : Entry} {passT : State → Prop}
    {AbT : State → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the loader's parses (the trust boundary) -/
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts (as `X64HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
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
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH (D) lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      X64Consumer.HeldOk2 (LH hp i).Λ (D).r0 (D).r1 th.st d.2.held →
      Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH (LH hp i).Λ (D).r0 (r1R) X lbl d s)
    (hG : ∀ w m, MemInv (D).G m → MemInv (GH hp i (G0H hp i) w) m)
    (pT0 : Loc)
    (pass : X64HelloW1.PassH (DH hp i (G0H hp i) P Z X hseg) passT)
    (hZ : ZStoreOk (LH hp i).exe Z)
    /- as `hello_obligations_IM`'s `hZW`, `hDd`, `hexe` -/
    (hZW : ∀ w s c, Z w s c [] → c.hold = none → X64HelloW1Store.StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c)
    {a : BitVec 64} (hDd : ∀ s fs, (D).own s fs = Spike.Lib.X64.HelloPh.ownGHXW (LH hp i) a s)
    (hexe : ∀ d s th stack tls r, SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R))
      (LH hp i).Λ asm E 0 d s th stack tls r → th.st.exe = (LH hp i).exe)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) P Z X hseg) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s' s0 s1 lbl
        lsize ts j own₀ l →
      X64HelloHPre.FrH (D) lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    (hWi : HWiH arch (R1R) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
      (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
      (DH hp i (G0H hp i) P Z X hseg) (fun _ => (D).r0) (fun _ => r1R) (LH hp i).Λ asm E
      (X64HelloHPre.FrH (D)))
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = true →
      (isa.exec s).isSome)
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = false → ∀ e,
      isa.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (X64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- The worker's instructions are `RelW1`. -/
    (hRW1 : ∀ w s c fs e, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → isa.exec s = some e →
      EvTree.RelW1 Arch.tso e)
    /- The worker's abort facts (`X64HelloRowsV2.helloRowsW1_of`'s). -/
    (hab1W : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → AbFacts (μE) AbT s)
    /- At `R1`'s `clone` one thread, the child out of `AbT` (`X64HelloRowsV2.helloRowsW1_of`'s). -/
    (hcl : ∀ d s tid th stack tls, (QQ).R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (Handover.childAfter abi d.2 tid th stack tls).st)
    /- The worker's invariant places every frame (`X64HelloPostWit.post_wit_hello`'s `hplW`). -/
    (hplW : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs →
      X64ConsumerS.PlacedSE (LH hp i).Λ ((QQ).SR w).lbl s c fs)
    /- From a `D.Wi` control on no frames, `print`'s call frame is placed (`X64HelloPostWit.post_wit_hello`'s
    `hcall`). -/
    (hcall : ∀ w st c, (DH hp i (G0H hp i) P Z X hseg).Wi w st c [] → ∀ c', LocalRunS helloSrc c c' →
      c'.term = X64HelloSplit.workerCallH →
      X64ConsumerS.FramesPlaced (LH hp i).Λ ((QQ).SR w).lbl st
        [⟨"u", X64HelloSplit.workerRestH, c'.env, [], .unit⟩]) :
    WakeObligationsR arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (R1R) E hpa passT (D) (r1R)) E
      (fun t tr => TiPre (AbH hp i) (AcH hp i) t tr ∧ TwH (LH hp i).Λ E AbT t tr) helloSrc :=
  hello_obligations_RP hp i P Z X hseg hpa hhp hd hoffs hlo hstat hpin2 hc hnz hB hE
    (Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13) hst0 h2 h1 hW0 hW1 hW2 h0t h0o
    h1t h2t h2o hCl hG pT0 pass hZ hZW hDd hexe hpc hWi hhalt1 hmapW
    ((X64HelloRowsV2.helloRowsW1_of (fun _ h => by rw [hpa] at h; cases h; exact PlaceWX.wideIn_of_placeWX hp) rfl
      rfl rfl hab1W hcl
      (X64HelloPostWit.post_wit_hello (Spike.Lib.X64WakeOSide.hwf_W hp i) rfl rfl X64HelloPostWit.hplM_helloM hplW
        hcall)).toW (Spike.Lib.X64WakeOSide.hwf_W hp i) hE (fun _ _ => rfl)
    (X64HelloOwn1.own1H_XW (X64HelloAssemblyI.own_QH hp i _ _ _ _ _ _ _ _ _ _ _ _) (fun _ _ => rfl)
      (fun w _ _ _ _ _ hm => X64HelloSelfOK.cT_ne_tcbWH_placedH hp i hm w.2.1 (X64HelloOkHR.okHR_self w))) rfl rfl
    (X64HelloSideI.hml_I hp i _ _ _ _ _ hpa)
    (X64HelloSideI.hAbX_I hp i _ _ _ _ _ (Option.some.inj (hpa.symm.trans hhp)) hpa) (fun _ => rfl)
    (X64HelloSideI.hfz_I hp i _ _ _ _ _ hpa) (fun _ _ => rfl) (X64HelloSideI.hES_I hp i _ _ _ _ _)
    (fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc) hRW1)

set_option hygiene false in
local notation "DG" => Spike.Lib.X64HelloRootO.helloDRg (asm := asm) hp i own E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
/-- `R1R` at `helloDRg own`. -/
local notation "R1G" => fun d s => R1OH arch (LH hp i).Λ (μH hp i E asm) (DG) XH d s ∧
  VPriv (LH hp i).Λ E d

set_option hygiene false in
local notation "QG" => QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R)

/-- **The assembly at the placed instance at the root, `hconv` wired** (see the module doc).
At an own map `own` (`helloDRg own`, the start segment at `W0Hg own`, `own`'s initial ownership `hown0`). -/
theorem hello_obligations_RVg (own : State → List (Loc × Val)) {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {passT : State → Prop}
    {AbT : State → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the loader's parses (the trust boundary) -/
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts (as `X64HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
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
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH (DG) lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      X64Consumer.HeldOk2 (LH hp i).Λ (DG).r0 (DG).r1 th.st d.2.held →
      Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH (LH hp i).Λ (DG).r0 (r1R) X lbl d s)
    (hG : ∀ w m, MemInv (DG).G m → MemInv (GH hp i (G0H hp i) w) m)
    (pT0 : Loc)
    (pass : X64HelloW1.PassH (DH hp i (G0H hp i) P Z X hseg) passT)
    (hZ : ZStoreOk (LH hp i).exe Z)
    /- as `hello_obligations_IM`'s `hZW`, `hDd`, `hexe` -/
    (hZW : ∀ w s c, Z w s c [] → c.hold = none → X64HelloW1Store.StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c)
    {a : BitVec 64} (hDd : ∀ s fs, (DG).own s fs = Spike.Lib.X64.HelloPh.ownGHXW (LH hp i) a s)
    (hexe : ∀ d s th stack tls r, SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R))
      (LH hp i).Λ asm E 0 d s th stack tls r → th.st.exe = (LH hp i).exe)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R))
        (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1G) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
        (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
        (DH hp i (G0H hp i) P Z X hseg) (fun _ => (DG).r0) (fun _ => r1R) (LH hp i).Λ w d th stack s s' s0 s1 lbl
        lsize ts j own₀ l →
      X64HelloHPre.FrH (DG) lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    (hWi : HWiH arch (R1G) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS)
      (fun w => w.1.pT) (PaH hp i E asm) (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa)
      (DH hp i (G0H hp i) P Z X hseg) (fun _ => (DG).r0) (fun _ => r1R) (LH hp i).Λ asm E
      (X64HelloHPre.FrH (DG)))
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = true →
      (isa.exec s).isSome)
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = false → ∀ e,
      isa.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (X64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- The worker's instructions are `RelW1`. -/
    (hRW1 : ∀ w s c fs e, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → isa.exec s = some e →
      EvTree.RelW1 Arch.tso e)
    /- The worker's abort facts (`X64HelloRowsV2.helloRowsW1_of`'s). -/
    (hab1W : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → AbFacts (μE) AbT s)
    /- At `R1`'s `clone` one thread, the child out of `AbT` (`X64HelloRowsV2.helloRowsW1_of`'s). -/
    (hcl : ∀ d s tid th stack tls, (QG).R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (Handover.childAfter abi d.2 tid th stack tls).st)
    /- The worker's invariant places every frame (`X64HelloPostWit.post_wit_hello`'s `hplW`). -/
    (hplW : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs →
      X64ConsumerS.PlacedSE (LH hp i).Λ ((QG).SR w).lbl s c fs)
    /- From a `D.Wi` control on no frames, `print`'s call frame is placed (`X64HelloPostWit.post_wit_hello`'s
    `hcall`). -/
    (hcall : ∀ w st c, (DH hp i (G0H hp i) P Z X hseg).Wi w st c [] → ∀ c', LocalRunS helloSrc c c' →
      c'.term = X64HelloSplit.workerCallH →
      X64ConsumerS.FramesPlaced (LH hp i).Λ ((QG).SR w).lbl st
        [⟨"u", X64HelloSplit.workerRestH, c'.env, [], .unit⟩]) :
    WakeObligationsR arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R)) E
      (fun t tr => TiPre (AbH hp i) (AcH hp i) t tr ∧ TwH (LH hp i).Λ E AbT t tr) helloSrc :=
  X64HelloAssemblyRP.hello_obligations_RPg hp i P Z X hseg own hpa hhp hd hoffs hlo hstat hpin2 hc hnz hB hE
    (Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp i hA13) hst0 hown0 h2 h1 hW0 hW1 hW2 h0t h0o
    h1t h2t h2o hCl hG pT0 pass hZ hZW hDd hexe hpc hWi hhalt1 hmapW
    ((X64HelloRowsV2.helloRowsW1_of (fun _ h => by rw [hpa] at h; cases h; exact PlaceWX.wideIn_of_placeWX hp) rfl
      rfl rfl hab1W hcl
      (X64HelloPostWit.post_wit_hello (Spike.Lib.X64WakeOSide.hwf_W hp i) rfl rfl X64HelloPostWit.hplM_helloM hplW
        hcall)).toW (Spike.Lib.X64WakeOSide.hwf_W hp i) hE (fun _ _ => rfl)
    (X64HelloOwn1.own1H_XW (X64HelloAssemblyI.own_QH hp i _ _ _ _ _ _ _ _ _ _ _ _) (fun _ _ => rfl)
      (fun w _ _ _ _ _ hm => X64HelloSelfOK.cT_ne_tcbWH_placedH hp i hm w.2.1 (X64HelloOkHR.okHR_self w))) rfl rfl
    (X64HelloSideI.hml_I hp i _ _ _ _ _ hpa)
    (X64HelloSideI.hAbX_I hp i _ _ _ _ _ (Option.some.inj (hpa.symm.trans hhp)) hpa) (fun _ => rfl)
    (X64HelloSideI.hfz_I hp i _ _ _ _ _ hpa) (fun _ _ => rfl) (X64HelloSideI.hES_I hp i _ _ _ _ _)
    (fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc) hRW1)

end Inst

end Spike.Lib.X64HelloAssemblyRV

/-- info: 'Spike.Lib.X64HelloAssemblyRV.hello_obligations_RV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyRV.hello_obligations_RV

/-- info: 'Spike.Lib.X64HelloAssemblyRV.hello_obligations_RVg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyRV.hello_obligations_RVg
