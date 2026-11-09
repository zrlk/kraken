/-
**hello.w on x86-64: the placed assembly at the root, source facts and `hti0` discharged** (the twin of
`Spike/Lib/HelloAssemblyRP.lean`: `X64HelloAssemblyR.hello_obligations_Rg` at the root's abort phases
`Ab := X64HelloOAb.AbH`, `Ac := X64HelloOAb.AcH`, the ones hello's rows instantiate).

`oPremH_Rg`'s source premises `hP`/`hsafe` are `X64HelloSrcOPrem.hello_hookOK`/`hello_srcSafeS` and its `hti0` is
`X64HelloOAb.hti0_H` (from the loader's parses and `hlo`).

- `hello_obligations_RPg`: the statement at `helloDRg own`; its premises are `hello_obligations_Rg`'s other than
  `hP`, `hsafe`, `hti0`.

## Unlike AArch64

- As `hello_obligations_Rg`: the label offsets `hoffs` and `hZW`, `hDd`, `hexe` are further premises, the
  loader's parses are `cellsOf asm`'s, and the segment end's bound is at `⟨Rm.base, -128, 40⟩`'s `fp 8`.
-/
import Spike.Lib.X64HelloAssemblyR
import Spike.Lib.X64HelloSrcOPrem
import Spike.Lib.X64HelloOAb

namespace Spike.Lib.X64HelloAssemblyRP

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
open Spike.Lib.X64.HelloPh.StartH0B (StartPH)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloSrcOPrem (hello_hookOK hello_srcSafeS)
open Spike.Lib.X64HelloOAb (AbH AcH hti0_H)

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
local notation "μE" => (target (kernel 2) E).marks asm (LH hp i).Λ

set_option hygiene false in
local notation "r1R" => Spike.Lib.X64WakeOSide.r1W hp i

set_option hygiene false in
local notation "DG" => Spike.Lib.X64HelloRootO.helloDRg (asm := asm) hp i own E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
/-- The pre-spawn relation at `helloDRg own`, with `VPriv` (`hello_obligations_IM`'s `R1 ∧ VPriv`). -/
local notation "R1G" => fun d s => R1OH arch (LH hp i).Λ (μH hp i E asm) (DG) XH d s ∧
  VPriv (LH hp i).Λ E d

/-- **The assembly at the placed instance at the root, `hP`/`hsafe`/`hti0` discharged** (see the module doc).
At an own map `own` (`helloDRg own`, the start segment at `W0Hg own`, `own`'s initial ownership `hown0`). -/
theorem hello_obligations_RPg (own : State → List (Loc × Val)) {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {passT : State → Prop}
    {Tw : Cfg → List Ev → Prop}
    {Ctx : FragS isa} {ls : Lsize} {frM : TermRun.Frame}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    /- the loader's parses (the trust boundary) -/
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts (as `X64HelloRootO.oPremH_Rg`) -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (LH hp i).pinA.toNat + 200 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- The second stack in the stack pool. -/
    (hsub1 : (r1R).Sub (LH hp i).Λ.stackPool)
    /- as `X64HelloRootO.oPremH_Rg`'s (the root's pre-spawn premises) -/
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
    (R : HelloRowsW arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R)) E
      (DH hp i (G0H hp i) P Z X hseg) (MH hp i (G0H hp i) E hpa) (AbW (LH hp i).exe)
      (hcwH hp i (G0H hp i) P Z X hseg) (hemH hp i (G0H hp i) P Z X hseg hZ) (AbH hp i) (AcH hp i) Tw) :
    WakeObligationsR arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R)) E
      (fun t tr => TiPre (AbH hp i) (AcH hp i) t tr ∧ Tw t tr) helloSrc :=
  X64HelloAssemblyR.hello_obligations_Rg hp i P Z X hseg own hpa hhp hd hoffs hlo hstat hpin2 hc hnz hB hE hsub1 hst0
    hown0 h2 h1 hW0 hW1 hW2
    h0t h0o h1t h2t h2o (hello_hookOK arch) (hello_srcSafeS arch _) (hti0_H hp i hpa hd hhp hlo E) hCl hG pT0 pass
    hZ hZW hDd hexe hpc hWi hhalt1 hmapW R

end Inst

end Spike.Lib.X64HelloAssemblyRP

/-- info: 'Spike.Lib.X64HelloAssemblyRP.hello_obligations_RPg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyRP.hello_obligations_RPg
