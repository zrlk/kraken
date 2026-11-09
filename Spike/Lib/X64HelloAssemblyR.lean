/-
**hello.w on x86-64: the placed assembly at the root's pre-spawn data** (the twin of
`Spike/Lib/HelloAssemblyR.lean`, at an own map `own`: `X64HelloAssemblyIM.hello_obligations_IM` at the
certificate's listing, its `O` and `hR1` from the root: `Dd := X64HelloRootO.helloDRg own …`, the pre-spawn relation
`R1OH … helloDRg own … XH`, `O` by `X64HelloOLift.hello_O_X` of `X64HelloRootO.oPremH_Rg`, `hR1` by `id`).

The records' second stack `r1c` is the root's `r1W`, so `hello_obligations_IM`'s `hsub1` and `oPremH_Rg`'s are one
premise.

- `hello_obligations_Rg`: the statement (AArch64 `hello_obligations_R`); its premises are `hello_obligations_IM`'s
  other than `O`/`hR1` and `oPremH_Rg`'s, its start relation by `X64HelloOHinit.hinit_Hg` from `own`'s initial
  ownership `hown0` and the start segment at `W0Hg own`.

## Unlike AArch64

- The loader's parses are `cellsOf asm = some …`, the data sections `asm.text`'s, and the listing's label offsets
  a further premise `hoffs` (shared by `hello_obligations_IM` and `oPremH_Rg`).
- main's memory side owns its TCB self word (`X64HelloMs.msHX`), so the park's ownership of it is closed
  (`X64HelloMainGH.hMainRH_ofGH`); the worker's segment `hseg` is at its owning side `msWHX`, and
  `hello_obligations_IM`'s `hZW`, `hDd`, `hexe` are premises here too.
- The clone's `ClonePreH` carries no label prefix; the segment end's region is `⟨Rm.base, -128, 40⟩`, its bound
  at `(R.fp 8).addr 0 - 8 - 16` (AArch64 `⟨Rm.base, -144, 48⟩`, `R.addr (-32)`).
-/
import Spike.Lib.X64HelloAssemblyIM
import Spike.Lib.X64HelloRootO
import Spike.Lib.X64HelloOLift
import Spike.Lib.X64HelloOHinit

namespace Spike.Lib.X64HelloAssemblyR

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
open Spike.Lib.X64HelloO (IH R1OH)
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
local notation "DG" => X64HelloRootO.helloDRg (asm := asm) hp i own E Ctx ls frM W1 inv1 W2 inv2

set_option hygiene false in
/-- The pre-spawn relation at the root's data `helloDRg own`, with `VPriv` (`hello_obligations_IM`'s
`R1 ∧ VPriv`). -/
local notation "R1G" => fun d s => R1OH arch (LH hp i).Λ (μH hp i E asm) (DG) XH d s ∧
  VPriv (LH hp i).Λ E d

/-- **The assembly at the placed instance at the root's pre-spawn data, at an own map `own`** (`helloDRg own`; the
start's relation at the load by `X64HelloOHinit.hinit_Hg` from `own`'s initial ownership `hown0` and the start
segment at `W0Hg own`). -/
theorem hello_obligations_Rg (own : State → List (Loc × Val)) {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {passT : State → Prop}
    {Ab Ac : State → Prop} {Tw : Cfg → List Ev → Prop}
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
      SFactsACH (LH hp i).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG)) (DG).L0 (DG).ls0 s c fs (DG).Dt Ab
        (DG).Cl Ac)
    (hW1 : ∀ l b n s c fs, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n → (DG).W1 l b n s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG))
        (X64ConsumerA.upd (DG).L0 l b) (X64ConsumerA.updN (DG).ls0 l n) s c fs (DG).Dt Ab (DG).Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, (DG).L0 l = none → AllocLand (DG).ar.heap (DG).ar.cells b n →
      X64ConsumerA.upd (DG).L0 l b l' = none → AllocLand (DG).ar.heap (DG).ar.cells b' n' →
      (DG).W2 l b n l' b' n' s c fs →
      SFactsACH (LH hp i).Λ μE helloSrc (DG).rd (DG).G (DG).own (DG).ar (IH (DG))
        (X64ConsumerA.upd (X64ConsumerA.upd (DG).L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN (DG).ls0 l n) l' n') s c fs (DG).Dt Ab (DG).Cl Ac)
    (h0t : Spike.Lib.X64HelloPreA.H0TakeH (LH hp i) (AX) (DG).inv0)
    (h0o : Spike.Lib.X64HelloPreA.H0TakeOwnH (LH hp i) (AX) (DG).inv0)
    (h1t : Spike.Lib.X64HelloPreA.Take1X.H1TakeXH (LH hp i) (AX) inv1)
    (h2t : Spike.Lib.X64HelloPreA.H2TakeH (LH hp i) (AX) inv2)
    (h2o : Spike.Lib.X64HelloPreA.H2TakeOwnH (LH hp i) (AX) inv2)
    (hP : HookOK (srcPo 2 arch helloSrc) helloSrc)
    (hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (IH (DG)))
    (hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm (LH hp i).Λ = some d → TIC Ab Ac [] d)
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
      (hcwH hp i (G0H hp i) P Z X hseg) (hemH hp i (G0H hp i) P Z X hseg hZ) Ab Ac Tw) :
    WakeObligationsR arch (LH hp i).Λ B asm
      (QH hp i (G0H hp i) P Z X hseg arch (R1G) E hpa passT (DG) (r1R)) E
      (fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) helloSrc :=
  X64HelloAssemblyIM.hello_obligations_IM hp i P Z X hseg hpa hhp hd hoffs hE hpin2 hlo
    (X64HelloOLift.hello_O_X (X64HelloRootO.oPremH_Rg hp i own hpa hpin2 hsub1 hc arch hB h2 h1 hW0 hW1 hW2 h0t h0o
      h1t h2t h2o hP hsafe hti0
      (X64HelloOHinit.hinit_Hg hp i hpa hd hoffs hstat hsub1 hc hpin2 arch hE μE (IH (DG)) ls hown0
        (.inl ⟨rfl, rfl, Spike.Lib.X64.HelloPh.RootH0.hstHg hp i E (fun _ => True) Ctx ls ls frM inv1 inv2 own
          hst0⟩))))
    (fun _ _ h => h) hCl hG pT0 pass hZ hZW hDd hexe hsub1 hpc hWi hhalt1 hmapW R

end Inst

end Spike.Lib.X64HelloAssemblyR

/-- info: 'Spike.Lib.X64HelloAssemblyR.hello_obligations_Rg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyR.hello_obligations_Rg
