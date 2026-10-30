/-
**wake.w's AArch64 root with the callee's take** (`CorrectE 2`):
`WakeRoot.wake_rootP` with `h1` from `WakeH1A.wake_h1A` (its `hmid` by
`WakeHatA.hmid_boxA`) in place of `WakeH1Root.wake_h1`; `hG` at `H1GA`.
`inv1R`, `msBot`, `inv0R`, `H1R`, `RootOpen`, `hokb_R` are `WakeRoot`'s.
No absolute address appears in this file.
-/
import Spike.Lib.A64WakeRoot
import Spike.Lib.A64WakeH1A

namespace Spike.Lib.WakeRootA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeSpawnR
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeOPremW (W0W W1W)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeRoot (inv1R H1R msBot inv0R RootOpen hokb_R)

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2)
  (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`wake_rootP` with the callee's take**: `CorrectE 2` at the
certificate's output from the loader check `hP`, the instance facts, per
entry `wake_h1A`'s premises (`hG` at `H1GA`, `hobl`) and `RootOpen` given
`h1`'s statement. The body is `wake_root`'s, `wake_h1A` for `wake_h1`. -/
theorem wake_rootPA (hp : PlaceW pcfg Λ0 SccCertificate.outLit) {arch : WeakMem.Arch} {B : Budget}
    (fs0 : Entry → List TermRun.Frame) (F0 : Entry → MachineData → Prop)
    /- the loader's check of the certificate (the trust boundary) -/
    (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (Ly).exe)
    (hnz : WakeOInit.NtZ Λ0 SccCertificate.outLit = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- `wake_h1A`'s premises per entry -/
    (hG : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ R F J0 t, WakeHMid.BoxPure (Ly) (F0 E) n R F J0 t →
        WakeH1A.H1GA hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) l b n R F t)
    (hobl : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      WakeRefSeg.RefObl hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) l b n)
    /- the rest of `OpenW`, given `h1`'s statement -/
    (hRO : ∀ E : Entry, E.Ok (Ly).Λ → H1R hp i ls0 Ctx (msBot hp i ls0 Ctx E (fs0 E)) (F0 E) E →
      RootOpen hp i ls0 Ctx frM E) :
    CorrectE 2 (wakeS arch) (Ly).Λ B SccCertificate.asm :=
  have hpa := (WakeSpawnRP.parsed_outLit hP).1
  have hwp := (WakeSpawnRP.parsed_outLit hP).2.1
  have hd := (WakeSpawnRP.parsed_outLit hP).2.2
  have hc := WakeFinalCAO.ctrZ_cert
  WakeFinalCAW.wake_finalCA_genW hp i (fun _ => WakeHG.cTW hp i) ls0 Ctx frM (inv0R hp i ls0 Ctx frM)
    (inv1R hp i ls0 Ctx)
    (r0 := fun _ => WakeOSide.r0W hp i) (r1 := fun _ => WakeOSide.r1W hp i)
    hpa hwp hd hlo hstat hpin2 hinit2 hwide (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13) hc hnz hB
    (fun E hE =>
      have h1 : H1R hp i ls0 Ctx (msBot hp i ls0 Ctx E (fs0 E)) (F0 E) E :=
        WakeH1A.wake_h1A hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) hpa hwp hlo hA13 hpin2 hc
          (hokb_R hp i ls0 hc E _ (fs0 E)) ⟨rfl, rfl, rfl, rfl⟩ (hG E hE) (hobl E hE)
      have hR := hRO E hE h1
      have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13
      have h0 : SegInvS (W0W hp i E DtW (Ctx E) (ls0 E) (frM E))
          (TakeCKS (WakeOSide.aW hp i E) (WakeOD.ClW hp i)) wakeSrc (L0T (Ly).Λ)
          (msOfA (Ly).Λ ((target (kernel 2) E).marks SccCertificate.asm (Ly).Λ) (fun _ => True)
            (WakeOG.gW hp i (WakeHG.cTW hp i))
            (fun s _ => Spike.Lib.A64.WakePh.ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (WakeOD.arW hp i)
            (I2 (WakeOD.arW hp i) (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (inv0R hp i ls0 Ctx frM E)
              (inv1R hp i ls0 Ctx E)) (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)))
          (inv0R hp i ls0 Ctx frM E) :=
        A64GfpS.segInvS_mono_xa A64GfpS.segInvS_gfpS (fun fs => A64GfpS.msOfA_with_xa fs) fun fs _ _ _ _ _ h =>
          A64GfpS.msOfA_xa_mono (fun _ _ _ _ _ hI => hI.elim (fun hF => hF.2.2.elim) .inr) fs h
      have hst := A64GfpS.gfpS_of_segWS hR.hst0 _ _ _ ⟨rfl, rfl, rfl⟩
      have hO := WakeOPremI.oPrem_WI hp i arch E (WakeHG.cTW hp i) (ls0 E) (Ctx E) (frM E) (inv0R hp i ls0 Ctx frM E)
        (inv1R hp i ls0 Ctx E) hpa hwp hd hlo hstat hpin2 hsub1 hc hnz hE.1 hB
        (WakeH1Inv.h1_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
          (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (inv0R hp i ls0 Ctx frM E))
        h0 (WakeH1Inv.h1Take_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E))
        (WakeH1Inv.h1TakeOwn_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)) hst hR.hctr0 hR.hnew0
      { h1 := WakeH1Inv.h1_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
          (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (inv0R hp i ls0 Ctx frM E)
        h0 := h0
        h1t := WakeH1Inv.h1Take_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
        h1o := WakeH1Inv.h1TakeOwn_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
        hst := hst
        hctr0 := hR.hctr0
        hnew0 := hR.hnew0
        hpost := WakeHClW.hpost_W hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) (frM E) (inv0R hp i ls0 Ctx frM E)
          (fun _ _ h => h.1) hO
        hCl := WakeHClW.hCl_W hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) (frM E) (inv0R hp i ls0 Ctx frM E)
          (fun _ _ h => h.1) hO hsub1 })
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end Spike.Lib.WakeRootA

/-- info: 'Spike.Lib.WakeRootA.wake_rootPA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRootA.wake_rootPA
