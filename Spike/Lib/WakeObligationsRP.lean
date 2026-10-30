/-
**wake.w on AArch64: the obligations at the owners' pieces**: `wake_obligations_RP`, `WakeSpawnR.wake_obligations_RS`
at the relation `R1 ∧ VPriv` (`WakePrivR.Pre1T.priv` of the given `Pre1T`)
with `HMainR` by `WakeMainHR.hMainR_of` (`hpv` by `WakePrivR.priv_of_R1`,
`ExeWide` the instance fact `hwide`).

**Open**: `hpre : HPre` and `hpc`, the owners' `MainPieces` per
witness tuple, both at `R1 ∧ VPriv`; with `WakeSpawnLt.pre1T_vpre`, `O` is itself `pre1T_vpre O'` and `R1` is
`R1' ∧ VPre`.

The owners state `hpre` and the `MainPieces` generic in the relation they
are given (any `R1`, reading only its conjuncts through `SpawnPrem`'s
`.1`), never at a bare `R1'`, so the conjunction
`(R1' ∧ VPre) ∧ VPriv` flows through unchanged.
-/
import Spike.Lib.WakeMainHR
import Spike.Lib.WakePrivR
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeObligationsRP

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeSpawnR
open Spike.Lib.WakePreTi (Pre1T TiPre)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.WakeMainHR (MainPieces)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`wake_obligations_RS` at `R1 ∧ VPriv` from the owners' pieces** (see
the module doc). -/
theorem wake_obligations_RP {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs) (hE : E.clear (RuntimeLayout.ofPlaceW hp i).Λ = true)
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E R1 Ab Ac)
    /- instance facts -/
    (hlo : (RuntimeLayout.ofPlaceW hp i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    /- OPEN: the pre-spawn segment's end -/
    (hpre : HPre hp i SccCertificate.asm E arch
      (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
      (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
    /- OPEN: main's pieces past the clone -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
        (RuntimeLayout.ofPlaceW hp i).Λ SccCertificate.asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀
        T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp cw tyP, MainPieces hp i w.1 d th r (Ctl.of s0) c Rm F₂ cA x29 ra tp cw tyP) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm
      (WakeAssemblyR.QR hp i hpa arch
        (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) r0 r1)
      E (TiPre Ab Ac) := by
  have hw : ∀ prog, (textProgram SccCertificate.asm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true := by
    intro prog h
    rw [hpa] at h
    cases h
    exact PlaceW.wideIn_of_placeW hp
  exact wake_obligations_RS hp i hpa hwp hd hE (WakePrivR.Pre1T.priv O hw) hlo hpin2 hinit2 hwide hpre
    (WakeMainHR.hMainR_of hp i hwide (fun _ _ h => WakePrivR.priv_of_R1 h) hpc)

end Inst

/-- info: 'Spike.Lib.WakeObligationsRP.wake_obligations_RP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_RP

end Spike.Lib.WakeObligationsRP
