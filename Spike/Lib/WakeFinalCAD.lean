/-
**wake.w's AArch64 statement with main's pieces from the segment end
alone** (`WakeMainHRD.hMainR_ofD`): as `WakeFinalCA.wake_finalCA_gen`, its
`hpc` naming only `MainSeg`, `hA` and `hZ` (the source fields and `hS`/`htls`/`hexit` supplied inside).

- `wake_obligations_RPD`: `WakeObligationsRP.wake_obligations_RP`'s
  conclusion, `HMainR` by `hMainR_ofD` (`hprog` from the loader's two
  parses).
- `wake_finalCA_genD`: `CorrectE 2` at every admissible entry, open `O`,
  `hpre`, `hpc` at every `E` with `E.Ok`.
-/
import Spike.Lib.WakeFinalCA
import Spike.Lib.WakeMainHRD
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeFinalCAD

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeSpawnR
open Spike.Lib.WakePreTi (Pre1T TiPre)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.WakeMainHRD (MainSeg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}

/-- **`wake_obligations_RP` with `HMainR` by `hMainR_ofD`** (see the module
doc). -/
theorem wake_obligations_RPD (hp : PlaceW pcfg Λ0 o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs) (hE : E.clear (RuntimeLayout.ofPlaceW hp i).Λ = true)
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E R1 Ab Ac)
    (hlo : (RuntimeLayout.ofPlaceW hp i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    (hpre : HPre hp i SccCertificate.asm E arch
      (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
      (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
        (RuntimeLayout.ofPlaceW hp i).Λ SccCertificate.asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀
        T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp, MainSeg hp i th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -96, 16⟩ : Region).addr (-32)).toNat) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm
      (WakeAssemblyR.QR hp i hpa arch
        (fun d s => R1 d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d) r0 r1)
      E (TiPre Ab Ac) := by
  have hw : ∀ prog, (textProgram SccCertificate.asm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true := by
    intro prog h
    rw [hpa] at h
    cases h
    exact PlaceW.wideIn_of_placeW hp
  have hprog : o.prog = wakeProg := Except.ok.inj (hpa.symm.trans hwp)
  exact wake_obligations_RS hp i hpa hwp hd hE (WakePrivR.Pre1T.priv O hw) hlo hpin2 hinit2 hwide hpre
    (WakeMainHRD.hMainR_ofD hp i hprog hwide (fun _ _ h => WakePrivR.priv_of_R1 h) hpc)

/-- **wake.w's AArch64 statement at any placed output, `hpc` from the segment end** (see the module doc). -/
theorem wake_finalCA_genD (hp : PlaceW pcfg Λ0 o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget}
    {R1 : Entry → Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    /- the loader's parses of the certificate -/
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs)
    /- instance facts -/
    (hlo : (RuntimeLayout.ofPlaceW hp i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    /- OPEN: the pre-spawn obligations -/
    (O : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ →
      Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E (R1 E) Ab Ac)
    /- OPEN: the pre-spawn segment's end -/
    (hpre : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ → HPre hp i SccCertificate.asm E arch
      (fun d s => R1 E d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
      (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
    /- OPEN: main's segment end past the clone -/
    (hpc : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ →
      ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch (fun d s => R1 E d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
        (RuntimeLayout.ofPlaceW hp i).Λ SccCertificate.asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch (fun d s => R1 E d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀
        T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp, MainSeg hp i th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -96, 16⟩ : Region).addr (-32)).toNat) :
    CorrectE 2 (wakeS arch) (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm :=
  fun E hE => WakeFinalCA.wake_correctAt (wake_obligations_RPD hp i hpa hwp hd hE.1 (O E hE)
    hlo hpin2 hinit2 hwide (hpre E hE) (hpc E hE))

end Inst

end Spike.Lib.WakeFinalCAD

/-- info: 'Spike.Lib.WakeFinalCAD.wake_obligations_RPD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAD.wake_obligations_RPD

/-- info: 'Spike.Lib.WakeFinalCAD.wake_finalCA_genD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAD.wake_finalCA_genD
