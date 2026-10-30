/-
**wake.w's AArch64 statement with `O` from `WakeO.wake_O`**: as
`WakeFinalCAD.wake_finalCA_genD`, its `O` replaced by the per-entry
instance data `D E` and `pre1T_of_seg`'s premises `WakeO.OPrem` at them
(owners in `Spike/Lib/WakeO.lean`), the relation `R1 E` fixed to
`WakeO.R1O … (D E)` (`(((RSAH ∧ NoObs) ∧ VPre) ∧ VPreC) ∧ VFlag`).

- `wake_finalCA_genO`: `CorrectE 2` at every admissible entry; open the
  instance facts, `hO`, `hpre`, `hpc`.
- `wake_finalCA_genOP`: the same at the certificate's output `outLit`, the
  parses from one loader check `hP : parsesTo asm outLit.prog outLit.secs`.
- `ctrZ_cert`: the counter's zeroed item at the certificate (`hok`'s `CtrZ`).
- `hnt_cert`: `scc_rt_nthreads` starts at `0` at the certificate (`NtZ`).
- `hstat_cert`: no static labels at the certificate (`WakeOHinit.hinit_W`'s
  `hstat`).
- `placeW_cert`: `hp` at wake's certificate (`prog_placeOK_1/2/4/6/8`, the
  layout its link `tablesOf`).
-/
import Spike.Lib.WakeFinalCAD
import Spike.Lib.WakeO
import Spike.Lib.PlaceWRt
import Spike.Lib.WakeSpawnRP
import Spike.Lib.Rt.A64ArenaOfPlaceW
import Spike.Lib.WakeOInit
import Spike.Lib.WakeOHinit

namespace Spike.Lib.WakeFinalCAO

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

/-- **wake.w's AArch64 statement at any placed output, `O` from the
pre-spawn premises** (see the module doc). -/
theorem wake_finalCA_genO (hp : PlaceW pcfg Λ0 o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget}
    {D : Entry → WakeO.OData} {r0 r1 : ιR hp i → Range}
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
    /- OPEN (segments, per-state facts, the rest): the pre-spawn premises -/
    (hO : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ →
      WakeO.OPrem arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E Ab Ac (D E))
    /- OPEN: the pre-spawn segment's end -/
    (hpre : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ → HPre hp i SccCertificate.asm E arch
      (fun d s => WakeO.R1O arch (RuntimeLayout.ofPlaceW hp i).Λ ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ) (D E) d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
      (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
    /- OPEN: main's segment end past the clone -/
    (hpc : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ →
      ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch (fun d s => WakeO.R1O arch (RuntimeLayout.ofPlaceW hp i).Λ ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ) (D E) d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
        (RuntimeLayout.ofPlaceW hp i).Λ SccCertificate.asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch (fun d s => WakeO.R1O arch (RuntimeLayout.ofPlaceW hp i).Λ ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ) (D E) d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀
        T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp, MainSeg hp i th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -96, 16⟩ : Region).addr (-32)).toNat) :
    CorrectE 2 (wakeS arch) (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm :=
  WakeFinalCAD.wake_finalCA_genD hp i hpa hwp hd hlo hpin2 hinit2 hwide (WakeO.wake_O hO) hpre hpc

/-- **`wake_finalCA_genO` at the certificate's output** `o := outLit`, its
three parses from the single loader check `hP` (`WakeSpawnRP.parsed_outLit`). -/
theorem wake_finalCA_genOP (hp : PlaceW pcfg Λ0 SccCertificate.outLit)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget}
    {D : Entry → WakeO.OData} {r0 r1 : ιR hp i → Range}
    /- the loader's check of the certificate (the trust boundary) -/
    (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    /- instance facts -/
    (hlo : (RuntimeLayout.ofPlaceW hp i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    /- OPEN (segments, per-state facts, the rest): the pre-spawn premises -/
    (hO : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ →
      WakeO.OPrem arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E Ab Ac (D E))
    /- OPEN: the pre-spawn segment's end -/
    (hpre : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ → HPre hp i SccCertificate.asm E arch
      (fun d s => WakeO.R1O arch (RuntimeLayout.ofPlaceW hp i).Λ ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ) (D E) d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
      (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i (WakeSpawnRP.parsed_outLit hP).1) r0 r1)
    /- OPEN: main's segment end past the clone -/
    (hpc : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ →
      ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch (fun d s => WakeO.R1O arch (RuntimeLayout.ofPlaceW hp i).Λ ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ) (D E) d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i (WakeSpawnRP.parsed_outLit hP).1) r0 r1)
        (RuntimeLayout.ofPlaceW hp i).Λ SccCertificate.asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch (fun d s => WakeO.R1O arch (RuntimeLayout.ofPlaceW hp i).Λ ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ) (D E) d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i (WakeSpawnRP.parsed_outLit hP).1) r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀
        T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp, MainSeg hp i th c Rm F₂ cA x29 ra tp ∧ lbl l = some cA.toNat ∧
        (RuntimeLayout.ofPlaceW hp i).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -96, 16⟩ : Region).addr (-32)).toNat) :
    CorrectE 2 (wakeS arch) (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm :=
  WakeFinalCAD.wake_finalCA_genD hp i (WakeSpawnRP.parsed_outLit hP).1 (WakeSpawnRP.parsed_outLit hP).2.1
    (WakeSpawnRP.parsed_outLit hP).2.2 hlo hpin2 hinit2 hwide (WakeO.wake_O hO) hpre hpc

end Inst

/-- **`hp` at wake's certificate**: its A1, A2, A4, A6, A8 at its link
layout (`placeOK2`'s, shared with `placeOK`). -/
theorem placeW_cert :
    PlaceW SccCertificate.placeCfg
      (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ SccCertificate.outLit :=
  ⟨SccCertificate.prog_placeOK_1, SccCertificate.prog_placeOK_2, SccCertificate.prog_placeOK_4,
    SccCertificate.prog_placeOK_6, SccCertificate.prog_placeOK_8⟩

/-- A key's lookup is one of the list's pairs. -/
private theorem lookup_mem {β : Type} : ∀ {l : List (String × β)} {k : String} {b : β},
    l.lookup k = some b → (k, b) ∈ l
  | [], _, _, h => by simp at h
  | (k', b') :: l, k, b, h => by
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have hne : (k == k') = false := by simpa using hk
      simp [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **The counter's zeroed item at wake's certificate** (`Rt.CtrZ`, `hok`'s
premise): `scc_rt_heap_use` labels an all-zero item of 8 bytes in the
emitted `.bss`/`.data`. -/
theorem ctrZ_cert : Spike.Lib.A64.Rt.CtrZ SccCertificate.outLit := by
  cases h : (Scc.Cert.Link.symItems (SccCertificate.outLit.secs.bss ++ SccCertificate.outLit.secs.data)).lookup
    Scc.Cert.PlaceOK.heapUseSym with
  | none => exact absurd h (by decide)
  | some its =>
    refine ⟨its, lookup_mem h, ?_, ?_⟩
    · have : ((Scc.Cert.Link.symItems (SccCertificate.outLit.secs.bss ++ SccCertificate.outLit.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map Scc.Cert.Link.allZero = some true := by decide
      rw [h] at this; simpa using this
    · have : ((Scc.Cert.Link.symItems (SccCertificate.outLit.secs.bss ++ SccCertificate.outLit.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map (fun its => decide (8 ≤ Scc.Cert.Link.itemLen its)) = some true := by
        decide
      rw [h] at this; simpa using this

/-- **`scc_rt_nthreads` starts at `0` at wake's certificate** (`NtZ`,
`WakeOInit.hown0_W`'s `hnt` by `hnt_of`). -/
theorem hnt_cert :
    Spike.Lib.WakeOInit.NtZ (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ
      SccCertificate.outLit = true := by
  decide +kernel

/-- **No static labels at wake's certificate** (`WakeOHinit.hinit_W`'s
`hstat`). -/
theorem hstat_cert : (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ.static = fun _ => none := rfl

/-- **wake's certificate's decided instance facts**: `hp` (`placeW_cert`),
`CtrZ` (`ctrZ_cert`), `NtZ` (`hnt_cert`) and `hstat` (`hstat_cert`).

A sanity check only, that the predicates are satisfiable, at the canonical
link layout `tablesOf placeCfg outLit` (code base `0x400000`). The binding
instance is `WakeLinkedA64` at `Λe`, the layout read from the `run.sh`-linked
ELF (`.text` at `0x210550` = `WakePh.lo`). The layout-specific facts (`hlo`,
`hpin2`, `hsub1`) are decided only there. -/
example :
    PlaceW SccCertificate.placeCfg
        (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ SccCertificate.outLit ∧
      Spike.Lib.A64.Rt.CtrZ SccCertificate.outLit ∧
      Spike.Lib.WakeOInit.NtZ (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ
        SccCertificate.outLit = true ∧
      (Scc.Cert.PlaceOK.A64.tablesOf SccCertificate.placeCfg SccCertificate.outLit).Λ.static = (fun _ => none) :=
  ⟨placeW_cert, ctrZ_cert, hnt_cert, hstat_cert⟩

end Spike.Lib.WakeFinalCAO

/-- info: 'Spike.Lib.WakeFinalCAO.placeW_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAO.placeW_cert

/-- info: 'Spike.Lib.WakeFinalCAO.ctrZ_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAO.ctrZ_cert

/-- info: 'Spike.Lib.WakeFinalCAO.hnt_cert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAO.hnt_cert

/-- info: 'Spike.Lib.WakeFinalCAO.hstat_cert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAO.hstat_cert

/-- info: 'Spike.Lib.WakeFinalCAO.wake_finalCA_genO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAO.wake_finalCA_genO

/-- info: 'Spike.Lib.WakeFinalCAO.wake_finalCA_genOP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeFinalCAO.wake_finalCA_genOP
