/-
**wake.w on AArch64: the top of the proof** (the analogue of `hello1_finalCA_gen`, `Spike/Test/A64Hello1FinalCA.lean`).

- `wake_correctAt`: `wake_correctE` at one entry state: `Correct` of the
  two-slot target at `E` from `WakeObligations` at `E` (the same proof,
  `Scc.Sem.correct_of_stepSim` with `wake_stepSim`; `wake_correctE` asks
  the obligations at every admissible entry).
- `wake_finalCA_gen`: at any placed output (`hp`, generic in `hp`/`i`),
  `CorrectE 2` (every entry state `Entry.Ok` admits, as
  `hello1_finalCA_gen`) for `wakeS`, at the placed layout and the
  certificate: per entry `E`, `wake_correctAt` at
  `WakeObligationsRP.wake_obligations_RP` (its `hE` is `Entry.Ok`'s
  `clear`).

**Open** (premises of `wake_finalCA_gen`, each at every admissible `E`):
the pre-spawn obligations `O` (`Pre1T` at `R1 E`; with `pre1T_vpre`, `R1 E := R1' E ∧ VPre`), `hpre` and `hpc` (the
`MainPieces`), both at `R1 E ∧ VPriv`; the loader's
parses `hpa`, `hwp`, `hd`; the instance facts `hlo`, `hpin2`, `hinit2`,
`hwide` (closed at `Λe` by the instance).

**Entry state.** No proof below uses `Entry.linux`'s value: the chain is
generic in `E` with `E.clear Λ` (`WakeSpawnR.wake_obligations_RE`, the
generic copy of `WakeAssemblyR.wake_obligations_R`, whose marks `μR` do not
depend on `E`).
-/
import Spike.Lib.WakeObligationsRP
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeFinalCA

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeSpawnR
open Spike.Lib.TwoSlot Spike.Lib.Handover Spike.Lib.A64TwoSlot
open Spike.Lib.WakePreTi (Pre1T TiPre)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.WakeMainHR (MainPieces)

/-- **wake.w is correct on AArch64 with two slots at one entry state**,
given the obligations there (`wake_correctE`'s proof at `E`). -/
theorem wake_correctAt {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Q : WakeRel}
    {E : Entry} {Ti : Cfg → List Ev → Prop} (O : WakeObligations arch Λ B asm Q E Ti) :
    Correct (target (kernel 2) E) (wakeS arch) Λ B asm := by
  have hsim := wake_stepSim O
  refine correct_of_stepSim hsim O.hwf ?_ ?_ ?_ ?_
  · obtain ⟨d, hd⟩ := O.hstart
    obtain ⟨u, hu, -⟩ := load_one hd
    exact ⟨_, hu⟩
  · intro t0 tr t h0 hr
    obtain ⟨s, -, hri, hR⟩ := hsim.reach h0 hr
    rcases hR with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, hca⟩
    · exact O.pre_progress d u s hR hu hpl hn
    · exact O.post_progress t s hP hri hca
  · intro t0 tr t tid es t' k s h0 hr hreach hR hs hk
    change (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' at hs
    have hTi : Ti t tr := by
      obtain ⟨s0, -, hR0⟩ := hsim.init t0 h0
      simpa using wake_tiRun O hr hR0 (O.ti_load t0 h0)
    rcases hR.2 with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩
    · obtain ⟨-, ⟨d', hd', rfl⟩ | ⟨rfl, -⟩⟩ := step_up_cases hn hs
      · exact O.pre_abort tr d u s tid es d' k hreach hR hu hpl hn hTi hd' hk
      · cases hk
    · exact O.post_abort tr t s tid es t' k hreach hP hTi hs hk
  · intro t s hR
    rcases hR with ⟨hri, ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩⟩
    · exact O.pre_wit d u s hR hu hpl hn
    · exact O.post_wit t s hP hri

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}

/-- **wake.w's AArch64 statement at any placed output** (see the module
doc): `CorrectE 2` (every admissible entry state) for `wakeS arch` at the
placed layout and the certificate, open `O`, `hpre`, `hpc` at every
admissible entry `E` (the relation `R1 E` may depend on it). -/
theorem wake_finalCA_gen (hp : PlaceW pcfg Λ0 o)
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
    /- OPEN: main's pieces past the clone -/
    (hpc : ∀ E : Entry, E.Ok (RuntimeLayout.ofPlaceW hp i).Λ →
      ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch (fun d s => R1 E d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
        (RuntimeLayout.ofPlaceW hp i).Λ SccCertificate.asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch (fun d s => R1 E d s ∧ VPriv (RuntimeLayout.ofPlaceW hp i).Λ E d)
        (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀
        T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA x29 ra tp cw tyP, MainPieces hp i w.1 d th r (Ctl.of s0) c Rm F₂ cA x29 ra tp cw tyP) :
    CorrectE 2 (wakeS arch) (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm :=
  fun E hE => wake_correctAt (WakeObligationsRP.wake_obligations_RP hp i hpa hwp hd hE.1 (O E hE)
    hlo hpin2 hinit2 hwide (hpre E hE) (hpc E hE))

end Inst

/-- info: 'Spike.Lib.WakeFinalCA.wake_correctAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_correctAt

/-- info: 'Spike.Lib.WakeFinalCA.wake_finalCA_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_finalCA_gen

end Spike.Lib.WakeFinalCA
