/-
**hello.w on AArch64: a step of the worker after the spawn keeps `Post`**
(row B8-gen1; `HelloAssembly.HelloRows.post_step1`, the twin of
`WakeW1.post_step1_of`): `Post` unpacks at `PT1hE`
(`HelloEmitPh.post_partsHE`): at `PT1h`, whose phase sum splits the step, or
mid-`write` (`EmitStep1`).

- The store phase: `Post` holds at wake's worker data `relW`
  (`HelloW1Store.post_toW`), where wake's `WakeW1.post_step1_of` applies
  (`WakeW1.WCompat` at `relW` is `HelloCompat`'s second part, `WCompatX` at
  `relW` is `WCompatXH`'s fields, `wcompatX_relW`); its `Post` at `relW`
  is `Post` at `Q` (`HelloW1Store.post_ofW`). `relW` changes `PT1` only, so
  its `atUnpk`, `atTexit` are `Q`'s.
- The print phase: `PrintStep1` (row B8-gen1p, this file's open part, to be
  discharged by the print phase's rows).

- `wcompatX_relW`: `WCompatX` at `relW` from `WCompatXH` (`krp` by
  `KRmod.permit`); `krpW_of`: `KrpW` from `WCompatXH.krp`.
- `post_step1_store`: the store phase (at `wr 1 = 0`, `relW`'s `KR`).
- `StoreWr0`, `storeWr0_of`: no byte of a worker `write` out in the store
  phase, at `KR = HelloKRE.KRHE` (design (i′)).
- `PrivAt`, `privAt_of_runInv`: the threads' private keys private (from
  the run invariant), `post_step1`'s premise for the worker's `write`.
- `EmitStep1`: the worker mid-`write` (row B8-W1E).
- `post_step1H`: `post_step1` given `PrintStep1`, `EmitStep1` and
  `StoreWr0`, at `Q.PT1 = PT1hE D` (the `rfl` at `HelloQ.helloQ`, also
  `HelloCompat`'s `WCompatH.pt1`).
-/
import Spike.Lib.HelloAssembly
import Spike.Lib.HelloKRE
import Spike.Lib.HelloEmitPh

namespace Spike.Lib.HelloStep1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh StorePh post_partsH)
open Spike.Lib.HelloW1Store (relW wsideW NoWrite post_toW post_ofW KrpW)
open Spike.Lib.HelloWorkerRR (WCompatXH)
open Spike.Lib.HelloAssembly (HelloCompat)
open Spike.Lib.HelloKRE (KRHE)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {AbW : isaLSE2.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D}

/-- **`WCompatX` at `relW`**: `WCompatXH`'s fields (`relW` changes `PT1`
only). -/
theorem wcompatX_relW (hx : WCompatXH Q D) : WakeW1.WCompatX (relW Q D hcw hem) (wsideW D hcw hem) :=
  ⟨hx.Gc, hx.own1, hx.sp0, hx.pt0p, fun _ _ _ _ _ _ _ h a b c d e =>
    ⟨h.1.permit a b c d e, by rw [a]; exact h.2⟩⟩

/-- **`KrpW` from `WCompatXH.krp`** (which has no premise on the bytes out
or the worker). -/
theorem krpW_of (hx : WCompatXH Q D) : KrpW Q D :=
  fun w t t' s s' s0 p h hwr a b c d e hW => hx.krp w t t' s s' s0 p h hwr a b c d e hW

/-- **A step of the worker in the store phase keeps `Post`**, by wake's
`post_step1_of` at `relW`. -/
theorem post_step1_store (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF) {w : Q.ι} {t t' : Cfg}
    {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    {oc : Option (Nat × Nat)} {es : List Ev} (hP : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hS : StorePh (D.cw w) s1) (hwr : t.2.wr 1 = 0) (hnu : ¬ Q.atUnpk t s) (hnt : ¬ Q.atTexit t s)
    (hs : (machine (kernel 2)).Step μ 1 t es t') :
    ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  obtain ⟨s', hr, hP'⟩ := WakeW1.post_step1_of hC.2.1 (wcompatX_relW hC.2.2.1) hwf
    (post_toW (hcw := hcw) (hem := hem) hP hS hwr) hnu hnt hs
  exact ⟨s', hr, post_ofW hC.1.pt1 (krpW_of hC.2.2.1) hP'⟩

/-- **No byte of a worker `write` out in the store phase** (the store
phase's premise of `relW`, design (i′)). -/
def StoreWr0 (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc, PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → StorePh (D.cw w) s1 →
    t.2.wr 1 = 0

/-- **`StoreWr0` at `KRHE`**: mid-`write` the worker is at a `write`
(`HelloKRE.wr1_zero`), which the store phase has not (`WakeW1.WCompat.sysOk`
at `relW`, `HelloCompat`'s second part). -/
theorem storeWr0_of {r0 r1 : Q.ι → Range} (hKR : Q.KR = KRHE D r0 r1)
    (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) : StoreWr0 Q D Λ := by
  intro w t s t0 t1 s0 s1 ts tp sp oc h hS
  have hl : HelloKRE.Lk D w t s := by
    have hk := h.kr
    rw [hKR] at hk
    exact hk.2
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  refine HelloKRE.wr1_zero hl ht1 ?_
  cases ha : abi.atSys t1.st
  · exact .inl rfl
  · refine .inr fun fd buf n hd => ?_
    have hW : HelloW1Store.WiS D w t1.st (Ctl.of s1) :=
      ⟨by rw [← hS.1]; exact h.pt1.1, rfl, hS.2.1, hS.2.2⟩
    rcases hC.2.1.sysOk w t1.st (Ctl.of s1) _ hW ha hd with he | ⟨hn, -⟩
    · cases he
    · exact hn fd buf n rfl

/-- **The threads' private memory is private** at some entry state clear of
the layout (`DmemPriv.DmemPriv`; the worker's `write` reads the buffer
outside its private keys): what `post_step1` takes of the run invariant
(`privAt_of_runInv`). -/
def PrivAt (Λ : Scc.Sem.Layout) (t : Cfg) : Prop :=
  ∃ Ent : Entry, Ent.clear Λ = true ∧ DmemPriv.DmemPriv abi Λ Ent t

/-- **`PrivAt` from the run invariant** (`WakeRunInv.RunInv`) at an entry
state clear of the layout. -/
theorem privAt_of_runInv {E : Entry} {t : Cfg} (hE : E.clear Λ = true) (hri : WakeRunInv.RunInv Λ E t) :
    PrivAt Λ t :=
  ⟨E, hE, hri.1.dmemPriv⟩

/-- **The print phase's obligation** (row B8-gen1p): from `Post`'s parts
with the worker in the print phase, a step of the worker other than its
unpark and exit rows keeps `Post`. -/
def PrintStep1 (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t', PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → PrivAt Λ t →
    PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
    (machine (kernel 2)).Step μ 1 t es t' → ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **The worker mid-`write`'s obligation** (row B8-W1E): from `Post`'s parts
mid-`write` (`HelloEmitPh.PartsE`) off the worker's invariant, a step of the
worker keeps `Post` (`HelloEmitW1.emitStep1_of`). -/
def EmitStep1 (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t', HelloEmitPh.PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → PrivAt Λ t →
    ¬ D.Wi w t1.st (Ctl.of s1) s1.stack → (machine (kernel 2)).Step μ 1 t es t' →
    ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **`HelloRows.post_step1`**, given the print phase's `PrintStep1` and the
worker mid-`write`'s `EmitStep1`: `Post` unpacks at `PT1hE`
(`HelloEmitPh.post_partsHE`), at `PartsH` by the phase, or at `PartsE`. -/
theorem post_step1H (hwf : Λ.WF) (hpr : PrintStep1 Q D μ Λ arch) (hpe : EmitStep1 Q D μ Λ arch)
    (hS0 : StoreWr0 Q D Λ) :
    HelloCompat Q D M μ Λ arch AbW hcw hem →
      ∀ t es t' s, Q.Post Λ t s → PrivAt Λ t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
        (machine (kernel 2)).Step μ 1 t es t' →
        ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  intro hC t es t' s hpost hpk hnu hnt hs
  rcases HelloEmitPh.post_partsHE hC.1.pt1 hpost with ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hP⟩ |
    ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hE, hn⟩
  · rcases hP.pt1.2.2.1 with hpp | hS
    · exact hpr w t s t0 t1 s0 s1 ts tp sp oc es t' hP hpk hpp.1 hnu hnt hs
    · exact post_step1_store hC hwf hP hS (hS0 w t s t0 t1 s0 s1 ts tp sp oc hP hS) hnu hnt hs
  · exact hpe w t s t0 t1 s0 s1 ts tp sp oc es t' hE hpk hn hs

/-- info: 'Spike.Lib.HelloStep1.post_step1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_step1H

end Spike.Lib.HelloStep1
