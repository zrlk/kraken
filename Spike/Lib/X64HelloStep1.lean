/-
**hello.w on x86-64: a step of the worker after the spawn keeps `Post`**
(`X64HelloAssembly.HelloRows.post_step1`, the twin of
`X64WakeW1.post_step1_of`): `Post` unpacks at `PT1hE`
(`X64HelloEmitPh.post_partsHE`): at `PT1h`, whose phase sum splits the step, or
mid-`write` (`EmitStep1`).

- The store phase: `Post` holds at wake's worker data `relW`
  (`X64HelloW1Store.post_toW`), where wake's `X64WakeW1.post_step1_of` applies
  (`X64WakeW1.WCompat` at `relW` is `HelloCompat`'s second part, `WCompatX` at
  `relW` is `WCompatXH`'s fields, `wcompatX_relW`); its `Post` at `relW`
  is `Post` at `Q` (`X64HelloW1Store.post_ofW`). `relW` changes `PT1` only, so
  its `atUnpk`, `atTexit` are `Q`'s.
- The print phase: `PrintStep1` (this file's open part, to be
  discharged by the print phase's lemmas).

- `wcompatX_relW`: `WCompatX` at `relW` from `WCompatXH` (`krp` by
  `KRmod.permit`); `krpW_of`: `KrpW` from `WCompatXH.krp`.
- `post_step1_store`: the store phase (at `wr 1 = 0`, `relW`'s `KR`).
- `StoreWr0`, `storeWr0_of`: no byte of a worker `write` out in the store
  phase, at `KR = X64HelloKRE.KRHE`.
- `PrivAt`, `privAt_of_runInv`: the threads' private keys private (from
  the run invariant), `post_step1`'s premise for the worker's `write`.
- `EmitStep1`: the worker mid-`write`.
- `post_step1H`: `post_step1` given `PrintStep1`, `EmitStep1` and
  `StoreWr0`, at `Q.PT1 = PT1hE D` (the `rfl` at `X64HelloQ.helloQ`, also
  `HelloCompat`'s `WCompatH.pt1`).

x86-64 twin of `Spike/Lib/HelloStep1.lean` (same names, namespaces with the `X64` prefix).
-/
import Spike.Lib.X64HelloAssembly
import Spike.Lib.X64HelloKRE
import Spike.Lib.X64HelloEmitPh

namespace Spike.Lib.X64HelloStep1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH PrintPh StorePh)
open Spike.Lib.X64HelloW1Store (relW wsideW NoWrite post_toW post_ofW KrpW)
open Spike.Lib.X64HelloWorkerRR (WCompatXH)
open Spike.Lib.X64HelloAssembly (HelloCompat)
open Spike.Lib.X64HelloKRE (KRHE)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : X64WakeM0.MSide Q.ι} {AbW : isa.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D}

/-- **`WCompatX` at `relW`**: `WCompatXH`'s fields (`relW` changes `PT1`
only). Unlike AArch64, x86-64's `WCompatX` has `ownConst1`/`ownMp1` in
place of `own1`; they are `WCompatXH`'s (the worker may own its TCB self
word). -/
theorem wcompatX_relW (hx : WCompatXH Q D) : X64WakeW1.WCompatX (relW Q D hcw hem) (wsideW D hcw hem) :=
  ⟨hx.Gc, hx.ownConst1, hx.ownMp1,
    hx.sp0, hx.pt0p, fun _ _ _ _ _ _ _ h a b c d e =>
    ⟨h.1.permit a b c d e, by rw [a]; exact h.2⟩⟩

/-- **`KrpW` from `WCompatXH.krp`** (which has no premise on the bytes out
or the worker). -/
theorem krpW_of (hx : WCompatXH Q D) : KrpW Q D :=
  fun w t t' s s' s0 p h hwr a b c d e hW => hx.krp w t t' s s' s0 p h hwr a b c d e hW

/-- **A step of the worker in the store phase keeps `Post`**, by wake's
`post_step1_of` at `relW`. -/
theorem post_step1_store (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF) {w : Q.ι} {t t' : Cfg}
    {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    {oc : Option (Nat × Nat)} {es : List Ev} (hP : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hS : StorePh (D.cw w) s1) (hwr : t.2.wr 1 = 0) (hnu : ¬ Q.atUnpk t s) (hnt : ¬ Q.atTexit t s)
    (hs : (machine (kernel 2)).Step μ 1 t es t') :
    ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  obtain ⟨s', hr, hP'⟩ := X64WakeW1.post_step1_of hC.2.1 (wcompatX_relW hC.2.2.1) hwf
    (post_toW (hcw := hcw) (hem := hem) hP hS hwr) hnu hnt hs
  exact ⟨s', hr, post_ofW hC.1.pt1 (krpW_of hC.2.2.1) hP'⟩

/-- **No byte of a worker `write` out in the store phase** (the store
phase's premise of `relW`). -/
def StoreWr0 (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc, PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → StorePh (D.cw w) s1 →
    t.2.wr 1 = 0

/-- **`StoreWr0` at `KRHE`**: mid-`write` the worker is at a `write`
(`X64HelloKRE.wr1_zero`), which the store phase has not (`X64WakeW1.WCompat.sysOk`
at `relW`, `HelloCompat`'s second part). -/
theorem storeWr0_of {r0 r1 : Q.ι → Range} (hKR : Q.KR = KRHE D r0 r1)
    (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) : StoreWr0 Q D Λ := by
  intro w t s t0 t1 s0 s1 ts tp sp oc h hS
  have hl : X64HelloKRE.Lk D w t s := by
    have hk := h.kr
    rw [hKR] at hk
    exact hk.2
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  refine X64HelloKRE.wr1_zero hl ht1 ?_
  cases ha : abi.atSys t1.st
  · exact .inl rfl
  · refine .inr fun fd buf n hd => ?_
    have hW : X64HelloW1Store.WiS D w t1.st (Ctl.of s1) :=
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

/-- **`PrivAt` from the run invariant** (`X64WakeRunInv.RunInv`) at an entry
state clear of the layout. -/
theorem privAt_of_runInv {E : Entry} {t : Cfg} (hE : E.clear Λ = true) (hri : X64WakeRunInv.RunInv Λ E t) :
    PrivAt Λ t :=
  ⟨E, hE, hri.1.dmemPriv⟩

/-- **The print phase's obligation**: from `Post`'s parts
with the worker in the print phase, a step of the worker other than its
unpark and exit steps keeps `Post`. -/
def PrintStep1 (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t', PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → PrivAt Λ t →
    PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
    (machine (kernel 2)).Step μ 1 t es t' → ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **The worker mid-`write`'s obligation**: from `Post`'s parts
mid-`write` (`X64HelloEmitPh.PartsE`) off the worker's invariant, a step of the
worker keeps `Post` (`X64HelloEmitW1.emitStep1_of`). -/
def EmitStep1 (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t', X64HelloEmitPh.PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → PrivAt Λ t →
    ¬ D.Wi w t1.st (Ctl.of s1) s1.stack → (machine (kernel 2)).Step μ 1 t es t' →
    ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **`HelloRows.post_step1`**, given the print phase's `PrintStep1` and the
worker mid-`write`'s `EmitStep1`: `Post` unpacks at `PT1hE`
(`X64HelloEmitPh.post_partsHE`), at `PartsH` by the phase, or at `PartsE`. -/
theorem post_step1H (hwf : Λ.WF) (hpr : PrintStep1 Q D μ Λ arch) (hpe : EmitStep1 Q D μ Λ arch)
    (hS0 : StoreWr0 Q D Λ) :
    HelloCompat Q D M μ Λ arch AbW hcw hem →
      ∀ t es t' s, Q.Post Λ t s → PrivAt Λ t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
        (machine (kernel 2)).Step μ 1 t es t' →
        ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  intro hC t es t' s hpost hpk hnu hnt hs
  rcases X64HelloEmitPh.post_partsHE hC.1.pt1 hpost with ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hP⟩ |
    ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hE, hn⟩
  · rcases hP.pt1.2.2.1 with hpp | hS
    · exact hpr w t s t0 t1 s0 s1 ts tp sp oc es t' hP hpk hpp.1 hnu hnt hs
    · exact post_step1_store hC hwf hP hS (hS0 w t s t0 t1 s0 s1 ts tp sp oc hP hS) hnu hnt hs
  · exact hpe w t s t0 t1 s0 s1 ts tp sp oc es t' hE hpk hn hs

/-- info: 'Spike.Lib.X64HelloStep1.post_step1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_step1H

end Spike.Lib.X64HelloStep1

/-- info: 'Spike.Lib.X64HelloStep1.wcompatX_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1.wcompatX_relW

/-- info: 'Spike.Lib.X64HelloStep1.krpW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1.krpW_of

/-- info: 'Spike.Lib.X64HelloStep1.post_step1_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1.post_step1_store

/-- info: 'Spike.Lib.X64HelloStep1.storeWr0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1.storeWr0_of

/-- info: 'Spike.Lib.X64HelloStep1.privAt_of_runInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1.privAt_of_runInv
