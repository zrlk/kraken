/-
**hello.w on AArch64: the worker's unpark after the spawn** (
`HelloAssembly.HelloRowsW.unpark_src`, the twin of `WakeW1.unpark_src_of`).

At the unpark row the source worker is at `wkUnpark`, which takes no local
step and is neither `print`'s call nor one of `print`'s anchors, so the
worker is not in the print phase (`printPh_not_unpk`): it is in the store
phase, where `Post` holds at wake's worker data `relW`
(`HelloW1Store.post_toW`) and wake's `WakeW1.unpark_src_of` applies (`relW`
changes `PT1` only, so its `atUnpk` is `Q`'s); its `Post` at `relW` is
`Post` at `Q` (`HelloW1Store.post_ofW`).

- `printPh_not_unpk`: the print phase is not at `wkUnpark`.
- `unpark_srcH`: `HelloRowsW.unpark_src`'s statement.
-/
import Spike.Lib.HelloStep1

namespace Spike.Lib.HelloUnpk

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh StorePh post_partsH localRunS_cases wkUnpark_noStep)
open Spike.Lib.HelloW1Store (relW wsideW NoWrite post_toW post_ofW)
open Spike.Lib.HelloAssembly (HelloCompat)

/-- **The print phase is not at `wkUnpark`**: before `print`'s call the
source worker runs to the call (`wkUnpark` takes no step and is not the
call); inside `print` it runs to an anchor (`wkUnpark` is none). -/
theorem printPh_not_unpk {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {s1 : TermRun.TTh}
    (h : PrintPh l n m cw s1) (ht : s1.term = wkUnpark) : False := by
  obtain ⟨w0, w1, w2, w4, -, -, -, -, -, ⟨-, hr⟩ | ⟨-, a, hr, ha, -⟩⟩ := h
  · rcases localRunS_cases hr with he | ⟨c₁, hs⟩
    · have : s1.term = HelloSplit.workerCallH := congrArg Ctl.term he
      rw [this] at ht
      simp [HelloSplit.workerCallH, wkUnpark] at ht
    · exact wkUnpark_noStep hs ht
  · rcases localRunS_cases hr with he | ⟨c₁, hs⟩
    · subst he
      rcases ha with ⟨k, -, he⟩ | ⟨k, mw, b, -, he⟩ | ⟨he, -⟩
      · have := congrArg Ctl.term he
        simp [Ctl.of, ht, HelloPrintSrcPub.ldCP, wkUnpark] at this
      · have := congrArg Ctl.term he
        simp [Ctl.of, ht, HelloPrintSrcPub.emitCP, PrintSrc.printEmit, wkUnpark] at this
      · simp [Ctl.of, ht, wkUnpark] at he
    · exact wkUnpark_noStep hs ht

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {AbW : isaLSE2.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D}

/-- **`HelloRowsW.unpark_src`**: the worker's unpark is the source unpark,
in the store phase by wake's `unpark_src_of` at `relW` (no byte of a worker
`write` out there: `HelloStep1.storeWr0_of` at `KRHE`; mid-`write` the worker
is in the print phase). -/
theorem unpark_srcH (hwf : Λ.WF) {r0 r1 : Q.ι → Range} (hKR : Q.KR = HelloKRE.KRHE D r0 r1) :
    HelloCompat Q D M μ Λ arch AbW hcw hem →
      ∀ t es t' s, Q.Post Λ t s → Q.atUnpk t s → (machine (kernel 2)).Step μ 1 t es t' →
        ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  intro hC t es t' s hpost hu hs
  have hu' : (relW Q D hcw hem).atUnpk t s := hu
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hP⟩ | ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hE, -⟩ :=
    HelloEmitPh.post_partsHE hC.1.pt1 hpost
  rotate_left
  · -- mid-`write` the worker is in the print phase, not at its unpark
    refine (printPh_not_unpk hE.pt1.2.2.2.2.1.1 ?_).elim
    rw [hC.2.1.atUnpk] at hu'
    obtain ⟨s1', h1, hterm⟩ := hu'
    rw [hE.s1_get] at h1
    cases h1
    exact hterm
  have hS : StorePh (D.cw w) s1 := by
    rcases hP.pt1.2.2.1 with ⟨hpp, -⟩ | hS
    · refine (printPh_not_unpk hpp ?_).elim
      rw [hC.2.1.atUnpk] at hu'
      obtain ⟨s1', h1, hterm⟩ := hu'
      rw [hP.s1_get] at h1
      cases h1
      exact hterm
    · exact hS
  obtain ⟨s', hr, hP'⟩ := WakeW1.unpark_src_of hC.2.1 (HelloStep1.wcompatX_relW hC.2.2.1) hwf
    (post_toW (hcw := hcw) (hem := hem) hP hS (HelloStep1.storeWr0_of hKR hC _ _ _ _ _ _ _ _ _ _ _ hP hS)) hu' hs
  exact ⟨s', hr, post_ofW hC.1.pt1 (HelloStep1.krpW_of hC.2.2.1) hP'⟩

/-- info: 'Spike.Lib.HelloUnpk.unpark_srcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpark_srcH

end Spike.Lib.HelloUnpk
