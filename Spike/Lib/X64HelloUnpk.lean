/-
**hello.w on x86-64: the worker's unpark after the spawn**
(`X64HelloAssembly.HelloRowsW.unpark_src`, the twin of `X64WakeW1.unpark_src_of`).

At the unpark row the source worker is at `wkUnpark`, which takes no local
step and is neither `print`'s call nor one of `print`'s anchors, so the
worker is not in the print phase (`printPh_not_unpk`): it is in the store
phase, where `Post` holds at wake's worker data `relW`
(`X64HelloW1Store.post_toW`) and wake's `X64WakeW1.unpark_src_of` applies (`relW`
changes `PT1` only, so its `atUnpk` is `Q`'s); its `Post` at `relW` is
`Post` at `Q` (`X64HelloW1Store.post_ofW`).

- `printPh_not_unpk`: the print phase is not at `wkUnpark`.
- `unpark_srcH`: `HelloRowsW.unpark_src`'s statement.

x86-64 twin of `Spike/Lib/HelloUnpk.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, `X64HelloStep1.wcompatX_relW` supplies x86-64's
`WCompatX` (`ownConst1`/`ownMp1` in place of `own1`).
-/
import Spike.Lib.X64HelloStep1

namespace Spike.Lib.X64HelloUnpk

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH PrintPh StorePh localRunS_cases wkUnpark_noStep)
open Spike.Lib.X64HelloW1Store (relW wsideW NoWrite post_toW post_ofW)
open Spike.Lib.X64HelloAssembly (HelloCompat)

/-- **The print phase is not at `wkUnpark`**: before `print`'s call the
source worker runs to the call (`wkUnpark` takes no step and is not the
call); inside `print` it runs to an anchor (`wkUnpark` is none). -/
theorem printPh_not_unpk {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {s1 : TermRun.TTh}
    (h : PrintPh l n m cw s1) (ht : s1.term = wkUnpark) : False := by
  obtain ⟨w0, w1, w2, w4, -, -, -, -, -, ⟨-, hr⟩ | ⟨-, a, hr, ha, -⟩⟩ := h
  · rcases localRunS_cases hr with he | ⟨c₁, hs⟩
    · have : s1.term = X64HelloSplit.workerCallH := congrArg Ctl.term he
      rw [this] at ht
      simp [X64HelloSplit.workerCallH, wkUnpark] at ht
    · exact wkUnpark_noStep hs ht
  · rcases localRunS_cases hr with he | ⟨c₁, hs⟩
    · subst he
      rcases ha with ⟨k, -, he⟩ | ⟨k, mw, b, -, he⟩ | ⟨he, -⟩
      · have := congrArg Ctl.term he
        simp [Ctl.of, ht, X64HelloPrintSrcPub.ldCP, wkUnpark] at this
      · have := congrArg Ctl.term he
        simp [Ctl.of, ht, X64HelloPrintSrcPub.emitCP, PrintSrc.printEmit, wkUnpark] at this
      · simp [Ctl.of, ht, wkUnpark] at he
    · exact wkUnpark_noStep hs ht

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : X64WakeM0.MSide Q.ι} {AbW : isa.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D}

/-- **`HelloRowsW.unpark_src`**: the worker's unpark is the source unpark,
in the store phase by wake's `unpark_src_of` at `relW` (no byte of a worker
`write` out there: `X64HelloStep1.storeWr0_of` at `KRHE`; mid-`write` the worker
is in the print phase). -/
theorem unpark_srcH (hwf : Λ.WF) {r0 r1 : Q.ι → Range} (hKR : Q.KR = X64HelloKRE.KRHE D r0 r1) :
    HelloCompat Q D M μ Λ arch AbW hcw hem →
      ∀ t es t' s, Q.Post Λ t s → Q.atUnpk t s → (machine (kernel 2)).Step μ 1 t es t' →
        ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  intro hC t es t' s hpost hu hs
  have hu' : (relW Q D hcw hem).atUnpk t s := hu
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hP⟩ | ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hE, -⟩ :=
    X64HelloEmitPh.post_partsHE hC.1.pt1 hpost
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
  obtain ⟨s', hr, hP'⟩ := X64WakeW1.unpark_src_of hC.2.1 (X64HelloStep1.wcompatX_relW hC.2.2.1) hwf
    (post_toW (hcw := hcw) (hem := hem) hP hS (X64HelloStep1.storeWr0_of hKR hC _ _ _ _ _ _ _ _ _ _ _ hP hS)) hu' hs
  exact ⟨s', hr, post_ofW hC.1.pt1 (X64HelloStep1.krpW_of hC.2.2.1) hP'⟩

/-- info: 'Spike.Lib.X64HelloUnpk.unpark_srcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpark_srcH

end Spike.Lib.X64HelloUnpk
