/-
**hello.w on AArch64: the worker's certification is append-free at `Post`**
(the worker's half; the twin of `WakeConv1.hconv_worker` /
`hconv_of'` at hello's worker data `PT1h` and kernel relation `KRH`).

As at wake: the worker's certifying runs stay in `HelloProm1.CInvH` (`Wi` at
a source thread in a phase, `HelloProm1.cstepH`), in both phases, where every
instruction tree of the certification semantics is `RelW1`
(`relW1_workerH`): off a system call it is the ISA's, `RelW1` at a state in
`Wi` by the named worker write fact `hW1`; at one it is a
choice of resumed states, or the ISA's fault (`WCompatH.sysExec`). `Post`
(unpacked as `HelloW1.PartsH`) puts the worker in `CInvH` (`PartsH.pt1`).

- `relW1_workerH`: the worker's certification trees are `RelW1`.
- `hconv1H`: the worker's half (`HelloConv0.hconv_ofH`'s `hconv1`).
- `hconvH`: `hconv` for both threads.
-/
import Spike.Lib.HelloConv0
import Spike.Lib.HelloProm1
import Spike.Lib.HelloNoCert

namespace Spike.Lib.HelloConv1

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeM0 Spike.Lib.Inv2Core
open Spike.Lib.HelloW1 (WSideH PT1h PartsH WCompatH post_partsH)
open Spike.Lib.HelloW1Store (NoWrite)
open Spike.Lib.HelloAssembly (HelloCompat)
open Spike.Lib.HelloProm1 (CInvH cstepH)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.A64HelloWriteK (KRH)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isaLSE2.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}

/-- **The worker's instructions under the certification semantics are
`RelW1`** at a state in `Wi`, at any kernel state, given that its ISA
instructions are (`hW1`). -/
theorem relW1_workerH (hC : WCompatH Q D μ Λ arch AbW)
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e)
    {k : KState} {w : Q.ι} {s : isaLSE2.State} {c : Ctl} {fs : List TermRun.Frame}
    (hwi : D.Wi w s c fs) {e : EvTree isaLSE2.State} (he : soloExec abi Arch.armv8 μ k 1 s = some e) :
    EvTree.RelW1 Arch.armv8 e := by
  have hs := hC.noSite w _ _ _ hwi
  cases hat : abi.atSys s
  · rw [soloExec_of_not_atSys abi hs hat] at he
    exact hW1 w _ _ _ _ hwi he
  · unfold soloExec at he
    rw [hs] at he
    simp only [hat, ite_true] at he
    split at he
    all_goals first
      | (cases he; exact .noW (.choose fun _ => .done _))
      | (obtain ⟨m, rfl⟩ := hC.sysExec w _ _ _ _ hwi hat he; exact .noW (.fault m))

/-- **The worker's certification is append-free at `Post`**, in either
phase (`HelloConv0.hconv_ofH`'s `hconv1`). -/
theorem hconv1H (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e) :
    ∀ t s, Q.Post Λ t s → t.2.exited = none → ∀ th, t.1.threads[1]? = some th → t.2.runs 1 = true →
      th.prom ≠ [] → CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 th t.1.mem →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 th t.1.mem := by
  intro t s hP _ th ht _ _ hc
  rcases HelloEmitPh.post_partsHE hC.1.pt1 hP with ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ |
    ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h, -⟩
  rotate_left
  · -- mid-`write`: no certification step, so the run is empty
    have e : th = t1 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
    subst e
    obtain ⟨⟨c, fs, hwi⟩, ha, ⟨buf, n, hd⟩, -⟩ := h.pt1
    obtain ⟨t', mem', hr, he⟩ := hc
    cases hr with
    | refl => exact ⟨_, .refl _, he⟩
    | step hs _ => exact (HelloNoCert.no_cstep_write (hC.1.noSite w _ _ _ hwi) ha hd hs).elim
  have e : th = t1 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
  subst e
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx', ho⟩ := hC.2.1.cT w
    rw [show (Q.C w).cT = wordLoc a' from hcT]; exact inLabel_wordLoc h.core.mem hwf hx' ho
  have hle := HelloStep1Rt.prom_leH h
  have hq : CInvH Q D w (th, t.1.mem) :=
    { wi := ⟨s1, h.pt1.1, h.pt1.2.2.1.imp_left fun x => ⟨x.1, x.2.2.1⟩⟩
      msgs := Scc.Sem.MemInv.msgsExcept h.core.memInv _
      init := h.core.memInv.1
      le := hle }
  exact CertReplay.certOkCNA_of_certOkC (P := CInvH Q D w)
    (fun x y hx' hs _ => (cstepH hC hms hcTin hx' hs).1)
    (fun x e hx' he => let ⟨_, hwi, _⟩ := hx'.wi; relW1_workerH hC.1 hW1 hwi he) hq hle hc

/-- **`hconv`** for both threads at hello's worker data: main by
`HelloConv0.hconv_mainH`, the worker by `hconv1H` (given `hW1`, the
worker's write fact). -/
theorem hconvH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hPT0 : Q.PT0 = PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e) :
    ∀ t s, Q.Post Λ t s → CertConv μ t :=
  HelloConv0.hconv_ofH hC.1.pt1 hC.2.2.2 hPT0 hKR (hconv1H hC hwf hms hW1)

/-- info: 'Spike.Lib.HelloConv1.relW1_workerH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relW1_workerH

/-- info: 'Spike.Lib.HelloConv1.hconv1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv1H

/-- info: 'Spike.Lib.HelloConv1.hconvH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconvH

end Spike.Lib.HelloConv1
