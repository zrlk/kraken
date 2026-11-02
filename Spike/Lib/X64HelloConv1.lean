/-
**hello.w on x86-64: the worker's certification is append-free at `Post`**
(the worker's half; the twin of `X64WakeConv1.hconv_worker` /
`hconv_of'` at hello's worker data `PT1h` and kernel relation `KRH`).

As at wake: the worker's certifying runs stay in `X64HelloProm1.CInvH` (`Wi` at
a source thread in a phase, `X64HelloProm1.cstepH`), in both phases, where every
instruction tree of the certification semantics is `RelW1`
(`relW1_workerH`): off a system call it is the ISA's, `RelW1` at a state in
`Wi` by the named worker write fact `hW1`; at one it is a
choice of resumed states, or the ISA's fault (`WCompatH.sysExec`). `Post`
(unpacked as `X64HelloW1.PartsH`) puts the worker in `CInvH` (`PartsH.pt1`).

- `relW1_workerH`: the worker's certification trees are `RelW1`.
- `hconv1H`: the worker's half (`X64HelloConv0.hconv_ofH`'s `hconv1`).
- `hconvH`: `hconv` for both threads.

x86-64 twin of `Spike/Lib/HelloConv1.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the certification trees are x86-64's (`certSem abi Arch.tso`).
-/
import Spike.Lib.X64HelloConv0
import Spike.Lib.X64HelloProm1
import Spike.Lib.X64HelloNoCert
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloConv1

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeW1 Spike.Lib.X64WakeM0 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH WCompatH)
open Spike.Lib.X64HelloW1Store (NoWrite)
open Spike.Lib.X64HelloAssembly (HelloCompat)
open Spike.Lib.X64HelloProm1 (CInvH cstepH)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloWriteK (KRH)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isa.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}

/-- **The worker's instructions under the certification semantics are
`RelW1`** at a state in `Wi`, at any kernel state, given that its ISA
instructions are (`hW1`). -/
theorem relW1_workerH (hC : WCompatH Q D μ Λ arch AbW)
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isa.exec s = some e → EvTree.RelW1 Arch.tso e)
    {k : KState} {w : Q.ι} {s : isa.State} {c : Ctl} {fs : List TermRun.Frame}
    (hwi : D.Wi w s c fs) {e : EvTree isa.State} (he : soloExec abi Arch.tso μ k 1 s = some e) :
    EvTree.RelW1 Arch.tso e := by
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
phase (`X64HelloConv0.hconv_ofH`'s `hconv1`). -/
theorem hconv1H (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hW1 : ∀ w s c fs e, D.Wi w s c fs → isa.exec s = some e → EvTree.RelW1 Arch.tso e) :
    ∀ t s, Q.Post Λ t s → t.2.exited = none → ∀ th, t.1.threads[1]? = some th → t.2.runs 1 = true →
      th.prom ≠ [] → CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 th t.1.mem →
      CertReplay.CertOkCNA Arch.tso (certSem abi Arch.tso μ t.2 1) 1 th t.1.mem := by
  intro t s hP _ th ht _ _ hc
  rcases X64HelloEmitPh.post_partsHE hC.1.pt1 hP with ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ |
    ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h, -⟩
  rotate_left
  · -- mid-`write`: no certification step, so the run is empty
    have e : th = t1 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
    subst e
    obtain ⟨⟨c, fs, hwi⟩, ha, ⟨buf, n, hd⟩, -⟩ := h.pt1
    obtain ⟨t', mem', hr, he⟩ := hc
    cases hr with
    | refl => exact ⟨_, .refl _, he⟩
    | step hs _ => exact (X64HelloNoCert.no_cstep_write (hC.1.noSite w _ _ _ hwi) ha hd hs).elim
  have e : th = t1 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
  subst e
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx', ho⟩ := hC.2.1.cT w
    rw [show (Q.C w).cT = wordLoc a' from hcT]; exact inLabel_wordLoc h.core.mem hwf hx' ho
  have hle := X64HelloStep1Rt.prom_leH h
  have hq : CInvH Q D w (th, t.1.mem) :=
    { wi := ⟨s1, h.pt1.1, h.pt1.2.2.1.imp_left fun x => ⟨x.1, x.2.2.1⟩⟩
      msgs := Scc.Sem.MemInv.msgsExcept h.core.memInv _
      init := h.core.memInv.1
      le := hle
      cov := h.core.cov1
      own := h.ownOk1 hown
      offW := fun st fs L v hv => ⟨fun e => hown.cT w _ _ _ _ _ _ _ v h.core.mem (by rw [← e]; exact hv),
        fun fs' => hown.mp w fs' st L v (by rw [hown.const w st fs st fs']; exact hv)⟩ }
  exact CertReplay.certOkCNA_of_certOkC (P := CInvH Q D w)
    (fun x y hx' hs _ => (cstepH hC hms hcTin hx' hs).1)
    (fun x e hx' he => let ⟨_, hwi, _⟩ := hx'.wi; relW1_workerH hC.1 hW1 hwi he) hq hle hc

/-- **`hconv`** for both threads at hello's worker data: main by
`X64HelloConv0.hconv_mainH`, the worker by `hconv1H` (given `hW1`). -/
theorem hconvH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : X64HelloOwn1.Own1H Q D Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (hW1 : ∀ w s c fs e, D.Wi w s c fs → isa.exec s = some e → EvTree.RelW1 Arch.tso e) :
    ∀ t s, Q.Post Λ t s → CertConv μ t :=
  X64HelloConv0.hconv_ofH hC.1.pt1 hC.2.2.2 hPT0 hKR (hconv1H hC hwf hms hown hW1)

/-- info: 'Spike.Lib.X64HelloConv1.relW1_workerH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relW1_workerH

/-- info: 'Spike.Lib.X64HelloConv1.hconv1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv1H

/-- info: 'Spike.Lib.X64HelloConv1.hconvH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconvH

end Spike.Lib.X64HelloConv1
