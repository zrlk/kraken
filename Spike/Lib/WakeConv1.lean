/-
**The worker's certification is append-free at `Post`** (`WakeAssembly`'s
`hconv` for thread 1, AArch64; `hconv_worker`, and `hconv_of'` for both
threads).

As for main (`Spike.Lib.WakeConv0`): the worker's certifying runs stay in
`WakeW1.CInv` (`WakeW1.cstep`, at any kernel state), where every instruction
tree of the certification semantics is `RelW1` (`relW1_worker`): off a system
call it is the ISA's, `RelW1` at a state in `Wi` by the named hypothesis `hW1`;
at one it is a choice of resumed states, or the ISA's fault
(`WCompat.sysExec`). `Post` puts the worker in `CInv` (`Parts.pt1`).
-/
import Spike.Lib.WakeConv0

namespace Spike.Lib.WakeConv1

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeM0 Spike.Lib.Inv2Core

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **The worker's instructions under the certification semantics are
`RelW1`** at a state in `Wi`, at any kernel state, given that its ISA
instructions are (`hW1`). -/
theorem relW1_worker (hC : WCompat Q D μ Λ arch)
    (hW1 : ∀ w s c e, D.Wi w s c → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e)
    {k : KState} {w : Q.ι} {s : isaLSE2.State} {c : Ctl}
    (hwi : D.Wi w s c) {e : EvTree isaLSE2.State} (he : soloExec abi Arch.armv8 μ k 1 s = some e) :
    EvTree.RelW1 Arch.armv8 e := by
  have hs := hC.noSite w _ _ hwi
  cases hat : abi.atSys s
  · rw [soloExec_of_not_atSys abi hs hat] at he
    exact hW1 w _ _ _ hwi he
  · unfold soloExec at he
    rw [hs] at he
    simp only [hat, ite_true] at he
    split at he
    all_goals first
      | (cases he; exact .noW (.choose fun _ => .done _))
      | (obtain ⟨m, rfl⟩ := hC.sysExec w _ _ _ hwi hat he; exact .noW (.fault m))

/-- **The worker's certification is append-free at `Post`.** -/
theorem hconv_worker (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF)
    (hW1 : ∀ w s c e, D.Wi w s c → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e)
    {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) {th : Thread isaLSE2} (ht : t.1.threads[1]? = some th)
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 th t.1.mem) :
    CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 th t.1.mem := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hP
  have e : th = t1 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
  subst e
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx', ho⟩ := hC.cT w
    rw [hcT]; exact inLabel_wordLoc h.core.mem hwf hx' ho
  have hq : CInv Q D w (th, t.1.mem) :=
    { wi := ⟨Ctl.of s1, h.pt1.1, h.wCtl⟩
      msgs := Scc.Sem.MemInv.msgsExcept h.core.memInv _
      init := h.core.memInv.1
      le := h.prom_le }
  exact CertReplay.certOkCNA_of_certOkC (P := CInv Q D w) (fun x y hx' hs _ => (cstep hC hx hcTin hx' hs).1)
    (fun x e hx' he => let ⟨_, hwi, _⟩ := hx'.wi; relW1_worker hC hW1 hwi he) hq h.prom_le hc

/-- **`hconv`** for both threads: main by `WakeConv0.hconv_main`, the worker
by `hconv_worker` (given `hW1`). -/
theorem hconv_of' (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hx : WCompatX Q D) (hwf : Λ.WF)
    (hPT0 : Q.PT0 = PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1)
    (hW1 : ∀ w s c e, D.Wi w s c → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e) :
    ∀ t s, Q.Post Λ t s → CertConv μ t :=
  WakeConv0.hconv_of hC hC0 hPT0 hKR fun _ _ hP _ _ ht _ _ hc => hconv_worker hC hx hwf hW1 hP ht hc

/-- info: 'Spike.Lib.WakeConv1.hconv_worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_worker

/-- info: 'Spike.Lib.WakeConv1.hconv_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_of'

end Spike.Lib.WakeConv1
