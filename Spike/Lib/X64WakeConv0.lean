/-
**main's certification is append-free at `Post`** (`WakeAssembly`'s `hconv`
for thread 0, x86-64; `hconv_main`, and `hconv_of` with the worker's half as
a named hypothesis).

main's certifying runs stay in `CInv0` (`X64WakeM0.cstep0`, at any kernel state),
where every instruction tree of the certification semantics is `RelW1`
(`relW1_main`): off a system call it is the ISA's (`WCompat0.relW0`); at one
it is a choice of resumed states, or the ISA's fault (`WCompat0.sysExec0`).
`CertReplay.certOkCNA_of_certOkC` then makes a certifying run append-free.
While the process runs, `Post` puts main in `CInv0` (`Parts.mi0`).

x86-64 twin of `Spike/Lib/WakeConv0.lean` (same names, namespaces with the
`X64` prefix).
-/
import Spike.Lib.X64WakeM0Prom
import Spike.Lib.CertReplay

namespace Spike.Lib.X64WakeConv0

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeW1 Spike.Lib.X64WakeM0

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **main's instructions under the certification semantics are `RelW1`**
at a state in `Mi`, at any kernel state. -/
theorem relW1_main (hC0 : WCompat0 Q M μ Λ) {k : KState} {w : Q.ι} {s : isa.State} {c : Ctl}
    (hmi : M.Mi w s c) {e : EvTree isa.State} (he : soloExec abi Arch.tso μ k 0 s = some e) :
    EvTree.RelW1 Arch.tso e := by
  have hs := hC0.noSite0 w _ _ hmi
  cases hat : abi.atSys s
  · rw [soloExec_of_not_atSys abi hs hat] at he
    exact hC0.relW0 w _ _ _ hmi he
  · unfold soloExec at he
    rw [hs] at he
    simp only [hat, ite_true] at he
    split at he
    all_goals first
      | (cases he; exact .noW (.choose fun _ => .done _))
      | (obtain ⟨m, rfl⟩ := hC0.sysExec0 w _ _ _ hmi hat he; exact .noW (.fault m))

/-- **main's certification is append-free at `Post`** while the process
runs. -/
theorem hconv_main (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = X64WakeKR.KR r0 r1) {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) (hx : t.2.exited = none)
    {th : Thread isa} (ht : t.1.threads[0]? = some th)
    (hc : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 0) 0 th t.1.mem) :
    CertReplay.CertOkCNA Arch.tso (certSem abi Arch.tso μ t.2 0) 0 th t.1.mem := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hP
  have e : th = t0 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
  subst e
  have hq : CInv0 Q M w (th, t.1.mem) :=
    { mi := ⟨Ctl.of s0, h.mi0 hPT0 hKR hx, h.mCtl hPT0⟩
      msgs := Scc.Sem.MemInv.msgsExcept h.core.memInv _
      init := h.core.memInv.1
      le := h.prom_le0
      own := fun st => by rw [hC0.ownConst0 w th.st st]; exact h.own0 hPT0
      cov := h.core.cov0 }
  exact CertReplay.certOkCNA_of_certOkC (P := CInv0 Q M w) (fun x y hx hs _ => (cstep0 hC0 hx hs).1)
    (fun x e hx he => let ⟨_, hmi, _⟩ := hx.mi; relW1_main hC0 hmi he) hq h.prom_le0 hc

/-- **`hconv`** from main's half (`hconv_main`) and the worker's (`hconv1`, a
named hypothesis): `Post` has no third thread. -/
theorem hconv_of (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = X64WakeKR.KR r0 r1)
    (hconv1 : ∀ t s, Q.Post Λ t s → t.2.exited = none → ∀ th, t.1.threads[1]? = some th → t.2.runs 1 = true →
      th.prom ≠ [] → CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 th t.1.mem →
      CertReplay.CertOkCNA Arch.tso (certSem abi Arch.tso μ t.2 1) 1 th t.1.mem) :
    ∀ t s, Q.Post Λ t s → CertConv μ t := by
  intro t s hP hx i th ht hr hp hc
  rcases i with _ | _ | n
  · exact hconv_main hC hC0 hPT0 hKR hP hx ht hc
  · exact hconv1 t s hP hx th ht hr hp hc
  · exfalso
    obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := post_parts hC hP
    rw [h.th] at ht
    simp at ht

/-- info: 'Spike.Lib.X64WakeConv0.hconv_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_main

/-- info: 'Spike.Lib.X64WakeConv0.hconv_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_of

end Spike.Lib.X64WakeConv0
