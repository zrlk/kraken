/-
**hello.w on x86-64: main's certification is append-free at `Post`**
(main's half; the twin of `X64WakeConv0.hconv_main` / `hconv_of` at
hello's worker data `PT1h` and kernel relation `KRH`).

As at wake: main's certifying runs stay in `X64WakeM0.CInv0` (`X64WakeM0.cstep0`),
where every instruction tree of the certification semantics is `RelW1`
(`X64WakeConv0.relW1_main`); `CertReplay.certOkCNA_of_certOkC` makes a
certifying run append-free. While the process runs, `Post` (unpacked as
`X64HelloW1.PartsH`) puts main in `CInv0` (`PartsH.mi0`, at `KRH`'s
`MainLive`).

- `hconv_mainH`: main's half.
- `hconv_ofH`: `hconv` from main's half and the worker's (`hconv1`, a named
  hypothesis): `Post` has no third thread.

x86-64 twin of `Spike/Lib/HelloConv0.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, `CInv0` carries `own` (main's owned words read as their
values, by `WCompat0.ownConst0` and the core) and `cov`.
-/
import Spike.Lib.X64HelloM0Post
import Spike.Lib.X64WakeConv0

namespace Spike.Lib.X64HelloConv0

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeW1 Spike.Lib.X64WakeM0
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloWriteK (KRH)

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout}

/-- **main's certification is append-free at `Post`** while the process
runs. -/
theorem hconv_mainH (hpt1 : Q.PT1 = X64HelloEmitPh.PT1hE D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) (hx : t.2.exited = none)
    {th : Thread isa} (ht : t.1.threads[0]? = some th)
    (hc : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 0) 0 th t.1.mem) :
    CertReplay.CertOkCNA Arch.tso (certSem abi Arch.tso μ t.2 0) 0 th t.1.mem := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := X64HelloM0.post_partsM hpt1 hP
  have e : th = t0 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
  subst e
  have hq : CInv0 Q M w (th, t.1.mem) :=
    { mi := ⟨Ctl.of s0, h.mi0 hPT0 hKR hx, h.mCtl hPT0⟩
      msgs := Scc.Sem.MemInv.msgsExcept h.core.memInv _
      init := h.core.memInv.1
      le := h.prom_le0
      own := fun st => by
        rw [hC0.ownConst0 w th.st st]
        have hpt0 := h.pt0
        rw [hPT0] at hpt0
        have h0 := h.core.own0
        simp only [ite_true] at h0
        rw [hpt0.2.1] at h0
        exact h0
      cov := h.core.cov0 }
  exact CertReplay.certOkCNA_of_certOkC (P := CInv0 Q M w) (fun x y hx hs _ => (cstep0 hC0 hx hs).1)
    (fun x e hx he => let ⟨_, hmi, _⟩ := hx.mi; X64WakeConv0.relW1_main hC0 hmi he) hq h.prom_le0 hc

/-- **`hconv`** from main's half (`hconv_mainH`) and the worker's (`hconv1`,
a named hypothesis): `Post` has no third thread. -/
theorem hconv_ofH (hpt1 : Q.PT1 = X64HelloEmitPh.PT1hE D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1)
    (hconv1 : ∀ t s, Q.Post Λ t s → t.2.exited = none → ∀ th, t.1.threads[1]? = some th → t.2.runs 1 = true →
      th.prom ≠ [] → CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 th t.1.mem →
      CertReplay.CertOkCNA Arch.tso (certSem abi Arch.tso μ t.2 1) 1 th t.1.mem) :
    ∀ t s, Q.Post Λ t s → CertConv μ t := by
  intro t s hP hx i th ht hr hp hc
  rcases i with _ | _ | n
  · exact hconv_mainH hpt1 hC0 hPT0 hKR hP hx ht hc
  · exact hconv1 t s hP hx th ht hr hp hc
  · exfalso
    obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := X64HelloM0.post_partsM hpt1 hP
    rw [h.th] at ht
    simp at ht

/-- info: 'Spike.Lib.X64HelloConv0.hconv_mainH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_mainH

/-- info: 'Spike.Lib.X64HelloConv0.hconv_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_ofH

end Spike.Lib.X64HelloConv0
