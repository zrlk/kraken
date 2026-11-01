/-
**hello.w on AArch64: main's certification is append-free at `Post`** (row
B8-genV, main's half; the twin of `WakeConv0.hconv_main` / `hconv_of` at
hello's worker data `PT1h` and kernel relation `KRH`).

As at wake: main's certifying runs stay in `WakeM0.CInv0` (`WakeM0.cstep0`),
where every instruction tree of the certification semantics is `RelW1`
(`WakeConv0.relW1_main`); `CertReplay.certOkCNA_of_certOkC` makes a
certifying run append-free. While the process runs, `Post` (unpacked as
`HelloW1.PartsH`) puts main in `CInv0` (`PartsH.mi0`, at `KRH`'s
`MainLive`).

- `hconv_mainH`: main's half.
- `hconv_ofH`: `hconv` from main's half and the worker's (`hconv1`, a named
  hypothesis): `Post` has no third thread.
-/
import Spike.Lib.HelloM0Post
import Spike.Lib.WakeConv0

namespace Spike.Lib.HelloConv0

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeM0
open Spike.Lib.HelloW1 (WSideH PT1h PartsH post_partsH)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.A64HelloWriteK (KRH)

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout}

/-- **main's certification is append-free at `Post`** while the process
runs. -/
theorem hconv_mainH (hpt1 : Q.PT1 = HelloEmitPh.PT1hE D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s) (hx : t.2.exited = none)
    {th : Thread isaLSE2} (ht : t.1.threads[0]? = some th)
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 th t.1.mem) :
    CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 th t.1.mem := by
  obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := HelloM0.post_partsM hpt1 hP
  have e : th = t0 := by rw [h.th] at ht; exact (Option.some.inj ht).symm
  subst e
  have hq : CInv0 Q M w (th, t.1.mem) :=
    { mi := ⟨Ctl.of s0, h.mi0 hPT0 hKR hx, h.mCtl hPT0⟩
      msgs := Scc.Sem.MemInv.msgsExcept h.core.memInv _
      init := h.core.memInv.1
      le := h.prom_le0 }
  exact CertReplay.certOkCNA_of_certOkC (P := CInv0 Q M w) (fun x y hx hs _ => (cstep0 hC0 hx hs).1)
    (fun x e hx he => let ⟨_, hmi, _⟩ := hx.mi; WakeConv0.relW1_main hC0 hmi he) hq h.prom_le0 hc

/-- **`hconv`** from main's half (`hconv_mainH`) and the worker's (`hconv1`,
a named hypothesis): `Post` has no third thread. -/
theorem hconv_ofH (hpt1 : Q.PT1 = HelloEmitPh.PT1hE D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1)
    (hconv1 : ∀ t s, Q.Post Λ t s → t.2.exited = none → ∀ th, t.1.threads[1]? = some th → t.2.runs 1 = true →
      th.prom ≠ [] → CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 th t.1.mem →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 th t.1.mem) :
    ∀ t s, Q.Post Λ t s → CertConv μ t := by
  intro t s hP hx i th ht hr hp hc
  rcases i with _ | _ | n
  · exact hconv_mainH hpt1 hC0 hPT0 hKR hP hx ht hc
  · exact hconv1 t s hP hx th ht hr hp hc
  · exfalso
    obtain ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, h⟩ := HelloM0.post_partsM hpt1 hP
    rw [h.th] at ht
    simp at ht

/-- info: 'Spike.Lib.HelloConv0.hconv_mainH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_mainH

/-- info: 'Spike.Lib.HelloConv0.hconv_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hconv_ofH

end Spike.Lib.HelloConv0
