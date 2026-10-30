/-
**wake.w on AArch64: `KR` under main's source permit** (`WCompatX.krp`): the
kernel-side relation `KR` reads main's source thread only through its term,
so a step keeping the kernel state, main's target thread and the source trace and
setting main's source permit keeps it (a congruence of `kr_frame1`).

- `kr_permit`: `WCompatX.krp` at `KR r0 r1`.
-/
import Spike.Lib.WakeKR

namespace Spike.Lib.WakeKR

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Spike.Lib.WakeA64

/-- **`kr_permit`** (`WCompatX.krp`): a step keeping the kernel state and
main's target thread, main's source thread changed only in its permit,
and the source trace kept, keeps `KR`. -/
theorem kr_permit {ι : Type} {r0 r1 : ι → Range} :
    ∀ w (t t' : Cfg) (s s' : TermRun.Cfg) (s0 : TermRun.TTh) (p : Option Nat), KR r0 r1 w t s → t'.2 = t.2 →
      t'.1.threads[0]? = t.1.threads[0]? → s.ths[0]? = some s0 → s'.ths[0]? = some { s0 with permit := p } →
      SrcSem.traceOf s' = SrcSem.traceOf s → KR r0 r1 w t' s' := by
  intro w t t' s s' s0 p ⟨hn, h0, h1, hh, hm, htr⟩ ht _ hs0 hs0' hs'
  rw [KR, ht]
  exact ⟨hn, h0, h1, hh, fun hx s0' h => by rw [hs0'] at h; cases h; exact hm hx s0 hs0, hs'.trans htr⟩

/-- info: 'Spike.Lib.WakeKR.kr_permit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeKR.kr_permit

end Spike.Lib.WakeKR
