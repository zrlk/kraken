/-
**wake.w on AArch64: the kernel-side relation after the spawn**: the datum `KR` of `WakeRel`, at the two stack ranges of the ghost
record (`r0 w` main's, `r1 w` the worker's).

- `KR r0 r1 w t s`: two slots, main's running, the worker's running or
  exited (never dormant again), the held list exactly
  `[(1, r1 w), (0, r0 w)]` (the clone moved `r1` to the worker, and neither
  thread releases nor takes after it), `WakeMLive.MainLive t.2 s`
  (main's source has not returned while the process runs), and no source
  event (`SrcSem.traceOf`, the observed list: `wakeSrc` has no exit event,
  and `park`/`unpark` add none).
  It reads the kernel state, main's source thread and the source trace
  only: neither memory, nor thread 1 of either side, nor the target
  threads.
- `kr_frame1`: `WCompat.kr`, a step keeping the kernel state, main's
  source thread and the source trace keeps `KR`.
- `kr_exit1`: `TexitFacts.kr_exit1`, slot 1 exiting keeps `KR`.
- `kr_live`: `WakeM0.LiveK`, the liveness projection.
- `kr_trace`: the empty-trace projection.
- `kr_start`: `KR` right after main's clone (`afterClone`) from main's
  kernel state at the clone (one running slot, the held list
  `[(0, r1), (0, r0)]` with `r1` handed), main's source term and an empty
  source trace.
-/
import Spike.Lib.WakeA64
import Spike.Lib.WakeMLive

namespace Spike.Lib.WakeKR

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.Handover Spike.Lib.WakeA64
open Spike.Lib.WakeMLive (wlRet MainLive)

/-- **The kernel-side relation after the spawn**, at the ghost record's
stack ranges `r0` (main's) and `r1` (the worker's). -/
def KR {ι : Type} (r0 r1 : ι → Range) (w : ι) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  t.2.slots.size = 2 ∧ (∃ j, t.2.slots[0]? = some (.run j)) ∧ t.2.slots[1]? ≠ some .dormant ∧
    t.2.held = [(1, r1 w), (0, r0 w)] ∧ MainLive t.2 s ∧ SrcSem.traceOf s = []

/-- **`kr_frame1`** (`WCompat.kr`): a step keeping the kernel state, main's
source thread and the source trace keeps `KR`. -/
theorem kr_frame1 {ι : Type} {r0 r1 : ι → Range} :
    ∀ w (t t' : Cfg) (s s' : TermRun.Cfg), KR r0 r1 w t s → t'.2 = t.2 →
      t'.1.threads[0]? = t.1.threads[0]? → s'.ths[0]? = s.ths[0]? → SrcSem.traceOf s' = SrcSem.traceOf s →
      KR r0 r1 w t' s' := by
  intro w t t' s s' ⟨hn, h0, h1, hh, hm, htr⟩ ht _ hs hs'
  rw [KR, ht]
  exact ⟨hn, h0, h1, hh, fun hx s0 hs0 => hm hx s0 (hs ▸ hs0), hs'.trans htr⟩

/-- **`kr_exit1`** (`TexitFacts.kr_exit1`): slot 1 exiting keeps `KR`. -/
theorem kr_exit1 {ι : Type} {r0 r1 : ι → Range} {P : Cfg → TermRun.Cfg → Prop} :
    ∀ w (t : Cfg) s, KR r0 r1 w t s → P t s → KR r0 r1 w (t.1, t.2.set 1 .exited) s := by
  intro w t s ⟨hn, ⟨j, h0⟩, _, hh, hm, htr⟩ _
  refine ⟨?_, ⟨j, ?_⟩, ?_, hh, hm, htr⟩
  · simp [KState.set, hn]
  · simp only [KState.set]
    rw [Array.set!, Array.getElem?_setIfInBounds_ne (by decide)]; exact h0
  · simp only [KState.set]
    rw [Array.set!, Array.getElem?_setIfInBounds_self_of_lt (by omega)]; simp

/-- **The liveness projection** (`WakeM0.LiveK`). -/
theorem kr_live {ι : Type} {r0 r1 : ι → Range} {w : ι} {t : Cfg} {s : TermRun.Cfg}
    (h : KR r0 r1 w t s) : MainLive t.2 s :=
  h.2.2.2.2.1

/-- **No source event is observed** (`SrcSem.traceOf`; main's
`exit_group`: the source observation is `[exit c]` only on a trace with no
exit). -/
theorem kr_trace {ι : Type} {r0 r1 : ι → Range} {w : ι} {t : Cfg} {s : TermRun.Cfg}
    (h : KR r0 r1 w t s) : SrcSem.traceOf s = [] :=
  h.2.2.2.2.2

/-- **`KR` at the clone**: main's kernel state with one running slot, the
held list `[(0, r1), (0, r0)]` with `r1` the handed range (`stack` its
end), `r0 ≠ r1`, main's source thread not at `wlRet`, and an empty source
trace. -/
theorem kr_start {ι : Type} {r0 r1 : ι → Range} {w : ι} {d : Cfg} {th : Thread isaLSE2}
    {stack tls : Nat} {r : BitVec 64} {s : TermRun.Cfg} {j : Nat}
    (hsl : d.2.slots = #[.run j]) (hh : d.2.held = [(0, r1 w), (0, r0 w)])
    (hst : (r1 w).lo + (r1 w).size = stack)
    (hm : ∀ s0, s.ths[0]? = some s0 → s0.term ≠ wlRet) (htr : SrcSem.traceOf s = []) :
    KR r0 r1 w (afterClone abi d 0 th stack tls r) s := by
  have hd : handed d.2 0 stack = some (0, r1 w) := by
    simp [handed, hh, hst]
  refine ⟨?_, ⟨j, ?_⟩, ?_, ?_, fun _ => hm, htr⟩
  · simp [afterClone, hsl]
  · simp [afterClone, hsl]
  · simp [afterClone, hsl]
  · simp only [afterClone, heldAfter, hd, hsl, Array.size_singleton, hh]
    simp

/-- info: 'Spike.Lib.WakeKR.kr_frame1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeKR.kr_frame1

/-- info: 'Spike.Lib.WakeKR.kr_exit1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeKR.kr_exit1

/-- info: 'Spike.Lib.WakeKR.kr_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeKR.kr_live

/-- info: 'Spike.Lib.WakeKR.kr_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeKR.kr_trace

/-- info: 'Spike.Lib.WakeKR.kr_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeKR.kr_start

end Spike.Lib.WakeKR
