/-
**hello.w on x86-64: the worker's `write`, step and kernel-relation side**
(the x86-64 twin of `Spike/Lib/A64HelloWriteK.lean`; the part independent
of the print phase).

- `step_twrite`: **a step of a thread at a `write` system call** is a
  `sysStep` of the kernel (no instruction or promise step at a system call,
  no `clone`, no transfer; `X64WakePost1.step_texit`'s shape).
- `KRH`: **hello's kernel-side relation after the spawn**, wake's
  `X64WakeKR.KR` with the source-trace clause `traceOf s = []` (false once
  the worker has printed) weakened to "no `exit` in the source trace".
  `krh_of_kr`: `KR` gives it; `krh_live`, `krh_noexit`: its projections.
- `krh_frame1`, `krh_exit1`: `X64WakeKR.kr_frame1`, `kr_exit1` for `KRH`
  (the frame lemma takes "no new `exit`" in place of an equal trace).
- `krh_set1_run`: setting slot 1 to `run m` keeps `KRH`.

**Deviation from the A64 file.** The machine is x86-64's (`isa`,
`Scc.Sem.X64.abi`, `X64WakeA64.Cfg`); a thread at a `syscall` is off the
transfer sites by `X64WakePost1.atSvc_atNop`. A64's `step_twrite_k` and
`krh_write` have no consumer and are not twinned.
-/
import Spike.Lib.X64WakeKR
import Spike.Lib.X64WakePost1
import Spike.Lib.HelloWrite

namespace Spike.Lib.X64HelloWriteK

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.X64WakeA64
open Spike.Lib.WakeMLive (MainLive)

/-! ## The step at a `write` call -/

/-- **A step of thread `tid` at a `write` system call** is a `sysStep`. -/
theorem step_twrite {μ : Marks} {tid : Nat} {t t' : (machine (kernel 2)).Cfg} {es : List Ev}
    {t1 : Thread isa} {fd buf n : Nat} (h1 : t.1.threads[tid]? = some t1) (hsys : abi.atSys t1.st = true)
    (hc : callOf abi t1 = some (.write fd buf n)) (hs : (machine (kernel 2)).Step μ tid t es t') :
    ∃ p, sysStep abi Arch.tso tid t p = some (es, t') := by
  cases hs with
  | instr _ hns _ _ => exact absurd ⟨t1, h1, hsys⟩ hns
  | spawn _ h =>
    obtain ⟨j, r, hsp, -⟩ := h
    unfold spawnStep at hsp
    erw [h1] at hsp
    simp only at hsp
    split at hsp
    · cases hsp
    · rw [hc] at hsp; cases hsp
  | sys _ h _ _ _ =>
    obtain ⟨p, hp, -⟩ := h
    exact ⟨p, hp⟩
  | xfer k _ _ h =>
    have hn : abi.atNop t1.st = false := Spike.Lib.X64WakePost1.atSvc_atNop hsys
    cases k with
    | take =>
      change takeStep abi tid t = some t' at h
      unfold takeStep at h
      erw [h1] at h
      simp only [hn, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    | release =>
      change releaseStep abi tid t = some t' at h
      unfold releaseStep at h
      erw [h1] at h
      simp only [hn, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-! ## The kernel relation -/

/-- **Hello's kernel-side relation after the spawn**: `X64WakeKR.KR` with no
`exit` in the source trace in place of an empty trace. -/
def KRH {ι : Type} (r0 r1 : ι → Range) (w : ι) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  t.2.slots.size = 2 ∧ (∃ j, t.2.slots[0]? = some (.run j)) ∧ t.2.slots[1]? ≠ some .dormant ∧
    t.2.held = [(1, r1 w), (0, r0 w)] ∧ MainLive t.2 s ∧ ∀ c, Ev.exit c ∉ SrcSem.traceOf s

/-- **`KR` gives `KRH`.** -/
theorem krh_of_kr {ι : Type} {r0 r1 : ι → Range} {w : ι} {t : Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakeKR.KR r0 r1 w t s) : KRH r0 r1 w t s := by
  obtain ⟨hn, h0, h1, hh, hm, htr⟩ := h
  exact ⟨hn, h0, h1, hh, hm, by simp [htr]⟩

/-- **The liveness projection.** -/
theorem krh_live {ι : Type} {r0 r1 : ι → Range} {w : ι} {t : Cfg} {s : TermRun.Cfg}
    (h : KRH r0 r1 w t s) : MainLive t.2 s :=
  h.2.2.2.2.1

/-- **No `exit` in the source trace.** -/
theorem krh_noexit {ι : Type} {r0 r1 : ι → Range} {w : ι} {t : Cfg} {s : TermRun.Cfg}
    (h : KRH r0 r1 w t s) : ∀ c, Ev.exit c ∉ SrcSem.traceOf s :=
  h.2.2.2.2.2

/-- **`krh_frame1`**: a step keeping the kernel state and main's source
thread, adding no `exit` to the source trace, keeps `KRH`. -/
theorem krh_frame1 {ι : Type} {r0 r1 : ι → Range} :
    ∀ w (t t' : Cfg) (s s' : TermRun.Cfg), KRH r0 r1 w t s → t'.2 = t.2 → s'.ths[0]? = s.ths[0]? →
      (∀ c, Ev.exit c ∈ SrcSem.traceOf s' → Ev.exit c ∈ SrcSem.traceOf s) → KRH r0 r1 w t' s' := by
  intro w t t' s s' ⟨hn, h0, h1, hh, hm, htr⟩ ht hs hs'
  rw [KRH, ht]
  exact ⟨hn, h0, h1, hh, fun hx s0 hs0 => hm hx s0 (hs ▸ hs0), fun c hc => htr c (hs' c hc)⟩

/-- **`krh_exit1`**: slot 1 exiting keeps `KRH`. -/
theorem krh_exit1 {ι : Type} {r0 r1 : ι → Range} :
    ∀ w (t : Cfg) s, KRH r0 r1 w t s → KRH r0 r1 w (t.1, t.2.set 1 .exited) s := by
  intro w t s ⟨hn, ⟨j, h0⟩, _, hh, hm, htr⟩
  refine ⟨?_, ⟨j, ?_⟩, ?_, hh, hm, htr⟩
  · simp [KState.set, hn]
  · simp only [KState.set]
    rw [Array.set!, Array.getElem?_setIfInBounds_ne (by decide)]; exact h0
  · simp only [KState.set]
    rw [Array.set!, Array.getElem?_setIfInBounds_self_of_lt (by omega)]; simp

/-- **`krh_set1_run`**: slot 1 set to `run m` keeps `KRH`. -/
theorem krh_set1_run {ι : Type} {r0 r1 : ι → Range} {w : ι} {t : Cfg} {s : TermRun.Cfg} (m : Nat)
    (h : KRH r0 r1 w t s) (x : Config isa) : KRH r0 r1 w (x, t.2.set 1 (.run m)) s := by
  obtain ⟨hn, ⟨j, h0⟩, _, hh, hm, htr⟩ := h
  refine ⟨?_, ⟨j, ?_⟩, ?_, hh, hm, htr⟩
  · simp [KState.set, hn]
  · simp only [KState.set]
    rw [Array.set!, Array.getElem?_setIfInBounds_ne (by decide)]; exact h0
  · simp only [KState.set]
    rw [Array.set!, Array.getElem?_setIfInBounds_self_of_lt (by omega)]; simp

/-- info: 'Spike.Lib.X64HelloWriteK.step_twrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_twrite

/-- info: 'Spike.Lib.X64HelloWriteK.krh_frame1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms krh_frame1

/-- info: 'Spike.Lib.X64HelloWriteK.krh_exit1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms krh_exit1

/-- info: 'Spike.Lib.X64HelloWriteK.krh_set1_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms krh_set1_run

end Spike.Lib.X64HelloWriteK
