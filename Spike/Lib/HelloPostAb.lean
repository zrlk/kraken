/-
**hello.w on AArch64: aborts after the spawn**: the
worker's `print` may abort after the spawn (its refused `write` reaches
`scc_rt_abort(4)`, then `scc_rt_abort_write`'s `exit_group(101)`), so
`WakeObligations.post_abort` is not vacuous at hello (as wake's
`WakeNoAbort.post_abort_of` is). Its `writeErr` abort is justified by the
`writeErr` the kernel emitted at the refused `write` (`Kernel.sysStep`'s
`writeRefused` return), carried in a trace invariant `TwH`.

- `TwH Λ E Ab t tr` (`hello_obligations`' `Tw`): the run invariant
  (`WakeRunInv.RunInv`, for the witness), and, off the lifts (the last slot
  not dormant), `W1`: thread 1's bytes out are those of a `write` it sits
  at (`A64Consumer.WrOk`), and thread 1 in the abort phase `Ab` means
  `Ev.writeErr` is in the trace.
- `tw_load`: at the load (a lift).
- `tw_step`: along every step from `Rw`. Before the spawn the configuration
  is a lift but after the `clone`, where the child is out of `Ab`
  (`hcl`). After it a step of main keeps thread 1 and its slot
  (`w1_frame`); a step of the worker enters `Ab` only at a refused `write`
  (`AbSt.abSys`, `Consumer1.Refusal`), which emits `writeErr`
  (`write_ret_cases`).
- `post_abortH`: an abort step after the spawn is the worker's at the
  `writeErr` site in `Ab` (main is at no abort site, `hoff0`), justified by
  `TwH`'s `writeErr`; the witness is `post_wit`'s (`hwit`) at `TwH`'s run
  invariant.
- `refused_enters`: non-vacuity of the `Ab` branch: the kernel's refused
  return to a `write` at `print`'s system call emits `writeErr` and lands in
  `WriteAb.Ab` (its `.ret` class) when the stored length is refused.

Rows: `hab1` (5i-hab1: the worker's states keep `Ab` but at a refused
`write` and are at the abort sites only at `writeErr` in `Ab`), `hcl`
(5i-hcl: at `R1`'s `clone` one thread, the child out of `Ab`).
-/
import Spike.Lib.WakeNoAbort
import Spike.Lib.WakeCert
import Spike.Lib.WakeW1Step
import Spike.Lib.WakeRunInv
import Spike.Lib.HelloWrite
import Spike.Lib.A64SFactsA
import Spike.Lib.A64WriteAb
import Spike.Lib.HelloW1Print
import Spike.Lib.A64HelloWriteK

namespace Spike.Lib.HelloPostAb

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeA64 Spike.Lib.Handover
open Spike.Lib.A64Consumer (WrOk)
open Spike.Lib.A64ConsumerA (AbSt)
open Spike.Lib.Consumer1 (Refusal)

/-! ## The trace invariant -/

/-- **Thread 1's facts**: its bytes out are those of a `write` it sits at,
and in the abort phase `Ab` the trace has the refusal's `writeErr`. -/
def W1 (Ab : State → Prop) (t : Cfg) (tr : List Ev) : Prop :=
  ∀ t1, t.1.threads[1]? = some t1 → WrOk t1 (t.2.wr 1) ∧ (Ab t1.st → Ev.writeErr ∈ tr)

/-- **hello's trace invariant after the spawn** (`hello_obligations`' `Tw`):
the run invariant, and `W1` off the lifts (the last slot not dormant). -/
def TwH (Λ : Scc.Sem.Layout) (E : Entry) (Ab : State → Prop) (t : Cfg) (tr : List Ev) : Prop :=
  WakeRunInv.RunInv Λ E t ∧ (t.2.slots.back? ≠ some Slot.dormant → W1 Ab t tr)

/-- **The worker's abort facts** at a state (row 5i-hab1): `AbSt` (off
`Ab`, no instruction enters it and a system call only as a refused
`write`), and at an abort site the kind is `writeErr`, in `Ab`. -/
structure AbFacts (μ : Marks) (Ab : State → Prop) (s : State) : Prop where
  ab : AbSt μ Ab s
  at_ : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .writeErr ∧ Ab s

/-- A lift's last slot is dormant. -/
theorem up_back (d : Cfg) (u : Thread isaLSE2) : (up d u).2.slots.back? = some Slot.dormant := by
  simp [up, upX]

/-! ## Kernel facts -/

/-- `wr` after setting the slot to `run j`. -/
theorem wr_set_run {x : KState} {tid j : Nat} (h : tid < x.slots.size) : (x.set tid (.run j)).wr tid = j := by
  simp [KState.wr, KState.set, h]

/-- `wr` after setting the slot to `exited`. -/
theorem wr_set_exited {x : KState} {tid : Nat} : (x.set tid .exited).wr tid = 0 := by
  unfold KState.wr KState.set
  by_cases h : tid < x.slots.size <;> simp [h]

/-- **A return of `write(fd, buf, n)`**: the byte count after `k ≥ 1` bytes,
or before any `-EINTR`/`-EAGAIN` with no event, or a refusal with
`writeErr`. -/
theorem write_ret_cases {A : Arch} {tid : Nat} {c c' : Config isaLSE2 × KState} {r : BitVec 64} {es : List Ev}
    {t : Thread isaLSE2} {fd buf n : Nat} (ht : c.1.threads[tid]? = some t)
    (hc : callOf abi t = some (.write fd buf n)) (h : sysStep abi A tid c (.ret r) = some (es, c')) :
    (0 < c.2.wr tid ∧ r = BitVec.ofNat 64 (c.2.wr tid) ∧ es = [] ∧
        c' = (c.1.withThread tid (retThread abi t r) c.1.mem, c.2.set tid (.run 0))) ∨
      (c.2.wr tid = 0 ∧ (r = neg eintr ∨ r = neg eagain) ∧ es = [] ∧
        c' = (c.1.withThread tid (retThread abi t r) c.1.mem, c.2)) ∨
      (c.2.wr tid = 0 ∧ writeRefused r = true ∧ es = [.writeErr] ∧
        c' = (c.1.withThread tid (retThread abi t r) c.1.mem, c.2)) := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  simp only at h
  split at h
  · rename_i hj
    split at h
    · rename_i hr
      subst hr
      simp only [back, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inl ⟨hj, rfl, rfl, rfl⟩
    · cases h
  · rename_i hj
    have hj0 : c.2.wr tid = 0 := by omega
    split at h
    · rename_i he
      simp only [back, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr (.inl ⟨hj0, he, rfl, rfl⟩)
    · split at h
      · rename_i hw
        simp only [back, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inr ⟨hj0, hw, rfl, rfl⟩)
      · cases h

/-- **A return of a call other than `write`, `exit`, `exit_group`** keeps the
kernel state. -/
theorem ret_ks {A : Arch} {tid : Nat} {c c' : Config isaLSE2 × KState} {r : BitVec 64} {es : List Ev}
    {t : Thread isaLSE2} {call : Call} (ht : c.1.threads[tid]? = some t) (hc : callOf abi t = some call)
    (hw : ∀ fd buf n, call ≠ .write fd buf n) (hx : call ≠ .exit) (hg : ∀ v, call ≠ .exitGroup v)
    (h : sysStep abi A tid c (.ret r) = some (es, c')) : c'.2 = c.2 := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  cases call with
  | write fd buf n => exact absurd rfl (hw fd buf n)
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | _ =>
    simp only at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; rfl)
      | (simp only [back, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl)

/-- **A range transfer keeps the memory, the other threads and every slot.** -/
theorem xferStep_frame {k : XferKind} {tid : Nat} {c c' : Config isaLSE2 × KState}
    (h : xferStep abi k tid c = some c') :
    (∀ i, i ≠ tid → c'.1.threads[i]? = c.1.threads[i]?) ∧ c'.2.slots = c.2.slots := by
  cases k <;> simp only [xferStep, takeStep, releaseStep] at h <;> split at h <;> try cases h
  all_goals
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨fun _ hi => WakeCert.withThread_ne hi, rfl⟩
    · cases h

/-! ## `W1` along the steps after the spawn -/

variable {μ : Marks} {Ab : State → Prop}

/-- `W1` with thread 1 and its slot kept. -/
theorem w1_frame {t t' : Cfg} {tr es : List Ev} (h1 : t'.1.threads[1]? = t.1.threads[1]?)
    (h2 : t'.2.slots[1]? = t.2.slots[1]?) (h : W1 Ab t tr) : W1 Ab t' (tr ++ es) := by
  intro t1 ht1
  rw [h1] at ht1
  have hw : t'.2.wr 1 = t.2.wr 1 := by simp only [KState.wr, h2]
  obtain ⟨hb, ha⟩ := h t1 ht1
  exact ⟨hw ▸ hb, fun hA => List.mem_append_left _ (ha hA)⟩

/-- No `clone` from a two-slot configuration with no dormant slot. -/
theorem no_spawn {tid j : Nat} {t t' : Cfg} {r : BitVec 64} (hn : t.1.threads.size = 2)
    (hK : (∃ j, t.2.slots[0]? = some (.run j)) ∧ t.2.slots[1]? ≠ some Slot.dormant)
    (h : spawnStep abi tid t j r = some t') : False := by
  obtain ⟨hd, hj⟩ := WakeCert.spawnStep_dormant h
  rw [hn] at hj
  rcases j with _ | _ | j
  · obtain ⟨j0, h0⟩ := hK.1
    rw [h0] at hd; cases hd
  · exact hK.2 hd
  · omega

/-- **A step of main keeps `W1`**: thread 1 and its slot are kept. -/
theorem w1_step0 {t t' : Cfg} {es tr : List Ev} (hn : t.1.threads.size = 2)
    (hK : (∃ j, t.2.slots[0]? = some (.run j)) ∧ t.2.slots[1]? ≠ some Slot.dormant)
    (hs : (machine (kernel 2)).Step μ 0 t es t') (h : W1 Ab t tr) : W1 Ab t' (tr ++ es) := by
  obtain ⟨⟨th, ht⟩, -, -⟩ := hs.runs
  have h10 : (1 : Nat) ≠ 0 := by decide
  rcases WakeW1.step1_cases ht hs with ⟨-, -, outs, o, -, -, rfl, -⟩ | ⟨-, w, -, rfl, -⟩ | ⟨p, hsy, -⟩ |
      ⟨-, j, r, hsp⟩ | ⟨-, k, -, hx⟩
  · exact w1_frame (WakeCert.withThread_ne h10) rfl h
  · exact w1_frame (WakeCert.withThread_ne h10) rfl h
  · obtain ⟨-, hth, hsl⟩ := WakeCert.sysStep_frame hsy
    exact w1_frame (hth 1 h10) (hsl 1 h10) h
  · exact (no_spawn hn hK hsp).elim
  · obtain ⟨hth, hsl⟩ := xferStep_frame hx
    exact w1_frame (hth 1 h10) (by rw [hsl]) h

/-- **A step of the worker keeps `W1`**: it enters `Ab` only at a refused
`write`, whose return emits `writeErr`. -/
theorem w1_step1 {t t' : Cfg} {es tr : List Ev} {t1 : Thread isaLSE2} (hn : t.1.threads.size = 2)
    (hK : t.2.slots.size = 2 ∧ (∃ j, t.2.slots[0]? = some (.run j)) ∧ t.2.slots[1]? ≠ some Slot.dormant)
    (ht1 : t.1.threads[1]? = some t1) (hF : AbFacts μ Ab t1.st) (hns : siteAt abi μ t1.st = none)
    (hs : (machine (kernel 2)).Step μ 1 t es t') (h : W1 Ab t tr) : W1 Ab t' (tr ++ es) := by
  obtain ⟨hwb, hab⟩ := h t1 ht1
  have hl1 : 1 < t.2.slots.size := by rw [hK.1]; decide
  -- thread 1 in `Ab` before the step: the trace already has `writeErr`
  have hold : ∀ u : Thread isaLSE2, u.st = t1.st → Ab u.st → Ev.writeErr ∈ tr ++ es :=
    fun u hu hA => List.mem_append_left _ (hab (hu ▸ hA))
  have hget : ∀ {u : Thread isaLSE2} {m : Memory} {v : Thread isaLSE2},
      (t.1.withThread 1 u m).threads[1]? = some v → v = u := fun hv =>
    (Option.some.inj ((Live.Sem.withThread_get_self ht1).symm.trans hv)).symm
  rcases WakeW1.step1_cases ht1 hs with ⟨rfl, hns', outs, o, hso, ho, rfl, -⟩ | ⟨rfl, w, -, rfl, -⟩ |
      ⟨p, hsy, -⟩ | ⟨-, j, r, hsp⟩ | ⟨-, k, hk, -⟩
  · -- an instruction: off a system call, so no bytes out; `Ab` not entered
    intro u hu
    obtain rfl := hget hu
    have hw0 : t.2.wr 1 = 0 := hwb.resolve_right fun ⟨ha, _⟩ => by rw [hns'] at ha; cases ha
    refine ⟨.inl hw0, fun hA => ?_⟩
    by_cases hA0 : Ab t1.st
    · exact List.mem_append_left _ (hab hA0)
    exact absurd hA (stepOne_allInv Arch.armv8 hso ho (hF.ab.abInstr hA0 hns')
      ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  · -- a promise: the state is kept
    intro u hu
    obtain rfl := hget hu
    exact ⟨hwb, hold _ rfl⟩
  · have hwr : ∀ fd buf n, callOf abi t1 = some (.write fd buf n) → t.2.wr 1 ≤ n := by
      intro fd buf n hc
      rcases hwb with h0 | ⟨-, fd', buf', n', hc', hle⟩
      · rw [h0]; exact Nat.zero_le _
      · rw [hc] at hc'; cases hc'; exact hle
    obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases ht1 hsy hwr
    have hat : abi.atSys t1.st = true := by
      simp only [ready, Bool.and_eq_true] at hr; exact hr.1.1
    rcases hcases with ⟨fd, buf, n, rd, b, u', rfl, rfl, hlt, -, hust, -, rfl⟩ |
      ⟨r, rfl, hnx, hng, -, -, u', hu', hsu, -⟩ | ⟨hw, -, -, rfl⟩ | ⟨v, hw, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · -- a byte of the `write`: the state kept, one more byte out
      intro u hu
      obtain rfl := hget hu
      refine ⟨.inr ⟨hust ▸ hat, fd, buf, n, ?_, ?_⟩, hold _ hust⟩
      · show decode abi.nrs (abi.nr u.st) (abi.arg u.st) = _
        rw [hust]; exact hcall
      · rw [wr_set_run hl1]; omega
    · -- a return
      by_cases hwc : ∃ fd buf n, call = .write fd buf n
      · obtain ⟨fd, buf, n, rfl⟩ := hwc
        rcases write_ret_cases ht1 hcall hsy with ⟨hj, rfl, rfl, rfl⟩ | ⟨hj, hr', rfl, rfl⟩ |
          ⟨hj, hw, rfl, rfl⟩
        · intro u hu
          obtain rfl := hget hu
          refine ⟨.inl (wr_set_run hl1), fun hA => ?_⟩
          by_cases hA0 : Ab t1.st
          · exact List.mem_append_left _ (hab hA0)
          have hu2 := hget hu'
          subst hu2
          obtain ⟨fd', buf', n', he, hrf⟩ := hF.ab.abSys hA0 hat _ hcall _ hsu hA
          cases he
          exact absurd rfl ((hrf _ (retThread_st (K := abi) t1 _).symm).2 _ hj (hwr _ _ _ hcall))
        · intro u hu
          obtain rfl := hget hu
          refine ⟨.inl hj, fun hA => ?_⟩
          by_cases hA0 : Ab t1.st
          · exact List.mem_append_left _ (hab hA0)
          have hu2 := hget hu'
          subst hu2
          obtain ⟨fd', buf', n', he, hrf⟩ := hF.ab.abSys hA0 hat _ hcall _ hsu hA
          have hrr := (hrf _ (retThread_st (K := abi) t1 _).symm).1
          rcases hr' with rfl | rfl <;> exact absurd hrr (by decide +kernel)
        · intro u hu
          obtain rfl := hget hu
          exact ⟨.inl hj, fun _ => List.mem_append_right _ (List.mem_singleton_self _)⟩
      · have hw0 : t.2.wr 1 = 0 := hwb.resolve_right fun ⟨_, fd, buf, n, hc, _⟩ => by
          rw [hcall] at hc; cases hc; exact hwc ⟨fd, buf, n, rfl⟩
        have hks := ret_ks ht1 hcall (fun fd buf n e => hwc ⟨fd, buf, n, e⟩) hnx hng hsy
        intro u hu
        rw [hu'] at hu
        cases hu
        refine ⟨.inl (by rw [hks]; exact hw0), fun hA => ?_⟩
        by_cases hA0 : Ab t1.st
        · exact List.mem_append_left _ (hab hA0)
        obtain ⟨fd, buf, n, he, -⟩ := hF.ab.abSys hA0 hat _ hcall _ hsu hA
        exact (hwc ⟨fd, buf, n, he⟩).elim
    · -- `exit`: the thread kept, its slot exited
      intro u hu
      rw [ht1] at hu; cases hu
      exact ⟨.inl wr_set_exited, hold _ rfl⟩
    · intro u hu
      rw [ht1] at hu; cases hu
      exact ⟨hwb, hold _ rfl⟩
    · intro u hu
      rw [ht1] at hu; cases hu
      exact ⟨hwb, hold _ rfl⟩
  · exact (no_spawn hn ⟨hK.2.1, hK.2.2⟩ hsp).elim
  · exfalso
    obtain ⟨a, ha, t2, ht2, hpc⟩ := hk
    cases (show some t2 = some t1 from ht2.symm.trans ht1)
    have hn' := siteAt_eq_none_iff.mp hns
    subst hpc
    cases k
    · exact hn'.1 ha
    · exact hn'.2 ha

end Spike.Lib.HelloPostAb
