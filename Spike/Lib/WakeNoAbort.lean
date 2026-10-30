/-
**wake.w after the spawn takes no abort step** (AArch64): `WakeObligations.post_abort` is vacuous. An `abort k` event
comes only from a system call `exit_group` (`sysStep_abort`) of a thread at
the abort site of kind `k` (`step_abort`). The worker makes no `exit_group`
call (`WCompat.sysOk`, `worker_noAbort`); main, while its source is live
(`WakeM0.LiveK`), is at no abort site of any kind (`hoff0`, the widened
`MSide.off`).

- `sysStep_abort`: a kernel system-call step emitting `abort k` is an
  `exit_group` of a thread at a system call.
- `step_abort`: an abort step of the two-slot machine is an `exit_group` at
  the abort site of its kind.
- `worker_noAbort`: from `Post`, thread 1 takes no abort step.
- `post_noAbort`, `post_abort_of`: from `Post`, no thread takes an abort
  step, so `post_abort` holds.
-/
import Spike.Lib.WakeW1Compat
import Spike.Lib.WakePostAb
import Spike.Lib.WakePreTi

namespace Spike.Lib.WakeNoAbort

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeA64 Spike.Lib.WakeW1

/-- **A system-call step emitting `abort k` is an `exit_group`** of a thread
at a system call. -/
theorem sysStep_abort {I : ISA} {K : Abi I} {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick}
    {es : List Ev} {k : AbortKind} (h : sysStep K A tid c p = some (es, c')) (hk : Ev.abort k ∈ es) :
    ∃ t v, c.1.threads[tid]? = some t ∧ K.atSys t.st = true ∧ callOf K t = some (.exitGroup v) := by
  unfold sysStep at h
  split at h
  · cases h
  next t ht =>
    split at h
    · cases h
    next hr =>
      have hs : K.atSys t.st = true := by
        simp only [ready] at hr; cases hA : K.atSys t.st <;> simp_all
      rcases hcall : callOf K t with _ | call
      · simp only [hcall] at h; cases h
      cases call <;> (try exact ⟨t, _, ht, hs, hcall⟩) <;> exfalso <;> cases p <;>
        simp only [hcall] at h <;> (try cases h) <;> (repeat' split at h) <;>
        simp_all [back, Option.map_eq_some_iff]
      all_goals first
        | (obtain ⟨_, _, -, he, -⟩ := h; subst he; simp at hk)
        | (obtain ⟨he, -⟩ := h; subst he; simp at hk)

/-- **An abort step is an `exit_group` at the abort site of its kind.** -/
theorem step_abort {μ : Marks} {tid : Nat} {t t' : Cfg} {es : List Ev} {k : AbortKind}
    (hs : (machine (kernel 2)).Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    ∃ th v, t.1.threads[tid]? = some th ∧ abi.atSys th.st = true ∧ callOf abi th = some (.exitGroup v) ∧
      ∃ a, μ.abortAt k = some a ∧ pcOf th.st = a := by
  obtain ⟨a, ha, th', hth', hpc⟩ := hs.abort_at hk
  match hs, hk with
  | .instr .., hk => simp at hk
  | .spawn .., hk => simp at hk
  | .xfer .., hk => simp at hk
  | .sys _ hsys _ _ _, hk =>
    obtain ⟨p, hp, -⟩ := hsys
    obtain ⟨th, v, hth, has, hc⟩ := sysStep_abort hp hk
    obtain rfl : th = th' := Option.some.inj (hth.symm.trans hth')
    exact ⟨th, v, hth, has, hc, a, ha, hpc⟩

variable {Q : WakeRel} {Λ : Scc.Sem.Layout}

/-- **No abort step from `Post`**: main, while its source is off its return
(`hlive`), is at no abort site (`hoff0`); the worker makes no `exit_group`
call (`hsys1`). -/
theorem post_noAbort {μ : Marks} (hlive : WakeM0.LiveK Q)
    (hoff0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.term ≠ WakeMLive.wlRet →
      ∀ k a, μ.abortAt k = some a → pcOf t0.st ≠ a)
    (hsys1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → abi.atSys t1.st = true → ∀ call,
      callOf abi t1 = some call → ∀ v, call ≠ .exitGroup v)
    {t t' : Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev} {k : AbortKind} (hP : Q.Post Λ t s)
    (hs : (machine (kernel 2)).Step μ tid t es t') (hk : Ev.abort k ∈ es) : False := by
  obtain ⟨th, v, hth, has, hc, a, ha, hpc⟩ := step_abort hs hk
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, -, h0, h1, -⟩, hK⟩ := hP
  have hl : s0.term ≠ WakeMLive.wlRet := hlive w t s hK hs.runs.2.1 s0 (by rw [hS]; rfl)
  rw [hT] at hth
  rcases tid with _ | _ | n
  · cases (show some t0 = some th from hth)
    simp only [WakeRel.PTw] at h0
    exact hoff0 _ _ _ _ _ h0.2 hl k a ha hpc
  · cases (show some t1 = some th from hth)
    simp only [WakeRel.PTw] at h1
    exact hsys1 _ _ _ _ _ h1 has _ hc v rfl
  · exact absurd hth (by simp)

/-- **The worker makes no `exit_group` call** (`WCompat.sysOk` at
`WCompat.pt1`): `post_noAbort`'s `hsys1`. -/
theorem sys1_of {D : WSide Q.ι} {μ' : Marks} {arch : WeakMem.Arch} (hC : WCompat Q D μ' Λ arch) :
    ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → abi.atSys t1.st = true → ∀ call,
      callOf abi t1 = some call → ∀ v, call ≠ .exitGroup v := by
  intro w tm sm t1 s1 h ha call hc v
  rw [hC.pt1] at h
  rcases hC.sysOk w _ _ call h.1 ha hc with rfl | ⟨-, hv⟩
  · exact nofun
  · exact hv v

/-- **`WakeObligations.post_abort`**, vacuously (`post_noAbort`). -/
theorem post_abort_of {arch : WeakMem.Arch} {B : Budget} {μ : Marks} {Ab Ac : State → Prop} (hlive : WakeM0.LiveK Q)
    (hoff0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.term ≠ WakeMLive.wlRet →
      ∀ k a, μ.abortAt k = some a → pcOf t0.st ≠ a)
    (hsys1 : ∀ w tm sm t1 s1, Q.PT1 w tm sm t1 s1 → abi.atSys t1.st = true → ∀ call,
      callOf abi t1 = some call → ∀ v, call ≠ .exitGroup v) :
    ∀ tr t s tid es t' k, (wakeS arch).Reach (obs tr) s → Q.Post Λ t s → WakePreTi.TiPre Ab Ac t tr →
      (machine (kernel 2)).Step μ tid t es t' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧
        AbortJustified B (wakeS arch) tr s i k :=
  fun _ _ _ _ _ _ _ _ hP _ hs hk => (post_noAbort hlive hoff0 hsys1 hP hs hk).elim

/-- info: 'Spike.Lib.WakeNoAbort.post_abort_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_abort_of

end Spike.Lib.WakeNoAbort
