/-
**main's `exit_group` after the spawn** (`post_step0`).

- `localRun_run_source_wc`: `LocalRun.run_source` under WeakCore's hook
  (`UsesWc`) with the no-exit fact at the starting configuration only, in
  place of `HookOK` (which asks it at every reachable configuration): a
  local run of thread 0 on one frame with no promise, from a control off
  `ret`, is a source run with `main`'s exit at its end as its trace.
- `mterm_ret`: the only `ret` among main's terms is `wlRet`.
- `post_exit0`: main's `exit_group` off every abort site keeps `Post`, the
  source emitting the exit (`MainExit`), main's source at `wlRet` after it.
-/
import Spike.Lib.SrcRun
import Spike.Lib.WakeM0Sys

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Scc.Sem (SrcSem)
open Scc.Sem.SrcSem (mainExit srcObs cutAtExit)

section Src

variable {P : SrcSem.SrcParams} {p : Prog}

/-- **A local run of thread 0 under WeakCore's hook** (`LocalRun.run_source`
with `UsesWc` and the no-exit fact at the start in place of `HookOK`). -/
theorem localRun_run_source_wc (hP : Scc.Sem.SrcOutProto.UsesWc P p) {c c' : Ctl} (h : LocalRun p c c') :
    ∀ {s : TermRun.Cfg} {th : TermRun.TTh}, s.ths[0]? = some th → th.term = c.term → th.env = c.env →
      th.σs = [] → th.stack = [] → th.promises = [] → (∀ a, c.term ≠ .ret a) →
      (∀ x, Scc.Sem.Ev.exit x ∉ P.hooks.trace s) →
      (SrcSem.source P p).Run s
        (mainExit { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } })
        { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } := by
  have hset : ∀ (c : TermRun.Cfg) (ths : Array TermRun.TTh), P.hooks.trace { c with ths := ths } = P.hooks.trace c :=
    fun _ _ => by rw [hP]; rfl
  induction h with
  | refl c =>
    intro s th hi ht he _ hst _ hr _
    have : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    rw [this]
    have hs : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [hs, show ({ s with ths := s.ths } : TermRun.Cfg) = s from rfl,
      mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h))]
    exact .refl _
  | @step c c₁ c' hs hrun ih =>
    intro s th hi ht he hσ hst hp hr hxT
    have hm := hs.mem_threadSteps (k := P.k) (arch := P.arch) hi ht he hσ hst
    have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hi' : ({ s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } : TermRun.Cfg).ths[0]? =
        some { th with term := c₁.term, env := c₁.env } := by
      simp [hlt]
    have hex0 : mainExit s = [] := mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h))
    have hstep : ∀ es, es = mainExit { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } →
        (SrcSem.source P p).step 0 s es { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } := by
      intro es hes
      refine ⟨hex0, .inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), ?_⟩
      · simp [TermRun.noPromises, hlt, hp]
      · rw [hes, obs_exit hxT (hset _ _) hex0]
    by_cases hr₁ : ∀ a, c₁.term ≠ .ret a
    · have h2 := ih hi' rfl rfl hσ hst hp hr₁ (by rw [hset]; exact hxT)
      simp only [set!_set!] at h2
      have hnil : mainExit { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } = [] :=
        mainExit_of_not_ret hi' hr₁
      have h1 : (SrcSem.source P p).Run s ([] ++ [])
          { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } :=
        Scc.Sem.LRun.step ⟨0, hstep [] hnil.symm⟩ (.refl _)
      exact Scc.Sem.LRun.trans h1 h2
    · have hc' : c' = c₁ := by
        cases hrun with
        | refl => rfl
        | step hs' _ => exact absurd (localStep_not_ret hs') hr₁
      subst hc'
      have h1 : (SrcSem.source P p).Run s
          (mainExit { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } ++ [])
          { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } :=
        Scc.Sem.LRun.step ⟨0, hstep _ rfl⟩ (.refl _)
      rwa [List.append_nil] at h1

end Src

/-- info: 'Spike.Lib.WakeM0.localRun_run_source_wc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localRun_run_source_wc

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1
open Spike.Lib.WakeMLive (wlRet)

/-- The only `ret` among main's terms is `wlRet`. -/
theorem mterm_ret {e : Expr} (hm : MTerm e) {a : At} (h : e = .ret a) : e = wlRet := by
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | simp [mTail, wlBody, wlIf, wlPark] at h

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **main's `exit_group` off every abort site keeps `Post`**: the row's
`SysOk` (off `abortAt` by `WCompat0.abortAt0`) is `MainExit`, a local run of
main's source to a control whose return is the exit event; the source runs
there with that event as its trace (no exit before it: `KR`'s empty trace),
landing at `wlRet` (`PT0`'s exited disjunct); the kernel state records the
exit, so `KR`'s `MainLive` holds vacuously. -/
theorem post_exit0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hmi : M.Mi w t0.st (Ctl.of s0)) (hat : abi.atSys t0.st = true) {v : Nat}
    (hd : decode abi.nrs (abi.nr t0.st) (abi.arg t0.st) = some (.exitGroup v))
    (hoff : ¬ ∃ k a, μ.abortAt k = some a ∧ pcOf t0.st = a) :
    ∃ s', (wakeS arch).Run s [.exit (exitCode v)] s' ∧
      Q.Post Λ (t.1, { t.2 with exited := some (.exit (exitCode v)) }) s' := by
  obtain ⟨hok, -⟩ := sys_rows0 hC0 hmi hat hd
  obtain ⟨c', hr, -, hex⟩ := hok.2.2.2 v rfl (fun hab => hoff (hC0.abortAt0 w _ hab))
  have hpt0 := h.pt0M hPT0
  have hctl' := localRun_mCtl hr (h.mCtl hPT0)
  have hlive : s0.term ≠ wlRet := hC0.live0 w _ _ hmi
  have hnr : ∀ a, (Ctl.of s0).term ≠ .ret a := fun a hra => hlive (mterm_ret (h.mCtl hPT0).term hra)
  have hk := h.kr
  rw [hKR] at hk
  obtain ⟨hn, h0, h1, hh, -, htr⟩ := hk
  let s0' : TermRun.TTh := { s0 with term := c'.term, env := c'.env }
  have hrun := localRun_run_source_wc (P := srcPo 2 arch wakeSrc) rfl hr h.s0_get rfl rfl hpt0.2.2.1 hpt0.2.1
    hpt0.2.2.2.2.2.1 hnr (fun x hx => by
      change Ev.exit x ∈ SrcSem.traceOf s at hx
      rw [htr] at hx; cases hx)
  have hs' : ({ s with ths := s.ths.set! 0 s0' } : TermRun.Cfg).ths = #[s0', s1] := by
    show s.ths.set! 0 s0' = _
    rw [h.ths]; rfl
  have hi' : ({ s with ths := s.ths.set! 0 s0' } : TermRun.Cfg).ths[0]? = some s0' := by rw [hs']; rfl
  have hme := hex _ s0' hi' rfl rfl hpt0.2.1
  have hret : s0'.term = wlRet := by
    by_cases hr' : ∀ a, s0'.term ≠ .ret a
    · rw [mainExit_of_not_ret hi' hr'] at hme; cases hme
    · obtain ⟨a, ha⟩ : ∃ a, s0'.term = .ret a := Classical.byContradiction fun hn => hr' fun a ha => hn ⟨a, ha⟩
      exact mterm_ret hctl'.term ha
  rw [hme] at hrun
  refine ⟨_, hrun, w, ⟨t0, t1, s0', s1, ts, tp, sp, h.th, hs', ?_, ?_, ?_, oc, h.prot⟩, ?_⟩
  · exact core0_same h.core (by simp) rfl rfl h.core.bnd0 h.core.cov0 h.core.scov0 h.core.own0 h.core.own_disj
      (fun L v hm => h.core.own_cov 0 L v (by decide) hm) h.core.noProm0
  · simp only [WakeRel.PTw, ite_true]
    refine ⟨h.preC, ?_⟩
    rw [hPT0]
    exact ⟨.inr hret, hpt0.2.1, hpt0.2.2.1, hctl'.term, hctl'.env, hpt0.2.2.2.2.2.1, hpt0.2.2.2.2.2.2⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    exact h.pt1
  · rw [hKR]
    exact ⟨hn, h0, h1, hh, fun hx => (by cases hx), htr⟩

/-- info: 'Spike.Lib.WakeM0.post_exit0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_exit0

end Spike.Lib.WakeM0
