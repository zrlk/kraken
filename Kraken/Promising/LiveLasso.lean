/-
**Stage 3: the two-thread spin lasso, generic in the
ISA and the architecture.** ISA-neutral.

`LiveTicketCex.lean` (AArch64, `TicketCexG.LassoChecks`, `lassoG`,
`lassoG_*`, `lasso_not_live`) and `LiveX64TicketCex.lean` (x64,
`LassoChecksX`, `lassoX`, `lassoX_*`, `lassoX_not_live`) refute
weak-fairness-only liveness with the same lasso: a replayed prefix of 16
steps from `c0` to `cS`, then a loop of 3 steps of thread 1 from `cS` back to
`cS`, forever; on the loop thread 0 is halted and thread 1 spins. Their
lasso lemmas are instances of the ones here (same names and statements
there).

- `Spec`: the data — architecture, kernel-evaluable `exec`/`deps` with their
  equations, the pc of a state, the spin and pre-critical-section addresses,
  and the two traces with their shapes.
- `Spec.Waiting`/`Spec.Done`/`Spec.loopOk`: as in both files.
- `Spec.Checks`: the kernel checks (the files' `LassoChecks`/`LassoChecksX`,
  field by field).
- `Spec.lasso`, `Spec.lasso_step`, …, `Spec.lasso_not_live`.
-/
import Kraken.Promising.LiveReach

namespace Kraken.Promising.Live.Lasso

open Kraken.Promising Kraken.Promising.Live

/-- **The data of a two-thread spin lasso**: a 16-step prefix and a 3-step
loop of thread 1, with kernel-evaluable `exec`/`deps`. -/
structure Spec (I : ISA) where
  A : Arch
  ex : I.State → Option (EvTree I.State)
  dp : I.State → InstrDeps I.RegId
  ex_eq : ex = I.exec
  dp_eq : dp = I.deps
  /-- The pc of a state. -/
  pcOf : I.State → Int64
  /-- The spin loop's addresses. -/
  spinPcs : List Int64
  /-- The addresses before the critical section (the spin loop's among them). -/
  prePcs : List Int64
  spin_pre : ∀ p ∈ spinPcs, p ∈ prePcs
  prefixTr : List (Nat × List Nat)
  loopTr : List (Nat × List Nat)
  prefix_len : prefixTr.length = 16
  loop_len : loopTr.length = 3
  loop_tid : ∀ (r : Nat) (h : r < loopTr.length), loopTr[r].1 = 1

namespace Spec

variable {I : ISA} (S : Spec I)

/-- Thread `tid` spins. -/
def Waiting (tid : Nat) (c : Config I) : Prop := ∃ t, c.threads[tid]? = some t ∧ S.pcOf t.st ∈ S.spinPcs

/-- Thread `tid` is past the spin loop. -/
def Done (tid : Nat) (c : Config I) : Prop := ∃ t, c.threads[tid]? = some t ∧ S.pcOf t.st ∉ S.prePcs

/-- Thread 0 halted, thread 1 spinning, two threads, no promises. -/
noncomputable def loopOk (c : Config I) : Bool :=
  c.threads.size == 2 &&
    (match c.threads[0]? with | some t => (S.ex t.st).isNone | none => false) &&
    (match c.threads[1]? with | some t => S.spinPcs.contains (S.pcOf t.st) | none => false) &&
    c.threads.all (·.prom.isEmpty)

/-- The kernel checks the lasso needs: the prefix replays from `c0` to `cS`,
one loop returns to `cS`, the loop's configurations satisfy `loopOk`, and the
prefix makes no promise. -/
structure Checks (c0 cS : Config I) : Prop where
  pre : reachRun I.exec I.deps S.A c0 S.prefixTr = some cS
  loop : reachRun I.exec I.deps S.A cS S.loopTr = some cS
  ok : (List.range 3).all (fun r => S.loopOk (liveRunAt S.ex S.dp S.A cS S.loopTr r)) = true
  prom : (List.range 17).all
    (fun k => (liveRunAt S.ex S.dp S.A c0 S.prefixTr k).threads.all (·.prom.isEmpty)) = true

variable {S} {c0 cS : Config I}

/-- The lasso from `c0`: the prefix, then the loop forever. -/
@[irreducible] noncomputable def lasso (S : Spec I) (c0 cS : Config I) (i : Nat) : Config I :=
  if i < 16 then liveRunAt I.exec I.deps S.A c0 S.prefixTr i
  else liveRunAt I.exec I.deps S.A cS S.loopTr ((i - 16) % 3)

theorem lasso_step (hL : S.Checks c0 cS) (i : Nat) : ∃ tid sel,
    reachStep I.exec I.deps S.A (S.lasso c0 cS i) tid sel = some (S.lasso c0 cS (i + 1)) ∧
      (16 ≤ i → tid = 1) := by
  by_cases hi : i < 15
  · have hlt : i < S.prefixTr.length := by rw [S.prefix_len]; omega
    have := liveRunAt_step I.exec I.deps S.A hL.pre hlt
    refine ⟨S.prefixTr[i].1, S.prefixTr[i].2, ?_, fun h => absurd h (by omega)⟩
    simp only [lasso, (show i < 16 by omega), ↓reduceIte, (show i + 1 < 16 by omega)]
    exact this
  by_cases h15 : i = 15
  · subst h15
    have hlt : 15 < S.prefixTr.length := by rw [S.prefix_len]; omega
    have := liveRunAt_step I.exec I.deps S.A hL.pre hlt
    rw [show (15 + 1 : Nat) = S.prefixTr.length from S.prefix_len.symm, liveRunAt_length _ _ _ hL.pre] at this
    refine ⟨S.prefixTr[15].1, S.prefixTr[15].2, ?_, fun h => absurd h (by omega)⟩
    simp only [lasso, (show 15 < 16 by omega), ↓reduceIte, (show ¬ 15 + 1 < 16 by omega),
      Nat.sub_self, Nat.zero_mod, liveRunAt_zero]
    exact this
  · have hr : (i - 16) % 3 < S.loopTr.length := by rw [S.loop_len]; omega
    have hstep := liveRunAt_step I.exec I.deps S.A hL.loop hr
    have hcase : (i - 16) % 3 = 0 ∨ (i - 16) % 3 = 1 ∨ (i - 16) % 3 = 2 := by omega
    refine ⟨S.loopTr[(i - 16) % 3].1, S.loopTr[(i - 16) % 3].2, ?_, fun _ => S.loop_tid _ hr⟩
    simp only [lasso, (show ¬ i < 16 by omega), ↓reduceIte, (show ¬ i + 1 < 16 by omega)]
    rw [show i + 1 - 16 = (i - 16) + 1 by omega, Nat.add_mod]
    rcases hcase with h | h | h
    · simp only [h] at hstep ⊢; exact hstep
    · simp only [h] at hstep ⊢; exact hstep
    · simp only [h] at hstep ⊢
      rw [show (2 + 1 : Nat) = S.loopTr.length from S.loop_len.symm, liveRunAt_length _ _ _ hL.loop] at hstep
      simpa [liveRunAt_zero] using hstep

theorem lasso_loopOk (hL : S.Checks c0 cS) {i : Nat} (hi : 16 ≤ i) :
    (S.lasso c0 cS i).threads.size = 2 ∧ (∃ t, (S.lasso c0 cS i).threads[0]? = some t ∧ t.halted = true) ∧
      S.Waiting 1 (S.lasso c0 cS i) ∧ ¬ S.Done 1 (S.lasso c0 cS i) := by
  have hk := List.all_eq_true.mp hL.ok ((i - 16) % 3) (List.mem_range.mpr (Nat.mod_lt _ (by omega)))
  rw [S.ex_eq, S.dp_eq] at hk
  simp only [lasso, (show ¬ i < 16 by omega), ↓reduceIte]
  generalize liveRunAt I.exec I.deps S.A cS S.loopTr ((i - 16) % 3) = c at hk ⊢
  simp only [loopOk, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨⟨⟨hsz, h0⟩, h1⟩, -⟩ := hk
  refine ⟨hsz, ?_, ?_, ?_⟩
  · split at h0
    · rename_i t ht; rw [S.ex_eq] at h0; exact ⟨t, ht, h0⟩
    · cases h0
  · split at h1
    · rename_i t ht; exact ⟨t, ht, List.elem_iff.mp h1⟩
    · cases h1
  · rintro ⟨t, ht, hn⟩
    split at h1
    · rename_i t' ht'
      rw [ht] at ht'; cases ht'
      exact hn (S.spin_pre _ (List.elem_iff.mp h1))
    · cases h1

theorem lasso_prom (hL : S.Checks c0 cS) (i tid : Nat) (t : Thread I)
    (ht : (S.lasso c0 cS i).threads[tid]? = some t) : t.prom = [] := by
  have hall : (S.lasso c0 cS i).threads.all (·.prom.isEmpty) = true := by
    by_cases hi : i < 16
    · have hk := List.all_eq_true.mp hL.prom i (List.mem_range.mpr (by omega))
      rw [S.ex_eq, S.dp_eq] at hk
      simpa only [lasso, hi, ↓reduceIte] using hk
    · have hk := List.all_eq_true.mp hL.ok ((i - 16) % 3) (List.mem_range.mpr (Nat.mod_lt _ (by omega)))
      rw [S.ex_eq, S.dp_eq] at hk
      simp only [loopOk, Bool.and_eq_true] at hk
      simpa only [lasso, hi, ↓reduceIte] using hk.2
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  exact List.isEmpty_iff.mp ((Array.all_eq_true.mp hall) tid hlt)

theorem lasso_scheduled (hL : S.Checks c0 cS) {fuel i : Nat} (hi : 16 ≤ i) :
    InstrScheduledAt S.A fuel (S.lasso c0 cS) 1 i := by
  obtain ⟨tid, sel, hs, ht⟩ := lasso_step hL i
  obtain rfl := ht hi
  exact ⟨reachStep_sound S.A fuel hs, (reachStep_instrBy S.A hs).1⟩

theorem lasso_not_enabled (hL : S.Checks c0 cS) {fuel tid i : Nat} (hi : 16 ≤ i) (htid : tid ≠ 1) :
    ¬ Enabled S.A fuel tid (S.lasso c0 cS i) := by
  obtain ⟨hsz, ⟨t, ht, hh⟩, -, -⟩ := lasso_loopOk hL hi
  rcases Nat.lt_or_ge tid 2 with hlt | hge
  · obtain rfl : tid = 0 := by omega
    exact not_enabled_of_halted ht hh
  · exact not_enabled_of_none (Array.getElem?_eq_none (by omega))

/-- The lasso makes no promise step. -/
theorem lasso_promiseFree (hL : S.Checks c0 cS) : PromiseFree S.A (S.lasso c0 cS) := by
  intro i tid hp
  obtain ⟨t', ht', hne⟩ := PromiseBy.prom_ne hp
  exact hne (lasso_prom hL (i + 1) tid t' ht')

/-- The lasso is weakly fair. -/
theorem lasso_weakFair (hL : S.Checks c0 cS) (fuel : Nat) : WeakFair S.A fuel (S.lasso c0 cS) := by
  intro tid ⟨n, hn⟩ m
  by_cases htid : tid = 1
  · subst htid
    obtain ⟨h1, h2⟩ := lasso_scheduled hL (fuel := fuel) (i := m + 16) (by omega)
    exact ⟨m + 16, by omega, h1, .inl h2⟩
  · exact absurd (hn (n + 16) (by omega)) (lasso_not_enabled hL (by omega) htid)

/-- The lasso is weakly fair for instruction steps. -/
theorem lasso_weakFairInstr (hL : S.Checks c0 cS) (fuel : Nat) :
    WeakFairInstr S.A fuel (S.lasso c0 cS) := by
  intro tid ⟨n, hn⟩ m
  by_cases htid : tid = 1
  · subst htid; exact ⟨m + 16, by omega, lasso_scheduled hL (by omega)⟩
  · obtain ⟨c', h1, h2⟩ := hn (n + 16) (by omega)
    exact absurd ⟨c', h1, .inl h2⟩ (lasso_not_enabled hL (by omega) htid)

/-- The lasso as a trace. -/
noncomputable def lassoTrace (hL : S.Checks c0 cS) (fuel : Nat) : TraceS S.A fuel I :=
  ⟨S.lasso c0 cS, fun i => .inl (reachStep_sound S.A fuel (lasso_step hL i).choose_spec.choose_spec.1)⟩

/-- **The lasso refutes weak-fairness-only liveness from any `c0` passing
the kernel checks.** -/
theorem lasso_not_live (hL : S.Checks c0 cS) (fuel : Nat) :
    ¬ LiveFrom S.A fuel c0
      (fun cfg => WeakFair S.A fuel cfg ∧ WeakFairInstr S.A fuel cfg ∧ PromiseFree S.A cfg)
      S.Waiting S.Done := by
  intro hl
  obtain ⟨j, hj, hd⟩ := hl (lassoTrace hL fuel) (by simp [lassoTrace, lasso, liveRunAt_zero])
    ⟨lasso_weakFair hL fuel, lasso_weakFairInstr hL fuel, lasso_promiseFree hL⟩ 1 16
    (lasso_loopOk hL (Nat.le_refl _)).2.2.1
  exact (lasso_loopOk hL hj).2.2.2 hd

end Spec

end Kraken.Promising.Live.Lasso
