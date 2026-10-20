/-
**Stage 3: program-independent trace lemmas for
promise-free liveness proofs.** ISA-neutral. `evconst`, `step_or`, `adv`
and `wt_self` generalise `LiveTicketPF.{evconst, step_or, adv, wt_H}` (which
carry that file's `ValidLayout (layout tkWorker)` section instance); those are
proved from these, and `pigeon` here is the original of
`LiveTicketInv.pigeon` and `LiveX64TicketInv.pigeon`.

- `evconst`: a bounded monotone sequence is eventually constant;
  `pigeon`: an injection of `[0, a)` into `[0, n)` has `a ≤ n`;
  `stable_of_mono`: a monotone family of subsets of `[0, M)` is eventually
  constant.
- `step_or`: on a promise-free stuttering trace every step stutters or is an
  instruction step of some thread; `get_persist`/`get_frame`: a thread stays
  in the configuration, and only its own steps change it.
- `adv`: under `WeakFairInstr`, a thread that is instruction-enabled from `n`
  on takes its next step: from any `j ≥ n` it is unchanged until some `k`
  where it takes an instruction step.
-/
import Kraken.Promising.LiveSpinSwpStep
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.SpinCommon

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.SpinStep

/-! ## Monotone sequences -/

/-- A bounded monotone sequence is eventually constant. -/
theorem evconst (M : Nat → Nat) (hmono : ∀ i j, i ≤ j → M i ≤ M j) (K i : Nat) (hb : ∀ j, i ≤ j → M j ≤ K) :
    ∃ n, i ≤ n ∧ ∀ j, n ≤ j → M j = M n := by
  suffices ∀ d i, K - M i ≤ d → (∀ j, i ≤ j → M j ≤ K) → ∃ n, i ≤ n ∧ ∀ j, n ≤ j → M j = M n from
    this _ i (Nat.le_refl _) hb
  intro d
  induction d with
  | zero => intro i hd hb; exact ⟨i, Nat.le_refl _, fun j hj => by
      have := hb j hj; have := hmono i j hj; have := hb i (Nat.le_refl _); omega⟩
  | succ d ih =>
    intro i hd hb
    by_cases hc : ∃ j, i ≤ j ∧ M j ≠ M i
    · obtain ⟨j, hj, hne⟩ := hc
      have := hmono i j hj; have := hb j hj
      obtain ⟨n, hn, h⟩ := ih j (by omega) (fun k hk => hb k (Nat.le_trans hj hk))
      exact ⟨n, Nat.le_trans hj hn, h⟩
    · exact ⟨i, Nat.le_refl _, fun j hj => Classical.byContradiction fun hne => hc ⟨j, hj, hne⟩⟩

theorem countP_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ L : List α, (∀ x ∈ L, p x = true → q x = true) → L.countP p ≤ L.countP q
  | [], _ => Nat.le_refl _
  | x :: L, h => by
    have ih := countP_le_of_imp p q L fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.countP_cons]
    have := h x (List.mem_cons_self ..)
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem countP_lt_of_imp {α : Type} (p q : α → Bool) :
    ∀ L : List α, (∀ x ∈ L, p x = true → q x = true) → (∃ x ∈ L, q x = true ∧ p x = false) →
      L.countP p < L.countP q
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | x :: L, h, ⟨y, hy, hqy, hpy⟩ => by
    have hle := countP_le_of_imp p q L fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [List.countP_cons]
    have := h x (List.mem_cons_self ..)
    rcases List.mem_cons.mp hy with rfl | hy
    · simp only [hqy, hpy]; simp; omega
    · have ih := countP_lt_of_imp p q L (fun z hz => h z (List.mem_cons_of_mem _ hz)) ⟨y, hy, hqy, hpy⟩
      cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- Pigeonhole: an injection of `[0, a)` into `[0, n)` has `a ≤ n`
(the instance-free original of `LiveTicketInv.pigeon` and
`LiveX64TicketInv.pigeon`). -/
theorem pigeon : ∀ (n a : Nat) (f : Nat → Nat), (∀ k < a, f k < n) →
    (∀ i j, i < a → j < a → f i = f j → i = j) → a ≤ n := by
  intro n
  induction n with
  | zero =>
    intro a f hf _
    cases a with
    | zero => exact Nat.le_refl _
    | succ a => exact absurd (hf 0 (by omega)) (by omega)
  | succ n ih =>
    intro a f hf hi
    cases a with
    | zero => omega
    | succ a =>
      have hne : ∀ k < a, f k ≠ f a := fun k hk e => by have := hi k a (by omega) (by omega) e; omega
      have := ih a (fun k => if f k < f a then f k else f k - 1) (fun k hk => by
        have h1 := hf k (by omega); have h2 := hf a (by omega); have := hne k hk
        split <;> omega) (fun i j hi' hj' e => by
        have := hne i hi'; have := hne j hj'
        apply hi i j (by omega) (by omega)
        split at e <;> split at e <;> omega)
      omega

/-- **A monotone family of subsets of `[0, M)` is eventually constant.** -/
theorem stable_of_mono (P : Nat → Nat → Prop) (M : Nat) (hb : ∀ k j, P k j → k < M)
    (hmono : ∀ k i j, i ≤ j → P k i → P k j) (i : Nat) :
    ∃ n, i ≤ n ∧ ∀ j, n ≤ j → ∀ k, P k j → P k n := by
  classical
  let C : Nat → Nat := fun j => (List.range M).countP fun k => decide (P k j)
  have hC : ∀ i j, i ≤ j → C i ≤ C j := fun i j hij =>
    countP_le_of_imp _ _ _ fun k _ hk => by simp only [decide_eq_true_eq] at hk ⊢; exact hmono k i j hij hk
  obtain ⟨n, hn, hc⟩ := evconst C hC M i fun j _ => Nat.le_trans List.countP_le_length (by simp)
  refine ⟨n, hn, fun j hj k hk => Classical.byContradiction fun hnk => ?_⟩
  have := countP_lt_of_imp (fun k => decide (P k n)) (fun k => decide (P k j)) (List.range M)
    (fun k _ h => by simp only [decide_eq_true_eq] at h ⊢; exact hmono k n j hj h)
    ⟨k, List.mem_range.mpr (hb k j hk), by simpa using hk, by simpa using hnk⟩
  have := hc j hj
  simp only [C] at this
  omega

/-! ## Promise-free traces -/

section Trace

variable {I : ISA} [I.LawfulState] {A : Arch} {fuel : Nat} {tr : TraceS A fuel I}
  (hpf : PromiseFree A tr.cfg)

include hpf

/-- On a promise-free trace every step stutters or is an instruction step. -/
theorem step_or (i : Nat) : tr.cfg (i + 1) = tr.cfg i ∨
    ∃ tid, InstrBy A tid (tr.cfg i) (tr.cfg (i + 1)) ∧ tr.cfg (i + 1) ∈ (succs A (tr.cfg i) fuel).1 := by
  rcases tr.step i with hm | ⟨-, he⟩
  · obtain ⟨tid, -, hi | hp⟩ := stepBy_of_mem_succs hm
    · exact .inr ⟨tid, hi, hm⟩
    · exact absurd hp (hpf i tid)
  · exact .inl he

/-- A thread stays in the configuration. -/
theorem get_persist {U j : Nat} {t : Thread I} (ht : (tr.cfg j).threads[U]? = some t) :
    ∀ k, j ≤ k → ∃ t', (tr.cfg k).threads[U]? = some t' := by
  intro k hk
  induction hk with
  | refl => exact ⟨t, ht⟩
  | @step k _ ih =>
    obtain ⟨t', h'⟩ := ih
    rcases step_or hpf k with he | ⟨tid, ⟨u, -, oc, hu, -, -, he⟩, -⟩
    · rw [he]; exact ⟨t', h'⟩
    · rw [he]
      by_cases e : U = tid
      · subst e; exact ⟨_, wt_tid hu⟩
      · exact ⟨t', by rw [wt_ne hu e]; exact h'⟩

/-- **The next step of a thread that is enabled from `n` on** (weak
fairness): from index `j ≥ n`, thread `U` is unchanged until some index `k`
where it takes an instruction step. -/
theorem adv (hwf : WeakFairInstr A fuel tr.cfg) {U n : Nat}
    (hen : ∀ j, n ≤ j → InstrEnabled A fuel U (tr.cfg j)) (j : Nat) (_hj : n ≤ j) {t : Thread I}
    (ht : (tr.cfg j).threads[U]? = some t) :
    ∃ k, j ≤ k ∧ (tr.cfg k).threads[U]? = some t ∧ ∃ outs oc, stepOne A t U (tr.cfg k).mem = some outs ∧
      .ok oc ∈ outs ∧ tr.cfg (k + 1) = (tr.cfg k).withThread U oc.thread oc.mem := by
  obtain ⟨k0, hk0, hs0⟩ := hwf U ⟨n, hen⟩ j
  suffices ∀ d j, k0 - j = d → j ≤ k0 → ∃ k, j ≤ k ∧ (tr.cfg k).threads[U]? = (tr.cfg j).threads[U]? ∧
      InstrScheduledAt A fuel tr.cfg U k by
    obtain ⟨k, hk, heq, -, t', outs, oc, ht', hs', ho, he⟩ := this _ j rfl hk0
    rw [heq, ht] at ht'; cases ht'
    exact ⟨k, hk, heq.trans ht, outs, oc, hs', ho, he⟩
  intro d
  induction d with
  | zero => intro j hd hj; obtain rfl : j = k0 := by omega
            exact ⟨j, Nat.le_refl _, rfl, hs0⟩
  | succ d ih =>
    intro j hd hj
    by_cases hsj : InstrScheduledAt A fuel tr.cfg U j
    · exact ⟨j, Nat.le_refl _, rfl, hsj⟩
    have heq : (tr.cfg (j + 1)).threads[U]? = (tr.cfg j).threads[U]? := by
      rcases step_or hpf j with he | ⟨tid, hi, hm⟩
      · rw [he]
      by_cases e : tid = U
      · subst e; exact absurd ⟨hm, hi⟩ hsj
      · obtain ⟨_, _, _, ht', -, -, he⟩ := hi; rw [he, wt_ne ht' (Ne.symm e)]
    obtain ⟨k, hk, h1, h2⟩ := ih (j + 1) (by omega) (by omega)
    exact ⟨k, by omega, h1.trans heq, h2⟩

/-- The number of threads is constant on a promise-free trace (the
instance-free original of the `size_eq` copies in
`LiveSpin{Cas,Swp,X64Cmpx,X64Xchg}PF`). -/
theorem size_eq : ∀ j, (tr.cfg j).threads.size = (tr.cfg 0).threads.size
  | 0 => rfl
  | j + 1 => by
    rcases step_or hpf j with he | ⟨tid, ⟨u, -, oc, -, -, -, he⟩, -⟩
    · rw [he]; exact size_eq j
    · rw [he]; simp only [Config.withThread]; simp [size_eq j]

/-- **An invariant along a promise-free trace** (the common part of
the ticket and spin locks' `trace_inv`): it holds at index `0` and every
instruction step keeps it. -/
theorem trace_inv_of (P : Config I → Prop) (h0 : P (tr.cfg 0))
    (hstep : ∀ i tid, P (tr.cfg i) → InstrBy A tid (tr.cfg i) (tr.cfg (i + 1)) →
      tr.cfg (i + 1) ∈ (succs A (tr.cfg i) fuel).1 → P (tr.cfg (i + 1))) :
    ∀ i, P (tr.cfg i)
  | 0 => h0
  | i + 1 => by
    rcases step_or hpf i with he | ⟨tid, hi, hm⟩
    · rw [he]; exact trace_inv_of P h0 hstep i
    · exact hstep i tid (trace_inv_of P h0 hstep i) hi hm

omit hpf [I.LawfulState] in
theorem wt_self {k U : Nat} {t : Thread I} {oc : Outcome I} (ht : (tr.cfg k).threads[U]? = some t)
    (he : tr.cfg (k + 1) = (tr.cfg k).withThread U oc.thread oc.mem) :
    (tr.cfg (k + 1)).threads[U]? = some oc.thread := by
  rw [he]; exact wt_tid ht

end Trace

end Kraken.Promising.Live.SpinCommon
