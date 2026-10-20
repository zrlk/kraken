/-
**Stage 3 liveness: proof rules on traces.**

- `LeadsTo P Q` (`P ↝ Q` on index predicates) with reflexivity,
  transitivity, monotonicity and case split.
- `leadsTo_wf1`: Lamport's WF1 rule for `WeakFairInstr`: if `P` is stable
  unless `Q`, thread `h` can take an instruction step while `P` holds, and
  each of its instruction steps from `P` establishes `Q`, then `P ↝ Q`.
- `leadsTo_rank`: well-founded ranking: if from `P` with rank `n` one
  reaches `Q` or `P` with a smaller rank, then `P ↝ Q`.
- `weakFairInstr_of_promiseFree`: on a trace with no promise step,
  `WeakFair` gives `WeakFairInstr`.
- `memFair_catchup`: the memory-fairness rule in `LeadsTo`-free form.

ISA-neutral, program-independent.
-/
import Kraken.Promising.LiveTrace

namespace Kraken.Promising.Live

variable {I : ISA}

/-! ## Leads-to -/

/-- **`P` leads to `Q`**: whenever `P` holds at index `i`, `Q` holds at some
index `j ≥ i`. -/
def LeadsTo (P Q : Nat → Prop) : Prop := ∀ i, P i → ∃ j, i ≤ j ∧ Q j

theorem LeadsTo.refl (P : Nat → Prop) : LeadsTo P P := fun i h => ⟨i, Nat.le_refl i, h⟩

theorem LeadsTo.mono {P P' Q Q' : Nat → Prop} (h : LeadsTo P Q) (hP : ∀ i, P' i → P i)
    (hQ : ∀ i, Q i → Q' i) : LeadsTo P' Q' := fun i hi =>
  let ⟨j, hj, hq⟩ := h i (hP i hi); ⟨j, hj, hQ j hq⟩

theorem LeadsTo.trans {P Q R : Nat → Prop} (h₁ : LeadsTo P Q) (h₂ : LeadsTo Q R) : LeadsTo P R :=
  fun i hi =>
    let ⟨j, hj, hq⟩ := h₁ i hi
    let ⟨k, hk, hr⟩ := h₂ j hq
    ⟨k, Nat.le_trans hj hk, hr⟩

theorem LeadsTo.or {P P' Q : Nat → Prop} (h : LeadsTo P Q) (h' : LeadsTo P' Q) :
    LeadsTo (fun i => P i ∨ P' i) Q := fun i hi => hi.elim (h i) (h' i)

/-- An immediate step: `P` at `i` gives `Q` at `i` or `i + 1`. -/
theorem LeadsTo.of_next {P Q : Nat → Prop} (h : ∀ i, P i → Q i ∨ Q (i + 1)) : LeadsTo P Q :=
  fun i hi => (h i hi).elim (fun hq => ⟨i, Nat.le_refl i, hq⟩) (fun hq => ⟨i + 1, Nat.le_succ i, hq⟩)

/-- **Ranking**: if `P` with rank `n` leads to `Q` or to `P` with a rank
below `n`, then `P` leads to `Q`. -/
theorem leadsTo_rank {P Q : Nat → Prop} (μ : Nat → Nat)
    (h : ∀ n, LeadsTo (fun i => P i ∧ μ i = n) (fun i => Q i ∨ (P i ∧ μ i < n))) : LeadsTo P Q := by
  suffices ∀ n, LeadsTo (fun i => P i ∧ μ i = n) Q from fun i hi => this (μ i) i ⟨hi, rfl⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hi
    obtain ⟨j, hij, hj | ⟨hp, hlt⟩⟩ := h n i hi
    · exact ⟨j, hij, hj⟩
    · obtain ⟨k, hjk, hk⟩ := ih (μ j) (by omega) j ⟨hp, rfl⟩
      exact ⟨k, Nat.le_trans hij hjk, hk⟩

/-! ## Weak fairness: WF1 -/

/-- **WF1** for `WeakFairInstr`: if `P` is stable unless `Q`, thread `h` can
take an instruction step at every configuration satisfying `P`, and every
instruction step of `h` from `P` establishes `Q`, then `P ↝ Q`. -/
theorem leadsTo_wf1 {A : Arch} {fuel : Nat} {cfg : Nat → Config I} (hfair : WeakFairInstr A fuel cfg)
    (h : Nat) {P Q : Nat → Prop}
    (hstay : ∀ i, P i → Q (i + 1) ∨ P (i + 1))
    (hen : ∀ i, P i → InstrEnabled A fuel h (cfg i))
    (hgo : ∀ i, P i → InstrScheduledAt A fuel cfg h i → Q (i + 1)) : LeadsTo P Q := by
  intro i hi
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ j, i ≤ j → ¬ Q j := fun j hj hq => hno ⟨j, hj, hq⟩
  have hall : ∀ k, P (i + k) := by
    intro k
    induction k with
    | zero => exact hi
    | succ k ih =>
      rcases hstay _ ih with hq | hp
      · exact absurd hq (hno' _ (by omega))
      · exact hp
  have hP : ∀ j, i ≤ j → P j := fun j hj => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj; exact hall k
  obtain ⟨j, hij, hs⟩ := hfair h ⟨i, fun j hj => hen j (hP j hj)⟩ i
  exact hno' (j + 1) (by omega) (hgo j (hP j hij) hs)

/-! ## Promise-free traces -/

/-- On a trace with no promise step, a step of a thread is an instruction
step. -/
theorem instrScheduledAt_of_promiseFree {A : Arch} {fuel : Nat} {cfg : Nat → Config I}
    (hpf : PromiseFree A cfg) {tid i : Nat} (h : ScheduledAt A fuel cfg tid i) :
    InstrScheduledAt A fuel cfg tid i :=
  ⟨h.1, h.2.resolve_right (hpf i tid)⟩

/-- **On a promise-free trace, weak fairness is weak fairness for
instruction steps.** -/
theorem weakFairInstr_of_promiseFree {A : Arch} {fuel : Nat} {cfg : Nat → Config I}
    (hpf : PromiseFree A cfg) (hf : WeakFair A fuel cfg) : WeakFairInstr A fuel cfg := by
  rintro tid ⟨n, hn⟩ m
  obtain ⟨i, hi, hs⟩ := hf tid ⟨n, fun i hi => let ⟨c', h1, h2⟩ := hn i hi; ⟨c', h1, .inl h2⟩⟩ m
  exact ⟨i, hi, instrScheduledAt_of_promiseFree hpf hs⟩

/-! ## Memory fairness -/

/-- **Catch-up**: under `MemFair`, a thread that reads `l` infinitely often
eventually has the message at `ts` (to `l`, in memory at `i`) in its
coherence view. -/
theorem memFair_catchup {A : Arch} {cfg : Nat → Config I} (hmf : MemFair A cfg) {tid : Nat} {l : Loc}
    (hinf : InfOften (fun i => ∃ ts, ReadsAt A cfg tid l ts i)) {i ts : Nat} {w : Msg}
    (hw : (cfg i).mem.get? ts = some w) (hl : w.loc = l) :
    ∃ j, i ≤ j ∧ ∃ t, (cfg j).threads[tid]? = some t ∧ ts ≤ t.views.getCoh l :=
  hmf tid l hinf i ts w hw hl

/-- **A reader that never catches up** (the common end of the spin
and ticket liveness proofs, `stuck_false`/`holder_false`): under `MemFair`, a
thread present at `n` that reads `l` infinitely often has, at some `j ≥ n`, a
coherence view of `l` at or past the last write of `l` at `n`; so if that is
impossible, `False`. -/
theorem memFair_lastWrite_false {A : Arch} {cfg : Nat → Config I} (hmf : MemFair A cfg) {tid : Nat} {l : Loc}
    (hinf : InfOften (fun i => ∃ ts, ReadsAt A cfg tid l ts i)) {n : Nat} {t0 : Thread I}
    (ht0 : (cfg n).threads[tid]? = some t0)
    (hat : ∀ j, n ≤ j → ∀ t, (cfg j).threads[tid]? = some t → (cfg n).mem.lastWrite l ≤ t.views.getCoh l → False) :
    False := by
  by_cases h0w : (cfg n).mem.lastWrite l = 0
  · exact hat n (Nat.le_refl _) t0 ht0 (by rw [h0w]; exact Nat.zero_le _)
  obtain ⟨w, hw, hl⟩ := Memory.get?_lastWriteBelow _ _ _ h0w
  obtain ⟨j, hj, t', ht', hc⟩ := memFair_catchup hmf hinf hw hl
  exact hat j hj t' ht' hc

end Kraken.Promising.Live

