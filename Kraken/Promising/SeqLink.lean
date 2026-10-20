/-
Conservativity, continued: `seqRun` as a predicate, and its transfer to
promise-free runs of the machine.

`Kraken.Promising.Conservative` shows that a promise-free run of a one-thread
configuration is a sequential run (`SeqReach`, built from `seqRun`). This file
turns that into the shape a program logic consumes.

- `EvTree.AllSeq tid mem Q t`: every sequential run of `t` against `mem` ends
  in a state and memory satisfying `Q` (`allSeq_iff`). It is the
  weakest-precondition reading of `seqRun`.
- `SeqReach.sim`: a simulation of the sequential runs by any `Eventually`-style
  step relation carries an `Eventually` judgment along a sequential run.
- `reachablePF_sim`: the same along promise-free runs of the machine, from a
  configuration of one fresh thread (`Thread.init_seq`).

The ISA files (`SeqLinkAArch64`, `SeqLinkX64`) instantiate the simulation with
Kraken's own single-threaded judgment.
-/
import Kraken.Promising.Conservative
import Kraken.OmniSemantics

namespace Kraken.Promising

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## `seqRun` as a predicate -/

/-- Every sequential run of the tree against `mem` (`seqRun`) ends in a state
and memory satisfying `Q`. A fault has no run. -/
def EvTree.AllSeq {σ : Type} (tid : Nat) (mem : Memory) (Q : σ → Memory → Prop) : EvTree σ → Prop
  | .done s => Q s mem
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).AllSeq tid mem Q
  | .load _ _ l ret => (ret (mem.finalVal l)).AllSeq tid mem Q
  | .store _ xcl l v ret =>
    (ret true).AllSeq tid (mem.append { loc := l, val := v, tid }).1 Q ∧
      (xcl = true → (ret false).AllSeq tid mem Q)
  | .rmw _ _ l op ret =>
    match op (mem.finalVal l) with
    | some v => (ret (mem.finalVal l)).AllSeq tid (mem.append { loc := l, val := v, tid }).1 Q
    | none => (ret (mem.finalVal l)).AllSeq tid mem Q
  | .fence _ ret => (ret ()).AllSeq tid mem Q

theorem EvTree.allSeq_iff {σ : Type} (tid : Nat) (t : EvTree σ) :
    ∀ (mem : Memory) (Q : σ → Memory → Prop), t.AllSeq tid mem Q ↔ ∀ p ∈ seqRun tid mem t, Q p.1 p.2 := by
  induction t with
  | done s => intro mem Q; simp [AllSeq, seqRun]
  | fault m => intro mem Q; simp [AllSeq, seqRun]
  | choose n k ih =>
    intro mem Q
    simp only [AllSeq, seqRun, List.mem_flatMap, List.mem_finRange, true_and]
    constructor
    · rintro h p ⟨i, hp⟩; exact (ih i mem Q).mp (h i) p hp
    · intro h i; exact (ih i mem Q).mpr fun p hp => h p ⟨i, hp⟩
  | load k xcl l ret ih => intro mem Q; exact ih _ mem Q
  | store k xcl l v ret ih =>
    intro mem Q
    simp only [AllSeq, seqRun, List.mem_append]
    cases xcl with
    | false =>
      simp only [Bool.false_eq_true, false_implies, and_true, ite_false, List.not_mem_nil, or_false]
      exact ih true _ Q
    | true =>
      simp only [forall_const, ite_true]
      rw [ih true _ Q, ih false mem Q]
      constructor
      · rintro ⟨h1, h2⟩ p (hp | hp)
        · exact h1 p hp
        · exact h2 p hp
      · intro h; exact ⟨fun p hp => h p (.inl hp), fun p hp => h p (.inr hp)⟩
  | rmw k noRet l op ret ih =>
    intro mem Q
    simp only [AllSeq, seqRun]
    cases op (mem.finalVal l) <;> exact ih _ _ Q
  | fence k ret ih => intro mem Q; exact ih () mem Q

theorem EvTree.AllSeq.mono {σ : Type} {tid : Nat} {Q Q' : σ → Memory → Prop} (hQ : ∀ s m, Q s m → Q' s m)
    {t : EvTree σ} {mem : Memory} (h : t.AllSeq tid mem Q) : t.AllSeq tid mem Q' :=
  (t.allSeq_iff tid mem Q').mpr fun p hp => hQ _ _ ((t.allSeq_iff tid mem Q).mp h p hp)

theorem EvTree.allSeq_map {σ τ : Type} (tid : Nat) (f : σ → τ) (t : EvTree σ) :
    ∀ (mem : Memory) (Q : τ → Memory → Prop), (t.map f).AllSeq tid mem Q ↔ t.AllSeq tid mem (fun s m => Q (f s) m) := by
  induction t with
  | done s => intro mem Q; rfl
  | fault m => intro mem Q; rfl
  | choose n k ih => intro mem Q; exact forall_congr' fun i => ih i mem Q
  | load k xcl l ret ih => intro mem Q; exact ih _ mem Q
  | store k xcl l v ret ih => intro mem Q; exact and_congr (ih true _ Q) (imp_congr_right fun _ => ih false mem Q)
  | rmw k noRet l op ret ih =>
    intro mem Q
    simp only [EvTree.map, AllSeq]
    split <;> exact ih _ _ Q
  | fence k ret ih => intro mem Q; exact ih () mem Q

/-! ## Carrying a judgment along sequential runs -/

section Sim

variable {I : ISA} {β : Type}

/-- A simulation of the sequential runs of `I` by a step relation `T` on
states `β` (in the shape `Eventually` consumes): from related states, every
sequential outcome of the instruction at the pc is related to a state in the
post-set of the `T` step. -/
def SeqSim (I : ISA) (tid : Nat) (Rel : I.State × Memory → β → Prop) (T : β → (β → Prop) → Prop) : Prop :=
  ∀ x y (R : β → Prop), Rel x y → T y R → ∀ tree, I.exec x.1 = some tree →
    tree.AllSeq tid x.2 (fun s m => ∃ y', Rel (s, m) y' ∧ R y')

/-- Along a sequential run, a simulated `Eventually` judgment either has been
met (`P` held at a related state on the way) or still holds at the end. -/
theorem SeqReach.sim {tid : Nat} {Rel : I.State × Memory → β → Prop} {T : β → (β → Prop) → Prop}
    (hsim : SeqSim I tid Rel T) {P : β → Prop} {x x' : I.State × Memory} (hr : SeqReach tid x x') :
    ∀ y, Rel x y → Eventually T P y →
      (∃ z y', SeqReach tid x z ∧ SeqReach tid z x' ∧ Rel z y' ∧ P y') ∨
        ∃ y', Rel x' y' ∧ Eventually T P y' := by
  induction hr with
  | refl p => intro y hxy hev; exact .inr ⟨y, hxy, hev⟩
  | @step s m p p' tree hex hp hrest ih =>
    intro y hxy hev
    cases hev with
    | done _ hP => exact .inl ⟨(s, m), y, .refl _, .step hex hp hrest, hxy, hP⟩
    | step _ mid hT hmid =>
      have hall := hsim (s, m) y mid hxy hT tree hex
      obtain ⟨y', hpy', hmy'⟩ := (tree.allSeq_iff tid m _).mp hall p hp
      rcases ih y' hpy' (hmid y' hmy') with ⟨z, y'', h1, h2, h3, h4⟩ | h
      · exact .inl ⟨z, y'', .step hex hp h1, h2, h3, h4⟩
      · exact .inr h

/-- A fresh thread on a memory without messages is `Seq`. -/
theorem Thread.init_seq (tid : Nat) (st : I.State) {m : Memory} (hm : m.msgs = #[]) :
    (Thread.init st : Thread I).Seq tid m := by
  have hlast : m.last = 0 := by simp [Memory.last, hm]
  have hcoh : ∀ l, m.lastWrite l = 0 := fun l => by have := m.lastWrite_le l; omega_t
  refine ⟨rfl, ⟨fun l => by rw [hcoh]; exact Nat.zero_le _, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨fun l => ?_, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _, Nat.zero_le _, fun l f h => ?_, Nat.zero_le _⟩
    · simp [Views.getCoh, Thread.init]
    · simp [Views.getFwd, Thread.init] at h
  · intro t ν l h; simp [Thread.init] at h
  · intro v hv
    rw [Thread.init, Array.mem_replicate] at hv
    rw [hv.2]; exact Nat.zero_le _
  · intro v hv
    rw [Thread.init, Array.mem_replicate] at hv
    rw [hv.2]; exact Nat.zero_le _

/-- Conservativity for a program logic: if a step relation `T` simulates the
sequential runs of `I`, an `Eventually T P` judgment about a fresh thread
carries over to every promise-free run of the one-thread configuration: the
run met `P` on the way, or the judgment still holds at its end. -/
theorem reachablePF_sim (A : Arch) (fuel : Nat) {Rel : I.State × Memory → β → Prop}
    {T : β → (β → Prop) → Prop} (hsim : SeqSim I 0 Rel T) {P : β → Prop}
    {st : I.State} {mem : Memory} (hm : mem.msgs = #[]) {y : β} (hxy : Rel (st, mem) y)
    (hev : Eventually T P y) {c : Config I} (hc : ReachablePF A fuel ⟨#[Thread.init st], mem⟩ c) :
    ∃ t', c.threads = #[t'] ∧
      ((∃ z y', SeqReach 0 (st, mem) z ∧ SeqReach 0 z (t'.st, c.mem) ∧ Rel z y' ∧ P y') ∨
        ∃ y', Rel (t'.st, c.mem) y' ∧ Eventually T P y') := by
  obtain ⟨t', h1, _, h3⟩ := reachablePF_sound A fuel hc (Thread.init st) mem rfl (Thread.init_seq 0 st hm)
  exact ⟨t', h1, SeqReach.sim hsim h3 y hxy hev⟩

end Sim

end Kraken.Promising
