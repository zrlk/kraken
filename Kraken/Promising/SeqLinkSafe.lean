/-
Conservativity for partial-correctness judgments (design note `Kraken/Promising/EnvWP.md` §8).

`SeqReach.sim` and `reachablePF_sim` (`Kraken.Promising.SeqLink`) carry an
`Eventually` judgment along a sequential run by one case analysis per step,
never by induction on the judgment. So they hold for `Safely` (partial
correctness, `Kraken.Safely`) word for word: `SeqReach.sim_safe`,
`reachablePF_sim_safe`. ISA-free: each ISA's environment link
(`env_link_halt_safe`) instantiates them.
-/
import Kraken.Promising.SeqLink
import Kraken.Safely

namespace Kraken.Promising

section Sim

variable {I : ISA} {β : Type}

/-- `SeqReach.sim` for `Safely`: along a sequential run, a simulated
partial-correctness judgment has been met on the way, or still holds at the
end. -/
theorem SeqReach.sim_safe {tid : Nat} {Rel : I.State × Memory → β → Prop} {T : β → (β → Prop) → Prop}
    (hsim : SeqSim I tid Rel T) {P : β → Prop} {x x' : I.State × Memory} (hr : SeqReach tid x x') :
    ∀ y, Rel x y → Safely T P y →
      (∃ z y', SeqReach tid x z ∧ SeqReach tid z x' ∧ Rel z y' ∧ P y') ∨
        ∃ y', Rel x' y' ∧ Safely T P y' := by
  induction hr with
  | refl p => intro y hxy hev; exact .inr ⟨y, hxy, hev⟩
  | @step s m p p' tree hex hp hrest ih =>
    intro y hxy hev
    rcases hev.unfold with hP | ⟨mid, hT, hmid⟩
    · exact .inl ⟨(s, m), y, .refl _, .step hex hp hrest, hxy, hP⟩
    · have hall := hsim (s, m) y mid hxy hT tree hex
      obtain ⟨y', hpy', hmy'⟩ := (tree.allSeq_iff tid m _).mp hall p hp
      rcases ih y' hpy' (hmid y' hmy') with ⟨z, y'', h1, h2, h3, h4⟩ | h
      · exact .inl ⟨z, y'', .step hex hp h1, h2, h3, h4⟩
      · exact .inr h

/-- `reachablePF_sim` for `Safely`: a partial-correctness judgment about a
fresh thread carries over to every promise-free run of the one-thread
configuration: the run met `P` on the way, or the judgment still holds at its
end. -/
theorem reachablePF_sim_safe (A : Arch) (fuel : Nat) {Rel : I.State × Memory → β → Prop}
    {T : β → (β → Prop) → Prop} (hsim : SeqSim I 0 Rel T) {P : β → Prop}
    {st : I.State} {mem : Memory} (hm : mem.msgs = #[]) {y : β} (hxy : Rel (st, mem) y)
    (hev : Safely T P y) {c : Config I} (hc : ReachablePF A fuel ⟨#[Thread.init st], mem⟩ c) :
    ∃ t', c.threads = #[t'] ∧
      ((∃ z y', SeqReach 0 (st, mem) z ∧ SeqReach 0 z (t'.st, c.mem) ∧ Rel z y' ∧ P y') ∨
        ∃ y', Rel (t'.st, c.mem) y' ∧ Safely T P y') := by
  obtain ⟨t', h1, _, h3⟩ := reachablePF_sound A fuel hc (Thread.init st) mem rfl (Thread.init_seq 0 st hm)
  exact ⟨t', h1, SeqReach.sim_safe hsim h3 y hxy hev⟩

end Sim

end Kraken.Promising
