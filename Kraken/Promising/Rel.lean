/-
Basic facts about the machine relation.

`Step A fuel` is the transition in the shape `Eventually` (Kraken's run
relation, `Kraken/OmniSemantics.lean`) consumes; `Reachable` is its
reflexive-transitive closure through single successors. The explorer
(`explore`) walks `Reachable` to the final configurations; it is a
`partial def` over hash sets, so its adequacy is by construction (it calls
`succs` and nothing else) rather than by theorem.

Proof work:
- Conservativity (§7.2) is in `Kraken/Promising/Conservative.lean`: for a
  one-thread configuration with no promises, promise-free runs of `succs`
  are runs of a sequential interpreter of the instruction's event tree on
  the memory (`reachablePF_sound`), with the invariant
  `∀ l, last write to l ≤ coh l ≤ |M|` on the thread's views. The memory
  lemmas below are its base case. `Kraken/Promising/SeqLink*.lean` carry
  Kraken's single-threaded judgment over to those runs, on a `dmem` merged
  with each shared location's last message.
- `deps` coverage: every register `Operation.interp` reads or writes appears
  in `Operation.deps`, per ISA.
-/
import Kraken.Promising.Machine
import Kraken.OmniSemantics

namespace Kraken.Promising

variable {I : ISA} (A : Arch) (fuel : Nat)

theorem Step.mono {c : Config I} {p q : Config I → Prop} (h : ∀ c, p c → q c) :
    Step A fuel c p → Step A fuel c q :=
  fun ⟨hne, hall⟩ => ⟨hne, fun c' hc' => h c' (hall c' hc')⟩

theorem Reachable.trans {a b c : Config I} (h₁ : Reachable A fuel a b) (h₂ : Reachable A fuel b c) :
    Reachable A fuel a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem Reachable.single {c c' : Config I} (h : c' ∈ (succs A c fuel).1) : Reachable A fuel c c' :=
  .step h (.refl c')

variable {A fuel} in
/-- **Invariant induction over `Reachable`**: a predicate kept by every
successor step holds at every configuration reachable from one where it
holds. (The shared skeleton of `configInv_reachable`,
`EnvG.Reachable.valInvA` and `EnvG.TicketX2.inv_reachable`.) -/
theorem Reachable.inv {P : Config I → Prop} (hstep : ∀ c c', P c → c' ∈ (succs A c fuel).1 → P c')
    {c c' : Config I} (h : Reachable A fuel c c') (h0 : P c) : P c' := by
  induction h with
  | refl => exact h0
  | step hs _ ih => exact ih (hstep _ _ h0 hs)

/-- A run that must reach `post` under every schedule reaches it along some
path of successors. -/
theorem Eventually.exists_reachable {c : Config I} {post : Config I → Prop}
    (h : Eventually (Step A fuel) post c) : ∃ c', Reachable A fuel c c' ∧ post c' := by
  induction h with
  | done c hp => exact ⟨c, .refl c, hp⟩
  | step c mid hstep _ ih =>
    obtain ⟨hne, hall⟩ := hstep
    match hs : (succs A c fuel).1 with
    | [] => exact absurd hs hne
    | c' :: _ =>
      have hmem : c' ∈ (succs A c fuel).1 := by rw [hs]; exact List.mem_cons_self
      obtain ⟨c'', hr, hp⟩ := ih c' (hall c' hmem)
      exact ⟨c'', .step hmem hr, hp⟩

/-! ## Memory -/

namespace Memory

theorem last_append (m : Memory) (w : Msg) : (m.append w).1.last = m.last + 1 := by
  simp [append, last]

theorem append_time (m : Memory) (w : Msg) : (m.append w).2 = m.last + 1 := rfl

/-- The fresh timestamp holds the appended message. -/
theorem get?_append_last (m : Memory) (w : Msg) : (m.append w).1.get? (m.last + 1) = some w := by
  simp [append, get?, last]

/-- Reading the appended message at its own timestamp and location gives its value. -/
theorem read?_append_last (m : Memory) (w : Msg) : (m.append w).1.read? w.loc (m.last + 1) = some w.val := by
  simp [read?, get?_append_last]

/-- Earlier timestamps are unchanged by an append. -/
theorem get?_append_of_le (m : Memory) (w : Msg) (t : Time) (h : t ≤ m.last) :
    (m.append w).1.get? t = m.get? t := by
  simp only [append, get?, last] at *
  split
  · rfl
  · next ht =>
    have : t - 1 < m.msgs.size := Nat.lt_of_lt_of_le (Nat.sub_one_lt ht) h
    rw [Array.getElem?_push_lt this, Array.getElem?_eq_getElem this]

/-- A message of a memory is a message of every extension. -/
theorem get?_of_prefix {m m' : Memory} (h : m.msgs.toList <+: m'.msgs.toList) {ts : Time} {w : Msg}
    (hg : m.get? ts = some w) : m'.get? ts = some w := by
  unfold Memory.get? at *
  split at hg
  · cases hg
  · rename_i h0
    simp only [h0, ↓reduceIte]
    rw [← Array.getElem?_toList] at hg ⊢
    obtain ⟨u, hu⟩ := h
    rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hg).1]
    exact hg

/-- A message of an extension at a timestamp of the memory is a message of
the memory. -/
theorem get?_of_prefix_le {m m' : Memory} (h : m.msgs.toList <+: m'.msgs.toList) {ts : Time} {w : Msg}
    (hle : ts ≤ m.last) (hg : m'.get? ts = some w) : m.get? ts = some w := by
  have h0 : ts ≠ 0 := by rintro rfl; simp [Memory.get?] at hg
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, m.get? ts = some w₀ := by
    unfold Memory.get?
    simp only [h0, ↓reduceIte]
    have h2 : ts ≤ m.msgs.size := hle
    exact ⟨_, Array.getElem?_eq_getElem (by simp only [Time] at *; omega)⟩
  rw [get?_of_prefix h hw₀] at hg
  rw [hw₀, hg]

end Memory

end Kraken.Promising
