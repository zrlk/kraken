/-
**A label's address at another base, or with a tail appended**
(ISA-neutral; shared by the linked proofs of post-pass texts on both ISAs):
the granule pass leaves the pre-pass cells unchanged and appends a tail (a
`.zero` filler, `.Lgw0:`, one descriptor word, `scc_text_end:`), and the
post-pass executable's code base moves. These are the facts of the
canonical loader's `labelAddr` (`Scc/Sem/Target.lean`) under both changes;
`Spike/Lib/A64TextTail.lean` and `Spike/Lib/X64TextTail.lean` state them for
each ISA's code labels.

- `labelAddr_shift`: a label's address moves with the base;
- `labelAddr_append_of`: a label of the list keeps its address with a tail
  appended (first occurrence);
- `labelAddr_append_none`: a label not in the list is the tail's, laid out
  from the list's end;
- `labelAddr_le`: a label's address is at most the list's end.
-/
import Scc.Sem.Target

namespace Spike.Lib.TextTail

open Scc.Sem

/-- **A label's address moves with the base.** -/
theorem labelAddr_shift {D : Type} (lb : D → Option String) (sz : D → Nat) (l : String) (δ : Nat) :
    ∀ (ds : List D) (b : Nat), labelAddr lb sz (b + δ) l ds = (labelAddr lb sz b l ds).map (· + δ)
  | [], _ => rfl
  | d :: ds, b => by
    simp only [labelAddr]
    split
    · rfl
    · rw [Nat.add_right_comm]; exact labelAddr_shift lb sz l δ ds (b + sz d)

/-- **A label of the list keeps its address with a tail appended** (the
first occurrence wins). -/
theorem labelAddr_append_of {D : Type} {lb : D → Option String} {sz : D → Nat} {l : String} {a : Nat}
    (T : List D) : ∀ {ds : List D} {b : Nat}, labelAddr lb sz b l ds = some a →
      labelAddr lb sz b l (ds ++ T) = some a
  | [], _, h => nomatch h
  | d :: ds, b, h => by
    simp only [labelAddr, List.cons_append] at h ⊢
    split
    · rename_i hd; simpa [hd] using h
    · rename_i hd; simp only [hd, ↓reduceIte] at h; exact labelAddr_append_of T h

/-- **A label not in the list is the tail's**, laid out from the list's
end. -/
theorem labelAddr_append_none {D : Type} {lb : D → Option String} {sz : D → Nat} {l : String}
    (T : List D) : ∀ {ds : List D} {b : Nat}, labelAddr lb sz b l ds = none →
      labelAddr lb sz b l (ds ++ T) = labelAddr lb sz (b + (ds.map sz).sum) l T
  | [], b, _ => by simp
  | d :: ds, b, h => by
    simp only [labelAddr, List.cons_append] at h ⊢
    split
    · rename_i hd; simp [hd] at h
    · rename_i hd
      simp only [hd, ↓reduceIte] at h
      rw [labelAddr_append_none T h, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **A label's address is at most the list's end** (the base plus every
cell's size). -/
theorem labelAddr_le {D : Type} {lb : D → Option String} {sz : D → Nat} {l : String} :
    ∀ {ds : List D} {b a : Nat}, labelAddr lb sz b l ds = some a → a ≤ b + (ds.map sz).sum
  | [], _, _, h => nomatch h
  | d :: ds, b, a, h => by
    simp only [labelAddr] at h
    split at h
    · cases h; simp
    · have := labelAddr_le h
      simp only [List.map_cons, List.sum_cons]
      omega

end Spike.Lib.TextTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.TextTail.labelAddr_shift' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.TextTail.labelAddr_shift

/-- info: 'Spike.Lib.TextTail.labelAddr_append_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.TextTail.labelAddr_append_of

/-- info: 'Spike.Lib.TextTail.labelAddr_append_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.TextTail.labelAddr_append_none

/-- info: 'Spike.Lib.TextTail.labelAddr_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.TextTail.labelAddr_le
