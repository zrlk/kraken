/-
Part 1: **the resource split of `msqueue3.kl`**
(the Michael–Scott queue, one enqueuer of `n1` then `n2`, two competing
dequeuers each dequeuing once; on `EnvGCAdj`). ISA-neutral.

The protocol is msqueue2's, unchanged (`EnvG/MsQueue2Ghost.lean`: `form2`,
`ghost2`, `planE2` for the enqueuer, `planD2` for **both** dequeuers): only
the enqueuer writes the links (the dequeuers' `casal`s address the fixed
`x0 = head`, `x1 = tail`), and a dequeuer's swing of `head` releases
`HeadF` by adjacency whoever the dequeuer is.

The split of the initial resources over three threads:

| thread | `head`/`tail` | other locations | identity |
|---|---|---|---|
| `0` enqueuer | `½` | all but `tokD2` | `tokE` whole |
| `1` dequeuer | `¼` | none | the acquire id `0` of every queue word |
| `2` dequeuer | `¼` | `tokD2` | `tokD2` whole |

The acquire ids are needed only at the final clean erasure (`slot_of_held`;
`EnvGCAdj` loads leave the resource unchanged), so one holder suffices.

Contents: `tokD2`, `fracE3`/`fracDa3`/`fracDb3`, `resE3`/`resDa3`/`resDb3`,
`tRes3`, `erase_init3`.
-/
import Kraken.Promising.SLR.EnvG.MsQueue2Ghost

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising

variable {I : ISA}

/-- The second dequeuer's identity token (a ghost location: no access of the
code has `1` byte). -/
def tokD2 (P : Params2) : Loc := ⟨P.t, 1⟩

theorem tokD2_ne_of_8 (P : Params2) {a : BitVec 64} : (⟨a, 8⟩ : Loc) ≠ tokD2 P := by simp [tokD2]

theorem tokE_tokD2 {P : Params2} (hL : QLocs2 P) : P.tokE ≠ tokD2 P := by
  simp only [Params.tokE, tokD2, ne_eq, Loc.mk.injEq, and_true]; exact hL.q1.ht

theorem not_isW_tokD2 (P : Params2) : ¬ P.IsW (tokD2 P) := by
  rintro (h | h | h | h | h) <;>
    simp [tokD2, Params.head, Params.tail, Params.dn, Params.nn, Params2.nn2] at h

/-! ## The initial resources -/

/-- The enqueuer's initial fractions: half of `head` and `tail`, nothing of
`tokD2`, all of every other location. -/
def fracE3 (P : Params2) (x : Loc) : Rat :=
  if x = P.head ∨ x = P.tail then 1 / 2 else if x = tokD2 P then 0 else 1

/-- The first dequeuer's initial fractions: a quarter of `head` and
`tail`. -/
def fracDa3 (P : Params2) (x : Loc) : Rat := if x = P.head ∨ x = P.tail then 1 / 4 else 0

/-- The second dequeuer's initial fractions: a quarter of `head` and `tail`,
all of `tokD2`. -/
def fracDb3 (P : Params2) (x : Loc) : Rat :=
  if x = P.head ∨ x = P.tail then 1 / 4 else if x = tokD2 P then 1 else 0

theorem fracE3_nonneg (P : Params2) (x : Loc) : 0 ≤ fracE3 P x := by
  unfold fracE3; (repeat' split) <;> grind
theorem fracDa3_nonneg (P : Params2) (x : Loc) : 0 ≤ fracDa3 P x := by unfold fracDa3; split <;> grind
theorem fracDb3_nonneg (P : Params2) (x : Loc) : 0 ≤ fracDb3 P x := by
  unfold fracDb3; (repeat' split) <;> grind

theorem frac3_add_le (P : Params2) (x : Loc) : fracE3 P x + (fracDa3 P x + fracDb3 P x) ≤ 1 := by
  unfold fracE3 fracDa3 fracDb3
  by_cases h1 : x = P.head ∨ x = P.tail
  · simp only [h1, ↓reduceIte]; grind
  · by_cases h2 : x = tokD2 P <;> simp only [h1, h2, ↓reduceIte] <;> grind

/-- The enqueuer's initial resource (no acquire id). -/
def resE3 (m : Memory) (P : Params2) : Res := Res.initOf m (fracE3 P) (fracE3_nonneg P)

/-- The first dequeuer's initial resource: its fractions and the acquire id
`0` of every queue word. -/
def resDa3 (m : Memory) (P : Params2) : Res :=
  ⟨(Res.initOf m (fracDa3 P) (fracDa3_nonneg P)).wr, fun x ι => if P.IsW x ∧ ι = 0 then 1 else 0⟩

/-- The second dequeuer's initial resource (no acquire id). -/
def resDb3 (m : Memory) (P : Params2) : Res := Res.initOf m (fracDb3 P) (fracDb3_nonneg P)

/-- The initial thread resources: the enqueuer is thread `0`, the dequeuers
threads `1` and `2`. -/
def tRes3 (m : Memory) (P : Params2) (i : Nat) : Res :=
  if i = 0 then resE3 m P else if i = 1 then resDa3 m P else if i = 2 then resDb3 m P else Res.unit

/-! ## Initial erasure -/

section Init

variable {s0 s1 s2 : I.State} {initMem : List (Loc × Val)}

theorem total_init3 (P : Params2) (m : Memory) :
    total (tRes3 m P) (ghost2 P) (Config.init [s0, s1, s2] initMem) =
      (resE3 m P).op ((resDa3 m P).op (resDb3 m P)) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost2, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes3 m P 0, tRes3 m P 1, tRes3 m P 2] = _
  simp [tRes3, Res.op_unit]

/-- **Initial erasure of the queue of `msqueue3.kl`.** -/
theorem erase_init3 {P : Params2} (hL : QLocs2 P) (T : Nat → Prop) :
    Erase (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost2 P) T (Config.init [s0, s1, s2] initMem) := by
  have htot := total_init3 (s0 := s0) (s1 := s1) (s2 := s2) (initMem := initMem) P
    (Config.init [s0, s1, s2] initMem).mem
  have ha : ∀ x ι, (total (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost2 P)
      (Config.init [s0, s1, s2] initMem)).acq x ι = if P.IsW x ∧ ι = 0 then 1 else 0 := by
    intro x ι; rw [htot]; show 0 + ((if P.IsW x ∧ ι = 0 then 1 else 0) + 0) = _; simp
  have hq : ∀ x, ((total (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost2 P)
      (Config.init [s0, s1, s2] initMem)).wr x).q = fracE3 P x + (fracDa3 P x + fracDb3 P x) := by
    intro x; rw [htot]; rfl
  have hX : ∀ x p, ((total (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost2 P)
      (Config.init [s0, s1, s2] initMem)).wr x).X p ↔
        (0 < fracE3 P x ∨ 0 < fracDa3 P x ∨ 0 < fracDb3 P x) ∧
          p = ((Config.init [s0, s1, s2] initMem).mem.initVal x, 0) := by
    intro x p; rw [htot]
    show (0 < fracE3 P x ∧ p = _) ∨ (0 < fracDa3 P x ∧ p = _) ∨ (0 < fracDb3 P x ∧ p = _) ↔ _
    constructor
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨.inl h, rfl⟩
      · exact ⟨.inr (.inl h), rfl⟩
      · exact ⟨.inr (.inr h), rfl⟩
    · rintro ⟨h | h | h, rfl⟩
      · exact .inl ⟨h, rfl⟩
      · exact .inr (.inl ⟨h, rfl⟩)
      · exact .inr (.inr ⟨h, rfl⟩)
  refine erase_init_ghost2 hL T ha (fun x => by rw [hq]; exact frac3_add_le P x) ?_
  -- write sets
  intro x hpos p
  rw [hX]
  have : 0 < fracE3 P x ∨ 0 < fracDa3 P x ∨ 0 < fracDb3 P x := by
    rw [hq] at hpos
    have := fracE3_nonneg P x; have := fracDa3_nonneg P x; have := fracDb3_nonneg P x
    by_cases h0 : 0 < fracE3 P x
    · exact .inl h0
    by_cases h1 : 0 < fracDa3 P x
    · exact .inr (.inl h1)
    · exact .inr (.inr (by grind))
  simp [this]

end Init

end Kraken.Promising.SLR.EnvG.MsQueue
