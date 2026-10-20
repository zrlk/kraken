/-
**Msqueue3 part 1: the ownership plan of the
x64 Michael–Scott queue with two try-once dequeuers**
`Kraken/Examples/LockFree/X64/msqueue3.kl` (thread `0` enqueues `n1` then
`n2` with `msqueue2.kl`'s code; threads `1` and `2` dequeue once each, `r12 :=
0` on an empty queue). ISA-neutral.

The queue words, `form` and `ghost₀` are `msqueue2.kl`'s
(`EnvG/X64MsQueue2Ghost.lean`) at parameters tracking the `head` swings
(`P.trk = true`, `Params.HW`): a `head` message is written by a dequeuer `w ∈
{1, 2}` and carries `w`'s **pop token** `P.popTok w` whole in its slot. Each dequeuer
holds its pop token whole until its single successful swing of `head`, which
gives it (`planD3 P w`); a dequeuer that found the queue empty still holds
it. This is the thread-history fact the final argument needs: a dequeuer
wrote at most one `head` message, and wrote none if it returned `0`.

The final shared postcondition is uniform in the thread, so each thread also
holds a **mark** `markT P w` whole that it never gives (`markT P 0 =
Params.tokH`, the enqueuer's `msqueue2.kl` token): two threads cannot hold
the same mark, so each of the three disjuncts of the postcondition belongs to
a different thread.

Resources: `head`/`tail` a third each; the enqueuer every other location
except the dequeuers' marks and pop tokens; dequeuer `w` its mark and pop
token, and dequeuer `1` the acquire id `0` of every queue word.

Contents: `markT`, `planD3` (+ validity, `rel`, `gives`, `keep`,
`give`), `fracE3`/`fracD3`, `resE3`/`resD3`, `tRes3`, `erase_init3`.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2Public

namespace Kraken.Promising.X64.EnvG.MsQueue3X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX

variable {I : ISA}

/-! ## Tracked threads, marks, pop tokens -/

/-- Thread `w`'s mark (`2 + w` bytes at `head`; `markT P 0 = P.tokH`). -/
def markT (P : Params) (w : Nat) : Loc := ⟨P.h, 2 + w⟩

theorem markT_zero (P : Params) : markT P 0 = P.tokH := rfl

section Distinct

variable (P : Params)

theorem markT_inj {w w' : Nat} (h : markT P w = markT P w') : w = w' := by
  simp only [markT, Loc.mk.injEq] at h; omega

theorem popTok_inj {w w' : Nat} (h : P.popTok w = P.popTok w') : w = w' := by
  simp only [Params.popTok, Loc.mk.injEq] at h; omega

theorem markT_ne_popTok (w w' : Nat) (hw : w ≤ 2) : markT P w ≠ P.popTok w' := by
  simp only [markT, Params.popTok, ne_eq, Loc.mk.injEq, not_and]; omega

theorem markT_ne_8 (w : Nat) (hw : w ≤ 2) (a : BitVec 64) : markT P w ≠ ⟨a, 8⟩ := by
  simp only [markT, ne_eq, Loc.mk.injEq, not_and]; omega

theorem popTok_ne_8 (w : Nat) (a : BitVec 64) : P.popTok w ≠ ⟨a, 8⟩ := by
  simp only [Params.popTok, ne_eq, Loc.mk.injEq, not_and]; omega

theorem markT_ne_1 (w : Nat) (a : BitVec 64) : markT P w ≠ ⟨a, 1⟩ := by
  simp only [markT, ne_eq, Loc.mk.injEq, not_and]; omega

theorem popTok_ne_1 (w : Nat) (a : BitVec 64) : P.popTok w ≠ ⟨a, 1⟩ := by
  simp only [Params.popTok, ne_eq, Loc.mk.injEq, not_and]; omega

theorem not_isW_popTok (w : Nat) : ¬ P.IsW (P.popTok w) := by
  rintro (h | h | h | h | h) <;>
    simp [Params.popTok, Params.head, Params.tail, Params.ls, Params.l1, Params.l2] at h <;> omega

end Distinct

/-! ## The dequeuers' plans -/

/-- **Dequeuer `w`'s plan**: every write to a queue word is a release; the
one at `head` gives `w`'s pop token. -/
def planD3 (P : Params) (w : Nat) : Plan :=
  ⟨[{ loc := P.head, gives := [P.popTok w] }, { loc := P.tail, gives := [] }, { loc := P.ls, gives := [] },
    { loc := P.l1, gives := [] }, { loc := P.l2, gives := [] }]⟩

theorem planD3_valid (P : Params) (w : Nat) : (planD3 P w).Valid := by
  intro e he
  simp only [planD3, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [Params.head, Params.popTok] <;> omega

theorem planD3_find_mem {P : Params} {w : Nat} {l : Loc} {v : Val} {e : Plan.Entry}
    (h : (planD3 P w).find? l v = some e) :
    e.loc = l ∧ e.split = none ∧ P.IsW l ∧ (e.gives = [] ∨ (l = P.head ∧ e.gives = [P.popTok w])) := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, -⟩ := hp
  refine ⟨rfl, ?_⟩
  simp only [planD3, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp [Params.IsW, Params.IsL]

theorem planD3_rel (P : Params) (w : Nat) (l : Loc) (v : Val) : (planD3 P w).rel l v = decide (P.IsW l) := by
  unfold Plan.rel
  cases h : (planD3 P w).find? l v with
  | some e => obtain ⟨-, -, hw, -⟩ := planD3_find_mem h; simp [hw]
  | none =>
    simp only [Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not]
    intro hw
    rw [Plan.find?, List.find?_eq_none] at h
    simp only [planD3, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true, decide_eq_true_eq,
      not_and, forall_eq_or_imp, forall_eq] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact h.1 rfl trivial
    · exact h.2.1 rfl trivial
    · exact h.2.2.1 rfl trivial
    · exact h.2.2.2.1 rfl trivial
    · exact h.2.2.2.2 rfl trivial

/-- What dequeuer `w`'s release of `v` to `l` gives: its pop token at
`head`, nothing elsewhere. -/
theorem planD3_gives (P : Params) (w : Nat) (l : Loc) (v : Val) :
    (planD3 P w).gives l v = if l = P.head then [P.popTok w] else [] := by
  split
  · subst l; simp [Plan.gives, Plan.find?, planD3]
  · rename_i hl
    unfold Plan.gives
    cases h : (planD3 P w).find? l v with
    | none => rfl
    | some e =>
      obtain ⟨-, -, -, hg⟩ := planD3_find_mem h
      rcases hg with hg | ⟨hl', -⟩
      · simp [hg]
      · exact absurd hl' hl

theorem planD3_keep (P : Params) (w : Nat) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planD3 P w).keep l v cl r = Res.drop ((planD3 P w).gives l v) r := by
  unfold Plan.keep Plan.gives
  cases h : (planD3 P w).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.keep, (planD3_find_mem h).2.1]

theorem planD3_give (P : Params) (w : Nat) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planD3 P w).give l v cl r = Res.only ((planD3 P w).gives l v) r := by
  unfold Plan.give Plan.gives
  cases h : (planD3 P w).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.give, (planD3_find_mem h).2.1]

/-! ## The initial resources -/

/-- The dequeuers' own ghost locations (marks and pop tokens). -/
def DOwn (P : Params) (x : Loc) : Prop :=
  x = markT P 1 ∨ x = markT P 2 ∨ x = P.popTok 1 ∨ x = P.popTok 2

instance (P : Params) (x : Loc) : Decidable (DOwn P x) := by unfold DOwn; infer_instance

/-- The enqueuer's initial fractions: a third of `head` and `tail`, all of
every other location but the dequeuers' marks and pop tokens. -/
def fracE3 (P : Params) (x : Loc) : Rat :=
  if x = P.head ∨ x = P.tail then 1 / 3 else if DOwn P x then 0 else 1

/-- Dequeuer `w`'s initial fractions: a third of `head` and `tail`, its mark
and pop token. -/
def fracD3 (P : Params) (w : Nat) (x : Loc) : Rat :=
  if x = P.head ∨ x = P.tail then 1 / 3 else if x = markT P w ∨ x = P.popTok w then 1 else 0

theorem fracE3_nonneg (P : Params) (x : Loc) : 0 ≤ fracE3 P x := by unfold fracE3; split <;> grind
theorem fracD3_nonneg (P : Params) (w : Nat) (x : Loc) : 0 ≤ fracD3 P w x := by unfold fracD3; split <;> grind

theorem frac3_add_le (P : Params) (x : Loc) : fracE3 P x + (fracD3 P 1 x + fracD3 P 2 x) ≤ 1 := by
  have h1 := markT_ne_popTok P 1 2 (by decide)
  have h2 := markT_ne_popTok P 2 1 (by decide)
  have h3 : markT P 1 ≠ markT P 2 := fun h => absurd (markT_inj P h) (by decide)
  have h4 : P.popTok 1 ≠ P.popTok 2 := fun h => absurd (popTok_inj P h) (by decide)
  have h5 := markT_ne_popTok P 1 1 (by decide)
  have h6 := markT_ne_popTok P 2 2 (by decide)
  unfold fracE3 fracD3 DOwn
  repeat' split
  all_goals grind

/-- The enqueuer's initial resource (no acquire id). -/
def resE3 (m : Memory) (P : Params) : Res := Res.initOf m (fracE3 P) (fracE3_nonneg P)

/-- Dequeuer `w`'s initial resource; dequeuer `1` also holds the acquire id
`0` of every queue word. -/
def resD3 (m : Memory) (P : Params) (w : Nat) : Res :=
  ⟨(Res.initOf m (fracD3 P w) (fracD3_nonneg P w)).wr, fun x ι => if w = 1 ∧ P.IsW x ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: the enqueuer is thread `0`, the dequeuers
threads `1` and `2`. -/
def tRes3 (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then resE3 m P else if i = 1 then resD3 m P 1 else if i = 2 then resD3 m P 2 else Res.unit

/-! ## Initial erasure -/

section Init

variable {s0 s1 s2 : I.State} {initMem : List (Loc × Val)}

theorem total_init3 (P : Params) (m : Memory) :
    total (tRes3 m P) (ghost₀ P) (Config.init [s0, s1, s2] initMem) =
      (resE3 m P).op ((resD3 m P 1).op (resD3 m P 2)) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost₀, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes3 m P 0, tRes3 m P 1, tRes3 m P 2] = _
  simp [tRes3, Res.op_unit]

/-- **Initial erasure of the queue with three threads.** -/
theorem erase_init3 {P : Params} (hL : QLocs P) (T : Nat → Prop) :
    Erase (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost₀ P) T (Config.init [s0, s1, s2] initMem) := by
  have htot := total_init3 (s0 := s0) (s1 := s1) (s2 := s2) (initMem := initMem) P
    (Config.init [s0, s1, s2] initMem).mem
  have ha : ∀ x ι, (total (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1, s2] initMem)).acq x ι = if P.IsW x ∧ ι = 0 then 1 else 0 := by
    intro x ι; rw [htot]
    show 0 + ((if 1 = 1 ∧ P.IsW x ∧ ι = 0 then 1 else 0) + (if 2 = 1 ∧ P.IsW x ∧ ι = 0 then 1 else 0)) = _
    simp
  have hq : ∀ x, ((total (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1, s2] initMem)).wr x).q = fracE3 P x + (fracD3 P 1 x + fracD3 P 2 x) := by
    intro x; rw [htot]; rfl
  have hX : ∀ x p, ((total (tRes3 (Config.init [s0, s1, s2] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1, s2] initMem)).wr x).X p ↔
        (0 < fracE3 P x ∨ 0 < fracD3 P 1 x ∨ 0 < fracD3 P 2 x) ∧
          p = ((Config.init [s0, s1, s2] initMem).mem.initVal x, 0) := by
    intro x p; rw [htot]
    show (0 < fracE3 P x ∧ p = _) ∨ ((0 < fracD3 P 1 x ∧ p = _) ∨ (0 < fracD3 P 2 x ∧ p = _)) ↔ _
    constructor
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨.inl h, rfl⟩
      · exact ⟨.inr (.inl h), rfl⟩
      · exact ⟨.inr (.inr h), rfl⟩
    · rintro ⟨h | h | h, rfl⟩
      · exact .inl ⟨h, rfl⟩
      · exact .inr (.inl ⟨h, rfl⟩)
      · exact .inr (.inr ⟨h, rfl⟩)
  refine erase_init_ghostX hL T ha (fun x => by rw [hq]; exact frac3_add_le P x) ?_
  -- write sets
  intro x hpos p
  rw [hX]
  have : 0 < fracE3 P x ∨ 0 < fracD3 P 1 x ∨ 0 < fracD3 P 2 x := by
    rw [hq] at hpos
    have := fracE3_nonneg P x; have := fracD3_nonneg P 1 x; have := fracD3_nonneg P 2 x
    by_cases h0 : 0 < fracE3 P x
    · exact .inl h0
    by_cases h1 : 0 < fracD3 P 1 x
    · exact .inr (.inl h1)
    · exact .inr (.inr (by grind))
  simp [this]

end Init

end Kraken.Promising.X64.EnvG.MsQueue3X
