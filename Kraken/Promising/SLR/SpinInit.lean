/-
Initial erasure for the spinlock counter (ISA-neutral): the
obligations `hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)`
and `hpend : ∀ ts, ts ∉ g₀.pend` of `Spinlock.counter_of_theorem1Pure`, for
both the AArch64 `swpWorker` and the x64 `spinWorker`.

The initial ghost `spinGhost Lk φ pool` has one release message, the initial
lock message `(Lk, 0)`, in release mode with release predicate `φ`; one
acquire predicate, `φ` itself (id `0`), which is the lock's update predicate
(`upd Lk = [0]`) and held by no resource; and one slot, the pool `pool`,
attached to `(Lk, 0)` under id `0`. Every other location has the release
predicate `Pred.emp` (it transfers nothing). Nothing is pending or claimed.

`Spinlock.erase_init` derives `Erase` from three facts about the resources
alone (the total resource `(threadsRes rF N).op pool` is valid, holds no
acquire id, and the write set of each tracked location is the initial
message), plus `φ` at the pool: `φ.P (initVal Lk) mem 0 pool`.

## Contents

- `Pred.emp`, `Pred.emp_pure`: the release predicate that holds of the empty
  resource only.
- `Spinlock.spinGhost`, `Spinlock.spinGhost_rel_Lk`, `spinGhost_acqPred_zero`,
  `spinGhost_upd_Lk`: the initial ghost and the facts `counter_of_theorem1Pure`
  asks of it (`hrel`, `hupd`, `hιlt`, `hφ`).
- `Spinlock.total_init`: the total resource at `Config.init`.
- `Spinlock.erase_init`, `Spinlock.pend_init`: initial erasure.
-/
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- The predicate that holds of the empty resource only: the release
predicate of a location whose messages transfer nothing. -/
def Pred.emp : Pred := ⟨fun _ _ _ r => r = Res.unit, fun _ _ _ _ _ _ h => h⟩

theorem Pred.emp_pure (v : Val) : Pred.emp.Pure v := fun _ _ => rfl

namespace Spinlock

/-- **The initial ghost of the spinlock**: the initial lock message in
release mode with release and update predicate `φ` (acquire id `0`) and the
slot `pool`; every other location relaxed with predicate `Pred.emp`. -/
def spinGhost (Lk : Loc) (φ : Pred) (pool : Res) : Ghost where
  rel x := if x = Lk then φ else Pred.emp
  acqTab := [φ]
  u := [⟨(Lk, 0), 0, pool⟩]
  relMsgs := [(Lk, 0)]
  pend := []
  upd x := if x = Lk then [0] else []
  claims := []

section Ghost

variable {Lk : Loc} {φ : Pred} {pool : Res}

theorem spinGhost_rel_Lk : (spinGhost Lk φ pool).rel Lk = φ := by simp [spinGhost]

theorem spinGhost_acqPred_zero : (spinGhost Lk φ pool).acqPred 0 = φ := rfl

theorem spinGhost_upd_Lk : (0 : PredId) ∈ (spinGhost Lk φ pool).upd Lk := by simp [spinGhost]

theorem spinGhost_acqTab_length : (spinGhost Lk φ pool).acqTab.length = 1 := rfl

theorem pend_init : ∀ ts, ts ∉ (spinGhost Lk φ pool).pend := fun _ h => by cases h

theorem slotsRes_spinGhost : (spinGhost Lk φ pool).slotsRes = pool := by
  simp [Ghost.slotsRes, spinGhost, Res.prod, Res.op_unit]

/-- The total resource at the initial configuration: the threads' and the
pool. -/
theorem total_init {rF : Nat → Res} {states : List I.State} {initMem : List (Loc × Val)} :
    total rF (spinGhost Lk φ pool) (Config.init states initMem) = (threadsRes rF states.length).op pool := by
  rw [total, slotsRes_spinGhost, Config.init_size]

end Ghost

/-- **Initial erasure of the spinlock** from facts about the resources: the
total `(threadsRes rF N).op pool` is valid and holds no acquire id, the
write set of every tracked location is its initial message, and the pool
satisfies `φ` at the initial lock value (view `0`). -/
theorem erase_init {rF : Nat → Res} {states : List I.State} {initMem : List (Loc × Val)}
    {Lk : Loc} {φ : Pred} {pool : Res} (T : Nat → Prop)
    (hvalid : ((threadsRes rF states.length).op pool).valid)
    (hacq : ∀ x ι, ((threadsRes rF states.length).op pool).acq x ι = 0)
    (hwrites : ∀ x, 0 < (((threadsRes rF states.length).op pool).wr x).q → ∀ p,
      (((threadsRes rF states.length).op pool).wr x).X p ↔
        p = ((Config.init states initMem).mem.initVal x, 0))
    (hpool : φ.P ((Config.init states initMem).mem.initVal Lk) (Config.init states initMem).mem 0 pool) :
    Erase rF (spinGhost Lk φ pool) T (Config.init states initMem) := by
  have ht := total_init (I := I) (rF := rF) (Lk := Lk) (φ := φ) (pool := pool) (states := states)
    (initMem := initMem)
  have hacq' : ∀ x ι, (total rF (spinGhost Lk φ pool) (Config.init states initMem)).acq x ι = 0 := by
    rw [ht]; exact hacq
  have hids : ∀ x, (spinGhost Lk φ pool).acqIds
      (total rF (spinGhost Lk φ pool) (Config.init states initMem)).acq x = [] := by
    intro x
    simp only [Ghost.acqIds, spinGhost_acqTab_length, List.range_one]
    have := hacq' x 0
    simp [this]
  refine Erase.init (by rw [ht]; exact hvalid) ?_ ?_ ?_ (by rw [ht]; exact hwrites) ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- slot ids
    intro s hs
    simp only [spinGhost, List.mem_singleton] at hs
    subst hs
    exact Nat.zero_lt_one
  · -- acquire ids
    intro x ι h
    rw [hacq'] at h
    exact absurd h (by decide)
  · -- release predicates split into acquire and update predicates
    intro x v m V r h
    rw [Ghost.acqPreds, hids, List.map_nil, List.nil_append]
    by_cases hx : x = Lk
    · subst hx
      simp only [spinGhost, ↓reduceIte] at h
      simp only [Ghost.updPreds, spinGhost, ↓reduceIte, List.map_cons, List.map_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, rfl⟩
    · simp only [spinGhost, hx, ↓reduceIte] at h
      simp only [Ghost.updPreds, spinGhost, hx, ↓reduceIte, List.map_nil]
      exact h
  · -- relaxed initial messages are pure
    intro x hx
    have hx' : x ≠ Lk := fun h => hx (by simp [spinGhost, h])
    simp only [spinGhost, hx', ↓reduceIte]
    exact Pred.emp_pure _
  · -- release messages are initial
    intro k hk
    simp only [spinGhost, List.mem_singleton] at hk
    subst hk
    rfl
  · -- slots are distinct
    simp [spinGhost]
  · -- slot domain
    intro k ι
    rw [hacq']
    simp only [spinGhost, List.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, .inr (by simp)⟩
    · rintro ⟨rfl, h⟩
      refine ⟨rfl, ?_⟩
      rcases h with h | h
      · exact absurd h (by decide)
      · simpa [eq_comm] using h
  · -- the pool satisfies its predicate
    intro s hs
    simp only [spinGhost, List.mem_singleton] at hs
    subst hs
    exact hpool
  · -- update ids
    intro x
    refine ⟨?_, fun ι hι => ?_⟩
    · simp only [spinGhost]; split <;> simp
    · simp only [spinGhost] at hι
      split at hι
      · simp only [List.mem_singleton] at hι
        subst hι
        exact ⟨Nat.zero_lt_one, hacq' x 0⟩
      · cases hι

end Spinlock

end Kraken.Promising.SLR
