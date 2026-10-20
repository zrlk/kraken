/-
**Part 3: the specification of the SPSC
ring** (`Examples/LockFree/X64/spsc_queue.kl`): locations, the release
predicates of the two indices, the plans, the initial resources and ghost,
and initial erasure.

**Locations** (`SP`: `b = buf0`, `h = head`, `t = tail`): the slots
`B0 = ⟨b, 4⟩`, `B1 = ⟨b + 256, 4⟩`, the indices `H = ⟨h, 4⟩`, `T = ⟨t, 4⟩`,
and two ghost tokens `GA = ⟨0, 5⟩`, `GB = ⟨1, 5⟩` (no access has width `5`).
The tokens tell the two `T := 1` releases apart: the first gives `GA` with
`buf0 = 1`, the second `GB` with `buf0 = 3`.

**The protocol.** The producer owns `T`, the consumer `H`. A slot moves to
the consumer with the producer's `T` release that publishes it, and `B0`
moves back to the producer with the consumer's first `H := 1` release (the
producer reuses `buf0` in round 3). So both indices carry resources:
- `psiT` (`T`'s release and acquire predicate): at `1`, all of `B0` with
  maximal write `1` and `GA`, or all of `B0` with maximal write `3` and `GB`;
  at `0`, nothing at view `0` (the initial message) or all of `B1` with
  maximal write `2`; nothing else. Impure at every value.
- `psiH`: at `1`, all of `B0` (every write at or below the message) and
  `GB`; at `0`, nothing (pure). Nothing else.

**The plans**: the producer's `T := 1` gives `B0`, `GA`, `GB`; its `T := 0`
gives `B1`. The consumer's `H := 1` gives `B0`, `GB`. The consumer's
`H := 0` and the data stores are unplanned (pure).

**Initial state**: the producer holds `T`, `B0`, `B1`, `GA` and the acquire
id `1` of `H` (predicate `psiH`); the consumer holds `H`, `GB` and the
acquire id `0` of `T` (predicate `psiT`). `T`'s initial message is a release
message (`psiT` is impure) with the empty slot of id `0`; `H`'s is relaxed.
Initial erasure is `erase_initGhostAcq` (`InitGhost.lean`).
-/
import Kraken.Promising.SLR.EnvG.X64MpSpec
import Kraken.Promising.SLR.EnvG.State
import Kraken.Promising.SLR.EnvG.SpscCommon
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG.SpscX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## Locations -/

/-- The SPSC parameters: `buf0`, `head`, `tail`. -/
structure SP where
  b : BitVec 64
  h : BitVec 64
  t : BitVec 64

namespace SP

/-- Slot `0`. -/
abbrev B0 (P : SP) : Loc := ⟨P.b, 4⟩
/-- Slot `1`, `0x100` bytes above slot `0`. -/
abbrev B1 (P : SP) : Loc := ⟨P.b + 256, 4⟩
/-- The consumer's index `head`. -/
abbrev H (P : SP) : Loc := ⟨P.h, 4⟩
/-- The producer's index `tail`. -/
abbrev T (P : SP) : Loc := ⟨P.t, 4⟩

end SP

/-- Ghost token `A` (no access has width `5`). -/
abbrev GA : Loc := ⟨0, 5⟩
/-- Ghost token `B`. -/
abbrev GB : Loc := ⟨1, 5⟩

/-- **The SPSC words are distinct**. -/
structure SpscLocs (P : SP) : Prop where
  bh : P.b ≠ P.h
  bt : P.b ≠ P.t
  b1h : P.b + 256 ≠ P.h
  b1t : P.b + 256 ≠ P.t
  ht : P.h ≠ P.t

namespace SpscLocs

variable {P : SP} (hL : SpscLocs P)
include hL

theorem b0_h : P.B0 ≠ P.H := fun e => hL.bh (congrArg Loc.addr e)
theorem b0_t : P.B0 ≠ P.T := fun e => hL.bt (congrArg Loc.addr e)
theorem b1_h : P.B1 ≠ P.H := fun e => hL.b1h (congrArg Loc.addr e)
theorem b1_t : P.B1 ≠ P.T := fun e => hL.b1t (congrArg Loc.addr e)
theorem h_t : P.H ≠ P.T := fun e => hL.ht (congrArg Loc.addr e)

end SpscLocs

theorem b0_b1 (P : SP) : P.B0 ≠ P.B1 := fun e => by
  have := congrArg Loc.addr e
  simp only at this
  bv_omega

theorem ga_gb : GA ≠ GB := by decide

/-- A word of width `4` is no ghost token. -/
theorem ne_ga {a : BitVec 64} : (⟨a, 4⟩ : Loc) ≠ GA := fun e => by have := congrArg Loc.bytes e; simp at this
theorem ne_gb {a : BitVec 64} : (⟨a, 4⟩ : Loc) ≠ GB := fun e => by have := congrArg Loc.bytes e; simp at this

/-! ## The predicates -/

-- `Full`: the ISA-neutral `SpscCommon.Full`.
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.Full ↦ Kraken.Promising.X64.EnvG.SpscX.Full]

/-- **`tail`'s predicate.** -/
def psiT (P : SP) : Pred where
  P v _ V R :=
    (v = 1#128 ∧ ((Full P.B0 1#128 V R ∧ (R.wr GA).q = 1) ∨ (Full P.B0 3#128 V R ∧ (R.wr GB).q = 1))) ∨
      (v = 0#128 ∧ ((V = 0 ∧ R = Res.unit) ∨ Full P.B1 2#128 V R))
  mono _ _ _ _ _ _ h := h

/-- **`head`'s predicate.** -/
def psiH (P : SP) : Pred where
  P v _ V R :=
    (v = 1#128 ∧ (R.wr P.B0).q = 1 ∧ (∀ p, (R.wr P.B0).X p → p.2 ≤ V) ∧ (R.wr GB).q = 1) ∨
      (v = 0#128 ∧ R = Res.unit)
  mono _ _ _ _ _ _ h := h

theorem unit_q (x : Loc) : (Res.unit.wr x).q = 0 := rfl

theorem psiT_impure (P : SP) (v : Val) : ¬ Pred.Pure (psiT P) v := fun h => by
  rcases h default 1 with ⟨-, ⟨⟨h1, -⟩, -⟩ | ⟨⟨h1, -⟩, -⟩⟩ | ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩
  · exact absurd h1 (by rw [unit_q]; decide)
  · exact absurd h1 (by rw [unit_q]; decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by rw [unit_q]; decide)

theorem psiH_pure_zero (P : SP) : Pred.Pure (psiH P) 0#128 := fun _ _ => .inr ⟨rfl, rfl⟩

/-- `psiH` is pure only at `0`. -/
theorem psiH_pure (P : SP) {v : Val} (h : Pred.Pure (psiH P) v) : v = 0#128 := by
  rcases h default 0 with ⟨-, h1, -⟩ | ⟨rfl, -⟩
  · exact absurd h1 (by rw [unit_q]; decide)
  · rfl

/-- **The release predicates**: `psiT` at `T`, `psiH` at `H`, `emp` elsewhere. -/
def relS (P : SP) (x : Loc) : Pred := if x = P.T then psiT P else if x = P.H then psiH P else Pred.emp

theorem relS_T (P : SP) : relS P P.T = psiT P := by simp [relS]

theorem relS_H {P : SP} (hL : SpscLocs P) : relS P P.H = psiH P := by simp [relS, hL.h_t]

theorem relS_other {P : SP} {x : Loc} (hT : x ≠ P.T) (hH : x ≠ P.H) : relS P x = Pred.emp := by
  simp [relS, hT, hH]

theorem relS_B0 {P : SP} (hL : SpscLocs P) : relS P P.B0 = Pred.emp := relS_other hL.b0_t hL.b0_h

theorem relS_B1 {P : SP} (hL : SpscLocs P) : relS P P.B1 = Pred.emp := relS_other hL.b1_t hL.b1_h

/-! ## The plans -/

/-- The producer's plan: `T := 1` gives `B0`, `GA`, `GB`; `T := 0` gives `B1`. -/
def prodPlan (P : SP) : Plan :=
  ⟨[{ loc := P.T, val := some 1#128, gives := [P.B0, GA, GB] }, { loc := P.T, val := some 0#128, gives := [P.B1] }]⟩

/-- The consumer's plan: `H := 1` gives `B0`, `GB`. -/
def consPlan (P : SP) : Plan := ⟨[{ loc := P.H, val := some 1#128, gives := [P.B0, GB] }]⟩

theorem prodPlan_valid {P : SP} (hL : SpscLocs P) : (prodPlan P).Valid := by
  intro e he
  simp only [prodPlan, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm hL.b0_t, ne_ga, ne_gb⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Ne.symm hL.b1_t

theorem consPlan_valid {P : SP} (hL : SpscLocs P) : (consPlan P).Valid := by
  intro e he
  simp only [consPlan, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨Ne.symm hL.b0_h, ne_gb⟩

/-! ## Initial resources -/

/-- The producer's initial fractions: `T`, `B0`, `B1`, `GA`. -/
def prodFrac (P : SP) (x : Loc) : Rat := if x = P.T ∨ x = P.B0 ∨ x = P.B1 ∨ x = GA then 1 else 0

/-- The consumer's initial fractions: `H`, `GB`. -/
def consFrac (P : SP) (x : Loc) : Rat := if x = P.H ∨ x = GB then 1 else 0

theorem prodFrac_nonneg (P : SP) (x : Loc) : 0 ≤ prodFrac P x := by unfold prodFrac; split <;> decide
theorem consFrac_nonneg (P : SP) (x : Loc) : 0 ≤ consFrac P x := by unfold consFrac; split <;> decide

/-- The producer's initial resource: its fractions at the initial messages,
and the acquire id `1` of `H`. -/
def prodRes (m : Memory) (P : SP) : Res :=
  ⟨(Res.initOf m (prodFrac P) (prodFrac_nonneg P)).wr, fun x ι => if x = P.H ∧ ι = 1 then 1 else 0⟩

/-- The consumer's initial resource: its fractions at the initial messages,
and the acquire id `0` of `T`. -/
def consRes (m : Memory) (P : SP) : Res :=
  ⟨(Res.initOf m (consFrac P) (consFrac_nonneg P)).wr, fun x ι => if x = P.T ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: thread `0` the producer, thread `1` the
consumer. -/
def spscRes (m : Memory) (P : SP) (i : Nat) : Res :=
  if i = 0 then prodRes m P else if i = 1 then consRes m P else Res.unit

/-! ## The initial ghost -/

/-- **The initial ghost**: `relS`; acquire ids `0` (`psiT`) and `1`
(`psiH`); `T`'s initial message in release mode with the empty slot of id
`0`. -/
def spscGhost (P : SP) : Ghost := initGhostAcq (relS P) [psiT P, psiH P] [P.T] [(P.T, 0, Res.unit)]

theorem spscGhost_rel (P : SP) : (spscGhost P).rel = relS P := rfl

theorem pend_spscGhost {P : SP} : ∀ ts, ts ∉ (spscGhost P).pend := fun _ h => by cases h

theorem spscGhost_len (P : SP) : (spscGhost P).acqTab.length = 2 := rfl
theorem spscGhost_pred0 (P : SP) : (spscGhost P).acqPred 0 = psiT P := rfl
theorem spscGhost_pred1 (P : SP) : (spscGhost P).acqPred 1 = psiH P := rfl

/-! ## Initial erasure -/

section Init

variable {sP sC : isa.State} {initMem : List (Loc × Val)}

/-- The initial total: the producer's and the consumer's resources (the slot
is empty). -/
theorem total_spscInit (P : SP) (m : Memory) :
    total (spscRes m P) (spscGhost P) (Config.init [sP, sC] initMem) = (prodRes m P).op (consRes m P) := by
  simp only [total, Config.init_size, threadsRes, Ghost.slotsRes, spscGhost, initGhostAcq, List.map_cons,
    List.map_nil, List.length_cons, List.length_nil]
  show (Res.prod [spscRes m P 0, spscRes m P 1]).op (Res.prod [Res.unit]) = _
  simp [spscRes, Res.op_unit, Res.prod]

theorem total_spscInit_q (P : SP) (m : Memory) (x : Loc) :
    ((total (spscRes m P) (spscGhost P) (Config.init [sP, sC] initMem)).wr x).q = prodFrac P x + consFrac P x := by
  rw [total_spscInit]; rfl

theorem total_spscInit_acq (P : SP) (m : Memory) (x : Loc) (ι : PredId) :
    (total (spscRes m P) (spscGhost P) (Config.init [sP, sC] initMem)).acq x ι =
      (if x = P.H ∧ ι = 1 then 1 else 0) + (if x = P.T ∧ ι = 0 then 1 else 0) := by
  rw [total_spscInit]; rfl

theorem frac_sum_le {P : SP} (hL : SpscLocs P) (x : Loc) : prodFrac P x + consFrac P x ≤ 1 := by
  unfold prodFrac consFrac
  by_cases hH : x = P.H
  · subst hH
    simp [hL.h_t, Ne.symm hL.b0_h, Ne.symm hL.b1_h]
    grind
  · by_cases hG : x = GB
    · subst hG
      have h1 : GB ≠ P.T := Ne.symm ne_gb
      have h2 : GB ≠ P.B0 := Ne.symm ne_gb
      have h3 : GB ≠ P.B1 := Ne.symm ne_gb
      simp only [h1, h2, h3, show GB ≠ GA from Ne.symm ga_gb, false_or, or_true, ↓reduceIte]
      grind
    · simp only [hH, hG, or_self, ↓reduceIte]
      split <;> grind

/-- **Initial erasure of the SPSC ring** (initial `tail` and `head` `0`). -/
theorem erase_spscInit {P : SP} (hL : SpscLocs P) (T : Nat → Prop)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    Erase (spscRes (Config.init [sP, sC] initMem).mem P) (spscGhost P) T (Config.init [sP, sC] initMem) := by
  have hq := total_spscInit_q (sP := sP) (sC := sC) (initMem := initMem) P (Config.init [sP, sC] initMem).mem
  have ha := total_spscInit_acq (sP := sP) (sC := sC) (initMem := initMem) P (Config.init [sP, sC] initMem).mem
  have hHT := hL.h_t
  have hids : ∀ x, (spscGhost P).acqIds
      (total (spscRes (Config.init [sP, sC] initMem).mem P) (spscGhost P) (Config.init [sP, sC] initMem)).acq x =
        if x = P.T then [0] else if x = P.H then [1] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [spscGhost_len]
    by_cases hx : x = P.T
    · subst hx; simp [ha, Ne.symm hHT, List.range_succ]
    · by_cases hx' : x = P.H
      · subst hx'; simp [ha, hHT, List.range_succ]
      · simp [ha, hx, hx', List.range_succ]
  have ht := total_spscInit (sP := sP) (sC := sC) (initMem := initMem) P (Config.init [sP, sC] initMem).mem
  unfold spscGhost at hq ha hids ht ⊢
  refine erase_initGhostAcq T (by simp) ⟨fun x => by rw [hq]; exact frac_sum_le hL x,
    fun x ι => by rw [ha]; split <;> split <;> grind⟩ ?_ ?_ ?_ ?_ (by simp) ?_ (by simp) ?_
  · -- held ids
    intro x ι h
    rw [ha] at h
    show ι < 2
    split at h <;> split at h
    · next h1 h2 => exact absurd (h1.1.symm.trans h2.1) hHT
    · next h1 _ => rw [h1.2]; decide
    · next _ h2 => rw [h2.2]; decide
    · exact absurd h (by decide)
  · -- the release predicates split
    intro x v m V r h
    rw [Ghost.acqPreds, hids]
    by_cases hx : x = P.T
    · subst hx
      simp only [↓reduceIte, List.map_cons, List.map_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, by rw [← relS_T]; exact h, rfl⟩
    · by_cases hx' : x = P.H
      · subst hx'
        simp only [hx, ↓reduceIte, List.map_cons, List.map_nil]
        exact ⟨r, Res.unit, (Res.op_unit r).symm, by rw [← relS_H hL]; exact h, rfl⟩
      · simp only [hx, hx', ↓reduceIte, List.map_nil]
        rw [relS_other hx hx'] at h
        exact h
  · -- write sets
    intro x hpos p
    rw [ht] at hpos ⊢
    show (0 < prodFrac P x ∧ p = _) ∨ (0 < consFrac P x ∧ p = _) ↔ _
    have h0 := prodFrac_nonneg P x
    have h1 := consFrac_nonneg P x
    change 0 < prodFrac P x + consFrac P x at hpos
    constructor
    · rintro (⟨-, rfl⟩ | ⟨-, rfl⟩) <;> rfl
    · rintro rfl
      by_cases hp : 0 < prodFrac P x
      · exact .inl ⟨hp, rfl⟩
      · exact .inr ⟨by grind, rfl⟩
  · -- relaxed initial messages are pure
    intro x hx
    have hne : x ≠ P.T := fun he => hx (by simp [he])
    show Pred.Pure (relS P x) _
    by_cases hx' : x = P.H
    · subst hx'; rw [relS_H hL, hH0]; exact psiH_pure_zero P
    · rw [relS_other hne hx']; exact Pred.emp_pure _
  · -- the held ids are the slots
    intro x hx ι
    simp only [List.mem_singleton] at hx
    subst hx
    rw [ha]
    simp [Ne.symm hHT, eq_comm]
  · -- the slot's predicate at view `0`
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    show (psiT P).P _ _ 0 Res.unit
    rw [hT0]
    exact .inr ⟨rfl, .inl ⟨rfl, rfl⟩⟩

end Init

end Kraken.Promising.X64.EnvG.SpscX

#print axioms Kraken.Promising.X64.EnvG.SpscX.erase_spscInit
