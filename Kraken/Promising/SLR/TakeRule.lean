/-
**Prototype.** The *take rule* under option (S): a
load-acquire that reads a release message `(l, ts)` moves the resource `R` of
the thread's own slot `(l, ts), ι` into the thread, swapping its acquire id
`ι` for a fresh `ι'` (option (S)).

## The swap (`takeGhost`, `takeRes`)

- The fresh id `ι' = g.acqTab.length` gets the predicate
  `(g.acqPred ι).takeAt ts`: `φ`, relaxed at the taken message only (it also
  accepts the unit resource at timestamp `ts`). `φ ⊆ φ'`, so the world
  condition `Erase.relAcq` survives the swap.
- Every slot `(k, ι)` of `l` is renamed `(k, ι')` with the same resource;
  the slot of the taken message keeps a unit resource. Slots of other
  locations, and slots of other ids, are untouched.
- The thread's resource drops `(l, ι)`, gains `(l, ι')` and `R`.

## What is proved here (the reach side)

- `CanAcqB.rename` / `reachB.rename`: bounded reach along a slot renaming
  (a `g'` slot is covered by a `g` slot at the same message whose id is the
  renamed-back id); the generalisation of `CanAcqB.cover` that renaming
  needs (`cover` asks `g'.u ⊆ g.u` below the bound, which renaming breaks).
- `takeFrameS`: **K2 under option (S)**: no resource whose acquire ids are
  all allocated in `g` (`AllocIds g`) gains bounded reach. It fails for the
  unscoped frame `K2₀` exactly at a `ρ` holding `ι'`.
- `takeOwn`: **K1**: the taking thread's bounded reach through messages
  `≤ b` does not grow once `ts ≤ b` (an acquire load puts `ts` below the
  floor, `AcqStep.le_wfloor`).
- `takeMayWrite`: the `acqLe` conjunct of `WpPostR` (unbounded reach).
- `RStepS` (the scoped analogue of `RStep`), `RStep.toS`, `RStepS.trans`,
  `RStepS.take`.

## The erasure law

- `TakeEraseLaw`: erasure is preserved by the swap (`Erase` at
  `(setRes rF tid (takeRes …), takeGhost …)`), for a taking thread exempt
  from promise validity (`T tid`, as `NPSafe`'s weak erasure). Proved in
  `SLR/TakeRuleErase.lean` (`Erase.take`, `takeEraseLaw`).

Nothing imports this file.
-/
import Kraken.Promising.SLR.ReachRules
import Kraken.Promising.SLR.NPSafePInst

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

private theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

private theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

private theorem le_sum_of_mem' {L : List Nat} {a : Nat} (h : a ∈ L) : a ≤ L.sum := by
  induction L with
  | nil => cases h
  | cons x L ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- An unbounded chain whose slots are all at or below `b` is bounded by `b`. -/
theorem CanAcq.toB {u : List Slot} {U : Loc → List PredId} {A : Loc → PredId → Nat} {b : Time}
    (hb : ∀ s ∈ u, s.key.2 ≤ b) {k : Key} {ι : PredId} (h : CanAcq u U A k ι) : CanAcqB u U A b k ι := by
  induction h with
  | base hs ha => exact .base hs (hb _ hs) ha
  | upd hs hu => exact .upd hs (hb _ hs) hu
  | step _ hs₁ hs₂ ha ih => exact .step ih hs₁ hs₂ (hb _ hs₂) ha

/-! ## The swap -/

/-- `φ` relaxed at the taken message: it also accepts the unit resource at
timestamp `ts` (a slot predicate's view is its message's timestamp). -/
def Pred.takeAt (φ : Pred) (ts : Time) : Pred where
  P v m V r := (V = ts ∧ r = Res.unit) ∨ φ.P v m V r
  mono v m m' V r hm h := h.imp id (φ.mono v m m' V r hm)

theorem Pred.le_takeAt (φ : Pred) (ts : Time) {v : Val} {m : Memory} {V : View} {r : Res} (h : φ.P v m V r) :
    (φ.takeAt ts).P v m V r := .inr h

/-- One slot under the swap: a slot of `l` with id `ι` is renamed `ι'`; the
slot of the taken message `(l, ts)` keeps a unit resource. -/
def takeSlot (l : Loc) (ι ι' : PredId) (ts : Time) (s : Slot) : Slot :=
  if s.key.1 = l ∧ s.id = ι then
    { key := s.key, id := ι', res := if s.key.2 = ts then Res.unit else s.res }
  else s

/-- The ghost after taking the slot `((l, ts), ι)`: the fresh id
`g.acqTab.length` is allocated with `(g.acqPred ι).takeAt ts`, and the
slots of `(l, ι)` are renamed to it. -/
def takeGhost (g : Ghost) (l : Loc) (ι : PredId) (ts : Time) : Ghost :=
  { g with
    acqTab := g.acqTab ++ [(g.acqPred ι).takeAt ts]
    u := g.u.map (takeSlot l ι g.acqTab.length ts) }

/-- `r` with the acquire id `ι` of `l` swapped for `ι'`. -/
def swapAcq (r : Res) (l : Loc) (ι ι' : PredId) : Res where
  wr := r.wr
  acq x j := if x = l ∧ j = ι then 0 else if x = l ∧ j = ι' then 1 else r.acq x j

/-- The taking thread's resource: `(l, ι)` swapped for `(l, ι')`, plus the
taken slot resource `R`. -/
def takeRes (r : Res) (l : Loc) (ι ι' : PredId) (R : Res) : Res := (swapAcq r l ι ι').op R

/-- Renaming back: `(l, ι')` came from `(l, ι)`. -/
def takeBk (l : Loc) (ι ι' : PredId) (y : Loc) (j : PredId) : PredId := if y = l ∧ j = ι' then ι else j

theorem takeGhost_le (g : Ghost) (l : Loc) (ι : PredId) (ts : Time) : g.Le (takeGhost g l ι ts) :=
  ⟨rfl, List.prefix_append _ _, fun _ => List.prefix_refl _⟩

theorem takeGhost_length (g : Ghost) (l : Loc) (ι : PredId) (ts : Time) :
    (takeGhost g l ι ts).acqTab.length = g.acqTab.length + 1 := by
  simp [takeGhost]

/-- Old ids keep their predicates. -/
theorem takeGhost_acqPred_old {g : Ghost} {l : Loc} {ι j : PredId} {ts : Time} (hj : j < g.acqTab.length) :
    (takeGhost g l ι ts).acqPred j = g.acqPred j := by
  simp only [Ghost.acqPred, takeGhost, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

/-- The fresh id has the relaxed predicate. -/
theorem takeGhost_acqPred_new (g : Ghost) (l : Loc) (ι : PredId) (ts : Time) :
    (takeGhost g l ι ts).acqPred g.acqTab.length = (g.acqPred ι).takeAt ts := by
  simp [Ghost.acqPred, takeGhost]

/-! ## Bounded reach along a renaming -/

/-- `a` is covered by `b`: every acquire id and every positive write
permission of `a` is one of `b`. -/
def ResCov (a b : Res) : Prop := (∀ y j, 1 ≤ a.acq y j → 1 ≤ b.acq y j) ∧ ∀ y, 0 < (a.wr y).q → 0 < (b.wr y).q

theorem ResCov.refl (a : Res) : ResCov a a := ⟨fun _ _ h => h, fun _ h => h⟩

theorem ResCov.unit (a : Res) : ResCov Res.unit a :=
  ⟨fun _ _ h => by simp [Res.unit] at h, fun _ h => by simp [Res.unit, Perm.unit] at h⟩

/-- **Bounded `canAcq` along a slot renaming.** Every `g'` slot at or below
`b` is covered by a `g` slot at the same message whose id is the renamed-back
id `bk`; no `g` slot resource holds a renamed id (`hbk`); update ids are
kept and not renamed; every id of `A'` is (renamed back) held by `A` or by a
slot `A` may acquire. Then a bounded chain at `g'` from `A'` renames back to
one at `g` from `A`. -/
theorem CanAcqB.rename {g g' : Ghost} {A A' : Loc → PredId → Nat} {b : Time} (bk : Loc → PredId → PredId)
    (hu : ∀ s' ∈ g'.u, s'.key.2 ≤ b →
      ∃ s ∈ g.u, s.key = s'.key ∧ s.id = bk s'.key.1 s'.id ∧ ResCov s'.res s.res)
    (hbk : ∀ s ∈ g.u, ∀ y j, 1 ≤ s.res.acq y j → bk y j = j)
    (hU : ∀ y j, j ∈ g'.upd y → j ∈ g.upd y ∧ bk y j = j)
    (hA : ∀ y j, 1 ≤ A' y j → 1 ≤ A y (bk y j) ∨
      ∃ s ∈ g.u, CanAcqB g.u g.upd A b s.key s.id ∧ 1 ≤ s.res.acq y (bk y j))
    {k : Key} {j : PredId} (h : CanAcqB g'.u g'.upd A' b k j) : CanAcqB g.u g.upd A b k (bk k.1 j) := by
  induction h with
  | @base s' hs' hk ha =>
    obtain ⟨s, hs, hkey, hid, -⟩ := hu s' hs' hk
    have hk' : s.key.2 ≤ b := by rw [hkey]; exact hk
    rcases hA _ _ ha with ha | ⟨s₀, hs₀, hc₀, ha₀⟩
    · have := CanAcqB.base (U := g.upd) (A := A) (b := b) hs hk' (by rw [hid, hkey]; exact ha)
      rwa [hid, hkey] at this
    · have := CanAcqB.step hc₀ hs₀ hs hk' (by rw [hid, hkey]; exact ha₀)
      rwa [hid, hkey] at this
  | @upd s' hs' hk hU' =>
    obtain ⟨s, hs, hkey, hid, -⟩ := hu s' hs' hk
    obtain ⟨hU1, hb⟩ := hU _ _ hU'
    have hk' : s.key.2 ≤ b := by rw [hkey]; exact hk
    have := CanAcqB.upd (A := A) hs hk' (by rw [hid, hkey, hb]; exact hU1)
    rwa [hid, hkey] at this
  | @step s₁' s₂' h₁ hs₁' hs₂' hk ha ih =>
    obtain ⟨s₁, hs₁, hkey₁, hid₁, hcov₁⟩ := hu s₁' hs₁' h₁.key_le
    obtain ⟨s₂, hs₂, hkey₂, hid₂, -⟩ := hu s₂' hs₂' hk
    have ha₁ := hcov₁.1 _ _ ha
    have hb2 := hbk s₁ hs₁ _ _ ha₁
    have hk' : s₂.key.2 ≤ b := by rw [hkey₂]; exact hk
    rw [← hid₁, ← hkey₁] at ih
    have := CanAcqB.step ih hs₁ hs₂ hk' (by rw [hid₂, hkey₂, hb2]; exact ha₁)
    rwa [hid₂, hkey₂] at this

/-- **Bounded reach along a slot renaming** (`CanAcqB.rename`, plus: every
write permission of `r'` is in `r`'s bounded reach at `g`). -/
theorem reachB.rename {g g' : Ghost} {r r' : Res} {b : Time} (bk : Loc → PredId → PredId)
    (hu : ∀ s' ∈ g'.u, s'.key.2 ≤ b →
      ∃ s ∈ g.u, s.key = s'.key ∧ s.id = bk s'.key.1 s'.id ∧ ResCov s'.res s.res)
    (hbk : ∀ s ∈ g.u, ∀ y j, 1 ≤ s.res.acq y j → bk y j = j)
    (hU : ∀ y j, j ∈ g'.upd y → j ∈ g.upd y ∧ bk y j = j)
    (hA : ∀ y j, 1 ≤ r'.acq y j → 1 ≤ r.acq y (bk y j) ∨
      ∃ s ∈ g.u, CanAcqB g.u g.upd r.acq b s.key s.id ∧ 1 ≤ s.res.acq y (bk y j))
    (hW : ∀ x, 0 < (r'.wr x).q → reachB r g x b) {x : Loc} (h : reachB r' g' x b) : reachB r g x b := by
  rcases h with h | ⟨s', hs', hk, hc, hq⟩
  · exact hW x h
  · obtain ⟨s, hs, hkey, hid, hcov⟩ := hu s' hs' hk
    have hc' := hc.rename bk hu hbk hU hA
    rw [← hid, ← hkey] at hc'
    exact .inr ⟨s, hs, by rw [hkey]; exact hk, hc', hcov.2 x hq⟩

/-! ## The take's slots under renaming -/

section Take

variable {g : Ghost} {l : Loc} {ι : PredId} {ts : Time}

/-- Every slot after the take is covered by its origin. Needs: no slot of
`g` has the fresh id (`Erase.slotIds`). -/
theorem takeGhost_cov (hfresh : ∀ s ∈ g.u, s.id ≠ g.acqTab.length) :
    ∀ s' ∈ (takeGhost g l ι ts).u, ∃ s ∈ g.u, s.key = s'.key ∧
      s.id = takeBk l ι g.acqTab.length s'.key.1 s'.id ∧ ResCov s'.res s.res := by
  intro s' hs'
  simp only [takeGhost, List.mem_map] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  refine ⟨s, hs, ?_⟩
  unfold takeSlot
  by_cases h : s.key.1 = l ∧ s.id = ι
  · rw [ite_t h]
    refine ⟨rfl, ?_, ?_⟩
    · unfold takeBk; rw [ite_t ⟨h.1, rfl⟩]; exact h.2
    · by_cases ht : s.key.2 = ts
      · rw [ite_t ht]; exact ResCov.unit _
      · rw [ite_f ht]; exact ResCov.refl _
  · rw [ite_f h]
    refine ⟨rfl, ?_, ResCov.refl _⟩
    unfold takeBk
    rw [ite_f]
    rintro ⟨-, he⟩
    exact hfresh s hs he

/-- No slot resource of `g` holds the fresh id at `l` (`Erase.acqIds`):
renaming back is the identity on what slot resources hold. -/
theorem takeBk_slot (hfree : ∀ s ∈ g.u, s.res.acq l g.acqTab.length = 0) :
    ∀ s ∈ g.u, ∀ y j, 1 ≤ s.res.acq y j → takeBk l ι g.acqTab.length y j = j := by
  intro s hs y j h
  unfold takeBk
  split
  · next he =>
    obtain ⟨h1, h2⟩ := he
    subst h1 h2
    exact absurd (hfree s hs) (by omega)
  · rfl

/-- Update ids are allocated, so never the fresh id. -/
theorem takeBk_upd (hupd : ∀ j ∈ g.upd l, j < g.acqTab.length) :
    ∀ y j, j ∈ (takeGhost g l ι ts).upd y → j ∈ g.upd y ∧ takeBk l ι g.acqTab.length y j = j := by
  intro y j hj
  refine ⟨hj, ?_⟩
  unfold takeBk
  split
  · next he =>
    obtain ⟨h1, h2⟩ := he
    subst h1 h2
    exact absurd (hupd _ hj) (Nat.lt_irrefl _)
  · rfl

/-- **K2 of the take under option (S).** No resource whose acquire ids are
all allocated in `g` gains bounded reach, for any bound. (For `K2₀` this
fails exactly at a `ρ` holding the fresh id `ι'`, which reaches the renamed
slots at old messages.) -/
theorem takeFrameS (hfresh : ∀ s ∈ g.u, s.id ≠ g.acqTab.length)
    (hfree : ∀ s ∈ g.u, s.res.acq l g.acqTab.length = 0) (hupd : ∀ j ∈ g.upd l, j < g.acqTab.length)
    (b : Time) (ρ : Res) (hρ : AllocIds g ρ) (x : Loc) (h : reachB ρ (takeGhost g l ι ts) x b) :
    reachB ρ g x b := by
  refine reachB.rename (takeBk l ι g.acqTab.length) (fun s' hs' _ => takeGhost_cov hfresh s' hs')
    (takeBk_slot hfree) (takeBk_upd hupd) (fun y j ha => .inl ?_) (fun _ h => .inl h) h
  unfold takeBk
  split
  · next he =>
    obtain ⟨h1, h2⟩ := he
    subst h1 h2
    exact absurd (hρ _ _ ha) (Nat.lt_irrefl _)
  · exact ha

/-- **K1 of the take.** The taking thread held `ι` for `l` and the taken
slot `((l, ts), ι, R)`; through messages up to any `b ≥ ts` its bounded
reach after the take is covered by the one before (the renamed slots by `ι`,
the taken resource by the taken slot). -/
theorem takeOwn (hfresh : ∀ s ∈ g.u, s.id ≠ g.acqTab.length)
    (hfree : ∀ s ∈ g.u, s.res.acq l g.acqTab.length = 0) (hupd : ∀ j ∈ g.upd l, j < g.acqTab.length)
    {r R : Res} (hι : 1 ≤ r.acq l ι) (hιlt : ι < g.acqTab.length) (hs : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u)
    {b : Time} (hts : ts ≤ b) (x : Loc) (h : reachB (takeRes r l ι g.acqTab.length R) (takeGhost g l ι ts) x b) :
    reachB r g x b := by
  have hT : CanAcqB g.u g.upd r.acq b (l, ts) ι := .base (s := ⟨(l, ts), ι, R⟩) hs hts hι
  refine reachB.rename (takeBk l ι g.acqTab.length) (fun s' hs' _ => takeGhost_cov hfresh s' hs')
    (takeBk_slot hfree) (takeBk_upd hupd) (fun y j ha => ?_) (fun y hy => ?_) h
  · simp only [takeRes, Res.op, swapAcq] at ha
    by_cases h1 : y = l ∧ j = ι
    · obtain ⟨h1, h2⟩ := h1
      subst h1 h2
      rw [ite_t ⟨rfl, rfl⟩] at ha
      have hne : takeBk y j g.acqTab.length y j = j := by
        unfold takeBk
        split
        · next he => exact absurd he.2 (Nat.ne_of_lt hιlt)
        · rfl
      refine .inr ⟨⟨(y, ts), j, R⟩, hs, hT, ?_⟩
      rw [hne]
      simp only at ha ⊢
      omega
    · rw [ite_f h1] at ha
      by_cases h2 : y = l ∧ j = g.acqTab.length
      · obtain ⟨h2, h3⟩ := h2
        subst h2 h3
        left
        unfold takeBk
        rw [ite_t ⟨rfl, rfl⟩]
        exact hι
      · rw [ite_f h2] at ha
        have hbk : takeBk l ι g.acqTab.length y j = j := by
          unfold takeBk; rw [ite_f h2]
        rw [hbk]
        by_cases h3 : 1 ≤ r.acq y j
        · exact .inl h3
        · exact .inr ⟨⟨(l, ts), ι, R⟩, hs, hT, by simp only; omega⟩
  · simp only [takeRes, swapAcq] at hy
    rcases Res.pos_op.mp hy with hy | hy
    · exact .inl hy
    · exact .inr ⟨⟨(l, ts), ι, R⟩, hs, hts, hT, hy⟩

/-- **`acqLe` of the take** (unbounded reach, `WpPostR`'s `mayWrite`
conjunct): `takeOwn` at the bound of the deepest slot. -/
theorem takeMayWrite (hfresh : ∀ s ∈ g.u, s.id ≠ g.acqTab.length)
    (hfree : ∀ s ∈ g.u, s.res.acq l g.acqTab.length = 0) (hupd : ∀ j ∈ g.upd l, j < g.acqTab.length)
    {r R : Res} (hι : 1 ≤ r.acq l ι) (hιlt : ι < g.acqTab.length) (hs : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u)
    (x : Loc) (h : mayWrite (takeRes r l ι g.acqTab.length R) (takeGhost g l ι ts) x) : mayWrite r g x := by
  -- every `CanAcq` chain is a `CanAcqB` chain at the bound `B` of all slot timestamps
  obtain ⟨B, hB⟩ : ∃ B, ts ≤ B ∧ ∀ s ∈ (takeGhost g l ι ts).u, s.key.2 ≤ B := by
    refine ⟨ts + ((takeGhost g l ι ts).u.map (·.key.2)).sum, Nat.le_add_right _ _, fun s hs => ?_⟩
    have := le_sum_of_mem' (List.mem_map_of_mem (f := fun s : Slot => s.key.2) hs)
    omega_t
  refine reachB_mayWrite (takeOwn hfresh hfree hupd hι hιlt hs hB.1 x ?_)
  rcases h with h | ⟨s, hs', hc, hq⟩
  · exact .inl h
  · exact .inr ⟨s, hs', hB.2 s hs', hc.toB hB.2, hq⟩

end Take

/-! ## `RStep` with option (S)'s frame -/

/-- K2 restricted to resources whose acquire ids are allocated in `g`
(option (S); `K2Scope (model I) AllocIds g g' B` unfolded). -/
def ReachFrameS (g g' : Ghost) (B : Time) : Prop :=
  ∀ b, b ≤ B → ∀ ρ, AllocIds g ρ → ∀ x, reachB ρ g' x b → reachB ρ g x b

theorem ReachFrameS.eq_K2Scope (g g' : Ghost) (B : Time) :
    ReachFrameS g g' B = K2Scope (model I) AllocIds g g' B := rfl

/-- **`RStep` with option (S)'s frame**: the acquire table only grows (so
`AllocIds` is stable along an instruction), K2 for allocated resources, K1
as in `RStep`. -/
def RStepS (B : Time) (r : Res) (g : Ghost) (r' : Res) (g' : Ghost) (cx : Ctx) : Prop :=
  g.acqTab.length ≤ g'.acqTab.length ∧ ReachFrameS g g' B ∧
    ∀ b, b ≤ B → cx.views.wfloor ≤ b → ∀ x, reachB r' g' x b → reachB r g x b

/-- Every existing event rule's `RStep` is an `RStepS` (its ghost changes
keep the acquire table). -/
theorem RStep.toS {B : Time} {r r' : Res} {g g' : Ghost} {cx : Ctx} (h : RStep B r g r' g' cx)
    (hlen : g.acqTab.length ≤ g'.acqTab.length) : RStepS B r g r' g' cx :=
  ⟨hlen, fun b hb ρ _ x hx => h.1 b hb ρ x hx, h.2⟩

theorem RStepS.trans {B : Time} {r r₁ r₂ : Res} {g g₁ g₂ : Ghost} {cx cx' : Ctx} (h₁ : RStepS B r g r₁ g₁ cx)
    (h₂ : RStepS B r₁ g₁ r₂ g₂ cx') (hf : cx.views.wfloor ≤ cx'.views.wfloor) : RStepS B r g r₂ g₂ cx' :=
  ⟨Nat.le_trans h₁.1 h₂.1,
    fun b hb ρ hρ x hx => h₁.2.1 b hb ρ hρ x
      (h₂.2.1 b hb ρ (fun y j hj => Nat.lt_of_lt_of_le (hρ y j hj) h₁.1) x hx),
    fun b hb hb' x hx => h₁.2.2 b hb (Nat.le_trans hf hb') x (h₂.2.2 b hb hb' x hx)⟩

/-- **The take as an `RStepS`**, at a context whose floor is at least the
taken timestamp (`AcqStep.le_wfloor` after a non-forwarded acquire load). -/
theorem RStepS.take {g : Ghost} {l : Loc} {ι : PredId} {ts : Time} {r R : Res} {B : Time} {cx : Ctx}
    (hfresh : ∀ s ∈ g.u, s.id ≠ g.acqTab.length)
    (hfree : ∀ s ∈ g.u, s.res.acq l g.acqTab.length = 0) (hupd : ∀ j ∈ g.upd l, j < g.acqTab.length)
    (hι : 1 ≤ r.acq l ι) (hιlt : ι < g.acqTab.length) (hs : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u)
    (hfl : ts ≤ cx.views.wfloor) :
    RStepS B r g (takeRes r l ι g.acqTab.length R) (takeGhost g l ι ts) cx :=
  ⟨by rw [takeGhost_length]; exact Nat.le_succ _,
    fun b _ ρ hρ x hx => takeFrameS hfresh hfree hupd b ρ hρ x hx,
    fun _ _ hb x hx => takeOwn hfresh hfree hupd hι hιlt hs (Nat.le_trans hfl hb) x hx⟩

/-- An acquire load (not forwarded from the thread's own write) puts the
taken timestamp below the floor of the context after it. -/
theorem take_floor_of_acqStep {A : Arch} {iv : InstrViews} {c₀ cx : Ctx} {ts : Time}
    (h : AcqStep A iv c₀ cx ts) : ts ≤ cx.views.wfloor :=
  h.le_wfloor

/-! ## The hypotheses from erasure -/

section FromErase

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

theorem Erase.take_fresh (E : Erase rF g T c) : ∀ s ∈ g.u, s.id ≠ g.acqTab.length :=
  fun s hs he => absurd (he ▸ E.slotIds s hs) (Nat.lt_irrefl _)

theorem Erase.take_upd (E : Erase rF g T c) (l : Loc) : ∀ j ∈ g.upd l, j < g.acqTab.length :=
  fun j hj => ((E.updIds l).2 j hj).1

/-- A slot resource is part of the total resource. -/
theorem slotsRes_acq_le {g : Ghost} {s : Slot} (hs : s ∈ g.u) (y : Loc) (j : PredId) :
    s.res.acq y j ≤ g.slotsRes.acq y j := by
  unfold Ghost.slotsRes
  have hm : s.res ∈ g.u.map (·.res) := List.mem_map_of_mem hs
  generalize g.u.map (·.res) = L at hm
  induction L with
  | nil => cases hm
  | cons a L ih =>
    simp only [Res.prod_cons, Res.op]
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · have := ih hm; omega

theorem Erase.take_free (E : Erase rF g T c) (l : Loc) : ∀ s ∈ g.u, s.res.acq l g.acqTab.length = 0 := by
  intro s hs
  rcases Nat.eq_zero_or_pos (s.res.acq l g.acqTab.length) with h0 | hne
  · exact h0
  exfalso
  have h1 := slotsRes_acq_le hs l g.acqTab.length
  have h2 := E.acqIds l g.acqTab.length (by
    show 1 ≤ ((threadsRes rF c.threads.size).op g.slotsRes).acq l g.acqTab.length
    simp only [Res.op]; omega)
  omega_t

/-- **K1/K2 of the take from erasure**: at an erased configuration where the
thread holds `ι` for `l` (allocated by `Erase.acqIds`) and the slot
`((l, ts), ι, R)` exists, the take is an `RStepS` at any context whose floor
is at least `ts`. -/
theorem Erase.rStepS_take (E : Erase rF g T c) {l : Loc} {ι : PredId} {ts : Time} {r R : Res} {B : Time}
    {cx : Ctx} (hι : 1 ≤ r.acq l ι) (hιlt : ι < g.acqTab.length) (hs : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u)
    (hfl : ts ≤ cx.views.wfloor) :
    RStepS B r g (takeRes r l ι g.acqTab.length R) (takeGhost g l ι ts) cx :=
  RStepS.take E.take_fresh (E.take_free l) (E.take_upd l) hι hιlt hs hfl

end FromErase

/-! ## The erasure law (statement; proof in `SLR/TakeRuleErase.lean`) -/

/-- **Erasure survives the take** (proved: `takeEraseLaw`). A thread `tid` holding `ι` for `l`
(and whose resource is part of an erased configuration) takes the slot
`((l, ts), ι, R)` of a release message: erasure holds at the swapped
resource and ghost. Clause analysis: `writes`, `pure`,
`relExists`, `promWf`, `pend`, `relSettled`, `claims*` are unchanged (write
permissions, memory, release modes, pending marks and claims are unchanged);
`valid`, `acqIds`, `slotIds`, `updIds` follow from the total resource
changing only by `(l, ι) ↦ (l, ι')`; `slotsNodup`, `slotsDom` from the
renaming being injective on `(key, id)` and `slotsDom` for `ι` before;
`slotsPred` from `φ ⊆ φ.takeAt ts` and the unit disjunct at `ts`;
`promValid` from `(l, ι)` being held by `tid` alone (no other chain passes
through a renamed slot; `tid` itself is exempt, `T tid`); `relAcq` needs `SepList` to be invariant under
permutation and monotone in each predicate (the held list loses `φ` at
`ι` and gains `φ.takeAt ts` at the end). -/
def TakeEraseLaw (I : ISA) : Prop :=
  ∀ (rF : Nat → Res) (g : Ghost) (T : Nat → Prop) (c : Config I) (tid : Nat) (r R : Res) (l : Loc)
    (ι : PredId) (ts : Time),
    Erase (setRes rF tid r) g T c → tid < c.threads.size → T tid → 1 ≤ r.acq l ι →
    (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u →
    Erase (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) T c

#print axioms CanAcqB.rename
#print axioms takeFrameS
#print axioms takeOwn
#print axioms takeMayWrite
#print axioms RStepS.take
#print axioms Erase.rStepS_take

end Kraken.Promising.SLR
