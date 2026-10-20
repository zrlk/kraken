/-
The resource algebra of the SLR-adapted resource model: Svendsen et al., *A
separation logic for a promising semantics*
(ESOP 2018, "SLR"), technical appendix §3.1, transferred to Kraken.

SLR's resources are `M = PlnPerm × WrPerm × AcqPerm`. Kraken drops `PlnPerm`
(SLR's non-atomic points-to): the hardware has no non-atomic locations, a
plain `LDR`/`STR` is SLR's relaxed access. What remains:

- `Perm`: a write permission `(π, X)` for one location, a fraction
  `0 ≤ π` with a write set `X` of (value, timestamp) pairs, `π = 0 → X = ∅`;
  composition adds fractions and unions write sets.
- `Res`: a write permission per location and a multiset of acquire
  permission ids (`PredId`) per location. SLR's acquire permissions are
  *sets* composed by disjoint union; multiplicities make composition total
  and validity (`≤ 1`) downward closed.

Composition `Res.op` is total; `Res.valid` (every fraction `≤ 1`, every
multiplicity `≤ 1`) is SLR's definedness. The laws of a partial commutative
monoid hold in this form: `op_assoc`, `op_comm`, `unit_op`, `op_unit`,
`valid_op_left` (validity is downward closed), `valid_unit`.

Predicates (`Pred`) are shallow and world-free: `Val → Memory → View → Res →
Prop`, monotone in the memory (`Memory.Prefix`). SLR stores *syntactic*
assertions in its world to break the circularity world → predicate → world;
here a predicate refers to an acquire permission by id, never by meaning, so
the world (`SLR.Ghost.acqTab`, in `Erasure.lean`) can map ids to predicates
without circularity. What this cannot express: predicates that mention a
location's `Acq`/`Rel` *by meaning* or quantify over predicates (higher-order
protocols, e.g. handing over a lock together with a protocol chosen at run
time). None of the Stage 2 targets (MP, spinlocks, Treiber) needs that.
-/
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising.SLR

/-! ## Write permissions -/

/-- SLR's `WrPerm` at one location: a fraction `q ≥ 0` and a write set `X`,
empty when the fraction is `0`. -/
structure Perm where
  q : Rat
  X : Val × Time → Prop
  nonneg : 0 ≤ q
  zero : q = 0 → ∀ p, ¬ X p

namespace Perm

@[ext] theorem ext {a b : Perm} (hq : a.q = b.q) (hX : a.X = b.X) : a = b := by
  cases a; cases b; simp only at hq hX; subst hq hX; rfl

/-- No permission: `(0, ∅)`. -/
def unit : Perm := ⟨0, fun _ => False, Rat.le_refl, fun _ _ h => h⟩

/-- `(π₁, X₁) • (π₂, X₂) = (π₁ + π₂, X₁ ∪ X₂)`. -/
def op (a b : Perm) : Perm where
  q := a.q + b.q
  X p := a.X p ∨ b.X p
  nonneg := by have := a.nonneg; have := b.nonneg; grind
  zero h p hp := by
    have ha := a.nonneg; have hb := b.nonneg
    have h1 : a.q = 0 := by grind
    have h2 : b.q = 0 := by grind
    rcases hp with hp | hp
    · exact a.zero h1 p hp
    · exact b.zero h2 p hp

theorem op_assoc (a b c : Perm) : (a.op b).op c = a.op (b.op c) := by
  apply ext
  · exact Rat.add_assoc _ _ _
  · simp only [op]; funext p; exact propext or_assoc

theorem op_comm (a b : Perm) : a.op b = b.op a := by
  apply ext
  · exact Rat.add_comm _ _
  · simp only [op]; funext p; exact propext or_comm

theorem unit_op (a : Perm) : unit.op a = a := by
  apply ext
  · exact Rat.zero_add _
  · simp only [op, unit, false_or]

theorem op_unit (a : Perm) : a.op unit = a := by
  rw [op_comm, unit_op]

theorem le_op_left (a b : Perm) : a.q ≤ (a.op b).q := by
  have := b.nonneg; simp only [op]; grind

theorem le_op_right (a b : Perm) : b.q ≤ (a.op b).q := by
  rw [op_comm]; exact le_op_left b a

theorem pos_op {a b : Perm} : 0 < (a.op b).q ↔ 0 < a.q ∨ 0 < b.q := by
  have := a.nonneg; have := b.nonneg; simp only [op]; grind

end Perm

/-! ## Resources -/

/-- A predicate identifier (SLR's `PredId`): an index into the world's table
of acquire predicates. -/
abbrev PredId := Nat

/-- SLR's resources without the non-atomic part: a write permission per
location and a multiset of acquire permission ids per location. -/
structure Res where
  wr : Loc → Perm
  acq : Loc → PredId → Nat

namespace Res

@[ext] theorem ext {a b : Res} (hw : a.wr = b.wr) (ha : a.acq = b.acq) : a = b := by
  cases a; cases b; simp only at hw ha; subst hw ha; rfl

/-- The empty resource `ε`. -/
def unit : Res := ⟨fun _ => Perm.unit, fun _ _ => 0⟩

/-- Composition (total; `valid` is SLR's definedness). -/
def op (a b : Res) : Res := ⟨fun x => (a.wr x).op (b.wr x), fun x ι => a.acq x ι + b.acq x ι⟩

/-- SLR's definedness of a composition: fractions `≤ 1`, acquire ids
disjoint. -/
def valid (a : Res) : Prop := (∀ x, (a.wr x).q ≤ 1) ∧ ∀ x ι, a.acq x ι ≤ 1

theorem op_assoc (a b c : Res) : (a.op b).op c = a.op (b.op c) := by
  apply ext
  · funext x; exact Perm.op_assoc _ _ _
  · funext x ι; exact Nat.add_assoc _ _ _

theorem op_comm (a b : Res) : a.op b = b.op a := by
  apply ext
  · funext x; exact Perm.op_comm _ _
  · funext x ι; exact Nat.add_comm _ _

theorem unit_op (a : Res) : unit.op a = a := by
  apply ext
  · funext x; exact Perm.unit_op _
  · funext x ι; exact Nat.zero_add _

theorem op_unit (a : Res) : a.op unit = a := by
  rw [op_comm, unit_op]

theorem op_left_comm (a b c : Res) : a.op (b.op c) = b.op (a.op c) := by
  rw [← op_assoc, op_comm a b, op_assoc]

/-- Validity is downward closed. -/
theorem valid_op_left {a b : Res} (h : (a.op b).valid) : a.valid :=
  ⟨fun x => Rat.le_trans (Perm.le_op_left _ _) (h.1 x), fun x ι => Nat.le_trans (Nat.le_add_right _ _) (h.2 x ι)⟩

theorem valid_op_right {a b : Res} (h : (a.op b).valid) : b.valid :=
  valid_op_left (op_comm a b ▸ h)

theorem valid_unit : unit.valid :=
  ⟨fun _ => by simp only [unit, Perm.unit]; decide, fun _ _ => Nat.zero_le _⟩

theorem pos_op {a b : Res} {x : Loc} : 0 < ((a.op b).wr x).q ↔ 0 < (a.wr x).q ∨ 0 < (b.wr x).q :=
  Perm.pos_op

/-- The composition of a list of resources, `Π`. -/
def prod (rs : List Res) : Res := rs.foldr op unit

@[simp] theorem prod_nil : prod [] = unit := rfl

@[simp] theorem prod_cons (r : Res) (rs : List Res) : prod (r :: rs) = r.op (prod rs) := rfl

theorem prod_append (rs ss : List Res) : prod (rs ++ ss) = (prod rs).op (prod ss) := by
  induction rs with
  | nil => simp [unit_op]
  | cons r rs ih => simp [ih, op_assoc]

theorem prod_perm {rs ss : List Res} (h : rs.Perm ss) : prod rs = prod ss := by
  induction h with
  | nil => rfl
  | cons r _ ih => simp [ih]
  | swap r s rs => simp [op_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A positive component makes the product positive (fractions are
non-negative). -/
theorem pos_prod_of_mem {rs : List Res} {r : Res} (hr : r ∈ rs) {x : Loc} (h : 0 < (r.wr x).q) :
    0 < ((prod rs).wr x).q := by
  induction rs with
  | nil => cases hr
  | cons s rs ih =>
    rw [prod_cons, pos_op]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact .inl h
    · exact .inr (ih hr)

/-- A component's write set is contained in the product's. -/
theorem X_prod_of_mem {rs : List Res} {r : Res} (hr : r ∈ rs) {x : Loc} {p : Val × Time}
    (h : (r.wr x).X p) : ((prod rs).wr x).X p := by
  induction rs with
  | nil => cases hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact .inl h
    · exact .inr (ih hr)

end Res

/-! ## Predicates -/

/-- A predicate of the logic, as the world stores it: on the value of a
message, the memory, a view (the message's timestamp: Kraken's timestamps are
global, so a release message's view is its own timestamp) and a resource.
Monotone in the memory, as SLR's propositions are upward closed in the
configuration. -/
structure Pred where
  P : Val → Memory → View → Res → Prop
  mono : ∀ v m m' V r, m.Prefix m' → P v m V r → P v m' V r

namespace Pred

/-- The predicate that holds of nothing (the default of an unallocated id). -/
def bot : Pred := ⟨fun _ _ _ _ => False, fun _ _ _ _ _ _ h => h⟩

/-- The predicate that holds of every resource (`⊤`). -/
def top : Pred := ⟨fun _ _ _ _ => True, fun _ _ _ _ _ _ h => h⟩

instance : Inhabited Pred := ⟨bot⟩

/-- `φ` is pure at `v`: it holds of the empty resource whatever the memory
and view (SLR: `(gconf⊥, V⊥, ε) ∈ ⟦φ(v)⟧`, equivalent for upward-closed
propositions). A relaxed message must satisfy its location's release
predicate purely: it transfers nothing. -/
def Pure (φ : Pred) (v : Val) : Prop := ∀ m V, φ.P v m V Res.unit

/-- The exact separating conjunction `⊛_{φ ∈ φs} φ(v)` of a list of
predicates at `v`: `r` splits into one part per predicate. -/
def SepList : List Pred → Val → Memory → View → Res → Prop
  | [], _, _, _, r => r = Res.unit
  | φ :: φs, v, m, V, r => ∃ r₁ r₂, r = r₁.op r₂ ∧ φ.P v m V r₁ ∧ SepList φs v m V r₂

end Pred

end Kraken.Promising.SLR
