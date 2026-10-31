import WeakCore.CopyPlan
import WeakCore.PairNat
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **EtaA**: the label algebra of one stack level of the relabel route.

Thread `i`'s fresh progression `fl k = freshLabel base n i k` is cut into `M` columns (`k % M`).  Every level `d`
uses three fresh columns above a base `b ≥ N`: cell copies (`cpy`), moves (`mv`) and box variants (`bvar`).
`Used c l`: `l` is a progression label of index `≥ N` in a column `< c` (touched by the levels so far);
`Fresh c l`: index `≥ N` in a column `≥ c` (untouched).  The level's bijection `σ′ = s ∘ σ` moves the ♭ preimage
of every old copy/variant label to its `mv` label, so that the old W objects keep their labels (`Ext`). -/

structure Plan where
  base : Nat
  n : Nat
  i : Nat
  M : Nat
  N : Nat
  hn : 0 < n
  hM : 0 < M

namespace Plan
variable (P : Plan)

def fl (k : Nat) : WeakMem.AllocLabel := freshLabel P.base P.n P.i k
def Used (c : Nat) (l : WeakMem.AllocLabel) : Prop := ∃ k, P.N ≤ k ∧ k % P.M < c ∧ l = P.fl k
def Fresh (c : Nat) (l : WeakMem.AllocLabel) : Prop := ∃ k, P.N ≤ k ∧ c ≤ k % P.M ∧ l = P.fl k
/-- Row `l` of column `c` above base `b`. -/
def lbl (b l c : Nat) : WeakMem.AllocLabel := planLbl P.base P.n P.i P.M b l c

variable {P}

theorem fl_inj {k₁ k₂ : Nat} (e : P.fl k₁ = P.fl k₂) : k₁ = k₂ := freshLabel_inj P.hn e

theorem fl_ge (k : Nat) : k ≤ P.fl k := by
  unfold fl freshLabel
  have := Nat.le_mul_of_pos_left k P.hn
  omega

theorem Used_mono {c c' : Nat} (h : c ≤ c') {l : WeakMem.AllocLabel} (hl : P.Used c l) : P.Used c' l := by
  obtain ⟨k, h1, h2, h3⟩ := hl; exact ⟨k, h1, Nat.lt_of_lt_of_le h2 h, h3⟩

theorem Fresh_anti {c c' : Nat} (h : c ≤ c') {l : WeakMem.AllocLabel} (hl : P.Fresh c' l) : P.Fresh c l := by
  obtain ⟨k, h1, h2, h3⟩ := hl; exact ⟨k, h1, Nat.le_trans h h2, h3⟩

theorem not_Used_of_Fresh {c : Nat} {l : WeakMem.AllocLabel} (hf : P.Fresh c l) : ¬ P.Used c l := by
  rintro ⟨k, -, h2, h3⟩
  obtain ⟨k', -, h2', h3'⟩ := hf
  have := fl_inj (h3.symm.trans h3')
  subst this; omega

theorem lbl_eq (b l c : Nat) : P.lbl b l c = P.fl (colIdx P.M b l c) := rfl

theorem colIdx_mod {b l c : Nat} (hc : c < P.M) : colIdx P.M b l c % P.M = c := by
  unfold colIdx; rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hc

theorem lbl_Fresh {b l c c₀ : Nat} (hc : c < P.M) (hc₀ : c₀ ≤ c) (hb : P.N ≤ b) : P.Fresh c₀ (P.lbl b l c) :=
  ⟨colIdx P.M b l c, Nat.le_trans hb (colIdx_ge P.hM), by rw [colIdx_mod hc]; exact hc₀, rfl⟩

theorem lbl_Used {b l c c₀ : Nat} (hc : c < c₀) (hM : c₀ ≤ P.M) (hb : P.N ≤ b) : P.Used c₀ (P.lbl b l c) :=
  ⟨colIdx P.M b l c, Nat.le_trans hb (colIdx_ge P.hM), by rw [colIdx_mod (Nat.lt_of_lt_of_le hc hM)]; exact hc, rfl⟩

theorem lbl_not_Used {b l c c₀ : Nat} (hc : c < P.M) (hc₀ : c₀ ≤ c) (hb : P.N ≤ b) : ¬ P.Used c₀ (P.lbl b l c) :=
  not_Used_of_Fresh (lbl_Fresh hc hc₀ hb)

theorem lbl_inj_row {b l₁ l₂ c : Nat} (hc : c < P.M) (e : P.lbl b l₁ c = P.lbl b l₂ c) : l₁ = l₂ :=
  colIdx_inj_row hc (fl_inj e)

theorem lbl_col_ne {b l₁ l₂ c₁ c₂ : Nat} (h₁ : c₁ < P.M) (h₂ : c₂ < P.M) (hne : c₁ ≠ c₂) :
    P.lbl b l₁ c₁ ≠ P.lbl b l₂ c₂ := fun e => hne (planLbl_inj P.hn h₁ h₂ e).1

/-- A label below `b` is not a progression label of index `≥ b`: the finite-set escape (stack and value words). -/
theorem fl_ne_of_lt {a b k : Nat} (ha : a < b) (hk : b ≤ k) : P.fl k ≠ a := by
  intro e; have h1 := fl_ge (P := P) k; rw [e] at h1; exact absurd (Nat.le_trans hk h1) (Nat.not_le.mpr ha)

theorem lbl_ne_of_lt {a b l c : Nat} (ha : a < b) : P.lbl b l c ≠ a :=
  fl_ne_of_lt ha (colIdx_ge P.hM)

theorem lbl_tail {b l c N' : Nat} (hb : N' ≤ b) : ∃ k, N' ≤ k ∧ P.lbl b l c = P.fl k :=
  ⟨colIdx P.M b l c, Nat.le_trans hb (colIdx_ge P.hM), rfl⟩

end Plan

/-- The state of the label algebra after some levels: columns `< c₀` used; the bijection `σ`/`τ` (♭ → W / W → ♭)
fixes every label outside `Used c₀`; the old cell copies `cp` and box variants `cpb` (W labels) lie in `Used c₀`. -/
structure Lv (P : Plan) where
  c₀ : Nat
  σ : WeakMem.AllocLabel → WeakMem.AllocLabel
  τ : WeakMem.AllocLabel → WeakMem.AllocLabel
  cp : WeakMem.AllocLabel → Prop
  cpb : WeakMem.AllocLabel → Prop
  sl : ∀ m, τ (σ m) = m
  sr : ∀ m, σ (τ m) = m
  fix : ∀ m, ¬ P.Used c₀ m → σ m = m
  cpU : ∀ m, cp m → P.Used c₀ m
  cpbU : ∀ m, cpb m → P.Used c₀ m
  /-- The merge-back map of the level below: the ♭ original of an old copy/variant, `τ` elsewhere. -/
  og : WeakMem.AllocLabel → WeakMem.AllocLabel
  ogτ : ∀ a, ¬ (cp a ∨ cpb a) → og a = τ a
  /-- Lower bound for this level's base. -/
  bnd : Nat
  hbnd : P.N ≤ bnd

namespace Lv
variable {P : Plan} (L : Lv P)

theorem fixτ (m : WeakMem.AllocLabel) (h : ¬ P.Used L.c₀ m) : L.τ m = m := by
  have := L.fix m h; rw [← this, L.sl]; exact this.symm

/-- The identity level (the base case of F4: `σ = id`, no copies, no variants). -/
def id0 (P : Plan) : Lv P :=
  { c₀ := 0, σ := fun m => m, τ := fun m => m, cp := fun _ => False, cpb := fun _ => False,
    sl := fun _ => rfl, sr := fun _ => rfl, fix := fun _ _ => rfl, cpU := fun _ h => h.elim, cpbU := fun _ h => h.elim,
    og := fun m => m, ogτ := fun _ _ => rfl, bnd := P.N, hbnd := Nat.le_refl _ }

/-! ### One level step: base `b`, columns `c₀` (copies), `c₀+1` (moves), `c₀+2` (variants) -/
section step
variable (b : Nat)

def cpy (l : WeakMem.AllocLabel) : WeakMem.AllocLabel := P.lbl b l L.c₀
def mv (l : WeakMem.AllocLabel) : WeakMem.AllocLabel := P.lbl b l (L.c₀ + 1)
def bvar (x k : Nat) : WeakMem.AllocLabel := P.lbl b (NatPair.pr x k) (L.c₀ + 2)

/-- The labels whose ♭ preimage must move: the old copies and variants. -/
def Old (m : WeakMem.AllocLabel) : Prop := L.cp m ∨ L.cpb m

open Classical in
/-- The move involution: `Old m ↔ mv m`, identity elsewhere. -/
noncomputable def s (m : WeakMem.AllocLabel) : WeakMem.AllocLabel :=
  if L.Old m then L.mv b m else if h : ∃ v, L.Old v ∧ m = L.mv b v then Classical.choose h else m

noncomputable def σ' (m : WeakMem.AllocLabel) : WeakMem.AllocLabel := L.s b (L.σ m)
noncomputable def τ' (m : WeakMem.AllocLabel) : WeakMem.AllocLabel := L.τ (L.s b m)

variable {L b}
variable (hM : L.c₀ + 3 ≤ P.M) (hb : P.N ≤ b)
include hM hb

omit hM hb in
theorem Old_Used {m : WeakMem.AllocLabel} (h : L.Old m) : P.Used L.c₀ m := by
  rcases h with h | h
  · exact L.cpU m h
  · exact L.cpbU m h

theorem cpy_not_Used (l : WeakMem.AllocLabel) : ¬ P.Used L.c₀ (L.cpy b l) :=
  Plan.lbl_not_Used (by omega) (Nat.le_refl _) hb
theorem mv_not_Used (l : WeakMem.AllocLabel) : ¬ P.Used L.c₀ (L.mv b l) :=
  Plan.lbl_not_Used (by omega) (by omega) hb
theorem bvar_not_Used (x k : Nat) : ¬ P.Used L.c₀ (L.bvar b x k) :=
  Plan.lbl_not_Used (by omega) (by omega) hb
theorem cpy_Fresh (l : WeakMem.AllocLabel) : P.Fresh L.c₀ (L.cpy b l) := Plan.lbl_Fresh (by omega) (Nat.le_refl _) hb
theorem mv_Fresh (l : WeakMem.AllocLabel) : P.Fresh L.c₀ (L.mv b l) := Plan.lbl_Fresh (by omega) (by omega) hb
theorem bvar_Fresh (x k : Nat) : P.Fresh L.c₀ (L.bvar b x k) := Plan.lbl_Fresh (by omega) (by omega) hb
theorem cpy_Used3 (l : WeakMem.AllocLabel) : P.Used (L.c₀ + 3) (L.cpy b l) := Plan.lbl_Used (by omega) hM hb
theorem mv_Used3 (l : WeakMem.AllocLabel) : P.Used (L.c₀ + 3) (L.mv b l) := Plan.lbl_Used (by omega) hM hb
theorem bvar_Used3 (x k : Nat) : P.Used (L.c₀ + 3) (L.bvar b x k) := Plan.lbl_Used (by omega) hM hb

theorem mv_not_Old (l : WeakMem.AllocLabel) : ¬ L.Old (L.mv b l) := fun h => mv_not_Used hM hb l (Old_Used h)
theorem cpy_not_Old (l : WeakMem.AllocLabel) : ¬ L.Old (L.cpy b l) := fun h => cpy_not_Used hM hb l (Old_Used h)
theorem bvar_not_Old (x k : Nat) : ¬ L.Old (L.bvar b x k) := fun h => bvar_not_Used hM hb (x := x) (k := k) (Old_Used h)

theorem mv_inj {l₁ l₂ : WeakMem.AllocLabel} (e : L.mv b l₁ = L.mv b l₂) : l₁ = l₂ := Plan.lbl_inj_row (by omega) e
theorem cpy_inj {l₁ l₂ : WeakMem.AllocLabel} (e : L.cpy b l₁ = L.cpy b l₂) : l₁ = l₂ := Plan.lbl_inj_row (by omega) e
theorem bvar_inj {x₁ k₁ x₂ k₂ : Nat} (e : L.bvar b x₁ k₁ = L.bvar b x₂ k₂) : x₁ = x₂ ∧ k₁ = k₂ :=
  NatPair.pr_inj (Plan.lbl_inj_row (by omega) e)
theorem cpy_ne_mv (l₁ l₂ : WeakMem.AllocLabel) : L.cpy b l₁ ≠ L.mv b l₂ := Plan.lbl_col_ne (by omega) (by omega) (by omega)
theorem cpy_ne_bvar (l x k : Nat) : L.cpy b l ≠ L.bvar b x k := Plan.lbl_col_ne (by omega) (by omega) (by omega)
theorem mv_ne_bvar (l x k : Nat) : L.mv b l ≠ L.bvar b x k := Plan.lbl_col_ne (by omega) (by omega) (by omega)

theorem s_old {m : WeakMem.AllocLabel} (h : L.Old m) : L.s b m = L.mv b m := by
  unfold s; rw [if_pos h]

theorem s_mv {v : WeakMem.AllocLabel} (hv : L.Old v) : L.s b (L.mv b v) = v := by
  unfold s
  rw [if_neg (mv_not_Old hM hb v)]
  have hex : ∃ v', L.Old v' ∧ L.mv b v = L.mv b v' := ⟨v, hv, rfl⟩
  rw [dif_pos hex]
  exact (mv_inj hM hb (Classical.choose_spec hex).2).symm

theorem s_other {m : WeakMem.AllocLabel} (h1 : ¬ L.Old m) (h2 : ∀ v, L.Old v → m ≠ L.mv b v) : L.s b m = m := by
  unfold s
  rw [if_neg h1]
  have : ¬ ∃ v, L.Old v ∧ m = L.mv b v := fun ⟨v, hv, e⟩ => h2 v hv e
  rw [dif_neg this]

theorem s_s (m : WeakMem.AllocLabel) : L.s b (L.s b m) = m := by
  by_cases h1 : L.Old m
  · rw [s_old hM hb h1, s_mv hM hb h1]
  · by_cases h2 : ∃ v, L.Old v ∧ m = L.mv b v
    · obtain ⟨v, hv, rfl⟩ := h2
      rw [s_mv hM hb hv, s_old hM hb hv]
    · have h2' : ∀ v, L.Old v → m ≠ L.mv b v := fun v hv e => h2 ⟨v, hv, e⟩
      rw [s_other hM hb h1 h2', s_other hM hb h1 h2']

theorem s_fix {m : WeakMem.AllocLabel} (h : ¬ P.Used (L.c₀ + 2) m) : L.s b m = m := by
  apply s_other hM hb
  · intro ho; exact h (Plan.Used_mono (by omega) (Old_Used ho))
  · intro v _ e; subst e; exact h (Plan.lbl_Used (by omega) (by omega) hb)

theorem σ'τ' (m : WeakMem.AllocLabel) : L.σ' b (L.τ' b m) = m := by
  unfold σ' τ'; rw [L.sr, s_s hM hb]
theorem τ'σ' (m : WeakMem.AllocLabel) : L.τ' b (L.σ' b m) = m := by
  unfold σ' τ'; rw [s_s hM hb, L.sl]

/-- `σ′` fixes every label outside the three new columns and the old ones. -/
theorem σ'_fix {m : WeakMem.AllocLabel} (h : ¬ P.Used (L.c₀ + 3) m) : L.σ' b m = m := by
  unfold σ'
  have h0 : ¬ P.Used L.c₀ m := fun u => h (Plan.Used_mono (by omega) u)
  rw [L.fix m h0]
  exact s_fix hM hb (fun u => h (Plan.Used_mono (by omega) u))
theorem τ'_fix {m : WeakMem.AllocLabel} (h : ¬ P.Used (L.c₀ + 3) m) : L.τ' b m = m := by
  have := σ'_fix hM hb h; rw [← this, τ'σ' hM hb]; exact this.symm

/-- The new copies and variants are fixed by `σ` and `s`, hence by `σ′`/`τ′`. -/
theorem σ_cpy (l : WeakMem.AllocLabel) : L.σ (L.cpy b l) = L.cpy b l := L.fix _ (cpy_not_Used hM hb l)
theorem s_cpy (l : WeakMem.AllocLabel) : L.s b (L.cpy b l) = L.cpy b l :=
  s_other hM hb (cpy_not_Old hM hb l) (fun v _ e => cpy_ne_mv hM hb l v e)
theorem σ'_cpy (l : WeakMem.AllocLabel) : L.σ' b (L.cpy b l) = L.cpy b l := by unfold σ'; rw [σ_cpy hM hb, s_cpy hM hb]
theorem τ'_cpy (l : WeakMem.AllocLabel) : L.τ' b (L.cpy b l) = L.cpy b l := by
  have := σ'_cpy hM hb (L := L) l; rw [← this, τ'σ' hM hb]; exact this.symm
theorem σ_bvar (x k : Nat) : L.σ (L.bvar b x k) = L.bvar b x k := L.fix _ (bvar_not_Used hM hb x k)
theorem s_bvar (x k : Nat) : L.s b (L.bvar b x k) = L.bvar b x k :=
  s_fix hM hb (Plan.lbl_not_Used (by omega) (by omega) hb)
theorem σ'_bvar (x k : Nat) : L.σ' b (L.bvar b x k) = L.bvar b x k := by unfold σ'; rw [σ_bvar hM hb, s_bvar hM hb]
theorem τ'_bvar (x k : Nat) : L.τ' b (L.bvar b x k) = L.bvar b x k := by
  have := σ'_bvar hM hb (L := L) x k; rw [← this, τ'σ' hM hb]; exact this.symm

/-- The ♭ preimage of an old copy/variant under `σ′` is its move label (blank in every env in play). -/
theorem τ'_old {m : WeakMem.AllocLabel} (h : L.Old m) : L.τ' b m = L.mv b m := by
  unfold τ'; rw [s_old hM hb h]; exact L.fixτ _ (mv_not_Used hM hb m)
theorem σ'_mv {m : WeakMem.AllocLabel} (h : L.Old m) : L.σ' b (L.mv b m) = m := by
  have := τ'_old hM hb h; rw [← this, σ'τ' hM hb]

/-- `σ′` agrees with `σ` wherever `σ m` is not old: in particular on every ♭ label holding an old W object
that is not a copy/variant, and on every label mentioned by old payloads. -/
theorem σ'_eq_σ {m : WeakMem.AllocLabel} (h : ¬ L.Old (L.σ m)) (h2 : ∀ v, L.Old v → L.σ m ≠ L.mv b v) :
    L.σ' b m = L.σ m := by unfold σ'; exact s_other hM hb h h2

theorem τ'_eq_τ {m : WeakMem.AllocLabel} (h : ¬ L.Old m) (h2 : ∀ v, L.Old v → m ≠ L.mv b v) :
    L.τ' b m = L.τ m := by unfold τ'; rw [s_other hM hb h h2]

end step
end Lv
end TermSound.Flat
