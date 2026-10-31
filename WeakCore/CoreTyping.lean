/-
# CoreTyping — the declarative judgement, and the checker's soundness  (T1b)

`CoreTerm.lean`'s checker is a program; this file states what it decides as
an inductive `Prop` and proves the program sound for it:

    check_sound : check p cx e = .ok () → Typed p cx e

**What makes the judgement declarative rather than the checker restated.**
  * Index reasoning is *semantic*.  Where the checker normalises linear forms
    (`norm`, `eqI`, `classify`, `pstep`), a rule here asks for entailment:
    every valuation of the index variables that satisfies the context's facts
    satisfies the conclusion.  So the judgement does not depend on the
    decision procedure, and §1 proves the procedure sound.
  * Type equality and subsumption are inductive relations (`TyEqS`, `SubS`),
    with index equality inside them semantic.
  * Choices the checker makes deterministically are existential here: which
    observation licenses a torn read, which parameter a protocol state is at,
    which fact an `ifeq` records.
  * Derivations, not runs: a typing is a tree, and T3 inducts on it.

What stays shared with the checker, by design: the context and its
bookkeeping (`Cx`, `push`, `use`, `bind`, `peek`, lookups), and the type
layer's predicates (`sharedOKIn`, `sensitiveIn`, `affineIn`, `wf`, …), which
are `CoreLang`'s definitions — both the checker and the judgement consult
them.

Two things are syntactic on purpose, and T3's invariant says why.
`unsealed` (§4.4 rule 7) is compared verbatim with the index of the token in
hand (`HoldsSealed`, `NoLeak`): every unfenced token of a block carries its
take's index unchanged, since no rule re-indexes a token except `push`'s
uniform shift.  (Writing this file found that `store` to a word did re-index
it; the checker now keeps the token's own index.)  And protocol states need
not be unique in `InState`: every word's protocol is `pwf`, because `mkWord`
is the only way to make one.

Where the judgement is *more* permissive than the checker, it is on purpose:
`ifeq` may learn nothing, `ifeqRec` has no occurs check (that is for `norm`'s
termination), `parity` allows shadowing a fact (which only forgets it), a
torn read is allowed while holding the token, and `add` may forget a sum.

Contents: §1 index semantics and the arithmetic proved sound; §2 `TyEqS`,
`SubS`; §3 the context-level premises; §4 the judgement; §5 soundness,
`checkProg_sound`; §6 the six library programs, typed by kernel evaluation.

Build:  LEAN_PATH=build lean CoreTyping.lean   (after CoreTerm.olean)
-/

import WeakCore.CoreTerm

namespace CoreTyping

open CoreLang CoreTerm

set_option linter.unusedSimpArgs false

/-! ## §1. Index semantics, and the arithmetic the checker decides -/

/-- A valuation of index variables. -/
abbrev Val := Nat → Nat

def ev (ρ : Val) : Idx → Nat
  | .lit n    => n
  | .var k    => ρ k
  | .add i j  => ev ρ i + ev ρ j
  | .sub i j  => ev ρ i - ev ρ j
  | .smul n i => n * ev ρ i

def csum (ρ : Val) : List (Nat × Nat) → Nat
  | [] => 0
  | (k, c) :: rest => c * ρ k + csum ρ rest

def _root_.CoreTerm.Lin.ev (ρ : Val) (a : Lin) : Nat := a.const + csum ρ a.coefs

/-- `ρ` satisfies the facts: every variable a fact defines has that value.
Shadowed facts are not required — forgetting a fact is sound. -/
def Sat (fs : Facts) (ρ : Val) : Prop := ∀ k t, fs.lookup k = some t → ρ k = ev ρ t

/-- `cx ⊨ φ`. -/
def Ent (cx : Cx) (φ : Val → Prop) : Prop := ∀ ρ, Sat cx.facts ρ → φ ρ

/-- Index equality, semantically. -/
def EqI (cx : Cx) (i j : Idx) : Prop := Ent cx fun ρ => ev ρ i = ev ρ j

theorem csum_ins (ρ : Val) (k c : Nat) : ∀ l, csum ρ (Lin.ins k c l) = c * ρ k + csum ρ l
  | [] => by simp [Lin.ins, csum]
  | (k', c') :: rest => by
      simp only [Lin.ins]
      split
      · rename_i h; simp at h; subst h; simp [csum]; rw [Nat.add_mul]; omega
      · split
        · simp [csum]
        · simp [csum, csum_ins ρ k c rest]; omega

theorem csum_foldl (ρ : Val) : ∀ (b acc : List (Nat × Nat)),
    csum ρ (b.foldl (fun acc p => Lin.ins p.1 p.2 acc) acc) = csum ρ acc + csum ρ b
  | [], acc => by simp [csum]
  | (k, c) :: rest, acc => by
      simp only [List.foldl]
      rw [csum_foldl ρ rest, csum_ins]; simp [csum]; omega

@[simp] theorem lev_add (ρ : Val) (a b : Lin) : (a.add b).ev ρ = a.ev ρ + b.ev ρ := by
  simp [Lin.add, Lin.ev, csum_foldl]; omega

theorem csum_scale (ρ : Val) (n : Nat) : ∀ l : List (Nat × Nat),
    csum ρ (l.map fun p => (p.1, n * p.2)) = n * csum ρ l
  | [] => by simp [csum]
  | (k, c) :: rest => by
      simp [csum, csum_scale ρ n rest, Nat.mul_add, Nat.mul_assoc]

@[simp] theorem lev_scale (ρ : Val) (n : Nat) (a : Lin) : (a.scale n).ev ρ = n * a.ev ρ := by
  unfold Lin.scale
  split
  · rename_i h; simp at h; subst h; simp [Lin.ev, Lin.ofConst, csum]
  · simp [Lin.ev, csum_scale, Nat.mul_add]

@[simp] theorem lev_ofConst (ρ : Val) (n : Nat) : (Lin.ofConst n).ev ρ = n := by
  simp [Lin.ofConst, Lin.ev, csum]

@[simp] theorem lev_ofVar (ρ : Val) (k : Nat) : (Lin.ofVar k).ev ρ = ρ k := by
  simp [Lin.ofVar, Lin.ev, csum]

/-- One level of normalisation is sound if what it hands on is. -/
theorem normWith_sound (fs : Facts) (ρ : Val) (hs : Sat fs ρ) (k : Idx → Option Lin)
    (hk : ∀ t l, k t = some l → l.ev ρ = ev ρ t) :
    ∀ (i : Idx) (l : Lin), normWith fs k i = some l → l.ev ρ = ev ρ i
  | .lit n, l, h => by simp [normWith] at h; subst h; simp [ev]
  | .var v, l, h => by
      cases hv : fs.lookup v with
      | none => simp [normWith, hv] at h; subst h; simp [ev]
      | some t =>
          simp [normWith, hv] at h
          rw [hk t l h, ev, hs v t hv]
  | .add a b, l, h => by
      simp only [normWith] at h
      cases ha : normWith fs k a <;> cases hb : normWith fs k b <;> simp [ha, hb] at h
      subst h
      simp [ev, normWith_sound fs ρ hs k hk a _ ha, normWith_sound fs ρ hs k hk b _ hb]
  | .sub a b, l, h => by simp [normWith] at h
  | .smul n a, l, h => by
      simp only [normWith] at h
      cases ha : normWith fs k a <;> simp [ha] at h
      subst h
      simp [ev, normWith_sound fs ρ hs k hk a _ ha]

/-- **`norm` is sound**: under the facts, the linear form has the term's value. -/
theorem norm_sound (fs : Facts) (ρ : Val) (hs : Sat fs ρ) :
    ∀ (fuel : Nat) (i : Idx) (l : Lin), norm fs fuel i = some l → l.ev ρ = ev ρ i
  | 0, i, l, h => normWith_sound fs ρ hs _ (fun _ _ h => by simp at h) i l h
  | f + 1, i, l, h => normWith_sound fs ρ hs _ (norm_sound fs ρ hs f) i l h

theorem eqI_sound (cx : Cx) (a b : Idx) (h : cx.eqI a b = true) : EqI cx a b := by
  intro ρ hs
  unfold Cx.eqI at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · subst h; rfl
  · split at h
    · rename_i x y hx hy
      simp at h; subst h
      have := norm_sound _ ρ hs _ _ _ hx
      have := norm_sound _ ρ hs _ _ _ hy
      omega
    · simp at h

/-- Index order, semantically (§3.7's bounds and `ini` weakening). -/
def LeI (cx : Cx) (i j : Idx) : Prop := Ent cx fun ρ => ev ρ i ≤ ev ρ j
def LtI (cx : Cx) (i j : Idx) : Prop := Ent cx fun ρ => ev ρ i < ev ρ j

theorem leI_sound (cx : Cx) (a b : Idx) (h : cx.leI a b = true) : LeI cx a b := by
  intro ρ hs
  unfold Cx.leI at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · subst h; exact Nat.le_refl _
  · split at h
    · rename_i x y hx hy
      unfold Lin.leB at h
      simp only [beq_iff_eq] at h
      have e1 := norm_sound _ ρ hs _ _ _ hx
      have e2 := norm_sound _ ρ hs _ _ _ hy
      have e3 := congrArg (Lin.ev ρ) h
      rw [lev_add] at e3
      omega
    · simp at h

theorem ltI_sound (cx : Cx) (a b : Idx) (h : cx.ltI a b = true) : LtI cx a b := by
  intro ρ hs
  have := leI_sound cx _ _ h ρ hs
  simp only [ev] at this
  omega

theorem csum_div (ρ : Val) (s : Nat) : ∀ l : List (Nat × Nat), l.all (fun p => p.2 % s == 0) →
    csum ρ l = s * csum ρ (l.map fun p => (p.1, p.2 / s))
  | [] => by simp [csum]
  | (k, c) :: rest => by
      intro h
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      simp only [csum, List.map, csum_div ρ s rest h.2, Nat.mul_add]
      rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.1)]

/-- **`divSub` is sound**: `a = s·k + off`. -/
theorem divSub_sound (ρ : Val) (a k : Lin) (s off : Nat) (h : a.divSub s off = some k) :
    a.ev ρ = s * k.ev ρ + off := by
  unfold Lin.divSub at h
  split at h
  · split at h
    · rename_i hs hc; simp at h hs hc; subst h hs
      obtain ⟨h1, h2⟩ := hc
      simp [Lin.ev, h1, csum, h2]
    · simp at h
  · split at h
    · rename_i hs hc
      simp at h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      simp only [Lin.ev]
      rw [csum_div ρ s _ h3, Nat.mul_add, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2)]
      omega
    · simp at h

theorem ev_toIdx_foldl (ρ : Val) : ∀ (l : List (Nat × Nat)) (acc : Idx),
    ev ρ (l.foldl (fun acc p => .add acc (if p.2 == 1 then .var p.1 else .smul p.2 (.var p.1))) acc)
      = ev ρ acc + csum ρ l
  | [], acc => by simp [csum]
  | (k, c) :: rest, acc => by
      simp only [List.foldl]
      rw [ev_toIdx_foldl ρ rest]
      simp only [csum]
      split <;> rename_i h <;> simp_all [ev] <;> omega

@[simp] theorem ev_toIdx (ρ : Val) (a : Lin) : ev ρ a.toIdx = a.ev ρ := by
  unfold Lin.toIdx; rw [ev_toIdx_foldl]; simp [ev, Lin.ev]

theorem asVar_ev (ρ : Val) (a : Lin) (v : Nat) (h : a.asVar? = some v) : a.ev ρ = ρ v := by
  unfold Lin.asVar? at h
  split at h <;> simp_all [Lin.ev, csum]

/-! ### Protocol states and transitions, semantically -/

/-- `i` is in state `c` of `P` at parameter `k`. -/
def InState (cx : Cx) (P : Proto) (i : Idx) (c : Nat) (k : Idx) : Prop :=
  ∃ cl, P.clauses[c]? = some cl ∧ Ent cx fun ρ => ev ρ i = cl.scale * ev ρ k + cl.off

/-- `(c, k) → (c', k')` is a transition of `P`: an ordinary one, whose
parameters differ by its `dk` at every valuation, or a wild one, which relates
any parameters. -/
def Step (cx : Cx) (P : Proto) (c : Nat) (k : Idx) (c' : Nat) (k' : Idx) : Prop :=
  (∃ dk : Int, (c, c', dk) ∈ P.trans ∧ Ent cx fun ρ => (ev ρ k' : Int) = ev ρ k + dk) ∨
  (c, c') ∈ P.wild

theorem mem_enumFrom {α : Type} : ∀ (l : List α) (i n : Nat) (a : α),
    (n, a) ∈ enumFrom l i → i ≤ n ∧ l[n - i]? = some a
  | [], _, _, _, h => by simp [enumFrom] at h
  | b :: bs, i, n, a, h => by
      simp only [enumFrom, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨h1, h2⟩ | h
      · subst h1 h2; simp
      · have := mem_enumFrom bs (i + 1) n a h
        refine ⟨by omega, ?_⟩
        have e : n - i = (n - (i + 1)) + 1 := by omega
        rw [e]; simpa using this.2

theorem classify_mem (P : Proto) (a : Lin) (c : Nat) (k : Lin) (h : classify P a = some (c, k)) :
    ∃ cl, P.clauses[c]? = some cl ∧ a.divSub cl.scale cl.off = some k := by
  unfold classify at h
  split at h
  · rename_i m hm
    simp at h; subst h
    have hmem : (c, k) ∈ (enumFrom P.clauses 0).filterMap
        (fun (n, cl) => (a.divSub cl.scale cl.off).map fun k => (n, k)) := by rw [hm]; simp
    simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨n, cl⟩, hn, k', hk, rfl, rfl⟩ := hmem
    have := mem_enumFrom _ 0 _ _ hn
    exact ⟨cl, by simpa using this.2, hk⟩
  · simp at h

theorem classifyM_sound (cx : Cx) (P : Proto) (i : Idx) (c : Nat) (k : Lin)
    (h : classifyM cx P i = .ok (c, k)) : InState cx P i c k.toIdx := by
  unfold classifyM at h
  cases hn : cx.norm i with
  | none => simp [hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some a =>
    simp only [hn, bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i m hm
      simp at h; subst h
      obtain ⟨cl, hc, hd⟩ := classify_mem P a c k hm
      refine ⟨cl, hc, fun ρ hs => ?_⟩
      have h1 := norm_sound _ ρ hs _ _ _ hn
      have h2 := divSub_sound ρ a k cl.scale cl.off hd
      simp; omega
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem pstep_sound (cx : Cx) (P : Proto) (c c' : Nat) (k k' : Lin)
    (h : pstep P c k c' k' = true) : Step cx P c k.toIdx c' k'.toIdx := by
  unfold pstep at h
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  rcases h with h | h
  case inr => exact Or.inr h
  left
  obtain ⟨⟨a, b, dk⟩, hm, ⟨rfl, rfl⟩, h⟩ := h
  refine ⟨dk, hm, fun ρ _ => ?_⟩
  split at h
  · rename_i hd
    simp only at hd
    simp only [beq_iff_eq] at h; subst h
    have := Int.toNat_of_nonneg hd
    simp; omega
  · rename_i hd
    simp only at hd
    simp only [beq_iff_eq] at h; subst h
    have := Int.toNat_of_nonneg (show 0 ≤ -dk by omega)
    simp; omega

/-! ### Pair protocols, semantically -/

/-- `k₁ ⋈ k₀ + d`, on values. -/
def Rel2Holds : Rel2 → Nat → Nat → Prop
  | .free, _, _ => True
  | .eq d, k0, k1 => (k1 : Int) = k0 + d
  | .le d, k0, k1 => (k1 : Int) ≤ k0 + d
  | .ge d, k0, k1 => (k1 : Int) ≥ k0 + d

theorem leB_sound (ρ : Val) (a b : Lin) (h : Lin.leB a b = true) : a.ev ρ ≤ b.ev ρ := by
  unfold Lin.leB at h
  simp only [beq_iff_eq] at h
  have e := congrArg (Lin.ev ρ) h
  rw [lev_add] at e
  omega

theorem rel2Holds_sound (ρ : Val) (rel : Rel2) (k0 k1 : Lin) (h : rel2Holds rel k0 k1 = true) :
    Rel2Holds rel (k0.ev ρ) (k1.ev ρ) := by
  cases rel with
  | free => trivial
  | eq d =>
    simp only [rel2Holds] at h
    split at h
    · rename_i hd
      simp only [beq_iff_eq] at h
      have e := congrArg (Lin.ev ρ) h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg hd
      simp only [Rel2Holds]; omega
    · rename_i hd
      simp only [beq_iff_eq] at h
      have e := congrArg (Lin.ev ρ) h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg (show 0 ≤ -d by omega)
      simp only [Rel2Holds]; omega
  | le d =>
    simp only [rel2Holds] at h
    split at h
    · rename_i hd
      have e := leB_sound ρ _ _ h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg hd
      simp only [Rel2Holds]; omega
    · rename_i hd
      have e := leB_sound ρ _ _ h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg (show 0 ≤ -d by omega)
      simp only [Rel2Holds]; omega
  | ge d =>
    simp only [rel2Holds] at h
    split at h
    · rename_i hd
      have e := leB_sound ρ _ _ h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg hd
      simp only [Rel2Holds]; omega
    · rename_i hd
      have e := leB_sound ρ _ _ h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg (show 0 ≤ -d by omega)
      simp only [Rel2Holds]; omega

/-- `(i₀, i₁)` is in pair state `c` of `P` at parameters `(k₀, k₁)`. -/
def InState2 (cx : Cx) (P : Proto2) (i0 i1 : Idx) (c : Nat) (k0 k1 : Idx) : Prop :=
  ∃ cl, P.clauses[c]? = some cl ∧ Ent cx fun ρ =>
    ev ρ i0 = cl.s0 * ev ρ k0 + cl.o0 ∧ ev ρ i1 = cl.s1 * ev ρ k1 + cl.o1 ∧
    Rel2Holds cl.rel (ev ρ k0) (ev ρ k1)

/-- One half of a pair move: by `d`, or forgotten. -/
def HalfStep (d : Option Int) (k k' : Nat) : Prop :=
  match d with
  | none => True
  | some d => (k' : Int) = k + d

def Step2 (cx : Cx) (P : Proto2) (c : Nat) (k0 k1 : Idx) (c' : Nat) (k0' k1' : Idx) : Prop :=
  ∃ d0 d1, (c, c', d0, d1) ∈ P.trans ∧
    Ent cx fun ρ => HalfStep d0 (ev ρ k0) (ev ρ k0') ∧ HalfStep d1 (ev ρ k1) (ev ρ k1')

/-- A pair move bumps the epoch: half 0 advances by one. -/
def Bump2 (cx : Cx) (k0 k0' : Idx) : Prop :=
  Ent cx fun ρ => HalfStep (some 1) (ev ρ k0) (ev ρ k0')

theorem pairMatch_some {a0 a1 : Lin} {n : Nat} {cl : Clause2} {m : Nat × Lin × Lin}
    (h : pairMatch a0 a1 n cl = some m) :
    ∃ k0 k1, m = (n, k0, k1) ∧ a0.divSub cl.s0 cl.o0 = some k0 ∧ a1.divSub cl.s1 cl.o1 = some k1 ∧
      rel2Holds cl.rel k0 k1 = true := by
  unfold pairMatch at h
  split at h
  · rename_i k0 k1 h0 h1
    split at h
    · rename_i hr; simp at h; subst h; exact ⟨k0, k1, rfl, h0, h1, hr⟩
    · simp at h
  · simp at h

theorem classify2_mem (P : Proto2) (a0 a1 : Lin) (c : Nat) (k0 k1 : Lin)
    (h : classify2 P a0 a1 = some (c, k0, k1)) :
    ∃ cl, P.clauses[c]? = some cl ∧ a0.divSub cl.s0 cl.o0 = some k0 ∧ a1.divSub cl.s1 cl.o1 = some k1 ∧
      rel2Holds cl.rel k0 k1 = true := by
  unfold classify2 at h
  split at h
  · rename_i m hm
    simp at h; subst h
    have hmem : (c, k0, k1) ∈ (enumFrom P.clauses 0).filterMap (fun (n, cl) => pairMatch a0 a1 n cl) := by
      rw [hm]; simp
    simp only [List.mem_filterMap] at hmem
    obtain ⟨⟨n, cl⟩, hn, hf⟩ := hmem
    obtain ⟨k0', k1', he, h0, h1, hr⟩ := pairMatch_some hf
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have := mem_enumFrom _ 0 _ _ hn
    exact ⟨cl, by simpa using this.2, h0, h1, hr⟩
  · simp at h

theorem classify2M_sound (cx : Cx) (P : Proto2) (i0 i1 : Idx) (c : Nat) (k0 k1 : Lin)
    (h : classify2M cx P i0 i1 = .ok (c, k0, k1)) : InState2 cx P i0 i1 c k0.toIdx k1.toIdx := by
  unfold classify2M at h
  cases hn0 : cx.norm i0 with
  | none => simp [hn0, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some a0 =>
    cases hn1 : cx.norm i1 with
    | none => simp [hn0, hn1, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | some a1 =>
      simp only [hn0, hn1, bind, Except.bind, pure, Except.pure] at h
      split at h
      · rename_i m hm
        simp at h; subst h
        obtain ⟨cl, hc, h0, h1, hr⟩ := classify2_mem P a0 a1 c k0 k1 hm
        refine ⟨cl, hc, fun ρ hs => ?_⟩
        have e0 := norm_sound _ ρ hs _ _ _ hn0
        have e1 := norm_sound _ ρ hs _ _ _ hn1
        have d0 := divSub_sound ρ a0 k0 cl.s0 cl.o0 h0
        have d1 := divSub_sound ρ a1 k1 cl.s1 cl.o1 h1
        have hr' := rel2Holds_sound ρ cl.rel k0 k1 hr
        simp only [ev_toIdx]
        exact ⟨by omega, by omega, hr'⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem clause2M_ok {P : Proto2} {c : Nat} {cl : Clause2} (h : clause2M P c = .ok cl) :
    P.clauses[c]? = some cl := by
  unfold clause2M at h; split at h <;> simp_all [pure, Except.pure]

theorem halfStep_sound (ρ : Val) (d : Option Int) (k k' : Lin) (h : halfStep d k k' = true) :
    HalfStep d (k.ev ρ) (k'.ev ρ) := by
  cases d with
  | none => trivial
  | some d =>
    simp only [halfStep] at h
    split at h
    · rename_i hd
      simp only [beq_iff_eq] at h
      have e := congrArg (Lin.ev ρ) h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg hd
      simp only [HalfStep]; omega
    · rename_i hd
      simp only [beq_iff_eq] at h
      have e := congrArg (Lin.ev ρ) h
      simp only [lev_add, lev_ofConst] at e
      have := Int.toNat_of_nonneg (show 0 ≤ -d by omega)
      simp only [HalfStep]; omega

theorem pstep2_sound (cx : Cx) (P : Proto2) (c c' : Nat) (k0 k1 k0' k1' : Lin)
    (h : pstep2 P c k0 k1 c' k0' k1' = true) :
    Step2 cx P c k0.toIdx k1.toIdx c' k0'.toIdx k1'.toIdx := by
  unfold pstep2 at h
  simp only [List.any_eq_true] at h
  obtain ⟨⟨a, b, d0, d1⟩, hm, h⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, h0⟩, h1⟩ := h
  refine ⟨d0, d1, hm, fun ρ _ => ?_⟩
  simp only [ev_toIdx]
  exact ⟨halfStep_sound ρ d0 k0 k0' h0, halfStep_sound ρ d1 k1 k1' h1⟩

theorem bump2_sound (cx : Cx) (P : Proto2) (k0 k0' : Lin) (h : bump2 P k0 k0' = true) :
    P.epoch = true ∧ Bump2 cx k0.toIdx k0'.toIdx := by
  simp only [bump2, Bool.and_eq_true] at h
  refine ⟨h.1, fun ρ _ => ?_⟩
  simp only [ev_toIdx]
  exact halfStep_sound ρ (some 1) k0 k0' h.2

/-! ## §2. Type equality and subsumption, with semantic index equality -/

def IEq (cx : Cx) (d : Nat) (i j : Idx) : Prop := i = j ∨ (d = 0 ∧ EqI cx i j)

inductive MEq (cx : Cx) (d : Nat) : Mode → Mode → Prop
  | own : MEq cx d .own .own
  | pub : MEq cx d .pub .pub
  | rgn {r s} : IEq cx d r s → MEq cx d (.rgn r) (.rgn s)

/-- `shareMove`, semantically: which way a `cas` between holding states moves
the read shares, with its parameter equations holding at every valuation. -/
inductive ShareMove (P : Proto) : Nat → Idx → Nat → Idx → Int → Prop
  | none {c k c' k'} : P.lends.contains c = false → P.lends.contains c' = false →
      P.lendsDown.contains c = false → P.lendsDown.contains c' = false →
      ShareMove P c k c' k' 0
  | stay {c k k'} : P.lends.contains c = true → P.lendsDown.contains c = false →
      (∀ ρ, ev ρ k = ev ρ k') → ShareMove P c k c k' 0
  | up {c k k'} : P.lends.contains c = true → P.lendsDown.contains c = false →
      (∀ ρ, ev ρ k' = ev ρ k + 1) → ShareMove P c k c k' 1
  | down {c k k'} : P.lends.contains c = true → P.lendsDown.contains c = false →
      (∀ ρ, ev ρ k = ev ρ k' + 1) → ShareMove P c k c k' (-1)
  | enter {c k c' k'} : P.lends.contains c = false → P.lends.contains c' = true →
      P.lendsDown.contains c = false → P.lendsDown.contains c' = false →
      (∀ ρ, ev ρ k' = 0) → ShareMove P c k c' k' 1
  | leave {c k c' k'} : P.lends.contains c = true → P.lends.contains c' = false →
      P.lendsDown.contains c = false → P.lendsDown.contains c' = false →
      (∀ ρ, ev ρ k = 0) → ShareMove P c k c' k' (-1)
  /-- Counting down: lending a share spends a free permit. -/
  | dlend {c k k'} : P.lendsDown.contains c = true → (∀ ρ, ev ρ k = ev ρ k' + 1) →
      ShareMove P c k c k' 1
  | dret {c k k'} : P.lendsDown.contains c = true → (∀ ρ, ev ρ k' = ev ρ k + 1) →
      ShareMove P c k c k' (-1)
  | dstay {c k k'} : P.lendsDown.contains c = true → (∀ ρ, ev ρ k = ev ρ k') →
      ShareMove P c k c k' 0

theorem shareMoveUp_sound (P : Proto) (c : Nat) (k : Lin) (c' : Nat) (k' : Lin) (m : Int)
    (hd : P.lendsDown.contains c = false) (hd' : P.lendsDown.contains c' = false)
    (h : shareMoveUp P c k c' k' = some m) : ShareMove P c k.toIdx c' k'.toIdx m := by
  unfold shareMoveUp at h
  cases hl : P.lends.contains c <;> cases hl' : P.lends.contains c' <;> simp only [hl, hl'] at h
  · simp at h; subst h; exact .none hl hl' hd hd'
  · split at h
    · rename_i he
      simp at h; subst h; simp at he
      exact .enter hl hl' hd hd' (fun ρ => by simp [he, Lin.ev, Lin.ofConst, csum])
    · simp at h
  · split at h
    · rename_i he
      simp at h; subst h; simp at he
      exact .leave hl hl' hd hd' (fun ρ => by simp [he, Lin.ev, Lin.ofConst, csum])
    · simp at h
  · split at h
    · simp at h
    · rename_i hc
      simp at hc; subst hc
      split at h
      · rename_i he
        simp at h; subst h; simp at he
        exact .up hl hd (fun ρ => by simp only [he, ev_toIdx, lev_add]; simp [Lin.ev, Lin.ofConst, csum])
      · split at h
        · rename_i he
          simp at h; subst h; simp at he
          exact .down hl hd (fun ρ => by simp only [he, ev_toIdx, lev_add]; simp [Lin.ev, Lin.ofConst, csum])
        · split at h
          · rename_i he
            simp at h; subst h; simp at he
            exact .stay hl hd (fun ρ => by simp [he])
          · simp at h

theorem shareMoveDown_sound (P : Proto) (c : Nat) (k : Lin) (c' : Nat) (k' : Lin) (m : Int)
    (h : shareMoveDown P c k c' k' = some m) : ShareMove P c k.toIdx c' k'.toIdx m := by
  unfold shareMoveDown at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hl⟩ := hc
    split at h
    · rename_i he
      simp at h; subst h; simp at he
      exact .dlend hl (fun ρ => by simp only [he, ev_toIdx, lev_add]; simp [Lin.ev, Lin.ofConst, csum])
    · split at h
      · rename_i he
        simp at h; subst h; simp at he
        exact .dret hl (fun ρ => by simp only [he, ev_toIdx, lev_add]; simp [Lin.ev, Lin.ofConst, csum])
      · split at h
        · rename_i he
          simp at h; subst h; simp at he
          exact .dstay hl (fun ρ => by simp [he])
        · simp at h
  · simp at h

theorem shareMove_sound (P : Proto) (c : Nat) (k : Lin) (c' : Nat) (k' : Lin) (m : Int)
    (h : shareMove P c k c' k' = some m) : ShareMove P c k.toIdx c' k'.toIdx m := by
  unfold shareMove at h
  cases hd : P.lendsDown.contains c <;> cases hd' : P.lendsDown.contains c' <;>
    simp only [hd, hd', Bool.or_true, Bool.true_or, Bool.or_false, ↓reduceIte,
      Bool.false_eq_true] at h
  · exact shareMoveUp_sound P c k c' k' m hd hd' h
  all_goals exact shareMoveDown_sound P c k c' k' m h


inductive TyEqS (cx : Cx) : Nat → Ty → Ty → Prop
  | refl {d a} : TyEqS cx d a a
  | intS {d i j} : IEq cx d i j → TyEqS cx d (.intS i) (.intS j)
  | prod {d a b a' b'} : TyEqS cx d a a' → TyEqS cx d b b' → TyEqS cx d (.prod a b) (.prod a' b')
  | sum {d a b a' b'} : TyEqS cx d a a' → TyEqS cx d b b' → TyEqS cx d (.sum a b) (.sum a' b')
  | code {d a b a' b' k} : TyEqS cx d a a' → TyEqS cx d b b' → TyEqS cx d (.code a b k) (.code a' b' k)
  | array {d i j t u} : IEq cx d i j → TyEqS cx d t u → TyEqS cx d (.array i t) (.array j u)
  | ptr {d μ ν t u} : MEq cx d μ ν → TyEqS cx d t u → TyEqS cx d (.ptr μ t) (.ptr ν u)
  | ptrOpt {d μ ν t u} : MEq cx d μ ν → TyEqS cx d t u → TyEqS cx d (.ptrOpt μ t) (.ptrOpt ν u)
  | loc {d μ ν t u} : MEq cx d μ ν → TyEqS cx d t u → TyEqS cx d (.loc μ t) (.loc ν u)
  | word {d r s P} : IEq cx d r s → TyEqS cx d (.word r P) (.word s P)
  | word2 {d r s} {P : Proto2} : IEq cx d r s → TyEqS cx d (.word2 r P) (.word2 s P)
  | tok2 {d r s a b a' b'} {P : Proto2} : IEq cx d r s → IEq cx d a a' → IEq cx d b b' →
      TyEqS cx d (.tok2 r P a b) (.tok2 s P a' b')
  | epair {d r s} {P : ECounter} : IEq cx d r s → TyEqS cx d (.epair r P) (.epair s P)
  | tokE {d r s a a'} {P : ECounter} : IEq cx d r s → IEq cx d a a' → TyEqS cx d (.tokE r P a) (.tokE s P a')
  | tokNone {d r s} : IEq cx d r s → TyEqS cx d (.tok r none) (.tok s none)
  | tokSome {d r s a b} {P : Proto} : IEq cx d r s → IEq cx d a b →
      TyEqS cx d (.tok r (some (P, a))) (.tok s (some (P, b)))
  | share {d r s} : IEq cx d r s → TyEqS cx d (.share r) (.share s)
  | cap {d c r s} : IEq cx d r s → TyEqS cx d (.cap c r) (.cap c s)
  | mu {d t u} : TyEqS cx d t u → TyEqS cx d (.mu t) (.mu u)
  | tex {d κ t u} : TyEqS cx d t u → TyEqS cx d (.tex κ t) (.tex κ u)
  | iall {d t u} : TyEqS cx (d + 1) t u → TyEqS cx d (.iall t) (.iall u)
  | iex {d t u} : TyEqS cx (d + 1) t u → TyEqS cx d (.iex t) (.iex u)
  | refine {d t u ψ} : TyEqS cx d t u → TyEqS cx d (.refine t ψ) (.refine u ψ)
  | refineIni {d t u i j} : IEq cx d i j → TyEqS cx d t u →
      TyEqS cx d (.refine t (.ini i)) (.refine u (.ini j))

theorem ieqD_sound {cx : Cx} {d : Nat} {i j : Idx} (h : ieqD cx d i j = true) : IEq cx d i j := by
  unfold ieqD at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, eqI_sound cx i j h2⟩

theorem meqD_sound {cx : Cx} {d : Nat} {μ ν : Mode} (h : meqD cx d μ ν = true) : MEq cx d μ ν := by
  cases μ <;> cases ν <;> simp [meqD] at h
  · exact .own
  · exact .pub
  · exact .rgn (ieqD_sound h)

theorem tyEq_sound (cx : Cx) : ∀ (d : Nat) (a b : Ty), tyEq cx d a b = true → TyEqS cx d a b := by
  intro d a b h
  induction a generalizing d b with
  | unit | void | int | tvar _ | fix _ _ | lanes _ _ | tid | opq _ =>
      cases b <;> simp_all [tyEq] <;> first | exact .refl | skip
  | intS i =>
      cases b <;> simp [tyEq] at h
      exact .intS (ieqD_sound h)
  | prod a₁ a₂ ih₁ ih₂ =>
      cases b <;> simp [tyEq] at h
      exact .prod (ih₁ _ _ h.1) (ih₂ _ _ h.2)
  | sum a₁ a₂ ih₁ ih₂ =>
      cases b <;> simp [tyEq] at h
      exact .sum (ih₁ _ _ h.1) (ih₂ _ _ h.2)
  | code a₁ a₂ k ih₁ ih₂ =>
      cases b <;> simp [tyEq] at h
      obtain ⟨⟨rfl, h1⟩, h2⟩ := h
      exact .code (ih₁ _ _ h1) (ih₂ _ _ h2)
  | array i t ih =>
      cases b <;> simp [tyEq] at h
      exact .array (ieqD_sound h.1) (ih _ _ h.2)
  | ptr μ t ih =>
      cases b <;> simp [tyEq] at h
      exact .ptr (meqD_sound h.1) (ih _ _ h.2)
  | ptrOpt μ t ih =>
      cases b <;> simp [tyEq] at h
      exact .ptrOpt (meqD_sound h.1) (ih _ _ h.2)
  | loc μ t ih =>
      cases b <;> simp [tyEq] at h
      exact .loc (meqD_sound h.1) (ih _ _ h.2)
  | word r P =>
      cases b <;> simp [tyEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact .word (ieqD_sound h1)
  | word2 r P =>
      cases b <;> simp [tyEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact .word2 (ieqD_sound h1)
  | tok2 r P i j =>
      cases b <;> simp [tyEq] at h
      obtain ⟨⟨⟨h1, rfl⟩, h2⟩, h3⟩ := h
      exact .tok2 (ieqD_sound h1) (ieqD_sound h2) (ieqD_sound h3)
  | epair r P =>
      cases b <;> simp [tyEq] at h
      obtain ⟨h1, rfl⟩ := h
      exact .epair (ieqD_sound h1)
  | tokE r P e =>
      cases b <;> simp [tyEq] at h
      obtain ⟨⟨h1, rfl⟩, h2⟩ := h
      exact .tokE (ieqD_sound h1) (ieqD_sound h2)
  | tok r i =>
      cases b <;> simp [tyEq] at h
      rename_i s j
      obtain ⟨h1, h2⟩ := h
      rcases i with _ | ⟨P, a⟩ <;> rcases j with _ | ⟨Q, b⟩ <;> simp at h2
      · exact .tokNone (ieqD_sound h1)
      · obtain ⟨rfl, h2⟩ := h2
        exact .tokSome (ieqD_sound h1) (ieqD_sound h2)
  | share r =>
      cases b <;> simp [tyEq] at h
      exact .share (ieqD_sound h)
  | cap c r =>
      cases b <;> simp [tyEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact .cap (ieqD_sound h2)
  | mu t ih =>
      cases b <;> simp [tyEq] at h
      exact .mu (ih _ _ h)
  | iall t ih =>
      cases b <;> simp [tyEq] at h
      exact .iall (ih _ _ h)
  | iex t ih =>
      cases b <;> simp [tyEq] at h
      exact .iex (ih _ _ h)
  | tex κ t ih =>
      cases b <;> simp [tyEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact .tex (ih _ _ h2)
  | refine t ψ ih =>
      cases b <;> simp [tyEq] at h
      rename_i u χ
      obtain ⟨h1, h2⟩ := h
      rcases h1 with rfl | h1
      · exact .refine (ih _ _ h2)
      · cases ψ <;> cases χ <;> simp [iniEq] at h1
        exact .refineIni (ieqD_sound h1) (ih _ _ h2)

theorem single_ev {l : Lin} {u s : Nat} (h : l.single? = some (u, s)) (ρ : Val) :
    l.ev ρ = s * ρ u := by
  unfold Lin.single? at h
  split at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h; simp [Lin.ev, csum]
  · simp at h

theorem lzero_ev {l : Lin} {u : Nat} (h : l.zeroVar? = some u) :
    ∃ s, 0 < s ∧ ∀ ρ, l.ev ρ = s * ρ u := by
  unfold Lin.zeroVar? at h
  split at h
  · rename_i n
    simp at h; subst h; exact ⟨n + 1, Nat.succ_pos _, fun ρ => by simp [Lin.ev, csum]⟩
  · simp at h

/-- `s·u = 0` with `s > 0`, one side or the other. -/
def ZeroEq (cx : Cx) (i j : Idx) (u s : Nat) : Prop :=
  0 < s ∧ ((EqI cx i (.smul s (.var u)) ∧ EqI cx j (.lit 0)) ∨
           (EqI cx j (.smul s (.var u)) ∧ EqI cx i (.lit 0)))

theorem zeroVar_sound {cx : Cx} {i j : Idx} {ni nj : Lin} {u : Nat} (hni : cx.norm i = some ni)
    (hnj : cx.norm j = some nj) (h : zeroVar ni nj = some u) : ∃ s, ZeroEq cx i j u s := by
  unfold zeroVar at h
  split at h
  · rename_i h0
    simp only [beq_iff_eq] at h0; subst h0
    obtain ⟨s, hs, he⟩ := lzero_ev h
    refine ⟨s, hs, .inl ⟨fun ρ hsat => ?_, fun ρ hsat => ?_⟩⟩
    · have e1 := norm_sound _ ρ hsat _ _ _ hni
      have e2 := he ρ
      simp [ev]; omega
    · have e1 := norm_sound _ ρ hsat _ _ _ hnj
      simp at e1; simp [ev]; omega
  · split at h
    · rename_i _ h0
      simp only [beq_iff_eq] at h0; subst h0
      obtain ⟨s, hs, he⟩ := lzero_ev h
      refine ⟨s, hs, .inr ⟨fun ρ hsat => ?_, fun ρ hsat => ?_⟩⟩
      · have e1 := norm_sound _ ρ hsat _ _ _ hnj
        have e2 := he ρ
        simp [ev]; omega
      · have e1 := norm_sound _ ρ hsat _ _ _ hni
        simp at e1; simp [ev]; omega
    · simp at h

/-- `ifeq`'s false branch: the context unchanged, or, when one side is `s·u`
and the other `0`, with `u = u' + 1` for a fresh `u'`. -/
inductive NoCx (cx : Cx) (i j : Idx) : Cx → Prop
  | same : NoCx cx i j cx
  | nzL {u s : Nat} : EqI cx i (.smul s (.var u)) → EqI cx j (.lit 0) → NoCx cx i j (nzCx cx u)
  | nzR {u s : Nat} : EqI cx j (.smul s (.var u)) → EqI cx i (.lit 0) → NoCx cx i j (nzCx cx u)

theorem noCx_sound {cx : Cx} {i j : Idx} {ni nj : Lin} (hni : cx.norm i = some ni)
    (hnj : cx.norm j = some nj) : NoCx cx i j (noCx cx ni nj) := by
  unfold noCx
  split
  · rename_i h0
    simp only [beq_iff_eq] at h0; subst h0
    split
    · rename_i u s hs
      refine .nzL (s := s) ?_ ?_
      · intro ρ hsat
        have e1 := norm_sound _ ρ hsat _ _ _ hni
        have e2 := single_ev hs ρ
        simp [ev]; omega
      · intro ρ hsat
        have e1 := norm_sound _ ρ hsat _ _ _ hnj
        simp at e1; simp [ev]; omega
    · exact .same
  · split
    · rename_i _ h0
      simp only [beq_iff_eq] at h0; subst h0
      split
      · rename_i u s hs
        refine .nzR (s := s) ?_ ?_
        · intro ρ hsat
          have e1 := norm_sound _ ρ hsat _ _ _ hnj
          have e2 := single_ev hs ρ
          simp [ev]; omega
        · intro ρ hsat
          have e1 := norm_sound _ ρ hsat _ _ _ hni
          simp at e1; simp [ev]; omega
      · exact .same
    · exact .same

/-- Subsumption: mirrors `sub`'s cases, with `TyEqS` for equality. -/
inductive SubS (cx : Cx) : Ty → Ty → Prop
  | eq {σ τ} : TyEqS cx 0 σ τ → SubS cx σ τ
  | intS {i} : SubS cx (.intS i) .int
  | refine {t ψ u} : SubS cx t u → SubS cx (.refine t ψ) u
  | iniWeak {t u i j} : TyEqS cx 0 t u → LeI cx j i → SubS cx (.refine t (.ini i)) (.refine u (.ini j))
  | nonNull {μ ν t u} : MEq cx 0 μ ν → TyEqS cx 0 t u → SubS cx (.ptr μ t) (.ptrOpt ν u)
  | prod {a b a' b'} : SubS cx a a' → SubS cx b b' → SubS cx (.prod a b) (.prod a' b')
  | sum {a b a' b'} : SubS cx a a' → SubS cx b b' → SubS cx (.sum a b) (.sum a' b')
  /-- A stronger capability is a weaker one: `pub ≤ bor ≤ rd`. -/
  | cap {c c' r s} : c.le c' = true → IEq cx 0 r s → SubS cx (.cap c r) (.cap c' s)
  /-- (M1, T1) A restricted function is a plain function. -/
  | codeR {a b a' b' f s ro} : TyEqS cx 0 a a' → TyEqS cx 0 b b' →
      SubS cx (.code a b (.restricted f s ro)) (.code a' b' .plain)
  /-- (M1, T1) A restricted function fits a larger budget slot; a read-only one fits a non-read-only slot. -/
  | codeRR {a b a' b' f s ro f' s' ro'} : f ≤ f' → s ≤ s' → (ro' = true → ro = true) → TyEqS cx 0 a a' → TyEqS cx 0 b b' →
      SubS cx (.code a b (.restricted f s ro)) (.code a' b' (.restricted f' s' ro'))

theorem sub_sound (cx : Cx) : ∀ (σ τ : Ty), sub cx σ τ = true → SubS cx σ τ := by
  intro σ
  induction σ with
  | refine t ψ ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases ψ <;> cases τ <;> (try exact .refine (ih _ h))
        all_goals (rename_i χ; cases χ <;> (try exact .refine (ih _ h)))
        all_goals
          simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          rcases h with ⟨h1, h2⟩ | h
          · exact .iniWeak (tyEq_sound cx 0 _ _ h1) (leI_sound cx _ _ h2)
          · exact .refine (ih _ h)
  | prod a b iha ihb =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .prod (iha _ h.1) (ihb _ h.2)
  | sum a b iha ihb =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .sum (iha _ h.1) (ihb _ h.2)
  | intS i =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .intS
  | ptr μ t ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> cases μ <;> (try simp at h)
        all_goals (try (rename_i ν _; cases ν <;> (try simp at h)))
        all_goals first
          | exact .nonNull (meqD_sound h.1) (tyEq_sound cx 0 _ _ h.2)
          | exact .nonNull .own (tyEq_sound cx 0 _ _ h)
          | exact .nonNull .pub (tyEq_sound cx 0 _ _ h)
          | exact .nonNull (.rgn (ieqD_sound h.1)) (tyEq_sound cx 0 _ _ h.2)
  | ptrOpt μ t ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> cases μ <;> (try simp at h)
        all_goals (try (rename_i ν _; cases ν <;> (try simp at h)))
  | loc μ t ih =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> cases μ <;> (try simp at h)
        all_goals (try (rename_i ν _; cases ν <;> (try simp at h)))
  | cap c r =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> simp at h
        exact .cap h.1 (ieqD_sound h.2)
  | code a b k _ _ =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> (try simp at h)
        rename_i a' b' k'
        cases k <;> cases k' <;> simp at h
        · exact .codeR (tyEq_sound cx 0 _ _ h.1) (tyEq_sound cx 0 _ _ h.2)
        · exact .codeRR h.1.1.1.1 h.1.1.1.2 (fun h' => by rcases h.1.1.2 with h'' | h'' <;> simp_all)
            (tyEq_sound cx 0 _ _ h.1.2) (tyEq_sound cx 0 _ _ h.2)
  | _ =>
      intro τ h
      unfold sub at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact .eq (tyEq_sound cx 0 _ _ h)
      · cases τ <;> simp at h

/-! ## §3. The checker's monad, and the context-level premises -/

@[simp] theorem bind_ok_iff {α β : Type} (m : M α) (f : α → M β) (b : β) :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [bind, Except.bind]

@[simp] theorem throw_ok_iff {α : Type} (s : String) (b : α) :
    (throw s : M α) = .ok b ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw, Except.error]

@[simp] theorem pure_ok_iff {α : Type} (a b : α) : (pure a : M α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

@[simp] theorem ite_throw_ok_iff {α : Type} (p : Prop) [Decidable p] (s : String) (u b : α) :
    ((if p then throw s else pure u) : M α) = .ok b ↔ ¬p ∧ u = b := by
  by_cases hp : p <;> simp [hp]

@[simp] theorem map_ok_iff {α β : Type} (f : α → β) (m : M α) (b : β) :
    (f <$> m) = .ok b ↔ ∃ a, m = .ok a ∧ f a = b := by
  cases m <;> simp [Functor.map, Except.map]

/-- `intIdx`, declaratively: an integer of known index. -/
def IntIdx (cx : Cx) (a : At) (i : Idx) : Prop :=
  ∃ t, cx.peek a = .ok t ∧ intOf t = some (some i)

theorem intIdx_sound {cx : Cx} {a : At} {i : Idx} (h : intIdx cx a = .ok i) : IntIdx cx a i := by
  unfold intIdx at h
  simp only [bind_ok_iff] at h
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, ?_⟩
  split at h
  · rename_i j hj; simp at h; subst h; exact hj
  · simp at h

/-- A live token (of either shape: `tokRgn`) for a region equal to `r`. -/
def HasTok (cx : Cx) (r : Idx) : Prop :=
  ∃ y t s, (y, t, true) ∈ cx.vars ∧ tokRgn t = some s ∧ EqI cx r s

/-- A live token for `r`, whose region is not waiting for `fence st`: the
premise of a store into a region (§4.4 rule 7). -/
def HoldsSealed (cx : Cx) (r : Idx) : Prop :=
  ∃ y t s, (y, t, true) ∈ cx.vars ∧ tokRgn t = some s ∧ EqI cx r s ∧ s ∉ cx.unsealed

theorem hasTok_witness {cx : Cx} {r : Idx} (h : cx.hasTok r = true) :
    ∃ y t s, (y, t, true) ∈ cx.vars ∧ tokRgn t = some s ∧ cx.eqI r s = true := by
  unfold Cx.hasTok at h
  simp only [List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨y, t, b⟩, hm, hb, ht⟩ := h
  simp at hb; subst hb
  split at ht
  · rename_i s hs; exact ⟨y, t, s, hm, hs, ht⟩
  · simp at ht

theorem hasTok_sound {cx : Cx} {r : Idx} (h : cx.hasTok r = true) : HasTok cx r := by
  obtain ⟨y, t, s, hm, hs, he⟩ := hasTok_witness h
  exact ⟨y, t, s, hm, hs, eqI_sound cx r s he⟩

/-- A live epoch token `Tok[r, P, e]` (affine: looked at, not consumed). -/
def HasTokE (cx : Cx) (r : Idx) (P : ECounter) (e : Idx) : Prop :=
  ∃ y r' e', (y, .tokE r' P e', true) ∈ cx.vars ∧ EqI cx r r' ∧ EqI cx e e'

theorem hasTokE_sound {cx : Cx} {r e : Idx} {P : ECounter} (h : cx.hasTokE r P e = true) :
    HasTokE cx r P e := by
  unfold Cx.hasTokE at h
  simp only [List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨y, t, b⟩, hm, hb, ht⟩ := h
  simp at hb; subst hb
  cases t <;> simp at ht
  obtain ⟨⟨h1, rfl⟩, h2⟩ := ht
  exact ⟨y, _, _, hm, eqI_sound _ _ _ h1, eqI_sound _ _ _ h2⟩

theorem sawFor_sound {cx : Cx} {w : String} {j m : Idx} (h : sawFor cx w j = some m) :
    (w, m, true) ∈ cx.saws ∧ EqI cx (.add m (.lit 1)) j := by
  simp only [sawFor, Option.map_eq_some_iff] at h
  obtain ⟨⟨w', m', o⟩, hf, hm⟩ := h
  simp only at hm; subst hm
  have hp := List.find?_some hf
  have hmem := List.mem_of_find?_eq_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨rfl, ho⟩, he⟩ := hp
  subst ho
  exact ⟨hmem, eqI_sound _ _ _ he⟩

/-- A live read share for a region equal to `r`: enough to load from it. -/
def HasShare (cx : Cx) (r : Idx) : Prop :=
  ∃ y s, (y, Ty.share s, true) ∈ cx.vars ∧ EqI cx r s

theorem isShareOf_true {cx : Cx} {r : Idx} {e : String × Ty × Bool} (h : cx.isShareOf r e = true) :
    ∃ y s, e = (y, Ty.share s, true) ∧ cx.eqI r s = true := by
  obtain ⟨y, t, b⟩ := e
  cases t <;> cases b <;> simp [Cx.isShareOf] at h
  exact ⟨y, _, rfl, h⟩

theorem hasShare_sound {cx : Cx} {r : Idx} (h : cx.hasShare r = true) : HasShare cx r := by
  unfold Cx.hasShare at h
  obtain ⟨e, hm, he⟩ := List.any_eq_true.mp h
  obtain ⟨y, s, rfl, hs⟩ := isShareOf_true he
  exact ⟨y, s, hm, eqI_sound cx r s hs⟩

theorem shareOf_sound {cx : Cx} {r : Idx} {y : String} (h : cx.shareOf r = some y) :
    ∃ s, (y, Ty.share s, true) ∈ cx.vars ∧ EqI cx r s := by
  unfold Cx.shareOf at h
  cases hf : cx.vars.find? (cx.isShareOf r) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    obtain ⟨y', s, rfl, hs⟩ := isShareOf_true (List.find?_some hf)
    simp only at h; subst h
    exact ⟨s, List.mem_of_find?_eq_some hf, eqI_sound cx r s hs⟩

/-- A capability for a region equal to `r`; with `w`, one that writes. -/
def HasCap (cx : Cx) (r : Idx) (w : Bool) : Prop :=
  ∃ y c q, (y, Ty.cap c q, true) ∈ cx.vars ∧ EqI cx r q ∧ (w = true → c.writes = true)

theorem isCapOf_true {cx : Cx} {r : Idx} {w : Bool} {e : String × Ty × Bool}
    (h : cx.isCapOf r w e = true) :
    ∃ y c q, e = (y, Ty.cap c q, true) ∧ cx.eqI r q = true ∧ (w = true → c.writes = true) := by
  obtain ⟨y, t, b⟩ := e
  cases t <;> cases b <;> simp [Cx.isCapOf] at h
  rename_i c q
  refine ⟨y, c, q, rfl, h.1, ?_⟩
  intro hw; subst hw; simpa using h.2

theorem hasCap_sound {cx : Cx} {r : Idx} {w : Bool} (h : cx.hasCap r w = true) : HasCap cx r w := by
  unfold Cx.hasCap at h
  obtain ⟨e, hm, he⟩ := List.any_eq_true.mp h
  obtain ⟨y, c, q, rfl, hq, hw⟩ := isCapOf_true he
  exact ⟨y, c, q, hm, eqI_sound cx r q hq, hw⟩

theorem casCellTy_sound {cx : Cx} {tw u : Ty} (h : casCellTy cx tw = .ok u) :
    cellOf tw = some (.pub, u) ∨ ∃ r, cellOf tw = some (.rgn r, u) ∧ HasCap cx r true := by
  unfold casCellTy at h
  split at h
  · rename_i u' hc; simp at h; subst h; exact .inl hc
  · rename_i r u' hc
    split at h
    · rename_i hcap; simp at h; subst h; exact .inr ⟨r, hc, hasCap_sound hcap⟩
    · simp at h
  · simp at h

/-- A `bor` capability for a region equal to `r`: exclusive access, lent from
a token. -/
def HasBor (cx : Cx) (r : Idx) : Prop :=
  ∃ y q, (y, Ty.cap .bor q, true) ∈ cx.vars ∧ EqI cx r q

theorem isBorOf_true {cx : Cx} {r : Idx} {e : String × Ty × Bool} (h : cx.isBorOf r e = true) :
    ∃ y q, e = (y, Ty.cap .bor q, true) ∧ cx.eqI r q = true := by
  obtain ⟨y, t, b⟩ := e
  cases t <;> cases b <;> simp [Cx.isBorOf] at h
  obtain ⟨rfl, h⟩ := h
  exact ⟨y, _, rfl, h⟩

theorem hasBor_sound {cx : Cx} {r : Idx} (h : cx.hasBor r = true) : HasBor cx r := by
  unfold Cx.hasBor at h
  obtain ⟨e, hm, he⟩ := List.any_eq_true.mp h
  obtain ⟨y, q, rfl, hq⟩ := isBorOf_true he
  exact ⟨y, q, hm, eqI_sound cx r q hq⟩

theorem readable_sound {cx : Cx} {r : Idx} (h : (cx.hasTok r || cx.hasShare r) = true) :
    HasTok cx r ∨ HasShare cx r := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact .inl (hasTok_sound h)
  · exact .inr (hasShare_sound h)

/-- `lendCx`, declaratively: the success context of a `cas` between holding
states, with the read-share bookkeeping `ShareMove` asks for. -/
inductive LendCx (cx : Cx) (acq rel : Bool) (r : Idx) (t : String) (P : Proto)
    (c : Nat) (k : Idx) (c' : Nat) (k' : Idx) : Cx → Prop
  | none {c₂ : Cx} : ShareMove P c k c' k' 0 → cx.bind t .unit = .ok c₂ →
      LendCx cx acq rel r t P c k c' k' c₂
  | up {c₂ : Cx} : ShareMove P c k c' k' 1 → acq = true → cx.bind t (.share r) = .ok c₂ →
      LendCx cx acq rel r t P c k c' k' c₂
  | down {c₁ c₂ : Cx} {y : String} {s : Idx} {ts : Ty} : ShareMove P c k c' k' (-1) → rel = true →
      (y, Ty.share s, true) ∈ cx.vars → EqI cx r s → cx.use (.var y) = .ok (ts, c₁) →
      c₁.bind t .unit = .ok c₂ → LendCx cx acq rel r t P c k c' k' c₂

theorem lendCx_sound {cx c₂ : Cx} {acq rel : Bool} {r : Idx} {t : String} {P : Proto}
    {c c' : Nat} {k k' : Lin}
    (h : lendCx cx acq rel r (shareMove P c k c' k') t = .ok c₂) :
    LendCx cx acq rel r t P c k.toIdx c' k'.toIdx c₂ := by
  unfold lendCx at h
  cases hm : shareMove P c k c' k' with
  | none => simp [hm] at h
  | some m =>
    simp only [hm] at h
    have hs := shareMove_sound P c k c' k' m hm
    split at h
    · rename_i h0; simp at h0; subst h0; exact .none hs h
    · split at h
      · rename_i h1; simp at h1; subst h1
        split at h
        · simp at h
        · rename_i ha; exact .up hs (by simpa using ha) h
      · split at h
        · rename_i h2; simp at h2; subst h2
          split at h
          · simp at h
          · rename_i hr
            split at h
            · simp at h
            · rename_i y hy
              obtain ⟨s, hmem, hse⟩ := shareOf_sound hy
              simp only [bind_ok_iff] at h
              obtain ⟨⟨ts, c₁⟩, h5, h6⟩ := h
              exact .down hs (by simpa using hr) hmem hse h5 h6
        · simp at h

theorem eqI_refl (cx : Cx) (r : Idx) : cx.eqI r r = true := by simp [Cx.eqI]

theorem sealed_not_mem {cx : Cx} {r s : Idx} (h : cx.sealedR r = true) (he : cx.eqI r s = true) :
    s ∉ cx.unsealed := by
  intro hs
  unfold Cx.sealedR at h
  simp only [Bool.not_eq_true', List.any_eq_false] at h
  exact absurd he (by simpa using h s hs)

theorem holdsSealed_sound {cx : Cx} {r : Idx} (h1 : cx.hasTok r = true) (h2 : cx.sealedR r = true) :
    HoldsSealed cx r := by
  obtain ⟨y, t, s, hm, hs, he⟩ := hasTok_witness h1
  exact ⟨y, t, s, hm, hs, eqI_sound cx r s he, sealed_not_mem h2 he⟩

/-- `xchgCell`, declaratively: an own cell, or a region cell held exclusively
(sealed token or `bor`).  The second type is what comes out. -/
inductive XchgCell (cx : Cx) : Ty → Ty → Ty → Prop
  | own {t u : Ty} : wordOf t = none → cellOf t = some (.own, u) → Ty.wordFreeIn cx.ke u = true → XchgCell cx t u u
  | rgn {t u : Ty} {r : Idx} : wordOf t = none → cellOf t = some (.rgn r, u) → Ty.wordFreeIn cx.ke u = true →
      Ty.noOwnIn cx.ke (adapt r u) = true →
      HoldsSealed cx r ∨ HasBor cx r → XchgCell cx t u (adapt r u)

theorem xchgCell_sound {cx : Cx} {t u o : Ty} (h : xchgCell cx t = .ok (u, o)) : XchgCell cx t u o := by
  unfold xchgCell at h
  split at h
  · simp at h
  · rename_i hw
    split at h
    · rename_i u' hc
      split at h
      · simp at h
      · rename_i hwf; simp at h; obtain ⟨rfl, rfl⟩ := h; exact .own hw hc (by simpa using hwf)
    · rename_i r u' hc
      split at h
      · simp at h
      rename_i hwf
      split at h
      · simp at h
      · rename_i hno
        split at h
        · rename_i hh
          simp at h; obtain ⟨rfl, rfl⟩ := h
          refine .rgn hw hc (by simpa using hwf) (by simpa using hno) ?_
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hh
          rcases hh with ⟨h1, h2⟩ | h3
          · exact .inl (holdsSealed_sound h1 h2)
          · exact .inr (hasBor_sound h3)
        · simp at h
    · simp at h
    · simp at h

/-- No token leaves while its region waits for `fence st`. -/
def NoLeak (cx : Cx) (t : Ty) : Prop := ∀ r ∈ toksOf t, r ∉ cx.unsealed

theorem noLeak_sound {cx : Cx} {t : Ty} {u : Unit} (h : noLeak cx t = .ok u) : NoLeak cx t := by
  unfold noLeak at h
  split at h
  · simp at h
  · rename_i hn
    intro r hr
    simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and, Bool.not_eq_false] at hn
    exact sealed_not_mem (by simpa using hn r hr) (eqI_refl cx r)

/-- A state at which a protocol word holds its region, at some parameter. -/
def Holds (cx : Cx) (P : Proto) (s : Idx) : Prop :=
  ∃ c k cl, P.clauses[c]? = some cl ∧ InState cx P s c k ∧ cl.holds = true

/-- §4.4 rule 2, declaratively: an ordered observation `Saw(w, s)` of the word
of a region equal to `r`, whose protocol is monotone and whose observed state
holds the region. -/
def TornLic (cx : Cx) (r : Idx) (w : String) (s : Idx) : Prop :=
  (w, s, true) ∈ cx.saws ∧
  ∃ t b r' P, cx.find w = .ok (t, b) ∧ wordOf t = some (r', P) ∧ EqI cx r r' ∧
    monotone P = true ∧ Holds cx P s

theorem firstOk_sound {α β : Type} (f : α → M β) :
    ∀ (l : List α) (why : String) (b : β), firstOk f l why = .ok b → ∃ a ∈ l, f a = .ok b
  | [], why, b, h => by simp [firstOk] at h
  | a :: as, why, b, h => by
      unfold firstOk at h
      split at h
      · rename_i b' hb; simp at h; subst h; exact ⟨a, by simp, hb⟩
      · obtain ⟨a', ha', hf⟩ := firstOk_sound f as _ b h
        exact ⟨a', by simp [ha'], hf⟩

theorem licenceOf_sound {cx : Cx} {r : Idx} {e : String × Idx × Bool} {w : String} {s : Idx}
    (h : licenceOf cx r e = .ok (w, s)) :
    e.1 = w ∧ e.2.1 = s ∧ ∃ t b r' P, cx.find w = .ok (t, b) ∧ wordOf t = some (r', P) ∧
      EqI cx r r' ∧ monotone P = true ∧ Holds cx P s := by
  obtain ⟨w₀, s₀, o⟩ := e
  simp only [licenceOf, bind_ok_iff] at h
  obtain ⟨⟨t, b⟩, hf, h⟩ := h
  simp only at h
  split at h
  · simp at h
  · rename_i r' P hw
    split at h
    · simp at h
    · rename_i he
      split at h
      · simp at h
      · rename_i hm
        split at h
        · rename_i c k hc
          split at h
          · rename_i cl hcl
            split at h
            · rename_i hh
              simp at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, rfl, t, b, r', P, hf, hw, eqI_sound _ _ _ (by simpa using he),
                by simpa using hm, c, k.toIdx, cl, hcl, classifyM_sound _ _ _ _ _ hc, hh⟩
            · simp at h
          · simp at h
        · simp at h

theorem tornLicence_sound {cx : Cx} {r : Idx} {w : String} {s : Idx}
    (h : tornLicence cx r = .ok (w, s)) : TornLic cx r w s := by
  unfold tornLicence at h
  simp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  obtain ⟨e, he, hl⟩ := firstOk_sound _ _ _ _ h
  obtain ⟨rfl, rfl, rest⟩ := licenceOf_sound hl
  simp only [List.mem_filter] at he
  obtain ⟨⟨hmem, _⟩, ho⟩ := he
  obtain ⟨w₀, s₀, o⟩ := e
  simp at ho; subst ho
  exact ⟨hmem, rest⟩

/-! ## §4. The judgement

`OpT p cx x op cx'`: in program `p`, `let x = op` takes context `cx` to `cx'`.
`Typed p cx e`: `e` is well typed in `cx`.  One rule per case of the
checker, with the checker's decisions replaced by `Prop`s: `SubS` for `sub`,
`EqI`/`InState`/`Step` for the arithmetic, `HasTok`/`HoldsSealed`/`NoLeak`/
`TornLic` for the region discipline, and existentials for the choices. -/

inductive FoldOK (cx : Cx) : Ty → Ty → Prop
  | ptr {μ ν : Mode} {u s : Ty} : MEq cx 0 μ ν → TyEqS cx 0 u (unfold1 (.mu s)) →
      FoldOK cx (.ptr μ u) (.ptr ν (.mu s))
  | ptrOpt {μ ν : Mode} {u s : Ty} : MEq cx 0 μ ν → TyEqS cx 0 u (unfold1 (.mu s)) →
      FoldOK cx (.ptrOpt μ u) (.ptrOpt ν (.mu s))
  | loc {μ ν : Mode} {u s : Ty} : MEq cx 0 μ ν → TyEqS cx 0 u (unfold1 (.mu s)) →
      FoldOK cx (.loc μ u) (.loc ν (.mu s))

/-- Observing protocol word `w` into `x`: a fresh index `var 0` for its value,
`Saw(w, var 0)`, and the re-check of every fenced torn read on `w`. -/
def observeCx (cx : Cx) (x w : String) (acq : Bool) : Cx :=
  let cx := cx.push x
  { cx with
    saws := (w, .var 0, acq) :: cx.saws
    torn := cx.torn.map fun (tn : Torn) =>
      if tn.w == w && tn.φ == Phase.fenced then { tn with φ := .rechecked (.var 0) } else tn }

/-- The context after `fence f`: `ld` (and `full`) orders observations and
advances torn reads; `st` (and `full`) seals the regions taken. -/
def fenceCx (cx : Cx) (f : Fence) : Cx :=
  let cx := if f != .st then
      { cx with torn := cx.torn.map fun (tn : Torn) => { tn with φ := phaseFence tn.φ }
                saws := cx.saws.map fun (w, s, _) => (w, s, true) }
    else cx
  if f != .ld then { cx with unsealed := [] } else cx

/-- The context in which a code block's body is checked. -/
def declCx (d : Decl) : Cx :=
  { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
    ke := d.tparams.reverse.map some }

inductive OpT (p : Prog) : Cx → String → Op → Cx → Prop
  | atom {cx c₁ c' : Cx} {x : String} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → c₁.bind x t = .ok c' → OpT p cx x (.atom a) c'
  | pair {cx c₁ c₂ c' : Cx} {x : String} {a b : At} {t u : Ty} :
      cx.use a = .ok (t, c₁) → c₁.use b = .ok (u, c₂) → c₂.bind x (.prod t u) = .ok c' →
      OpT p cx x (.pair a b) c'
  | inl {cx c₁ c' : Cx} {x : String} {a : At} {t τ : Ty} :
      τ.wf cx.ke.length 0 = true → cx.use a = .ok (t, c₁) → c₁.bind x (.sum t τ) = .ok c' →
      OpT p cx x (.inl τ a) c'
  | inr {cx c₁ c' : Cx} {x : String} {a : At} {t τ : Ty} :
      τ.wf cx.ke.length 0 = true → cx.use a = .ok (t, c₁) → c₁.bind x (.sum τ t) = .ok c' →
      OpT p cx x (.inr τ a) c'
  | addS {cx c' : Cx} {x : String} {a b : At} {t u : Ty} {i j : Idx} :
      cx.peek a = .ok t → cx.peek b = .ok u → intOf t = some (some i) → intOf u = some (some j) →
      cx.bind x (.intS (.add i j)) = .ok c' → OpT p cx x (.add a b) c'
  | addI {cx c' : Cx} {x : String} {a b : At} {t u : Ty} {o o' : Option Idx} :
      cx.peek a = .ok t → cx.peek b = .ok u → intOf t = some o → intOf u = some o' →
      cx.bind x .int = .ok c' → OpT p cx x (.add a b) c'
  | subS {cx c' : Cx} {x : String} {a b : At} {t u : Ty} {i j d : Idx} :
      cx.peek a = .ok t → cx.peek b = .ok u → intOf t = some (some i) → intOf u = some (some j) →
      Ent cx (fun ρ => ev ρ d + ev ρ j = ev ρ i) →
      cx.bind x (.intS d) = .ok c' → OpT p cx x (.sub a b) c'
  | new {cx c₁ c' : Cx} {x : String} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → t.secondClass = false → c₁.bind x (.ptr .own t) = .ok c' →
      OpT p cx x (.new a (some t)) c'
  | isTy {cx c' : Cx} {x : String} {a : At} {τ b : Ty} {κ : Kind} :
      cx.peek a = .ok (.tex κ b) → slotOK b = true → τ.wf 0 0 = true → tgtOK τ = true →
      admitsIn cx κ τ = true → cx.bind x (.ptrOpt .pub τ) = .ok c' → OpT p cx x (.isTy a τ) c'
  | publish {cx c₁ c' : Cx} {x : String} {a : At} {u : Ty} :
      cx.use a = .ok (.ptr .own u, c₁) → Ty.sharedOKIn c₁.ke (.ptr .pub u) = true →
      c₁.bind x (.ptr .pub u) = .ok c' → OpT p cx x (.publish a) c'
  | publishBuf {cx c₁ c' : Cx} {x : String} {a : At} {n k : Idx} {u : Ty} :
      cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) →
      Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true →
      c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c' → OpT p cx x (.publish a) c'
  /-- D1: `publish` with a region-mode result.  The fence (runtime) hides the
  placeholders; the token gates the writes, so none is needed here. -/
  | intoRgn {cx c₁ c' : Cx} {x rn : String} {a : At} {r : Idx} {u : Ty} :
      cx.idx rn = .ok r → cx.use a = .ok (.ptr .own u, c₁) → rgnCellOK c₁.ke u = true →
      c₁.bind x (.ptr (.rgn r) u) = .ok c' → OpT p cx x (.intoRgn rn a) c'
  | intoRgnBuf {cx c₁ c' : Cx} {x rn : String} {a : At} {r n k : Idx} {u : Ty} :
      cx.idx rn = .ok r → cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) →
      rgnCellOK c₁.ke (.array n u) = true →
      c₁.bind x (.refine (.loc (.rgn r) (.array n u)) (.ini k)) = .ok c' → OpT p cx x (.intoRgn rn a) c'
  | newBuf {cx c' : Cx} {x : String} {n : At} {τ : Ty} {k : Idx} :
      τ.wf cx.ke.length cx.inames.length = true → τ.secondClass = false →
      cx.opaqueOK τ = true → τ.arrFree = true → IntIdx cx n k →
      cx.bind x (.refine (.loc .own (.array k τ))
        (.ini (if zeroableIn [] cx.ke τ then k else .lit 0))) = .ok c' → OpT p cx x (.newBuf n τ) c'
  | idxOwn {cx c₁ c' : Cx} {x : String} {b i : At} {t t' u : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → IntIdx cx i j → LtI cx j n → LtI cx j k →
      cx.opaqueOK u = true → cx.use b = .ok (t', c₁) → c₁.bind x (.loc .own u) = .ok c' →
      OpT p cx x (.idx b i) c'
  | idxShared {cx c' : Cx} {x : String} {b i : At} {t u : Ty} {μ : Mode} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (μ, n, u, k) → μ ≠ .own → IntIdx cx i j → LtI cx j n →
      LtI cx j k → cx.opaqueOK u = true → cx.bind x (.loc μ u) = .ok c' → OpT p cx x (.idx b i) c'
  | bufInit {cx c₁ c₂ c' : Cx} {x : String} {b i v : At} {t tv u : Ty} {n k j : Idx} :
      cx.use b = .ok (t, c₁) → bufOf t = some (.own, n, u, k) → IntIdx c₁ i j → EqI c₁ j k →
      LtI c₁ k n → c₁.use v = .ok (tv, c₂) → SubS c₂ tv u →
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' →
      OpT p cx x (.bufInit b i v) c'
  | null {cx c' : Cx} {x : String} {μ : Mode} {τ : Ty} :
      (Ty.ptrOpt μ τ).wf cx.ke.length cx.inames.length = true →
      cx.bind x (.ptrOpt μ τ) = .ok c' → OpT p cx x (.null μ τ) c'
  | fold {cx c₁ c' : Cx} {x : String} {a : At} {t τ : Ty} :
      τ.wf cx.ke.length cx.inames.length = true → cx.use a = .ok (t, c₁) → FoldOK c₁ t τ →
      c₁.bind x τ = .ok c' → OpT p cx x (.fold a τ) c'
  | fldOwn {cx c₁ c' : Cx} {x : String} {i : Nat} {a : At} {t t' u c1 c2 : Ty} :
      cx.peek a = .ok t → cellOf t = some (.own, u) → unfold1 u = .prod c1 c2 →
      (i ≠ 0 → cx.opaqueOK c1 = true) →
      cx.use a = .ok (t', c₁) → c₁.bind x (.loc .own (if i == 0 then c1 else c2)) = .ok c' →
      OpT p cx x (.fld i a) c'
  | fldShared {cx c' : Cx} {x : String} {i : Nat} {a : At} {t u c1 c2 : Ty} {μ : Mode} :
      cx.peek a = .ok t → cellOf t = some (μ, u) → μ ≠ .own → unfold1 u = .prod c1 c2 →
      (i ≠ 0 → cx.opaqueOK c1 = true) →
      cx.bind x (.loc μ (if i == 0 then c1 else c2)) = .ok c' → OpT p cx x (.fld i a) c'
  | loadWord {cx c' : Cx} {x w : String} {acq : Bool} {t : Ty} {rP : Idx × Proto} :
      cx.peek (.var w) = .ok t → wordOf t = some rP → rP.2.ghost = false →
      (observeCx cx x w acq).bind x (.intS (.var 0)) = .ok c' → OpT p cx x (.load acq (.var w)) c'
  | loadOwn {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.own, u) → affine cx.ke u = false →
      cx.bind x u = .ok c' → OpT p cx x (.load acq a) c'
  | loadPub {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.pub, u) → affine cx.ke u = false →
      (Ty.sensitiveIn cx.ke u = true → acq = true) →
      cx.bind x u = .ok c' → OpT p cx x (.load acq a) c'
  | loadRgn {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) → HasTok cx r ∨ HasShare cx r →
      affine cx.ke (adapt r u) = false →
      cx.bind x (adapt r u) = .ok c' → OpT p cx x (.load acq a) c'
  /-- Under a capability: pub discipline, so a view-sensitive load needs `acq`. -/
  | loadCap {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) → HasCap cx r false →
      (Ty.sensitiveIn cx.ke (adapt r u) = true → acq = true) → affine cx.ke (adapt r u) = false →
      cx.bind x (adapt r u) = .ok c' → OpT p cx x (.load acq a) c'
  | loadTorn {cx : Cx} {x w : String} {acq : Bool} {a : At} {t u : Ty} {r s : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) → TornLic cx r w s →
      cx.vars.any (·.1 == x) = false → cx.torn.any (·.x == x) = false →
      OpT p cx x (.load acq a) { cx with torn := ⟨x, adapt r u, w, s, .opn⟩ :: cx.torn }
  | storeWordGive {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v tk : At} {t : Ty} {r r' i j k k' : Idx}
      {P : Proto} {c c₂ : Nat} {cl cl' : Clause} :
      cx.peek a = .ok t → wordOf t = some (r, P) → cx.use tk = .ok (.tok r' (some (P, i)), c₁) →
      EqI c₁ r r' → IntIdx c₁ v j →
      InState c₁ P i c k → P.clauses[c]? = some cl → InState c₁ P j c₂ k' → P.clauses[c₂]? = some cl' →
      cl.holds = false → Step c₁ P c k c₂ k' → cl'.holds = true → (P.ghost = false → rel = true) →
      c₁.bind x .unit = .ok c' → OpT p cx x (.store rel a v (some tk)) c'
  | storeWordKeep {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v tk : At} {t : Ty} {r r' i j k k' : Idx}
      {P : Proto} {c c₂ : Nat} {cl cl' : Clause} :
      cx.peek a = .ok t → wordOf t = some (r, P) → cx.use tk = .ok (.tok r' (some (P, i)), c₁) →
      EqI c₁ r r' → IntIdx c₁ v j →
      InState c₁ P i c k → P.clauses[c]? = some cl → InState c₁ P j c₂ k' → P.clauses[c₂]? = some cl' →
      cl.holds = false → Step c₁ P c k c₂ k' → cl'.holds = false → P.ticket = false →
      c₁.bind x (.tok r' (some (P, j))) = .ok c' → OpT p cx x (.store rel a v (some tk)) c'
  /-- The ticket lock's release: a held-to-held store under `ticket` hands the
  lock on (the next ticket's holder claims it) rather than keeping a token. -/
  | storeWordHand {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v tk : At} {t : Ty} {r r' i j k k' : Idx}
      {P : Proto} {c c₂ : Nat} {cl cl' : Clause} :
      cx.peek a = .ok t → wordOf t = some (r, P) → cx.use tk = .ok (.tok r' (some (P, i)), c₁) →
      EqI c₁ r r' → IntIdx c₁ v j →
      InState c₁ P i c k → P.clauses[c]? = some cl → InState c₁ P j c₂ k' → P.clauses[c₂]? = some cl' →
      cl.holds = false → Step c₁ P c k c₂ k' → cl'.holds = false → P.ticket = true → rel = true →
      c₁.bind x .unit = .ok c' → OpT p cx x (.store rel a v (some tk)) c'
  | storeOwn {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.own, u) → Ty.wordFreeIn cx.ke u = true → cx.use v = .ok (tv, c₁) →
      SubS c₁ tv u → c₁.bind x .unit = .ok c' → OpT p cx x (.store rel a v tok) c'
  | storePub {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.pub, u) → Ty.wordFreeIn cx.ke u = true → cx.use v = .ok (tv, c₁) →
      SubS c₁ tv u → (Ty.sensitiveIn c₁.ke u = true → rel = true) →
      c₁.bind x .unit = .ok c' → OpT p cx x (.store rel a v tok) c'
  | storeRgn {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty}
      {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) → Ty.wordFreeIn cx.ke u = true → cx.use v = .ok (tv, c₁) →
      HoldsSealed c₁ r → (SubS c₁ tv u ∨ SubS c₁ tv (adapt r u)) →
      c₁.bind x .unit = .ok c' → OpT p cx x (.store rel a v tok) c'
  | storeCap {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At} {t u tv : Ty}
      {r : Idx} :
      cx.peek a = .ok t → wordOf t = none → cellOf t = some (.rgn r, u) → Ty.wordFreeIn cx.ke u = true → cx.use v = .ok (tv, c₁) →
      HasCap c₁ r true → (Ty.sensitiveIn c₁.ke u = true → rel = true) →
      (SubS c₁ tv u ∨ SubS c₁ tv (adapt r u)) →
      c₁.bind x .unit = .ok c' → OpT p cx x (.store rel a v tok) c'
  | fence {cx c' : Cx} {x : String} {f : Fence} :
      (fenceCx cx f).bind x .unit = .ok c' → OpT p cx x (.fence f) c'
  | mkWord {cx c₁ c' : Cx} {x rn : String} {P : Proto} {v tk : At} {r r' j k : Idx} {c : Nat}
      {cl : Clause} :
      cx.idx rn = .ok r → pwf P = true → cx.use tk = .ok (.tok r' none, c₁) → EqI c₁ r r' →
      IntIdx c₁ v j → InState c₁ P j c k → P.clauses[c]? = some cl → P.ghost = false → cl.holds = true →
      c₁.bind x (.word r P) = .ok c' → OpT p cx x (.mkWord rn P v tk) c'
  /-- A ghost word is born taken: there is no runtime word to arbitrate a take. -/
  | mkWordGhost {cx c₁ c' : Cx} {x rn : String} {P : Proto} {v tk : At} {r r' j k : Idx} {c : Nat}
      {cl : Clause} :
      cx.idx rn = .ok r → pwf P = true → cx.use tk = .ok (.tok r' none, c₁) → EqI c₁ r r' →
      IntIdx c₁ v j → InState c₁ P j c k → P.clauses[c]? = some cl → P.ghost = true → cl.holds = false →
      c₁.bind x (.prod (.word r P) (.tok r (some (P, j)))) = .ok c' → OpT p cx x (.mkWord rn P v tk) c'
  /-- A protocol pair: born from a fresh region token, in a shared state. -/
  | mkWord2 {cx c₁ c' : Cx} {x rn : String} {P : Proto2} {v0 v1 tk : At} {r r' j0 j1 k0 k1 : Idx}
      {c : Nat} {cl : Clause2} :
      cx.idx rn = .ok r → pwf2 P = true → cx.use tk = .ok (.tok r' none, c₁) → EqI c₁ r r' →
      IntIdx c₁ v0 j0 → IntIdx c₁ v1 j1 → InState2 c₁ P j0 j1 c k0 k1 → P.clauses[c]? = some cl →
      cl.holds = true → c₁.bind x (.word2 r P) = .ok c' → OpT p cx x (.mkWord2 rn P v0 v1 tk) c'
  /-- Observing a pair: two fresh indices, no `Saw` (a pair licenses no torn read). -/
  | ldp {cx c' : Cx} {x w n0 n1 : String} {acq : Bool} {t : Ty} :
      cx.peek (.var w) = .ok t → pairRef t = true →
      ((cx.push n0).push n1).bind x (.prod (.intS (.var 1)) (.intS (.var 0))) = .ok c' →
      OpT p cx x (.ldp acq (.var w) n0 n1) c'
  /-- An epoch pair `EPair[r, P]`: a `pub` payload `(epoch, value)` under the
  epoch counter `P` of region `r`.  It holds nothing, so no token is needed. -/
  | mkEPair {cx c' : Cx} {x rn : String} {P : ECounter} {v0 v1 : At} {r j0 j1 : Idx} :
      cx.idx rn = .ok r → pwfE P = true → IntIdx cx v0 j0 → IntIdx cx v1 j1 →
      cx.bind x (.epair r P) = .ok c' → OpT p cx x (.mkEPair rn P v0 v1) c'
  /-- A ticket lock from the region's token: dispenser (an epoch counter) and
  owner (a `ticket` protocol), both at `v`; nothing holds the owner's token. -/
  | mkTicket {cx c₁ c' : Cx} {x rn : String} {N P : Proto} {v tk : At} {r r' j : Idx} :
      cx.idx rn = .ok r → pwf N = true → N.epoch = true → pwf P = true → P.ticket = true →
      cx.use tk = .ok (.tok r' none, c₁) → EqI c₁ r r' → IntIdx c₁ v j →
      c₁.bind x (.prod (.word r N) (.word r P)) = .ok c' → OpT p cx x (.mkTicket rn N P v tk) c'
  /-- Acquisition by observation: ticket `j` (an epoch token of the region)
  and an ordered observation `Saw(w, m)` of the owner with `m + 1 = j` yield
  the owner's token at `m`.  The ticket is consumed. -/
  | claim {cx c₁ c' : Cx} {x w : String} {tk : At} {t : Ty} {rP : Idx × Proto} {Q : ECounter}
      {r' j m : Idx} :
      cx.peek (.var w) = .ok t → wordOf t = some rP → rP.2.ticket = true →
      cx.use tk = .ok (.tokE r' Q j, c₁) → EqI c₁ rP.1 r' →
      (w, m, true) ∈ c₁.saws → EqI c₁ (.add m (.lit 1)) j →
      c₁.bind x (.tok rP.1 (some (rP.2, m))) = .ok c' → OpT p cx x (.claim (.var w) tk) c'
  /-- A fetch-op on a plain `Int` cell -- `pub`, or a region cell under a
  writing capability, as `casCell`: the old value, as an `Int`.  The cell's
  type is invariant and nothing is duplicated, so the race is one the
  language already allows. -/
  | fetchCell {cx c₁ c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {tw tv : Ty} :
      cx.peek a = .ok tw → wordOf tw = none →
      (cellOf tw = some (.pub, .int) ∨ ∃ r, cellOf tw = some (.rgn r, .int) ∧ HasCap cx r true) →
      cx.use v = .ok (tv, c₁) → SubS c₁ tv .int → c₁.bind x .int = .ok c' →
      OpT p cx x (.fetch o acq rel a v) c'
  /-- A fetch-add of 1 on an epoch counter (`P.epoch`): enters the next epoch
  and yields its token with the old value, under an existential for the old
  value (`fetchEpochTy`).  The counter's one move is `+1` from every state. -/
  | fetchEpoch {cx c' : Cx} {x : String} {acq rel : Bool} {a v : At} {tw : Ty} {r j : Idx} {P : Proto} :
      cx.peek a = .ok tw → wordOf tw = some (r, P) → P.epoch = true → acq = true →
      IntIdx cx v j → EqI cx j (.lit 1) → cx.bind x (fetchEpochTy r P) = .ok c' →
      OpT p cx x (.fetch .add acq rel a v) c'
  /-- A fetch-add of a constant `d` on a protocol word whose every family is
  shared and has a `+d` move (`fetchOK`): the old value, as an `Int`.  Nothing
  changes hands, whichever state the word was in. -/
  | fetchShare {cx c' : Cx} {x : String} {acq rel : Bool} {a v : At} {tw : Ty} {r j : Idx} {P : Proto}
      {d : Nat} :
      cx.peek a = .ok tw → wordOf tw = some (r, P) → P.epoch = false →
      IntIdx cx v j → EqI cx j (.lit d) → fetchOK P d = true → cx.bind x .int = .ok c' →
      OpT p cx x (.fetch .add acq rel a v) c'
  | stpGive {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty}
      {r r' i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c₂ : Nat} {cl cl' : Clause2} :
      cx.peek a = .ok t → word2Of t = some (r, P) → cx.use tk = .ok (.tok2 r' P i0 i1, c₁) →
      EqI c₁ r r' → IntIdx c₁ v0 j0 → IntIdx c₁ v1 j1 →
      InState2 c₁ P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 c₁ P j0 j1 c₂ k0' k1' → P.clauses[c₂]? = some cl' →
      cl.holds = false → Step2 c₁ P c k0 k1 c₂ k0' k1' → cl'.holds = true → rel = true →
      c₁.bind x .unit = .ok c' → OpT p cx x (.stp rel a v0 v1 tk) c'
  | stpKeep {cx c₁ c' : Cx} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty}
      {r r' i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c₂ : Nat} {cl cl' : Clause2} :
      cx.peek a = .ok t → word2Of t = some (r, P) → cx.use tk = .ok (.tok2 r' P i0 i1, c₁) →
      EqI c₁ r r' → IntIdx c₁ v0 j0 → IntIdx c₁ v1 j1 →
      InState2 c₁ P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 c₁ P j0 j1 c₂ k0' k1' → P.clauses[c₂]? = some cl' →
      cl.holds = false → Step2 c₁ P c k0 k1 c₂ k0' k1' → cl'.holds = false →
      c₁.bind x (.tok2 r' P j0 j1) = .ok c' → OpT p cx x (.stp rel a v0 v1 tk) c'
  | pack {cx c₁ c' : Cx} {x wn : String} {a : At} {w : Idx} {body t : Ty} :
      cx.idx wn = .ok w → (Ty.iex body).wf cx.ke.length cx.inames.length = true → cx.use a = .ok (t, c₁) →
      NoLeak c₁ t → SubS c₁ t (instT [w] 0 body) → c₁.bind x (.iex body) = .ok c' →
      OpT p cx x (.pack a wn (.iex body)) c'
  /-- A type existential: the variable guarded, the witness admitted, the value
  the body at the witness. -/
  | packT {cx c₁ c' : Cx} {x : String} {a : At} {σ body t : Ty} {κ : Kind} :
      body.guardT 0 = true → (Ty.tex κ body).wf cx.ke.length 0 = true → admitsIn cx κ σ = true →
      cx.use a = .ok (t, c₁) → NoLeak c₁ t → SubS c₁ t (Ty.substT 0 σ body) →
      c₁.bind x (.tex κ body) = .ok c' → OpT p cx x (.packT a σ (.tex κ body)) c'
  | validate {cx c' : Cx} {x y : String} {tn : Torn} {v : Idx} :
      cx.torn.find? (·.x == y) = some tn → tn.φ = .rechecked v → EqI cx v tn.s →
      affine cx.ke tn.ty = false → cx.bind x tn.ty = .ok c' → OpT p cx x (.validate y) c'
  | call {cx c₁ c' : Cx} {x f : String} {is : List String} {a : At} {ts : List Ty} {d : Decl}
      {at_ rt t : Ty} :
      p.find f = .ok d → instantiate cx d is ts = .ok (at_, rt) → cx.use a = .ok (t, c₁) →
      NoLeak c₁ t → SubS c₁ t at_ → c₁.bind x rt = .ok c' → OpT p cx x (.call f is a ts) c'
  /-- A runtime spawn (`checkOp`'s `.spawn`): the child's body is checked by `tailCheck`. -/
  | spawn {cx c₁ c' : Cx} {x f : String} {a : At} {T : Ty} {ts : List Ty} {t : Ty} {d : Decl} {at_ rt : Ty} :
      cx.use a = .ok (t, c₁) → SubS c₁ t T → (affine c₁.ke t || affine c₁.ke T) = false →
      T.wf c₁.ke.length 0 = true → ts.all (·.wf c₁.ke.length 0) = true →
      TermClose.tb 0 T = true → ts.all (TermClose.tb 0) = true →
      TermScope.drf T = true → ts.all TermScope.drf = true →
      TermScope.wrapOK T = true → ts.all TermScope.argOK = true →
      p.find f = .ok d → instantiate { vars := [("a", T, true)], ret := .unit } d [] ts = .ok (at_, rt) →
      tailCheck p { vars := [("a", T, true)], ret := rt } f [] (.var "a") ts = .ok () →
      (TermClose.tb 0 rt && TermTv.mg rt && TermTv.noIallV rt) = true →
      c₁.bind x .tid = .ok c' → OpT p cx x (.spawn f a T ts) c'
  /-- (E1) A trusted extern (`checkOp`'s `.ext`): the argument at the extern's type. -/
  | ext {cx c₁ c' : Cx} {x : String} {n : ExtName} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → n.ok = true → SubS c₁ t n.sig.1 → c₁.bind x n.sig.2 = .ok c' →
      OpT p cx x (.ext n a) c'
  /-- Lend a token or share: it is used up and recorded as lent. -/
  | borrow {cx c₁ c' : Cx} {x y : String} {c : Cap} {a : At} {t t' : Ty} {r : Idx} :
      varOf a = .ok y → cx.peek a = .ok t → lendOf cx c t = .ok r → cx.use a = .ok (t', c₁) →
      { c₁ with lent := y :: c₁.lent }.bind x (.cap c r) = .ok c' → OpT p cx x (.borrow c a) c'
  /-- Freeze a region: its fresh token is spent for good, for a copyable `frz`. -/
  | freeze {cx c₁ c' : Cx} {x : String} {a : At} {r : Idx} :
      cx.use a = .ok (.tok r none, c₁) → c₁.sealedR r = true → c₁.bind x (.cap .frz r) = .ok c' →
      OpT p cx x (.freeze a) c'
  | endBorrow {cx c' : Cx} {x y : String} {a : At} :
      varOf a = .ok y → cx.lent.contains y = true → (cx.endCx y).bind x .unit = .ok c' →
      OpT p cx x (.endBorrow a) c'
  /-- Exchange in an exclusively held cell: the new value goes in, the old comes out. -/
  | xchg {cx c₁ c' : Cx} {x : String} {a v : At} {t u o tv : Ty} :
      cx.peek a = .ok t → XchgCell cx t u o → cx.use v = .ok (tv, c₁) →
      (SubS c₁ tv u ∨ SubS c₁ tv o) → c₁.bind x o = .ok c' → OpT p cx x (.xchg a v) c'
  /-- A monomorphic code block as a value. -/
  | fnptr {cx c' : Cx} {x f : String} {d : Decl} :
      p.find f = .ok d → d.tparams = [] → d.idx = [] →
      cx.bind x (.code d.argTy d.retTy (match d.kind with | .restricted f s ro _ => .restricted f s ro | _ => .plain)) = .ok c' →
      OpT p cx x (.fnptr f) c'
  /-- A call through a code value: `call`'s rule at the value's signature. -/
  | callc {cx c₁ c' : Cx} {x : String} {f a : At} {tf σ τ t : Ty} :
      cx.peek f = .ok tf → codeOf tf = some (σ, τ) → cx.use a = .ok (t, c₁) → NoLeak c₁ t →
      SubS c₁ t σ → c₁.bind x τ = .ok c' → OpT p cx x (.callc f a) c'
  /-- `a mod n` for `n = v + 1`: fresh `d` then `k`, and `v := k + d`, so `k < n`. -/
  | rem {cx c' : Cx} {x : String} {a n : At} {ta : Ty} {o : Option Idx} {j : Idx} {v : Nat} :
      cx.peek a = .ok ta → intOf ta = some o → IntIdx cx n j → EqI cx j (.add (.var v) (.lit 1)) →
      { (cx.push (x ++ "_d")).push x with
          facts := (v + 2, .add (.var 0) (.var 1)) :: ((cx.push (x ++ "_d")).push x).facts }.bind x
        (.intS (.var 0)) = .ok c' → OpT p cx x (.rem a n) c'
  /-- A `let` for indices: fresh `x`, defined as the integer's index. -/
  | nameI {cx c' : Cx} {x : String} {a : At} {j : Idx} :
      IntIdx cx a j →
      { cx.push x with facts := (0, j.shift 0) :: (cx.push x).facts }.bind x (.intS (.var 0)) = .ok c' →
      OpT p cx x (.nameI a) c'
  /-- Exchange at an initialised slot of an own buffer, by value: the buffer stays. -/
  | xchgAt {cx c₁ c' : Cx} {x : String} {b i v : At} {t tv u : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → Ty.wordFreeIn cx.ke u = true → IntIdx cx i j → LtI cx j n → LtI cx j k →
      cx.use v = .ok (tv, c₁) → SubS c₁ tv u → c₁.bind x u = .ok c' → OpT p cx x (.xchgAt b i v) c'
  /-- Read a copyable initialised slot of an own buffer, by value. -/
  | loadAt {cx c' : Cx} {x : String} {b i : At} {t u : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → IntIdx cx i j → LtI cx j n → LtI cx j k →
      affine cx.ke u = false → cx.bind x u = .ok c' → OpT p cx x (.loadAt b i) c'
  /-- Pure 64-bit word operations on integers: the result is a plain `Int`. -/
  | bits {cx c' : Cx} {x : String} {o : BitOp} {a b : At} {ta tb : Ty} {oa ob : Option Idx} :
      cx.peek a = .ok ta → cx.peek b = .ok tb → intOf ta = some oa → intOf tb = some ob →
      cx.bind x .int = .ok c' → OpT p cx x (.bits o a b) c'
  | bit1 {cx c' : Cx} {x : String} {o : BitOp1} {a : At} {ta : Ty} {oa : Option Idx} :
      cx.peek a = .ok ta → intOf ta = some oa → cx.bind x .int = .ok c' → OpT p cx x (.bit1 o a) c'
  | vmatch {cx c' : Cx} {x : String} {lo hi b : At} {t1 t2 t3 : Ty} {o1 o2 o3 : Option Idx} :
      cx.peek lo = .ok t1 → cx.peek hi = .ok t2 → cx.peek b = .ok t3 →
      intOf t1 = some o1 → intOf t2 = some o2 → intOf t3 = some o3 →
      cx.bind x .int = .ok c' → OpT p cx x (.vmatch lo hi b) c'
  /-- `a & m` for `m = v`: fresh `d` then `k`, and `v := k + d`, so `k ≤ m`. -/
  | band {cx c' : Cx} {x : String} {a m : At} {ta : Ty} {o : Option Idx} {j : Idx} {v : Nat} :
      cx.peek a = .ok ta → intOf ta = some o → IntIdx cx m j → EqI cx j (.var v) →
      { (cx.push (x ++ "_d")).push x with
          facts := (v + 2, .add (.var 0) (.var 1)) :: ((cx.push (x ++ "_d")).push x).facts }.bind x
        (.intS (.var 0)) = .ok c' → OpT p cx x (.band a m) c'
  /-- The zero of a well-formed Zeroable, first-class type. -/
  | zero {cx c' : Cx} {x : String} {τ : Ty} :
      τ.wf cx.ke.length cx.inames.length = true → τ.secondClass = false →
      zeroableIn [] cx.ke τ = true → cx.bind x τ = .ok c' → OpT p cx x (.zero τ) c'
  /-- `xchgAt` on the component at field path `q` of a slot. -/
  | xchgAtF {cx c₁ c' : Cx} {x : String} {b i v : At} {q : List Nat} {t tv u c : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → compTy u q = some c →
      cx.opaqueOK u = true →
      Ty.wordFreeIn cx.ke c = true → IntIdx cx i j → LtI cx j n → LtI cx j k →
      cx.use v = .ok (tv, c₁) → SubS c₁ tv c → c₁.bind x c = .ok c' → OpT p cx x (.xchgAtF b i q v) c'
  /-- `loadAt` of a copyable component at field path `q` of a slot. -/
  | loadAtF {cx c' : Cx} {x : String} {b i : At} {q : List Nat} {t u c : Ty} {n k j : Idx} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → compTy u q = some c →
      cx.opaqueOK u = true →
      IntIdx cx i j → LtI cx j n → LtI cx j k →
      affine cx.ke c = false → cx.bind x c = .ok c' → OpT p cx x (.loadAtF b i q) c'
  /-- Fixed-width integers: pure conversions, arithmetic and lane access. -/
  | cvt {cx c' : Cx} {x : String} {sg : Bool} {w : Wd} {a : At} {ta : Ty} :
      cx.peek a = .ok ta → cvtSrc ta = true → cx.bind x (.fix sg w) = .ok c' → OpT p cx x (.cvt sg w a) c'
  | toInt {cx c' : Cx} {x : String} {a : At} {ta : Ty} :
      cx.peek a = .ok ta → toIntSrc ta = true → cx.bind x .int = .ok c' → OpT p cx x (.toInt a) c'
  | asLanes {cx c' : Cx} {x : String} {sg : Bool} {w : Wd} {a : At} {ta : Ty} :
      cx.peek a = .ok ta → (intOf ta).isSome = true → cx.bind x (.lanes sg w) = .ok c' →
      OpT p cx x (.asLanes sg w a) c'
  | fop {cx c' : Cx} {x : String} {o : FOp} {a b : At} {ta tb : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → cx.peek b = .ok tb → fixOf ta = some q → fixOf tb = some q →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpT p cx x (.fop o a b) c'
  | fcmp {cx c' : Cx} {x : String} {o : FCmp} {a b : At} {ta tb : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → cx.peek b = .ok tb → fixOf ta = some q → fixOf tb = some q →
      cx.bind x .int = .ok c' → OpT p cx x (.fcmp o a b) c'
  | fop1 {cx c' : Cx} {x : String} {o : FOp1} {a : At} {ta : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → fixOf ta = some q → cx.bind x (.fix q.1 q.2) = .ok c' → OpT p cx x (.fop1 o a) c'
  | lane {cx c' : Cx} {x : String} {a j : At} {ta tj : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → lanesOf ta = some q → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpT p cx x (.lane a j) c'
  | setLane {cx c' : Cx} {x : String} {a j v : At} {ta tj tv : Ty} {q : Bool × Wd} :
      cx.peek a = .ok ta → lanesOf ta = some q → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.peek v = .ok tv → fixOf tv = some q → cx.bind x (.lanes q.1 q.2) = .ok c' →
      OpT p cx x (.setLane a j v) c'
  /-- Lane `j mod 64/w` of word `wi` of an own buffer of `lanes`. -/
  | ldlw {cx c' : Cx} {x : String} {b wi j : At} {t u tj : Ty} {n k jw : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → IntIdx cx wi jw →
      LtI cx jw n → LtI cx jw k → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpT p cx x (.ldlw b wi j) c'
  | stlw {cx c' : Cx} {x : String} {b wi j v : At} {t u tj tv : Ty} {n k jw : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → IntIdx cx wi jw →
      LtI cx jw n → LtI cx jw k → cx.peek j = .ok tj → (intOf tj).isSome = true →
      cx.peek v = .ok tv → fixOf tv = some q → cx.bind x .unit = .ok c' → OpT p cx x (.stlw b wi j v) c'
  /-- Lane `i` of an own buffer of `lanes`. -/
  | ldl {cx c' : Cx} {x : String} {b i : At} {t u : Ty} {n k j : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → IntIdx cx i j →
      LtI cx j (.smul q.2.lanes n) → LtI cx j (.smul q.2.lanes k) →
      cx.bind x (.fix q.1 q.2) = .ok c' → OpT p cx x (.ldl b i) c'
  /-- A sub-word store: own buffers only. -/
  | stl {cx c' : Cx} {x : String} {b i v : At} {t u tv : Ty} {n k j : Idx} {q : Bool × Wd} :
      cx.peek b = .ok t → bufOf t = some (.own, n, u, k) → lanesOf u = some q → IntIdx cx i j →
      LtI cx j (.smul q.2.lanes n) → LtI cx j (.smul q.2.lanes k) →
      cx.peek v = .ok tv → fixOf tv = some q → cx.bind x .unit = .ok c' → OpT p cx x (.stl b i v) c'

/-- Both operands are integers, at least one of unknown index; or (E1) both are `ThreadId`s. -/
def PlainEq (cx : Cx) (a b : At) : Prop :=
  ∃ ta tb, cx.peek a = .ok ta ∧ cx.peek b = .ok tb ∧ (((intOf ta).isSome ∧ (intOf tb).isSome ∧
    (intOf ta = some none ∨ intOf tb = some none)) ∨ (tidOf ta = true ∧ tidOf tb = true))

theorem plainIntT_iff (t : Ty) : plainIntT t = true ↔ intOf t = some none := by
  unfold plainIntT; split <;> simp_all

theorem plainEq_sound {cx : Cx} {a b : At} (h : plainEq cx a b = true) : PlainEq cx a b := by
  unfold plainEq at h
  split at h
  · rename_i ta tb ha hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, plainIntT_iff] at h
    rcases h with h | h
    · exact ⟨ta, tb, ha, hb, .inl ⟨h.1.1, h.1.2, h.2⟩⟩
    · exact ⟨ta, tb, ha, hb, .inr h⟩
  · simp at h

inductive Typed (p : Prog) : Cx → Expr → Prop
  | let_ {cx c₁ : Cx} {x : String} {op : Op} {e : Expr} :
      OpT p cx x op c₁ → Typed p c₁ e → Typed p cx (.let_ x op e)
  | split {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {e : Expr} {u v : Ty} :
      cx.use a = .ok (.prod u v, c₁) → c₁.bind x u = .ok c₂ → c₂.bind y v = .ok c₃ →
      Typed p c₃ e → Typed p cx (.split a x y e)
  | unpack {cx c₁ c₂ : Cx} {a : At} {i x : String} {e : Expr} {b : Ty} :
      cx.use a = .ok (.iex b, c₁) → (c₁.push i).bind x b = .ok c₂ → Typed p c₂ e →
      Typed p cx (.unpack a i x e)
  /-- The variable is fresh, of the package's kind, and opaque in `e`. -/
  | unpackT {cx c₁ c₂ : Cx} {a : At} {α x : String} {e : Expr} {κ : Kind} {b : Ty} :
      cx.use a = .ok (.tex κ b, c₁) → b.guardT 0 = true → (c₁.pushT κ).bind x b = .ok c₂ →
      Typed p c₂ e → Typed p cx (.unpackT a α x e)
  | region {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {e : Expr} {u : Ty} :
      cx.use a = .ok (.ptr .own u, c₁) → rgnCellOK c₁.ke u = true →
      (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂ →
      c₂.bind tn (.tok (.var 0) none) = .ok c₃ → Typed p c₃ e → Typed p cx (.region a rn pn tn e)
  /-- An own buffer opened as a region: the pointer is a region locative. -/
  | regionBuf {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {e : Expr} {n k : Idx} {u : Ty} :
      cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) →
      rgnCellOK c₁.ke (.array n u) = true →
      (c₁.push rn).bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0)) = .ok c₂ →
      c₂.bind tn (.tok (.var 0) none) = .ok c₃ → Typed p c₃ e → Typed p cx (.region a rn pn tn e)
  /-- Published memory seen as a fresh region with a first-class capability. -/
  | openPub {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn cn : String} {e : Expr} {u : Ty} :
      cx.use a = .ok (.ptr .pub u, c₁) →
      (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂ →
      c₂.bind cn (.cap .pub (.var 0)) = .ok c₃ → Typed p c₃ e → Typed p cx (.openPub a rn pn cn e)
  | case {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty} :
      cx.use a = .ok (.sum u v, c₁) → c₁.bind x u = .ok c₂ → Typed p c₂ e₁ →
      c₁.bind y v = .ok c₃ → Typed p c₃ e₂ → Typed p cx (.case a x e₁ y e₂)
  | ifnull {cx c₁ c₂ : Cx} {a : At} {y : String} {e₁ e₂ : Expr} {μ : Mode} {u : Ty} :
      cx.use a = .ok (.ptrOpt μ u, c₁) → Typed p c₁ e₁ →
      c₁.bind y (.ptr μ u) = .ok c₂ → Typed p c₂ e₂ → Typed p cx (.ifnull a e₁ y e₂)
  /-- Split a free index variable by parity.  Shadowing an existing fact for
  `v` would only forget it, so no side condition is needed. -/
  | parity {cx : Cx} {a : At} {k : String} {ev od : Expr} {i : Idx} {v : Nat} :
      IntIdx cx a i → EqI cx i (.var v) →
      Typed p { cx.push k with facts := (v + 1, .smul 2 (.var 0)) :: (cx.push k).facts } ev →
      Typed p { cx.push k with facts := (v + 1, .add (.smul 2 (.var 0)) (.lit 1)) :: (cx.push k).facts } od →
      Typed p cx (.parity a k ev od)
  /-- Equality of plain integers: nothing is learnt either way. -/
  | ifeqPlain {cx : Cx} {a b : At} {yes no : Expr} :
      PlainEq cx a b → Typed p cx yes → Typed p cx no → Typed p cx (.ifeq a b yes no)
  /-- Equality test, learning nothing on success. -/
  | ifeq {cx c' : Cx} {a b : At} {yes no : Expr} {i j : Idx} :
      IntIdx cx a i → IntIdx cx b j → Typed p cx yes → NoCx cx i j c' → Typed p c' no →
      Typed p cx (.ifeq a b yes no)
  /-- Equality test, recording `v = t` on success, where the operands are
  (equal to) `var v` and `t`, either way round. -/
  | ifeqRec {cx c' : Cx} {a b : At} {yes no : Expr} {i j t : Idx} {v : Nat} :
      IntIdx cx a i → IntIdx cx b j →
      ((EqI cx i (.var v) ∧ EqI cx j t) ∨ (EqI cx j (.var v) ∧ EqI cx i t)) →
      Typed p { cx with facts := (v, t) :: cx.facts } yes → NoCx cx i j c' → Typed p c' no →
      Typed p cx (.ifeq a b yes no)
  /-- Equality with zero of a positive multiple `s·u`: record `u = 0`. -/
  | ifeqZero {cx c' : Cx} {a b : At} {yes no : Expr} {i j : Idx} {u s : Nat} :
      IntIdx cx a i → IntIdx cx b j → ZeroEq cx i j u s →
      Typed p { cx with facts := (u, .lit 0) :: cx.facts } yes → NoCx cx i j c' → Typed p c' no →
      Typed p cx (.ifeq a b yes no)
  | casCell {cx c₁ c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw u te tv : Ty} :
      cx.peek w = .ok tw → wordOf tw = none →
      (cellOf tw = some (.pub, u) ∨ ∃ r, cellOf tw = some (.rgn r, u) ∧ HasCap cx r true) →
      u.rawWords = some 1 →
      affine cx.ke u = false → cx.peek e = .ok te → cx.use v = .ok (tv, c₁) →
      SubS c₁ te u → SubS c₁ tv u → (Ty.sensitiveIn c₁.ke u = true → acq = true ∧ rel = true) →
      c₁.bind t .unit = .ok c₂ → Typed p c₂ ok → Typed p c₁ fail →
      Typed p cx (.cas acq rel w e v t ok fail)
  | casShare {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j k k' : Idx} {P : Proto} {c c' : Nat} {cl cl' : Clause} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.ghost = false → IntIdx cx e i → IntIdx cx v j →
      InState cx P i c k → P.clauses[c]? = some cl → InState cx P j c' k' → P.clauses[c']? = some cl' →
      cl.holds = true → Step cx P c k c' k' → cl'.holds = true →
      LendCx cx acq rel r t P c k c' k' c₂ → Typed p c₂ ok → Typed p cx fail →
      Typed p cx (.cas acq rel w e v t ok fail)
  | casTake {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j k k' : Idx} {P : Proto} {c c' : Nat} {cl cl' : Clause} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.ghost = false → IntIdx cx e i → IntIdx cx v j →
      InState cx P i c k → P.clauses[c]? = some cl → InState cx P j c' k' → P.clauses[c']? = some cl' →
      cl.holds = true → Step cx P c k c' k' → cl'.holds = false → P.lends.contains c = false →
      P.lendsDown.contains c = false → acq = true →
      cx.bind t (.tok r (some (P, j))) = .ok c₂ →
      Typed p (if monotone P then { c₂ with unsealed := r :: c₂.unsealed } else c₂) ok →
      Typed p cx fail → Typed p cx (.cas acq rel w e v t ok fail)
  /-- `cas` on an epoch counter (`P.epoch`): `e -> e + 1` enters the epoch and
  yields its token `Tok[r, P, e + 1]`; the counter has no held state, so no
  region changes hands. -/
  | casEpoch {cx c₂ : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i j k k' : Idx} {P : Proto} {c c' : Nat} :
      cx.peek w = .ok tw → wordOf tw = some (r, P) → P.epoch = true → acq = true →
      IntIdx cx e i → IntIdx cx v j → InState cx P i c k → InState cx P j c' k' →
      Step cx P c k c' k' → cx.bind t (.tokE r (.word P) j) = .ok c₂ → Typed p c₂ ok → Typed p cx fail →
      Typed p cx (.cas acq rel w e v t ok fail)
  /-- The epoch-fenced write: `casp` on an epoch pair, whose new epoch a live
  epoch token names; it publishes (`rel`). -/
  | caspE {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 : Idx} {P : ECounter} :
      cx.peek w = .ok tw → word2Of tw = none → epairOf tw = some (r, P) → rel = true →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 → HasTokE cx r P j0 →
      cx.bind t .unit = .ok c₂ → Typed p c₂ ok → Typed p cx fail →
      Typed p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  /-- `casp` between shared states of an epoch pair whose move bumps the epoch
  (half 0 advances by one): it enters the new epoch and yields its token
  `Tok[r, P, e + 1]` (needs `acq`). -/
  | caspBump {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c' : Nat} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 →
      InState2 cx P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 cx P j0 j1 c' k0' k1' → P.clauses[c']? = some cl' →
      cl.holds = true → Step2 cx P c k0 k1 c' k0' k1' → cl'.holds = true →
      P.epoch = true → Bump2 cx k0 k0' → acq = true →
      cx.bind t (.tokE r (.pair P) j0) = .ok c₂ → Typed p c₂ ok → Typed p cx fail →
      Typed p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  /-- `casp` between shared pair states: nothing changes hands. -/
  | caspMove {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c' : Nat} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 →
      InState2 cx P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 cx P j0 j1 c' k0' k1' → P.clauses[c']? = some cl' →
      cl.holds = true → Step2 cx P c k0 k1 c' k0' k1' → cl'.holds = true →
      cx.bind t .unit = .ok c₂ → Typed p c₂ ok → Typed p cx fail →
      Typed p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  /-- `casp` into a held pair state takes the region (needs `acq`); a pair
  licenses no torn read, so no region is left unsealed. -/
  | caspTake {cx c₂ : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr} {tw : Ty}
      {r i0 i1 j0 j1 k0 k1 k0' k1' : Idx} {P : Proto2} {c c' : Nat} {cl cl' : Clause2} :
      cx.peek w = .ok tw → word2Of tw = some (r, P) →
      IntIdx cx e0 i0 → IntIdx cx e1 i1 → IntIdx cx v0 j0 → IntIdx cx v1 j1 →
      InState2 cx P i0 i1 c k0 k1 → P.clauses[c]? = some cl →
      InState2 cx P j0 j1 c' k0' k1' → P.clauses[c']? = some cl' →
      cl.holds = true → Step2 cx P c k0 k1 c' k0' k1' → cl'.holds = false → acq = true →
      cx.bind t (.tok2 r P j0 j1) = .ok c₂ → Typed p c₂ ok → Typed p cx fail →
      Typed p cx (.casp acq rel w e0 e1 v0 v1 t ok fail)
  | ret {cx c₁ : Cx} {a : At} {t : Ty} :
      cx.use a = .ok (t, c₁) → NoLeak c₁ t → SubS c₁ t c₁.ret → Typed p cx (.ret a)
  | tail {cx c₁ : Cx} {f : String} {is : List String} {a : At} {ts : List Ty} {d : Decl} {at_ rt t : Ty} :
      p.find f = .ok d → instantiate cx d is ts = .ok (at_, rt) → cx.use a = .ok (t, c₁) →
      NoLeak c₁ t → SubS c₁ t at_ → SubS c₁ rt c₁.ret → Typed p cx (.tail f is a ts)

/-- A well-typed code block: a well-formed signature, and a typed body. -/
def DeclT (p : Prog) (d : Decl) : Prop :=
  d.argTy.wf d.tparams.length d.idx.length = true ∧ d.retTy.wf d.tparams.length d.idx.length = true ∧
  d.argTy.scTop = true ∧ d.retTy.secondClass = false ∧
  Typed p (declCx d) d.body

/-- A well-typed program: every code block is. -/
def ProgT (p : Prog) : Prop := ∀ d ∈ p, DeclT p d

/-! ## §5. Soundness -/

theorem foldOk_sound {cx : Cx} {t τ : Ty} (h : foldOk cx t τ = true) : FoldOK cx t τ := by
  unfold foldOk at h
  split at h <;> (try simp only [Bool.and_eq_true] at h)
  · exact .ptr (meqD_sound h.1) (tyEq_sound _ _ _ _ h.2)
  · exact .ptrOpt (meqD_sound h.1) (tyEq_sound _ _ _ _ h.2)
  · exact .loc (meqD_sound h.1) (tyEq_sound _ _ _ _ h.2)
  · simp at h

theorem ne_true {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

theorem clauseM_ok {P : Proto} {c : Nat} {cl : Clause} (h : clauseM P c = .ok cl) :
    P.clauses[c]? = some cl := by
  unfold clauseM at h; split at h <;> simp_all

theorem succVar_ev (ρ : Val) (a : Lin) (v : Nat) (h : a.succVar? = some v) : a.ev ρ = ρ v + 1 := by
  unfold Lin.succVar? at h
  split at h <;> simp_all [Lin.ev, csum] <;> omega

theorem succVar_eqI {cx : Cx} {i : Idx} {v : Nat} (h : (cx.norm i).bind Lin.succVar? = some v) :
    EqI cx i (.add (.var v) (.lit 1)) := by
  intro ρ hs
  cases hn : cx.norm i with
  | none => simp [hn] at h
  | some a =>
      simp [hn] at h
      have h1 := norm_sound _ ρ hs _ _ _ hn
      have h2 := succVar_ev ρ a v h
      simp [ev]; omega

theorem asVar_eqI {cx : Cx} {i : Idx} {v : Nat} (h : (cx.norm i).bind Lin.asVar? = some v) :
    EqI cx i (.var v) := by
  intro ρ hs
  cases hn : cx.norm i with
  | none => simp [hn] at h
  | some a =>
      simp [hn] at h
      have h1 := norm_sound _ ρ hs _ _ _ hn
      have h2 := asVar_ev ρ a v h
      simp [ev]; omega

set_option maxHeartbeats 800000 in
theorem checkOp_sound (p : Prog) (cx : Cx) (x : String) (op : Op) (cx' : Cx)
    (h : checkOp p cx x op = .ok cx') : OpT p cx x op cx' := by
  cases op with
  | atom a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h2⟩ := h
      exact .atom h1 h2
  | pair a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, ⟨u, c₂⟩, h2, h3⟩ := h
      exact .pair h1 h2 h3
  | inl τ a =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, h2⟩ := h
        exact .inl (by simpa using hw) h1 h2
  | inr τ a =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, h2⟩ := h
        exact .inr (by simpa using hw) h1 h2
  | add a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, u, hu, h⟩ := h
      split at h
      · exact .addS ht hu (by assumption) (by assumption) h
      · exact .addI ht hu (by assumption) (by assumption) h
      · simp at h
  | sub a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, u, hu, h⟩ := h
      split at h
      · rename_i i j hi hj
        split at h
        · rename_i ni nj hni hnj
          split at h
          · rename_i hle
            refine .subS ht hu hi hj ?_ h
            intro ρ hs
            have e1 := norm_sound _ ρ hs _ _ _ hni
            have e2 := norm_sound _ ρ hs _ _ _ hnj
            unfold Lin.leB at hle
            simp only [beq_iff_eq] at hle
            have e3 := congrArg (Lin.ev ρ) hle
            rw [lev_add] at e3
            simp only [ev_toIdx]
            omega
          · simp at h
        · simp at h
      · simp at h
  | new a T =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        cases T with
        | none => simp at h
        | some T =>
          by_cases hT : t = T
          · subst hT
            exact .new h1 (by simpa using hs) (by simpa using h)
          · simp [hT] at h
  | publish a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      split at h
      · rename_i u heq
        split at h
        · simp only at heq; subst heq; exact .publish h1 (by assumption) h
        · simp at h
      · rename_i n u k heq
        split at h
        · simp only at heq; subst heq; exact .publishBuf h1 (by assumption) h
        · simp at h
      · simp at h
  | intoRgn rn a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, ⟨t, c₁⟩, h1, h⟩ := h
      split at h
      · rename_i u heq
        split at h
        · simp only at heq; subst heq; exact .intoRgn hr h1 (by assumption) h
        · simp at h
      · rename_i n u k heq
        split at h
        · simp only at heq; subst heq; exact .intoRgnBuf hr h1 (by assumption) h
        · simp at h
      · simp at h
  | newBuf n τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        split at h
        · simp at h
        · rename_i hsc
          split at h
          · simp at h
          · rename_i hop
            split at h
            · simp at h
            · rename_i har
              simp only [bind_ok_iff] at h
              obtain ⟨k, hk, h⟩ := h
              exact .newBuf (by simpa using hw) (by simpa using hsc) (by simpa using hop) (by simpa using har)
                (intIdx_sound hk) h
  | idx b i =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i c hc
        obtain ⟨μ, n, u, k⟩ := c
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i hn
          split at h
          · simp at h
          · rename_i hk
            split at h
            · simp at h
            rename_i hop
            split at h
            · rename_i hown
              simp only [bind_ok_iff, map_ok_iff] at h
              obtain ⟨c₁, ⟨⟨t', c₁'⟩, hu1, rfl⟩, h⟩ := h
              simp only [beq_iff_eq] at hown; subst hown
              exact .idxOwn ht hc (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                (ltI_sound _ _ _ (by simpa using hk)) (by simpa using hop) hu1 h
            · rename_i hown
              simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
              exact .idxShared ht hc (by simpa using hown) (intIdx_sound hj)
                (ltI_sound _ _ _ (by simpa using hn)) (ltI_sound _ _ _ (by simpa using hk))
                (by simpa using hop) h
      · simp at h
  | bufInit b i v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i he
          split at h
          · simp at h
          · rename_i hl
            simp only [bind_ok_iff] at h
            obtain ⟨⟨tv, c₂⟩, h2, h⟩ := h
            split at h
            · simp at h
            · rename_i hs
              exact .bufInit h1 hc (intIdx_sound hj) (eqI_sound _ _ _ (by simpa using he))
                (ltI_sound _ _ _ (by simpa using hl)) h2 (sub_sound _ _ _ (by simpa using hs)) h
      · simp at h
      · simp at h
  | null μ τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        exact .null (by simpa using hw) h
  | fold a τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
        split at h
        · rename_i hok; exact .fold (by simpa using hw) h1 (foldOk_sound hok) h
        · simp at h
  | fld i a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i μu hc
        obtain ⟨μ, u⟩ := μu
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · rename_i c1 c2 hu
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
          split at h
          · simp at h
          rename_i hop
          split at h
          · rename_i hown
            simp only [bind_ok_iff, map_ok_iff] at h
            obtain ⟨c₁, ⟨⟨t', c₁'⟩, hu1, rfl⟩, h⟩ := h
            simp only [beq_iff_eq] at hown; subst hown
            exact .fldOwn ht hc hu (by simpa using hop) hu1 h
          · rename_i hown
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
            exact .fldShared ht hc (by simpa using hown) hu (by simpa using hop) h
        · simp at h
      · simp at h
  | load acq a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · split at h
        · simp at h
        · rename_i hg
          exact .loadWord ht (by assumption) (by simpa using hg) h
      · simp at h
      · rename_i hw
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i ha
            exact .loadOwn ht hw (by assumption) (ne_true ha) h
        · split at h
          · simp at h
          · rename_i ha
            split at h
            · simp at h
            · rename_i hs
              exact .loadPub ht hw (by assumption) (by simpa using ha) (fun hsen => by simpa [hsen] using hs) h
        · rename_i r u hc
          split at h
          · rename_i htok
            split at h
            · simp at h
            · rename_i ha
              exact .loadRgn ht hw hc (readable_sound htok) (by simpa using ha) h
          · split at h
            · rename_i hcap
              split at h
              · simp at h
              · rename_i hs
                split at h
                · simp at h
                · rename_i ha
                  exact .loadCap ht hw hc (hasCap_sound hcap) (fun hsen => by simpa [hsen] using hs)
                    (by simpa using ha) h
            · simp only [bind_ok_iff] at h
              obtain ⟨⟨w, s⟩, hl, h⟩ := h
              split at h
              · simp at h
              · rename_i hfresh
                simp only [pure_ok_iff] at h; subst h
                simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hfresh
                exact .loadTorn ht hw hc (tornLicence_sound hl) hfresh.1 hfresh.2
  | store rel a v tok =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i r P hw
        split at h
        · rename_i tk
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
          obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i r' Q i'
          split at h <;> (try (simp at h; done))
          rename_i he
          split at h <;> (try (simp at h; done))
          rename_i hq
          obtain rfl : Q = P := by simpa using hq
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
          obtain ⟨j, hj, c, k, hc, c', k', hc', cl, hcl, cl', hcl', h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i hnh
          split at h <;> (try (simp at h; done))
          rename_i hps
          split at h
          · rename_i hh'
            split at h <;> (try (simp at h; done))
            rename_i hrel
            exact .storeWordGive ht hw h1 (eqI_sound _ _ _ (by simpa using he)) (intIdx_sound hj)
              (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (classifyM_sound _ _ _ _ _ hc')
              (clauseM_ok hcl') (by simpa using hnh) (pstep_sound _ _ _ _ _ _ (by simpa using hps))
              hh' (fun hg => by simpa [hg] using hrel) h
          · rename_i hh'
            split at h
            · rename_i htk
              split at h <;> (try (simp at h; done))
              rename_i hrel
              exact .storeWordHand ht hw h1 (eqI_sound _ _ _ (by simpa using he)) (intIdx_sound hj)
                (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (classifyM_sound _ _ _ _ _ hc')
                (clauseM_ok hcl') (by simpa using hnh) (pstep_sound _ _ _ _ _ _ (by simpa using hps))
                (by simpa using hh') htk (by simpa using hrel) h
            · rename_i htk
              exact .storeWordKeep ht hw h1 (eqI_sound _ _ _ (by simpa using he)) (intIdx_sound hj)
                (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (classifyM_sound _ _ _ _ _ hc')
                (clauseM_ok hcl') (by simpa using hnh) (pstep_sound _ _ _ _ _ _ (by simpa using hps))
                (by simpa using hh') (by simpa using htk) h
        · simp at h
      · rename_i hw
        split at h
        · simp at h
        · rename_i μ u hc
          split at h
          · simp at h
          rename_i hwf
          have hwf : Ty.wordFreeIn cx.ke u = true := by simpa using hwf
          simp only [bind_ok_iff] at h
          obtain ⟨⟨tv, c₁⟩, h1, h⟩ := h
          cases μ with
          | own =>
              simp only at h
              split at h
              · exact .storeOwn ht hw hc hwf h1 (sub_sound _ _ _ (by assumption)) h
              · simp at h
          | pub =>
              simp only at h
              split at h
              · simp at h
              · rename_i hs
                split at h
                · simp at h
                · rename_i hsr
                  exact .storePub ht hw hc hwf h1 (sub_sound _ _ _ (by simpa using hs))
                    (fun hsen => by simpa [hsen] using hsr) h
          | rgn r =>
              simp only at h
              split at h
              · rename_i ht1
                split at h
                · simp at h
                · rename_i ht2
                  split at h
                  · rename_i hs
                    simp only [Bool.or_eq_true] at hs
                    exact .storeRgn ht hw hc hwf h1
                      (holdsSealed_sound (by simpa using ht1) (by simpa using ht2))
                      (hs.imp (sub_sound _ _ _) (sub_sound _ _ _)) h
                  · simp at h
              · split at h
                · rename_i hcap
                  split at h
                  · simp at h
                  · rename_i hsr
                    split at h
                    · rename_i hs
                      simp only [Bool.or_eq_true] at hs
                      exact .storeCap ht hw hc hwf h1 (hasCap_sound hcap)
                        (fun hsen => by simpa [hsen] using hsr)
                        (hs.imp (sub_sound _ _ _) (sub_sound _ _ _)) h
                    · simp at h
                · simp at h
  | fence f => exact .fence h
  | mkWord rn P v tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h
      · simp at h
      · rename_i hp
        simp only [bind_ok_iff] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h
        · rename_i r'
          split at h
          · simp at h
          · rename_i he
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
            obtain ⟨j, hj, c, k, hc, cl, hcl, h⟩ := h
            try dsimp only at h
            split at h
            · rename_i hg
              split at h
              · simp at h
              · rename_i hh
                exact .mkWordGhost hr (by simpa using hp) h1 (eqI_sound _ _ _ (by simpa using he))
                  (intIdx_sound hj) (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) hg (by simpa using hh) h
            · rename_i hg
              split at h
              · simp at h
              · rename_i hh
                exact .mkWord hr (by simpa using hp) h1 (eqI_sound _ _ _ (by simpa using he)) (intIdx_sound hj)
                  (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (by simpa using hg) (by simpa using hh) h
        · simp at h
        · simp at h
  | mkWord2 rn P v0 v1 tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h
      · simp at h
      · rename_i hp
        simp only [bind_ok_iff] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h
        · rename_i r'
          split at h
          · simp at h
          · rename_i he
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
            obtain ⟨j0, hj0, j1, hj1, c, k0, k1, hc, cl, hcl, h⟩ := h
            try dsimp only at h
            split at h
            · simp at h
            · rename_i hh
              exact .mkWord2 hr (by simpa using hp) h1 (eqI_sound _ _ _ (by simpa using he))
                (intIdx_sound hj0) (intIdx_sound hj1) (classify2M_sound _ _ _ _ _ _ _ hc)
                (clause2M_ok hcl) (by simpa using hh) h
        · simp at h
        · simp at h
  | ldp acq a n0 n1 =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i hp
        split at h
        · exact .ldp ht hp h
        · simp at h
      · simp at h
  | mkEPair rn P v0 v1 =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h <;> (try (simp at h; done))
      rename_i hp
      simp only [bind_ok_iff] at h
      obtain ⟨j0, hj0, j1, hj1, h⟩ := h
      exact .mkEPair hr (by simpa using hp) (intIdx_sound hj0) (intIdx_sound hj1) h
  | mkTicket rn N P v tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h <;> (try (simp at h; done))
      rename_i hN
      obtain ⟨hN1, hN2⟩ : pwf N = true ∧ N.epoch = true := by simpa using hN
      split at h <;> (try (simp at h; done))
      rename_i hP
      obtain ⟨hP1, hP2⟩ : pwf P = true ∧ P.ticket = true := by simpa using hP
      simp only [bind_ok_iff] at h
      obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i r'
        split at h
        · simp at h
        · rename_i he
          simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
          obtain ⟨j, hj, h⟩ := h
          exact .mkTicket hr hN1 hN2 hP1 hP2 h1 (eqI_sound _ _ _ (by simpa using he)) (intIdx_sound hj) h
      · simp at h
      · simp at h
  | claim a tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · split at h <;> (try (simp at h; done))
        rename_i htk
        simp only [bind_ok_iff] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h
        · split at h
          · simp at h
          · rename_i he
            simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
            split at h
            · rename_i hs
              exact .claim ht (by assumption) (by simpa using htk) h1 (eqI_sound _ _ _ (by simpa using he))
                (sawFor_sound hs).1 (sawFor_sound hs).2 h
            · simp at h
        · simp at h
      · simp at h
      · simp at h
  | stp rel a v0 v1 tk =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i r P hw
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i r' Q i0' i1'
        split at h <;> (try (simp at h; done))
        rename_i he
        split at h <;> (try (simp at h; done))
        rename_i hq
        obtain rfl : Q = P := by simpa using hq
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left', Prod.exists] at h
        obtain ⟨j0, hj0, j1, hj1, c, k0, k1, hc, c', k0', k1', hc', cl, hcl, cl', hcl', h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hnh
        split at h <;> (try (simp at h; done))
        rename_i hps
        split at h
        · rename_i hh'
          split at h <;> (try (simp at h; done))
          rename_i hrel
          exact .stpGive ht hw h1 (eqI_sound _ _ _ (by simpa using he)) (intIdx_sound hj0) (intIdx_sound hj1)
            (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
            (clause2M_ok hcl') (by simpa using hnh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
            hh' (by simpa using hrel) h
        · rename_i hh'
          exact .stpKeep ht hw h1 (eqI_sound _ _ _ (by simpa using he)) (intIdx_sound hj0) (intIdx_sound hj1)
            (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
            (clause2M_ok hcl') (by simpa using hnh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
            (by simpa using hh') h
  | fetch o acq rel a v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨tw, htw, h⟩ := h
      split at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨u, hc, h⟩ := h
        split at h <;> (try (simp at h; done))
        rename_i hu
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨tv, c₁, h1, h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hs
        have hu' : u = .int := by simpa using hu
        subst hu'
        exact .fetchCell htw hw (casCellTy_sound hc) h1 (sub_sound _ _ _ (by simpa using hs)) h
      · rename_i r P hw
        split at h <;> (try (simp at h; done))
        rename_i ho
        have ho' : o = .add := by simpa using ho
        subst ho'
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        cases hep : P.epoch
        case true =>
          simp only [hep, ↓reduceIte] at h
          split at h <;> (try (simp at h; done))
          rename_i hacq
          split at h <;> (try (simp at h; done))
          rename_i he
          exact .fetchEpoch htw hw hep (by simpa using hacq) (intIdx_sound hj)
            (eqI_sound _ _ _ (by simpa using he)) h
        case false =>
          simp only [hep, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at h
          obtain ⟨d, _, h⟩ := h
          split at h <;> (try (simp at h; done))
          rename_i he
          split at h <;> (try (simp at h; done))
          rename_i hok
          exact .fetchShare htw hw hep (intIdx_sound hj) (eqI_sound _ _ _ (by simpa using he))
            (by simpa using hok) h
  | pack a wn τ =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨w, hw, h⟩ := h
      split at h
      · rename_i body
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        · rename_i hwf
          simp only [bind_ok_iff] at h
          obtain ⟨⟨t, c₁⟩, h1, u, hn, h⟩ := h
          try dsimp only at h
          split at h
          · exact .pack hw (by simpa using hwf) h1 (noLeak_sound hn) (sub_sound _ _ _ (by assumption)) h
          · simp at h
      · simp at h
  | packT a σ τ =>
      simp only [checkOp] at h
      split at h
      · rename_i κ body
        split at h
        · simp at h
        · rename_i hg
          split at h
          · simp at h
          · rename_i hwf
            split at h
            · simp at h
            · rename_i had
              simp only [bind_ok_iff] at h
              obtain ⟨⟨t, c₁⟩, h1, u, hn, h⟩ := h
              try dsimp only at h
              split at h
              · exact .packT (by simpa using hg) (by simpa using hwf) (by simpa using had) h1
                  (noLeak_sound hn) (sub_sound _ _ _ (by assumption)) h
              · simp at h
      · simp at h
  | validate y =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i tn htn
        split at h
        · rename_i v hv
          split at h
          · simp at h
          · rename_i he
            split at h
            · simp at h
            · rename_i ha
              exact .validate htn hv (eqI_sound _ _ _ (by simpa using he)) (by simpa using ha) h
        · simp at h
        · simp at h
  | call f is a ts =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨d, hd, ⟨at_, rt⟩, hi, ⟨t, c₁⟩, h1, u, hn, h⟩ := h
      split at h
      · simp at h
      · rename_i hs
        exact .call hd hi h1 (noLeak_sound hn) (sub_sound _ _ _ (by simpa using hs)) h
  | spawn f a T ts =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      have nor : ∀ {b c : Bool}, (!b || !c) = false → b = true ∧ c = true := by
        intro b c h; cases b <;> cases c <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)
      dsimp only at h
      generalize hsb : sub c₁ t T = sb at h
      cases sb
      · cases h
      rw [if_neg (by decide)] at h
      generalize hb2 : (affine c₁.ke t || affine c₁.ke T) = b2 at h
      cases b2
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb3 : (!Ty.wf c₁.ke.length 0 T || !ts.all fun x => Ty.wf c₁.ke.length 0 x) = b3 at h
      cases b3
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb4 : (!TermClose.tb 0 T || !ts.all (TermClose.tb 0)) = b4 at h
      cases b4
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb5 : (!TermScope.drf T || !ts.all TermScope.drf) = b5 at h
      cases b5
      case true => cases h
      rw [if_neg (by decide)] at h
      generalize hb6 : (!TermScope.wrapOK T || !ts.all TermScope.argOK) = b6 at h
      cases b6
      case true => cases h
      rw [if_neg (by decide)] at h
      simp only [bind_ok_iff] at h
      obtain ⟨d, hd, ⟨at_, rt⟩, hi, u, hc, h⟩ := h
      generalize hb7 : (TermClose.tb 0 rt && TermTv.mg rt && TermTv.noIallV rt) = b7 at h
      cases b7
      · cases h
      rw [if_neg (by decide)] at h
      obtain ⟨hW1, hW2⟩ := nor hb3
      obtain ⟨hT1, hT2⟩ := nor hb4
      obtain ⟨hD1, hD2⟩ := nor hb5
      obtain ⟨hK1, hK2⟩ := nor hb6
      exact .spawn h1 (sub_sound _ _ _ hsb) hb2 hW1 hW2 hT1 hT2 hD1 hD2 hK1 hK2 hd hi hc hb7 h
  | ext n a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      dsimp only at h
      generalize hok : n.ok = ok at h
      cases ok
      · cases h
      rw [if_neg (by decide)] at h
      generalize hsb : sub c₁ t n.sig.1 = sb at h
      cases sb
      · cases h
      rw [if_neg (by decide)] at h
      exact .ext h1 hok (sub_sound _ _ _ hsb) h
  | isTy a τ =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      cases t <;> try (simp at h; done)
      rename_i κ b
      by_cases h1 : slotOK b = true <;> simp [h1] at h
      by_cases h2 : τ.wf 0 0 = true <;> simp [h2] at h
      by_cases h3 : tgtOK τ = true <;> simp [h3] at h
      by_cases h4 : admitsIn cx κ τ = true <;> simp [h4] at h
      exact .isTy ht h1 h2 h3 h4 h
  | borrow c a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨y, hy, t, ht, r, hr, ⟨t', c₁⟩, h1, h⟩ := h
      exact .borrow hy ht hr h1 h
  | endBorrow a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨y, hy, h⟩ := h
      split at h
      · simp at h
      · rename_i hl
        exact .endBorrow hy (by simpa using hl) h
  | xchg a v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, ⟨u, o⟩, hx, ⟨tv, c₁⟩, h1, h⟩ := h
      split at h
      · simp at h
      · rename_i hs
        have hs' : sub c₁ tv u = true ∨ sub c₁ tv o = true := by
          revert hs; cases sub c₁ tv u <;> cases sub c₁ tv o <;> simp
        exact .xchg ht (xchgCell_sound hx) h1
          (hs'.elim (fun e => .inl (sub_sound _ _ _ e)) (fun e => .inr (sub_sound _ _ _ e))) h
  | fnptr f =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨d, hd, h⟩ := h
      split at h
      · simp at h
      · rename_i hm
        have hm' : d.tparams = [] ∧ d.idx = [] := by simpa using hm
        exact .fnptr hd hm'.1 hm'.2 h
  | callc f a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨tf, htf, h⟩ := h
      split at h
      · rename_i σ τ hc
        simp only [bind_ok_iff] at h
        obtain ⟨⟨t, c₁⟩, h1, u, hn, h⟩ := h
        split at h
        · simp at h
        · rename_i hs
          exact .callc htf hc h1 (noLeak_sound hn) (sub_sound _ _ _ (by simpa using hs)) h
      · simp at h
  | rem a n =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, h⟩ := h
      split at h
      · simp at h
      · rename_i hi
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i v hv
          cases e : intOf ta with
          | none => simp [e] at hi
          | some o => exact .rem hta e (intIdx_sound hj) (succVar_eqI hv) h
  | nameI a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨j, hj, h⟩ := h
      exact .nameI (intIdx_sound hj) h
  | xchgAt b i v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        rename_i hwf
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i hn
          split at h
          · simp at h
          · rename_i hk
            simp only [bind_ok_iff] at h
            obtain ⟨⟨tv, c₁⟩, h1, h⟩ := h
            split at h
            · simp at h
            · rename_i hs
              exact .xchgAt ht hc (by simpa using hwf) (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                (ltI_sound _ _ _ (by simpa using hk)) h1 (sub_sound _ _ _ (by simpa using hs)) h
      · simp at h
      · simp at h
  | loadAt b i =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i hn
          split at h
          · simp at h
          · rename_i hk
            split at h
            · simp at h
            · rename_i ha
              exact .loadAt ht hc (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                (ltI_sound _ _ _ (by simpa using hk)) (by simpa using ha) h
      · simp at h
      · simp at h
  | bits o a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, tb, htb, h⟩ := h
      split at h
      · rename_i oa ob ea eb
        exact .bits hta htb ea eb h
      · simp at h
  | bit1 o a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, h⟩ := h
      split at h
      · rename_i oa ea
        exact .bit1 hta ea h
      · simp at h
  | vmatch lo hi b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t1, h1, t2, h2, t3, h3, h⟩ := h
      split at h
      · rename_i o1 o2 o3 e1 e2 e3
        exact .vmatch h1 h2 h3 e1 e2 e3 h
      · simp at h
  | band a m =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, hta, h⟩ := h
      split at h
      · simp at h
      · rename_i hi
        simp only [bind_ok_iff] at h
        obtain ⟨j, hj, h⟩ := h
        split at h
        · simp at h
        · rename_i v hv
          cases e : intOf ta with
          | none => simp [e] at hi
          | some o => exact .band hta e (intIdx_sound hj) (asVar_eqI hv) h
  | zero τ =>
      simp only [checkOp] at h
      split at h
      · simp at h
      · rename_i hw
        split at h
        · simp at h
        · rename_i hs
          split at h
          · simp at h
          · rename_i hz
            exact .zero (by simpa using hw) (by simpa using hs) (by simpa using hz) h
  | xchgAtF b i q v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        · rename_i c hq
          split at h
          · simp at h
          rename_i hop
          split at h
          · simp at h
          rename_i hwf
          simp only [bind_ok_iff] at h
          obtain ⟨j, hj, h⟩ := h
          split at h
          · simp at h
          · rename_i hn
            split at h
            · simp at h
            · rename_i hk
              simp only [bind_ok_iff] at h
              obtain ⟨⟨tv, c₁⟩, h1, h⟩ := h
              split at h
              · simp at h
              · rename_i hs
                exact .xchgAtF ht hc hq (by simpa using hop) (by simpa using hwf) (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                  (ltI_sound _ _ _ (by simpa using hk)) h1 (sub_sound _ _ _ (by simpa using hs)) h
      · simp at h
      · simp at h
  | loadAtF b i q =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · rename_i n u k hc
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        split at h
        · simp at h
        · rename_i c hq
          split at h
          · simp at h
          rename_i hop
          simp only [bind_ok_iff] at h
          obtain ⟨j, hj, h⟩ := h
          split at h
          · simp at h
          · rename_i hn
            split at h
            · simp at h
            · rename_i hk
              split at h
              · simp at h
              · rename_i ha
                exact .loadAtF ht hc hq (by simpa using hop) (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                  (ltI_sound _ _ _ (by simpa using hk)) (by simpa using ha) h
      · simp at h
      · simp at h
  | cvt sg w a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i hc
        exact .cvt ht (by simpa using hc) h
  | toInt a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i hc
        exact .toInt ht (by simpa using hc) h
  | asLanes sg w a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i hc
        exact .asLanes ht (by simpa [Option.isSome_iff_ne_none] using hc) h
  | fop o a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, tb, htb, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        split at h
        · simp at h
        · rename_i hq'
          exact .fop ht htb hq (by simpa using hq') h
  | fcmp o a b =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, tb, htb, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        split at h
        · simp at h
        · rename_i hq'
          exact .fcmp ht htb hq (by simpa using hq') h
  | fop1 o a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        exact .fop1 ht hq h
  | lane a j =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        simp only [bind_ok_iff] at h
        obtain ⟨tj, htj, h⟩ := h
        split at h
        · simp at h
        · rename_i hl
          exact .lane ht hq htj (by simpa [Option.isSome_iff_ne_none] using hl) h
  | setLane a j v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨ta, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i q hq
        simp only [bind_ok_iff] at h
        obtain ⟨tj, htj, h⟩ := h
        split at h
        · simp at h
        · rename_i hl
          simp only [bind_ok_iff] at h
          obtain ⟨tv, htv, h⟩ := h
          split at h
          · simp at h
          · rename_i hv
            exact .setLane ht hq htj (by simpa [Option.isSome_iff_ne_none] using hl) htv
              (by simpa using hv) h
  | ldlw b wi j =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨jw, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                simp only [bind_ok_iff] at h
                obtain ⟨tj, htj, h⟩ := h
                split at h
                · simp at h
                · rename_i hl
                  exact .ldlw ht hb hq (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                    (ltI_sound _ _ _ (by simpa using hk)) htj
                    (by simpa [Option.isSome_iff_ne_none] using hl) h
  | stlw b wi j v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨jw, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                simp only [bind_ok_iff] at h
                obtain ⟨tj, htj, h⟩ := h
                split at h
                · simp at h
                · rename_i hl
                  simp only [bind_ok_iff] at h
                  obtain ⟨tv, htv, h⟩ := h
                  split at h
                  · simp at h
                  · rename_i hv
                    exact .stlw ht hb hq (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                      (ltI_sound _ _ _ (by simpa using hk)) htj
                      (by simpa [Option.isSome_iff_ne_none] using hl) htv (by simpa using hv) h
  | ldl b i =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨j, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                exact .ldl ht hb hq (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                  (ltI_sound _ _ _ (by simpa using hk)) h
  | stl b i v =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨t, ht, h⟩ := h
      split at h
      · simp at h
      · rename_i μ n u k hb
        split at h
        · simp at h
        · rename_i hμ
          have hμ' : μ = .own := by simpa using hμ
          subst hμ'
          split at h
          · simp at h
          · rename_i q hq
            simp only [bind_ok_iff] at h
            obtain ⟨j, hj, h⟩ := h
            split at h
            · simp at h
            · rename_i hn
              split at h
              · simp at h
              · rename_i hk
                simp only [bind_ok_iff] at h
                obtain ⟨tv, htv, h⟩ := h
                split at h
                · simp at h
                · rename_i hv
                  exact .stl ht hb hq (intIdx_sound hj) (ltI_sound _ _ _ (by simpa using hn))
                    (ltI_sound _ _ _ (by simpa using hk)) htv (by simpa using hv) h
  | freeze a =>
      simp only [checkOp, bind_ok_iff] at h
      obtain ⟨⟨tt, c₁⟩, h1, h⟩ := h
      split at h
      · split at h
        · simp at h
        · rename_i hs
          subst_vars
          exact .freeze h1 (by simpa using hs) h
      · simp at h
      · simp at h

theorem check_sound (p : Prog) : ∀ (e : Expr) (cx : Cx), check p cx e = .ok () → Typed p cx e := by
  intro e
  induction e with
  | let_ x op e ih =>
      intro cx h
      simp only [check_let, bind_ok_iff] at h
      obtain ⟨c₁, h1, h2⟩ := h
      exact .let_ (checkOp_sound p cx x op c₁ h1) (ih c₁ h2)
  | split a x y e ih =>
      intro cx h
      simp only [check_split, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u v
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
        exact .split h1 h2 h3 (ih c₃ h4)
      · simp at h
  | unpack a i x e ih =>
      intro cx h
      simp only [check_unpack, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i b
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, h3⟩ := h
        exact .unpack h1 h2 (ih c₂ h3)
      · simp at h
  | unpackT a α x e ih =>
      intro cx h
      simp only [check_unpackT, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i κ b
        split at h
        · simp at h
        · rename_i hg
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, h3⟩ := h
          exact .unpackT h1 (by simpa using hg) h2 (ih c₂ h3)
      · simp at h
  | region a rn pn tn e ih =>
      intro cx h
      simp only [check_region, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u
        split at h
        · simp at h
        · rename_i hs
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
          exact .region h1 (by simpa using hs) h2 h3 (ih c₃ h4)
      · split at h
        · simp at h
        · rename_i hs
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
          exact .regionBuf h1 (by simpa using hs) h2 h3 (ih c₃ h4)
      · simp at h
  | openPub a rn pn cn e ih =>
      intro cx h
      simp only [check_openPub, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
        exact .openPub h1 h2 h3 (ih c₃ h4)
      · simp at h
  | case a x e₁ y e₂ ih₁ ih₂ =>
      intro cx h
      simp only [check_case, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u v
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, _, h3, c₃, h4, h5⟩ := h
        exact .case h1 h2 (ih₁ c₂ h3) h4 (ih₂ c₃ h5)
      · simp at h
  | ifnull a e₁ y e₂ ih₁ ih₂ =>
      intro cx h
      simp only [check_ifnull, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i μ u
        simp only [bind_ok_iff] at h
        obtain ⟨_, h2, c₂, h3, h4⟩ := h
        exact .ifnull h1 (ih₁ c₁ h2) h3 (ih₂ c₂ h4)
      · simp at h
  | parity a k ev od ihe iho =>
      intro cx h
      simp only [check_parity, bind_ok_iff] at h
      obtain ⟨i, hi, h⟩ := h
      split at h
      · rename_i v hv
        simp only [bind_ok_iff, pure_ok_iff, exists_eq_left'] at h
        obtain ⟨_, h1, h2⟩ := h
        exact .parity (intIdx_sound hi) (asVar_eqI hv) (ihe _ h1) (iho _ h2)
      · simp at h
  | ifeq a b yes no ihy ihn =>
      intro cx h
      simp only [check_ifeq] at h
      split at h
      · rename_i hpe
        simp only [bind_ok_iff] at h
        obtain ⟨_, h1, h2⟩ := h
        exact .ifeqPlain (plainEq_sound hpe) (ihy cx h1) (ihn cx h2)
      simp only [bind_ok_iff] at h
      obtain ⟨i, hi, j, hj, h⟩ := h
      split at h
      · rename_i ni nj hni hnj
        split at h
        · simp only [bind_ok_iff] at h
          obtain ⟨_, h1, h2⟩ := h
          exact .ifeq (intIdx_sound hi) (intIdx_sound hj) (ihy cx h1) (noCx_sound hni hnj) (ihn _ h2)
        · split at h
          · split at h
            · simp at h
            · simp only [bind_ok_iff] at h
              obtain ⟨_, h1, h2⟩ := h
              refine .ifeqRec (intIdx_sound hi) (intIdx_sound hj) (.inl ⟨?_, ?_⟩) (ihy _ h1) (noCx_sound hni hnj) (ihn _ h2)
              · intro ρ hs
                have e1 := norm_sound _ ρ hs _ _ _ hni
                have e2 := asVar_ev ρ ni _ (by assumption)
                simp [ev]; omega
              · intro ρ hs
                have e1 := norm_sound _ ρ hs _ _ _ hnj
                simp; omega
          · split at h
            · simp at h
            · simp only [bind_ok_iff] at h
              obtain ⟨_, h1, h2⟩ := h
              refine .ifeqRec (intIdx_sound hi) (intIdx_sound hj) (.inr ⟨?_, ?_⟩) (ihy _ h1) (noCx_sound hni hnj) (ihn _ h2)
              · intro ρ hs
                have e1 := norm_sound _ ρ hs _ _ _ hnj
                have e2 := asVar_ev ρ nj _ (by assumption)
                simp [ev]; omega
              · intro ρ hs
                have e1 := norm_sound _ ρ hs _ _ _ hni
                simp; omega
          · split at h
            · rename_i u hz
              simp only [bind_ok_iff] at h
              obtain ⟨_, h1, h2⟩ := h
              obtain ⟨s, hze⟩ := zeroVar_sound hni hnj hz
              exact .ifeqZero (intIdx_sound hi) (intIdx_sound hj) hze (ihy _ h1)
                (noCx_sound hni hnj) (ihn _ h2)
            · simp at h
      · simp at h
  | cas acq rel w e v t ok fail ihok ihf =>
      intro cx h
      simp only [check_cas, bind_ok_iff] at h
      obtain ⟨tw, htw, h⟩ := h
      split at h
      · rename_i hw
        simp only [bind_ok_iff] at h
        obtain ⟨u, hc, h⟩ := h
        split at h <;> (try (simp at h; done))
        rename_i hraw
        split at h <;> (try (simp at h; done))
        rename_i haff
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨te, hte, tv, c₁, h1, h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hse
        split at h <;> (try (simp at h; done))
        rename_i hsv
        split at h <;> (try (simp at h; done))
        rename_i hsens
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, _, h3, h4⟩ := h
        exact .casCell htw hw (casCellTy_sound hc) (by simpa using hraw) (by simpa using haff) hte h1
          (sub_sound _ _ _ (by simpa using hse)) (sub_sound _ _ _ (by simpa using hsv))
          (fun hs => by simpa [hs] using hsens) h2 (ihok c₂ h3) (ihf c₁ h4)
      · rename_i r P hw
        cases hep : P.epoch
        case true =>
          simp only [hep, ↓reduceIte] at h
          split at h <;> (try (simp at h; done))
          rename_i hacq
          simp only [bind_ok_iff, Prod.exists] at h
          obtain ⟨i, hi, j, hj, c, k, hc, c', k', hc', h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i hps
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .casEpoch htw hw hep (by simpa using hacq) (intIdx_sound hi) (intIdx_sound hj)
            (classifyM_sound _ _ _ _ _ hc) (classifyM_sound _ _ _ _ _ hc')
            (pstep_sound _ _ _ _ _ _ (by simpa using hps)) h3 (ihok c₂ h4) (ihf cx h2)
        simp only [hep, Bool.false_eq_true, ↓reduceIte] at h
        cases hg : P.ghost
        case true => simp only [hg, ↓reduceIte] at h; simp at h
        simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨i, hi, j, hj, c, k, hc, c', k', hc', cl, hcl, cl', hcl', h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hh
        split at h <;> (try (simp at h; done))
        rename_i hps
        split at h
        · rename_i hh'
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .casShare htw hw (by simpa using hg) (intIdx_sound hi) (intIdx_sound hj)
            (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (classifyM_sound _ _ _ _ _ hc')
            (clauseM_ok hcl') (by simpa using hh) (pstep_sound _ _ _ _ _ _ (by simpa using hps))
            hh' (lendCx_sound h3) (ihok c₂ h4) (ihf cx h2)
        · rename_i hh'
          split at h <;> (try (simp at h; done))
          rename_i hlend
          split at h <;> (try (simp at h; done))
          rename_i hacq
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .casTake htw hw (by simpa using hg) (intIdx_sound hi) (intIdx_sound hj)
            (classifyM_sound _ _ _ _ _ hc) (clauseM_ok hcl) (classifyM_sound _ _ _ _ _ hc')
            (clauseM_ok hcl') (by simpa using hh) (pstep_sound _ _ _ _ _ _ (by simpa using hps))
            (by simpa using hh')
            (by simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hlend; exact hlend.1)
            (by simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hlend; exact hlend.2)
            (by simpa using hacq) h3 (ihok _ h4) (ihf cx h2)
  | casp acq rel w e0 e1 v0 v1 t ok fail ihok ihf =>
      intro cx h
      simp only [check_casp, bind_ok_iff] at h
      obtain ⟨tw, htw, h⟩ := h
      split at h
      · rename_i hw2
        split at h
        · simp at h
        · rename_i r P hw
          split at h <;> (try (simp at h; done))
          rename_i hrel
          simp only [bind_ok_iff] at h
          obtain ⟨i0, hi0, i1, hi1, j0, hj0, j1, hj1, h⟩ := h
          try dsimp only at h
          split at h <;> (try (simp at h; done))
          rename_i htk
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .caspE htw hw2 hw (by simpa using hrel) (intIdx_sound hi0) (intIdx_sound hi1)
            (intIdx_sound hj0) (intIdx_sound hj1) (hasTokE_sound (by simpa using htk)) h3
            (ihok c₂ h4) (ihf cx h2)
      · rename_i r P hw
        simp only [bind_ok_iff, Prod.exists] at h
        obtain ⟨i0, hi0, i1, hi1, j0, hj0, j1, hj1, c, k0, k1, hc, c', k0', k1', hc', cl, hcl, cl', hcl', h⟩ := h
        try dsimp only at h
        split at h <;> (try (simp at h; done))
        rename_i hh
        split at h <;> (try (simp at h; done))
        rename_i hps
        split at h
        · rename_i hh'
          split at h
          · rename_i hb
            split at h <;> (try (simp at h; done))
            rename_i hacq
            simp only [bind_ok_iff] at h
            obtain ⟨c₂, h3, _, h4, h2⟩ := h
            obtain ⟨hep, hbump⟩ := bump2_sound cx P k0 k0' hb
            exact .caspBump htw hw (intIdx_sound hi0) (intIdx_sound hi1) (intIdx_sound hj0) (intIdx_sound hj1)
              (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
              (clause2M_ok hcl') (by simpa using hh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
              hh' hep hbump (by simpa using hacq) h3 (ihok c₂ h4) (ihf cx h2)
          · simp only [bind_ok_iff] at h
            obtain ⟨c₂, h3, _, h4, h2⟩ := h
            exact .caspMove htw hw (intIdx_sound hi0) (intIdx_sound hi1) (intIdx_sound hj0) (intIdx_sound hj1)
              (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
              (clause2M_ok hcl') (by simpa using hh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
              hh' h3 (ihok c₂ h4) (ihf cx h2)
        · rename_i hh'
          split at h <;> (try (simp at h; done))
          rename_i hacq
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h3, _, h4, h2⟩ := h
          exact .caspTake htw hw (intIdx_sound hi0) (intIdx_sound hi1) (intIdx_sound hj0) (intIdx_sound hj1)
            (classify2M_sound _ _ _ _ _ _ _ hc) (clause2M_ok hcl) (classify2M_sound _ _ _ _ _ _ _ hc')
            (clause2M_ok hcl') (by simpa using hh) (pstep2_sound _ _ _ _ _ _ _ _ (by simpa using hps))
            (by simpa using hh') (by simpa using hacq) h3 (ihok c₂ h4) (ihf cx h2)
  | ret a =>
      intro cx h
      simp only [check_ret, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, u, hn, u', _, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        exact .ret h1 (noLeak_sound hn) (sub_sound _ _ _ (by simpa using hs))
  | tail f is a ts =>
      intro cx h
      simp only [check_tail, tailCheck, bind_ok_iff] at h
      obtain ⟨d, hd, ⟨at_, rt⟩, hi, ⟨t, c₁⟩, h1, u, hn, u', _, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        split at h
        · simp at h
        · rename_i hr
          exact .tail hd hi h1 (noLeak_sound hn) (sub_sound _ _ _ (by simpa using hs))
            (sub_sound _ _ _ (by simpa using hr))

/-- **The checker is sound** for a code block. -/
theorem checkDecl_sound (p : Prog) (d : Decl) (h : checkDecl p d = .ok ()) : DeclT p d := by
  rw [checkDecl_eq] at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hwf
    split at h
    · simp at h
    · rename_i hsc
      simp at hwf hsc
      -- (M1, T6) the kind rules run after `check`
      simp only [bind_ok_iff] at h
      obtain ⟨u, h1, -⟩ := h
      exact ⟨hwf.1, hwf.2, hsc.1, hsc.2, check_sound p d.body _ ((check_eq_checkBinders _ _ _).2 ⟨u, h1⟩)⟩

theorem forM_ok {α : Type} (f : α → M Unit) : ∀ (l : List α), l.forM f = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _, a, ha => by simp at ha
  | b :: bs, h, a, ha => by
      have h' : (f b >>= fun _ => bs.forM f) = .ok () := h
      simp only [bind_ok_iff] at h'
      obtain ⟨u, hb, hr⟩ := h'
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hb
      · exact forM_ok f bs hr a ha

/-- An accepted program passed its duplicate-name prefix: the decls' `forM` is accepted. -/
theorem checkProg_forM {p : Prog} (h : checkProg p = .ok ()) : p.forM (checkDecl p) = .ok () := by
  unfold checkProg at h
  split at h
  · split at h
    · simp at h
    · simp at h; exact h.2
  · simp at h; exact h.2

/-- **The checker is sound** (T1b): an accepted program is well typed. -/
theorem checkProg_sound (p : Prog) (h : checkProg p = .ok ()) : ProgT p :=
  fun d hd => checkDecl_sound p d (forM_ok _ p (checkProg_forM h) d hd)

/-! ## §6. The library programs are well typed

The checker's verdict on each library program, computed by the kernel —
`decide +kernel`, not `native_decide`, so the proofs rest on no axiom beyond
Lean's own — and turned into a derivation by `checkProg_sound`.  (That is why
`norm` is structural: the kernel cannot unfold well-founded recursion.) -/

theorem ok_of_accepts {r : M Unit} (h : accepts r = true) : r = .ok () := by
  cases r with
  | error e => simp [accepts] at h
  | ok u => rfl

theorem mutexLib_typed : ProgT mutexLib :=
  checkProg_sound _ (ok_of_accepts (by decide +kernel))

theorem seqLib_typed : ProgT seqLib :=
  checkProg_sound _ (ok_of_accepts (by decide +kernel))

theorem queueLib_typed : ProgT (queueLib .int) :=
  checkProg_sound _ (ok_of_accepts (by decide +kernel))

theorem polyQueueLib_typed : ProgT polyQueueLib :=
  checkProg_sound _ (ok_of_accepts (by decide +kernel))

theorem claimLib_typed : ProgT (claimLib .int true ++ [useClaimedD]) :=
  checkProg_sound _ (ok_of_accepts (by decide +kernel))

theorem pcLib_typed : ProgT pcLib :=
  checkProg_sound _ (ok_of_accepts (by decide +kernel))

-- Read back by check-promises.sh: present, and without `sorryAx`.
#print axioms checkProg_sound
#print axioms seqLib_typed
#print axioms pcLib_typed

end CoreTyping
