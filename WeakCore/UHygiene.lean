/-
# UHygiene — the elaboration's temporaries are fresh (hygiene by reservation)

UnElab's parser refuses every name beginning with `%` (`noReserved`: no user binder, variable, or name inside a
nested head is reserved).  The elaborator's binders are then the only reserved ones, and they are fresh:

`Fresh k e`: along every path of `e`, each reserved binder is a temporary `tmp j` with `j` at least the counter
reached so far, and the counter then moves past `j`; so along a path the temporaries are strictly increasing
(no temporary shadows another, and none shadows or is shadowed by a user name, which is never reserved).  The
names a head binds outside its atoms (`ldp … as (n0, n1)`) and the index binders of `unpack`/`region`/
`openPub`/`parity` are not reserved at all.

**Theorem** `elabT_fresh : noReservedE e = true → Fresh k (elabT k e)` (and `elabDecl_fresh` for a block).
-/
import WeakCore.UnElab
open CoreLang CoreTerm UnElab

namespace UHygiene

theorem reserved_tmp (j : Nat) : reserved (tmp j) = true := by
  unfold reserved tmp String.startsWith
  simp

/-- The names a head binds outside its atom positions are not reserved. -/
def headOK : Op → Bool
  | .ldp _ _ n0 n1 => !reserved n0 && !reserved n1
  | _ => true

/-- A binder `x` at counter `k`, then `P` at the next counter: a reserved binder is a temporary `tmp j`, `k ≤ j`,
and the counter moves to `j + 1`; any other binder leaves it. -/
def FreshB (k : Nat) (x : String) (P : Nat → Prop) : Prop :=
  if reserved x = true then ∃ j, x = tmp j ∧ k ≤ j ∧ P (j + 1) else P k

/-- Along every path, reserved binders are strictly increasing temporaries, from `k` on. -/
def Fresh : Nat → Expr → Prop
  | k, .let_ x op e => headOK op = true ∧ FreshB k x (fun k' => Fresh k' e)
  | k, .split _ x y e => FreshB k x (fun k1 => FreshB k1 y (fun k2 => Fresh k2 e))
  | k, .unpack _ i x e => reserved i = false ∧ FreshB k x (fun k' => Fresh k' e)
  | k, .unpackT _ a x e => reserved a = false ∧ FreshB k x (fun k' => Fresh k' e)
  | k, .region _ r p t e => reserved r = false ∧ FreshB k p (fun k1 => FreshB k1 t (fun k2 => Fresh k2 e))
  | k, .openPub _ r p c e => reserved r = false ∧ FreshB k p (fun k1 => FreshB k1 c (fun k2 => Fresh k2 e))
  | k, .case _ x e₁ y e₂ => FreshB k x (fun k' => Fresh k' e₁) ∧ FreshB k y (fun k' => Fresh k' e₂)
  | k, .ifnull _ e₁ x e₂ => Fresh k e₁ ∧ FreshB k x (fun k' => Fresh k' e₂)
  | k, .parity _ n ev od => reserved n = false ∧ Fresh k ev ∧ Fresh k od
  | k, .ifeq _ _ yes no => Fresh k yes ∧ Fresh k no
  | k, .cas _ _ _ _ _ t ok fail => FreshB k t (fun k' => Fresh k' ok) ∧ FreshB k t (fun k' => Fresh k' fail)
  | k, .casp _ _ _ _ _ _ _ t ok fail =>
      FreshB k t (fun k' => Fresh k' ok) ∧ FreshB k t (fun k' => Fresh k' fail)
  | _, .ret _ => True
  | _, .tail .. => True

/-! ## Monotonicity -/

theorem FreshB_mono {P : Nat → Prop} (hP : ∀ a b, b ≤ a → P a → P b) {k k' : Nat} {x : String}
    (hk : k' ≤ k) (h : FreshB k x P) : FreshB k' x P := by
  unfold FreshB at *
  split
  · rename_i hr; simp only [hr, ite_true] at h
    obtain ⟨j, hj, hkj, hp⟩ := h
    exact ⟨j, hj, Nat.le_trans hk hkj, hp⟩
  · rename_i hr; simp only [hr] at h
    exact hP _ _ hk h

theorem fresh_mono : ∀ (e : Expr) {k k' : Nat}, k' ≤ k → Fresh k e → Fresh k' e
  | .let_ x op e, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨h.1, FreshB_mono (fun a b hab => fresh_mono e hab) hk h.2⟩
  | .split _ x y e, k, k', hk, h => by
      simp only [Fresh] at *
      exact FreshB_mono (fun a b hab => FreshB_mono (fun a b hab => fresh_mono e hab) hab) hk h
  | .unpack _ i x e, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨h.1, FreshB_mono (fun a b hab => fresh_mono e hab) hk h.2⟩
  | .unpackT _ a x e, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨h.1, FreshB_mono (fun a b hab => fresh_mono e hab) hk h.2⟩
  | .region _ r p t e, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨h.1, FreshB_mono (fun a b hab => FreshB_mono (fun a b hab => fresh_mono e hab) hab) hk h.2⟩
  | .openPub _ r p c e, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨h.1, FreshB_mono (fun a b hab => FreshB_mono (fun a b hab => fresh_mono e hab) hab) hk h.2⟩
  | .case _ x e₁ y e₂, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨FreshB_mono (fun a b hab => fresh_mono e₁ hab) hk h.1,
             FreshB_mono (fun a b hab => fresh_mono e₂ hab) hk h.2⟩
  | .ifnull _ e₁ x e₂, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨fresh_mono e₁ hk h.1, FreshB_mono (fun a b hab => fresh_mono e₂ hab) hk h.2⟩
  | .parity _ n ev od, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨h.1, fresh_mono ev hk h.2.1, fresh_mono od hk h.2.2⟩
  | .ifeq _ _ yes no, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨fresh_mono yes hk h.1, fresh_mono no hk h.2⟩
  | .cas _ _ _ _ _ t ok fail, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨FreshB_mono (fun a b hab => fresh_mono ok hab) hk h.1,
             FreshB_mono (fun a b hab => fresh_mono fail hab) hk h.2⟩
  | .casp _ _ _ _ _ _ _ t ok fail, k, k', hk, h => by
      simp only [Fresh] at *
      exact ⟨FreshB_mono (fun a b hab => fresh_mono ok hab) hk h.1,
             FreshB_mono (fun a b hab => fresh_mono fail hab) hk h.2⟩
  | .ret _, _, _, _, _ => trivial
  | .tail .., _, _, _, _ => trivial

/-! ## Binders -/

theorem FreshB_user {k : Nat} {x : String} {P : Nat → Prop} (hx : reserved x = false) (h : P k) : FreshB k x P := by
  unfold FreshB; simp [hx, h]

theorem FreshB_tmp {k j : Nat} {P : Nat → Prop} (hj : k ≤ j) (h : P (j + 1)) : FreshB k (tmp j) P := by
  unfold FreshB; simp only [reserved_tmp, ite_true]; exact ⟨j, rfl, hj, h⟩

theorem binder_fresh {k : Nat} {o : Option String} {P : Nat → Prop} (ho : noResPat (.bind o) = true)
    (h : P (binder o k).2) : k ≤ (binder o k).2 ∧ FreshB k (binder o k).1 P := by
  cases o with
  | some x =>
      simp only [noResPat, Bool.not_eq_true'] at ho
      exact ⟨Nat.le_refl _, FreshB_user ho h⟩
  | none => exact ⟨Nat.le_succ _, FreshB_tmp (Nat.le_refl _) h⟩

theorem patBinder_fresh {k : Nat} {p : UPat} {P : Nat → Prop} (hp : noResPat p = true)
    (h : P (patBinder p k).2) : k ≤ (patBinder p k).2 ∧ FreshB k (patBinder p k).1 P := by
  cases p with
  | bind o => exact binder_fresh hp h
  | pair _ _ => exact ⟨Nat.le_succ _, FreshB_tmp (Nat.le_refl _) h⟩

theorem lets_append (l₁ l₂ : List (String × Op)) (e : Expr) : lets (l₁ ++ l₂) e = lets l₁ (lets l₂ e) := by
  induction l₁ with
  | nil => rfl
  | cons b l ih => cases b; simp only [List.cons_append, lets, ih]

theorem headOK_setAts (h : Op) (as : List At) (hh : noResHead h = true) : headOK (setAts h as) = true := by
  cases h <;> simp only [setAts, noResHead] at * <;> (try split) <;> simp_all [headOK]

/-! ## Operands -/

mutual
theorem elabArg_fresh (k : Nat) (a : UArg) (ha : noResArg a = true) :
    k ≤ (elabArg k a).2.2 ∧ ∀ e, Fresh (elabArg k a).2.2 e → Fresh k (lets (elabArg k a).1 e) := by
  match a with
  | .at _ => exact ⟨Nat.le_refl _, fun e h => h⟩
  | .op h args =>
      simp only [noResArg, Bool.and_eq_true] at ha
      have ih := elabArgs_fresh k args ha.2
      refine ⟨Nat.le_trans ih.1 (Nat.le_succ _), fun e he => ?_⟩
      simp only [elabArg, lets_append, lets]
      exact ih.2 _ ⟨headOK_setAts _ _ ha.1, FreshB_tmp (Nat.le_refl _) he⟩

theorem elabArgs_fresh (k : Nat) (as : List UArg) (ha : noResArgs as = true) :
    k ≤ (elabArgs k as).2.2 ∧ ∀ e, Fresh (elabArgs k as).2.2 e → Fresh k (lets (elabArgs k as).1 e) := by
  match as with
  | [] => exact ⟨Nat.le_refl _, fun e h => h⟩
  | a :: rest =>
      simp only [noResArgs, Bool.and_eq_true] at ha
      have h1 := elabArg_fresh k a ha.1
      have h2 := elabArgs_fresh (elabArg k a).2.2 rest ha.2
      refine ⟨Nat.le_trans h1.1 h2.1, fun e he => ?_⟩
      simp only [elabArgs, lets_append]
      exact h1.2 _ (h2.2 _ he)
end

/-! ## Patterns -/

theorem destr_fresh (p : UPat) : noResPat p = true →
    ∀ (k : Nat) (s : At) (c : Nat → Expr), (∀ j, k ≤ j → Fresh j (c j)) → Fresh k (destr k s p c) := by
  induction p with
  | bind o => intro _ k s c hc; exact hc k (Nat.le_refl _)
  | pair p q ihp ihq =>
      intro hp k s c hc
      simp only [noResPat, Bool.and_eq_true] at hp
      simp only [destr, Fresh]
      have h1 := (patBinder_fresh (k := k) (P := fun _ => True) hp.1 trivial).1
      have h2 := (patBinder_fresh (k := (patBinder p k).2) (P := fun _ => True) hp.2 trivial).1
      refine (patBinder_fresh hp.1 ?_).2
      refine (patBinder_fresh hp.2 ?_).2
      refine ihp hp.1 _ _ _ fun j hj => ihq hp.2 _ _ _ fun j' hj' => hc j' ?_
      exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans hj hj'))

/-! ## Terms -/

theorem noResArgs_two {a b : UArg} (ha : noResArg a = true) (hb : noResArg b = true) : noResArgs [a, b] = true := by
  simp [noResArgs, ha, hb]

/-- **Hygiene**: the elaboration of a term without reserved names has fresh temporaries. -/
theorem elabT_fresh : ∀ (e : UExpr) (k : Nat), noReservedE e = true → Fresh k (elabT k e)
  | .let_ x h args e, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, and_assoc] at hn
      obtain ⟨hx, hh, ha, he⟩ := hn
      simp only [elabT]
      refine (elabArgs_fresh k args ha).2 _ ?_
      simp only [Fresh]
      exact ⟨headOK_setAts _ _ hh, (binder_fresh hx (elabT_fresh e _ he)).2⟩
  | .split a p q e, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, and_assoc] at hn
      obtain ⟨ha, hp, hq, he⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      exact destr_fresh (.pair p q) (by simp [noResPat, hp, hq]) _ _ _ fun j _ => elabT_fresh e j he
  | .unpack a i x e, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, hi, hx, he⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      simp only [Fresh]
      exact ⟨hi, FreshB_user hx (elabT_fresh e _ he)⟩
  | .unpackT a al x e, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, hi, hx, he⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      simp only [Fresh]
      exact ⟨hi, FreshB_user hx (elabT_fresh e _ he)⟩
  | .region a r p t e, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, hr, hp, ht, he⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      simp only [Fresh]
      exact ⟨hr, FreshB_user hp (FreshB_user ht (elabT_fresh e _ he))⟩
  | .openPub a r p c e, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, hr, hp, hc, he⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      simp only [Fresh]
      exact ⟨hr, FreshB_user hp (FreshB_user hc (elabT_fresh e _ he))⟩
  | .case a x e₁ y e₂, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, hx, hy, h1, h2⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      simp only [Fresh]
      exact ⟨FreshB_user hx (elabT_fresh e₁ _ h1), FreshB_user hy (elabT_fresh e₂ _ h2)⟩
  | .ifnull a e₁ x e₂, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, hx, h1, h2⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      simp only [Fresh]
      exact ⟨elabT_fresh e₁ _ h1, FreshB_user hx (elabT_fresh e₂ _ h2)⟩
  | .parity a n ev od, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, hk, h1, h2⟩ := hn
      simp only [elabT]
      refine (elabArg_fresh k a ha).2 _ ?_
      simp only [Fresh]
      exact ⟨hk, elabT_fresh ev _ h1, elabT_fresh od _ h2⟩
  | .ifeq a b yes no, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, and_assoc] at hn
      obtain ⟨ha, hb, h1, h2⟩ := hn
      simp only [elabT]
      refine (elabArgs_fresh k [a, b] (noResArgs_two ha hb)).2 _ ?_
      simp only [Fresh]
      exact ⟨elabT_fresh yes _ h1, elabT_fresh no _ h2⟩
  | .cas acq rel w e v t ok fail, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, ht, h1, h2⟩ := hn
      simp only [elabT]
      refine (elabArgs_fresh k _ ha).2 _ ?_
      simp only [Fresh]
      exact ⟨FreshB_user ht (elabT_fresh ok _ h1), FreshB_user ht (elabT_fresh fail _ h2)⟩
  | .casp acq rel w e0 e1 v0 v1 t ok fail, k, hn => by
      simp only [noReservedE, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hn
      obtain ⟨ha, ht, h1, h2⟩ := hn
      simp only [elabT]
      refine (elabArgs_fresh k _ ha).2 _ ?_
      simp only [Fresh]
      exact ⟨FreshB_user ht (elabT_fresh ok _ h1), FreshB_user ht (elabT_fresh fail _ h2)⟩
  | .ret a, k, hn => by
      simp only [noReservedE] at hn
      simp only [elabT]
      exact (elabArg_fresh k a hn).2 _ trivial
  | .tail f is a ts, k, hn => by
      simp only [noReservedE] at hn
      simp only [elabT]
      exact (elabArg_fresh k a hn).2 _ trivial

/-- A block: its argument is not reserved, and its body's temporaries are fresh from `%0`. -/
theorem elabDecl_fresh (d : UDecl) (h : !reserved d.arg && noReservedE d.body) :
    reserved (elabDecl d).arg = false ∧ Fresh 0 (elabDecl d).body := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1, elabT_fresh d.body 0 h.2⟩

/-- A program: every block. -/
theorem elabProg_fresh (U : UProg) (h : noReserved U = true) :
    ∀ d ∈ elabProg U, reserved d.arg = false ∧ Fresh 0 d.body := by
  intro d hd
  simp only [elabProg, List.mem_map] at hd
  obtain ⟨u, hu, rfl⟩ := hd
  simp only [noReserved, List.all_eq_true] at h
  exact elabDecl_fresh u (h u hu)

#print axioms reserved_tmp
#print axioms fresh_mono
#print axioms elabArg_fresh
#print axioms destr_fresh
#print axioms elabT_fresh
#print axioms elabProg_fresh

end UHygiene
