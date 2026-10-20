import WeakCore.TermSound

/-!
# KindSound — row 18's kind lemmas (T3b-2e)

`CoreLang.coversInstances` sampled the claim; this file proves it.  A
polymorphic block is checked once, each type parameter answering from its
kind, and then instantiated at admitted types.  Every property the checker
concludes of a generic type holds of each instance: generic `sharedOK`,
`coupledOK`, `noOwn`, `Zeroable`, `wordFree` imply the instance's, and generic
*not* view-sensitive / *not* affine imply the instance's.

Layout of the proof:
* §A type shifts (`shiftT`) leave every predicate alone, given the kind
  environment gains the matching entry (weakening);
* §B index shifts (`shiftI`) leave every predicate alone (`zeroableIn` moves its
  index environment along);
* §C `zeroableIn` is monotone in what is known about indices;
* §D substitution keeps every defined width and arm summary (`info`);
* §E the predicates under substitution: the row-18 lemma, for the checker's
  simultaneous `substTs` and `admitsIn`, and `coversInstances` as a theorem.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace KindSound
open CoreLang CoreTerm TermSound

/-! ## §A. Type shifts -/

/-- Insert kind entry `x` at position `c`. -/
def insK (c : Nat) (x : Option Kind) (ke : KEnv) : KEnv := ke.take c ++ x :: ke.drop c

theorem insK_succ (c : Nat) (x y : Option Kind) (ke : KEnv) :
    y :: insK c x ke = insK (c + 1) x (y :: ke) := by
  simp [insK]

theorem insK_zero (x : Option Kind) (ke : KEnv) : insK 0 x ke = x :: ke := by
  simp [insK]

theorem get_insK_lt {c k : Nat} (x : Option Kind) {ke : KEnv} (hc : c ≤ ke.length) (hk : k < c) :
    (insK c x ke)[k]? = ke[k]? := by
  unfold insK
  rw [List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_take, hk]

theorem get_insK_ge {c k : Nat} (x : Option Kind) {ke : KEnv} (hc : c ≤ ke.length) (hk : c ≤ k) :
    (insK c x ke)[k + 1]? = ke[k]? := by
  unfold insK
  rw [List.getElem?_append_right (by simp; omega)]
  have e : k + 1 - (List.take c ke).length = (k - c) + 1 := by simp; omega
  rw [e]
  simp [List.getElem?_drop]
  congr 1; omega

theorem ask_insK (c k : Nat) (x : Option Kind) (ke : KEnv) (hc : c ≤ ke.length) (r : Bool)
    (f : Kind → Bool) :
    (insK c x ke).ask (if k ≥ c then k + 1 else k) r f = ke.ask k r f := by
  unfold KEnv.ask
  by_cases h : k ≥ c
  · rw [if_pos h, get_insK_ge x hc h]
  · rw [if_neg h, get_insK_lt x hc (Nat.lt_of_not_le h)]

theorem fits_shiftT (t : Ty) (c : Nat) : (t.shiftT c).fitsGranule = t.fitsGranule := by
  simp only [Ty.fitsGranule, width_shiftT]

theorem payloadFree_shiftT (t : Ty) (c : Nat) : (t.shiftT c).payloadFree = t.payloadFree := by
  simp only [Ty.payloadFree, info_top_shiftT]

/-- `Zeroable` (and the zero arms) under a type shift. -/
theorem zero_shiftT : ∀ (t : Ty) (env : IEnv) (c : Nat) (ke : KEnv) (x : Option Kind), c ≤ ke.length →
    zeroableIn env (insK c x ke) (t.shiftT c) = zeroableIn env ke t ∧
    ∀ sel : Ty → Bool, (∀ (u : Ty) (c' : Nat), sel (u.shiftT c') = sel u) →
      zeroArmP sel env (insK c x ke) (t.shiftT c) = zeroArmP sel env ke t := by
  have pf : ∀ (u : Ty) (c' : Nat), Ty.payloadFree (u.shiftT c') = Ty.payloadFree u := payloadFree_shiftT
  have tr : ∀ (u : Ty) (c' : Nat), (fun _ : Ty => true) (u.shiftT c') = (fun _ : Ty => true) u := fun _ _ => rfl
  -- a leaf arm: the zero arm is its own zeroability, if selected
  have leaf : ∀ (t : Ty) (env : IEnv) (c : Nat) (K ke : KEnv) (sel : Ty → Bool),
      zeroableIn env K (t.shiftT c) = zeroableIn env ke t → sel (t.shiftT c) = sel t →
      zeroArmP sel env K (t.shiftT c) = (if sel (t.shiftT c) then some (zeroableIn env K (t.shiftT c)) else none) →
      zeroArmP sel env ke t = (if sel t then some (zeroableIn env ke t) else none) →
      zeroArmP sel env K (t.shiftT c) = zeroArmP sel env ke t := by
    intro t env c K ke sel h hs e1 e2
    rw [e1, e2, h, hs]
  intro t
  induction t with
  | prod a b iha ihb =>
      intro env c ke x hc
      have h : zeroableIn env (insK c x ke) ((Ty.prod a b).shiftT c) = zeroableIn env ke (.prod a b) := by
        simp only [Ty.shiftT, zeroableIn, (iha env c ke x hc).1, (ihb env c ke x hc).1]
      exact ⟨h, fun sel hs => leaf (.prod a b) env c _ ke sel h (hs _ c) (by simp only [Ty.shiftT, zeroArmP] <;> rfl) (by simp only [zeroArmP])⟩
  | sum a b iha ihb =>
      intro env c ke x hc
      have e : info Ty.top (.sum (a.shiftT c) (b.shiftT c)) = info Ty.top (.sum a b) :=
        info_top_shiftT (.sum a b) c
      refine ⟨?_, fun sel hs => ?_⟩
      · simp only [Ty.shiftT, zeroableIn, Ty.tier, e, (iha env c ke x hc).2 _ pf, (ihb env c ke x hc).2 _ pf,
          (iha env c ke x hc).2 (fun _ => true) tr, (ihb env c ke x hc).2 (fun _ => true) tr]
      · simp only [Ty.shiftT, zeroArmP, (iha env c ke x hc).2 sel hs, (ihb env c ke x hc).2 sel hs]
  | array i t ih =>
      intro env c ke x hc
      have h : zeroableIn env (insK c x ke) ((Ty.array i t).shiftT c) = zeroableIn env ke (.array i t) := by
        simp only [Ty.shiftT, zeroableIn, (ih env c ke x hc).1]
      exact ⟨h, fun sel hs => leaf (.array i t) env c _ ke sel h (hs _ c) (by simp only [Ty.shiftT, zeroArmP] <;> rfl) (by simp only [zeroArmP])⟩
  | loc μ t ih =>
      intro env c ke x hc
      have h : zeroableIn env (insK c x ke) ((Ty.loc μ t).shiftT c) = zeroableIn env ke (.loc μ t) := by
        cases t with
        | array i u => simp only [Ty.shiftT, zeroableIn]
        | tvar j => simp only [Ty.shiftT]; split <;> simp only [zeroableIn]
        | _ => simp only [Ty.shiftT, zeroableIn]
      exact ⟨h, fun sel hs => leaf (.loc μ t) env c _ ke sel h (hs _ c) (by simp only [Ty.shiftT, zeroArmP] <;> rfl) (by simp only [zeroArmP])⟩
  | tvar k =>
      intro env c ke x hc
      have e := ask_insK c k x ke hc false (·.zero)
      have h : zeroableIn env (insK c x ke) ((Ty.tvar k).shiftT c) = zeroableIn env ke (.tvar k) := by
        by_cases hk : k ≥ c
        · rw [if_pos hk] at e; simp only [Ty.shiftT, if_pos hk, zeroableIn, e]
        · rw [if_neg hk] at e; simp only [Ty.shiftT, if_neg hk, zeroableIn, e]
      refine ⟨h, fun sel hs => leaf (.tvar k) env c _ ke sel h (hs _ c) ?_ (by simp only [zeroArmP])⟩
      by_cases hk : k ≥ c
      · simp only [Ty.shiftT, if_pos hk, zeroArmP]
      · simp only [Ty.shiftT, if_neg hk, zeroArmP]
  | mu t ih =>
      intro env c ke x hc
      have h := ih env (c + 1) (none :: ke) x (by simp; omega)
      refine ⟨by simp only [Ty.shiftT, zeroableIn, insK_succ, h.1], fun sel hs => ?_⟩
      simp only [Ty.shiftT, zeroArmP, insK_succ, h.2 sel hs]
  | tex κ t ih =>
      intro env c ke x hc
      have h := ih env (c + 1) (none :: ke) x (by simp; omega)
      refine ⟨by simp only [Ty.shiftT, zeroableIn], fun sel hs => ?_⟩
      simp only [Ty.shiftT, zeroArmP, insK_succ, h.2 sel hs]
  | iall t ih =>
      intro env c ke x hc
      have h := ih (none :: env) c ke x hc
      exact ⟨by simp only [Ty.shiftT, zeroableIn, h.1], fun sel hs => by simp only [Ty.shiftT, zeroArmP, h.2 sel hs]⟩
  | iex t ih =>
      intro env c ke x hc
      have h := ih (some 0 :: env) c ke x hc
      exact ⟨by simp only [Ty.shiftT, zeroableIn, h.1], fun sel hs => by simp only [Ty.shiftT, zeroArmP, h.2 sel hs]⟩
  | refine t ψ ih =>
      intro env c ke x hc
      have h := ih env c ke x hc
      exact ⟨by simp only [Ty.shiftT, zeroableIn, h.1], fun sel hs => by simp only [Ty.shiftT, zeroArmP, h.2 sel hs]⟩
  | void => intro env c ke x hc; exact ⟨by simp only [Ty.shiftT, zeroableIn], fun _ _ => by simp only [Ty.shiftT, zeroArmP]⟩
  | _ =>
      intro env c ke x hc
      refine ⟨by simp only [Ty.shiftT, zeroableIn], fun sel hs => ?_⟩
      exact leaf _ env c _ ke sel (by simp only [Ty.shiftT, zeroableIn]) (hs _ c) (by simp only [Ty.shiftT, zeroArmP] <;> rfl) (by simp only [zeroArmP])

/-- The element a reference's `ini` is about (`pointeeZeroableIn`). -/
def elemOf : Ty → Ty
  | .array _ e => e
  | u => u

theorem pz_ptr (ke : KEnv) (μ : Mode) (u : Ty) :
    Ty.pointeeZeroableIn ke (.ptr μ u) = zeroableIn [] ke (elemOf u) := by
  cases u <;> simp [Ty.pointeeZeroableIn, elemOf]
theorem pz_ptrOpt (ke : KEnv) (μ : Mode) (u : Ty) :
    Ty.pointeeZeroableIn ke (.ptrOpt μ u) = zeroableIn [] ke (elemOf u) := by
  cases u <;> simp [Ty.pointeeZeroableIn, elemOf]
theorem pz_loc (ke : KEnv) (μ : Mode) (u : Ty) :
    Ty.pointeeZeroableIn ke (.loc μ u) = zeroableIn [] ke (elemOf u) := by
  cases u <;> simp [Ty.pointeeZeroableIn, elemOf]

theorem elemOf_shiftT (u : Ty) (c : Nat) : elemOf (u.shiftT c) = (elemOf u).shiftT c := by
  cases u with
  | tvar j => simp only [Ty.shiftT]; split <;> simp [elemOf, Ty.shiftT, *]
  | _ => rfl

theorem pz_shiftT (t : Ty) (c : Nat) (ke : KEnv) (x : Option Kind) (hc : c ≤ ke.length) :
    Ty.pointeeZeroableIn (insK c x ke) (t.shiftT c) = Ty.pointeeZeroableIn ke t := by
  cases t with
  | ptr μ u => simp only [Ty.shiftT, pz_ptr, elemOf_shiftT, (zero_shiftT _ [] c ke x hc).1]
  | ptrOpt μ u => simp only [Ty.shiftT, pz_ptrOpt, elemOf_shiftT, (zero_shiftT _ [] c ke x hc).1]
  | loc μ u => simp only [Ty.shiftT, pz_loc, elemOf_shiftT, (zero_shiftT _ [] c ke x hc).1]
  | tvar j => simp only [Ty.shiftT]; split <;> rfl
  | _ => rfl

theorem sens_shiftT : ∀ (t : Ty) (c : Nat) (ke : KEnv) (x : Option Kind), c ≤ ke.length →
    Ty.sensitiveIn (insK c x ke) (t.shiftT c) = Ty.sensitiveIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, iha c ke x hc, ihb c ke x hc]
  | sum a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, iha c ke x hc, ihb c ke x hc]
  | array i t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, ih c ke x hc]
  | mu t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, insK_succ, ih (c + 1) (none :: ke) x (by simp; omega)]
  | tex κ t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, insK_succ, ih (c + 1) (some κ :: ke) x (by simp; omega)]
  | iall t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, ih c ke x hc]
  | iex t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, ih c ke x hc]
  | refine t ψ ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn, ih c ke x hc, pz_shiftT t c ke x hc]
  | tvar k =>
      intro c ke x hc
      have e := ask_insK c k x ke hc false (·.insens)
      by_cases hk : k ≥ c
      · rw [if_pos hk] at e; simp only [Ty.shiftT, if_pos hk, Ty.sensitiveIn, e]
      · rw [if_neg hk] at e; simp only [Ty.shiftT, if_neg hk, Ty.sensitiveIn, e]
  | cap s r => intro c ke x hc; cases s <;> simp only [Ty.shiftT, Ty.sensitiveIn]
  | _ => intro c ke x hc; simp only [Ty.shiftT, Ty.sensitiveIn]

theorem coupled_shiftT : ∀ (t : Ty) (c : Nat) (ke : KEnv) (x : Option Kind), c ≤ ke.length →
    Ty.coupledOKIn (insK c x ke) (t.shiftT c) = Ty.coupledOKIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.coupledOKIn, iha c ke x hc, ihb c ke x hc]
  | sum a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.coupledOKIn, iha c ke x hc, ihb c ke x hc]
  | array i t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.coupledOKIn, ih c ke x hc]
  | mu t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.coupledOKIn, insK_succ, ih (c + 1) (none :: ke) x (by simp; omega)]
  | tex κ t ih =>
      intro c ke x hc
      have e := fits_shiftT (.tex κ t) c
      simp only [Ty.shiftT] at e
      simp only [Ty.shiftT, Ty.coupledOKIn, insK_succ, ih (c + 1) (some κ :: ke) x (by simp; omega),
        countT_shiftT t (c + 1) 0 (by omega), e]
  | iall t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.coupledOKIn, ih c ke x hc]
  | iex t ih =>
      intro c ke x hc
      have e := fits_shiftT (.iex t) c
      simp only [Ty.shiftT] at e
      simp only [Ty.shiftT, Ty.coupledOKIn, ih c ke x hc, countI_shiftT t c 0, e]
  | refine t ψ ih => intro c ke x hc; simp only [Ty.shiftT, Ty.coupledOKIn, ih c ke x hc]
  | tvar k =>
      intro c ke x hc
      have e := ask_insK c k x ke hc true (·.share)
      by_cases hk : k ≥ c
      · rw [if_pos hk] at e; simp only [Ty.shiftT, if_pos hk, Ty.coupledOKIn, e]
      · rw [if_neg hk] at e; simp only [Ty.shiftT, if_neg hk, Ty.coupledOKIn, e]
  | _ => intro c ke x hc; simp only [Ty.shiftT, Ty.coupledOKIn]

theorem noOwn_shiftT : ∀ (t : Ty) (c : Nat) (ke : KEnv) (x : Option Kind), c ≤ ke.length →
    Ty.noOwnIn (insK c x ke) (t.shiftT c) = Ty.noOwnIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, iha c ke x hc, ihb c ke x hc]
  | sum a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, iha c ke x hc, ihb c ke x hc]
  | array i t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, ih c ke x hc]
  | ptr μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.noOwnIn, ih c ke x hc]
  | ptrOpt μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.noOwnIn, ih c ke x hc]
  | loc μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.noOwnIn, ih c ke x hc]
  | mu t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, insK_succ, ih (c + 1) (none :: ke) x (by simp; omega)]
  | tex κ t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, insK_succ, ih (c + 1) (some κ :: ke) x (by simp; omega)]
  | iall t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, ih c ke x hc]
  | iex t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, ih c ke x hc]
  | refine t ψ ih => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn, ih c ke x hc]
  | tvar k =>
      intro c ke x hc
      have e := ask_insK c k x ke hc true (·.noOwn)
      by_cases hk : k ≥ c
      · rw [if_pos hk] at e; simp only [Ty.shiftT, if_pos hk, Ty.noOwnIn, e]
      · rw [if_neg hk] at e; simp only [Ty.shiftT, if_neg hk, Ty.noOwnIn, e]
  | _ => intro c ke x hc; simp only [Ty.shiftT, Ty.noOwnIn]

theorem affine_shiftT : ∀ (t : Ty) (c : Nat) (ke : KEnv) (x : Option Kind), c ≤ ke.length →
    Ty.affineIn (insK c x ke) (t.shiftT c) = Ty.affineIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, iha c ke x hc, ihb c ke x hc]
  | sum a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, iha c ke x hc, ihb c ke x hc]
  | array i t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, ih c ke x hc]
  | ptr μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.affineIn]
  | ptrOpt μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.affineIn]
  | loc μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.affineIn]
  | mu t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, insK_succ, ih (c + 1) (none :: ke) x (by simp; omega)]
  | tex κ t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, insK_succ, ih (c + 1) (some κ :: ke) x (by simp; omega)]
  | iall t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, ih c ke x hc]
  | iex t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, ih c ke x hc]
  | refine t ψ ih => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn, ih c ke x hc]
  | tvar k =>
      intro c ke x hc
      have e := ask_insK c k x ke hc true (·.copy)
      by_cases hk : k ≥ c
      · rw [if_pos hk] at e; simp only [Ty.shiftT, if_pos hk, Ty.affineIn, e]
      · rw [if_neg hk] at e; simp only [Ty.shiftT, if_neg hk, Ty.affineIn, e]
  | _ => intro c ke x hc; simp only [Ty.shiftT, Ty.affineIn]

theorem shared_shiftT : ∀ (t : Ty) (c : Nat) (ke : KEnv) (x : Option Kind), c ≤ ke.length →
    Ty.sharedOKIn (insK c x ke) (t.shiftT c) = Ty.sharedOKIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, iha c ke x hc, ihb c ke x hc]
  | sum a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, iha c ke x hc, ihb c ke x hc]
  | code a b iha ihb => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, iha c ke x hc, ihb c ke x hc]
  | array i t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, ih c ke x hc]
  | ptr μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.sharedOKIn, ih c ke x hc, coupled_shiftT t c ke x hc, noOwn_shiftT t c ke x hc]
  | ptrOpt μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.sharedOKIn, ih c ke x hc, coupled_shiftT t c ke x hc, noOwn_shiftT t c ke x hc]
  | loc μ t ih => intro c ke x hc; cases μ <;> simp only [Ty.shiftT, Ty.sharedOKIn, ih c ke x hc, coupled_shiftT t c ke x hc, noOwn_shiftT t c ke x hc]
  | mu t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, insK_succ, ih (c + 1) (none :: ke) x (by simp; omega)]
  | tex κ t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, insK_succ, ih (c + 1) (some κ :: ke) x (by simp; omega)]
  | iall t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, ih c ke x hc]
  | iex t ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, ih c ke x hc]
  | refine t ψ ih => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn, ih c ke x hc]
  | tvar k => intro c ke x hc; simp only [Ty.shiftT]; split <;> simp only [Ty.sharedOKIn]
  | _ => intro c ke x hc; simp only [Ty.shiftT, Ty.sharedOKIn]

/-! ### Many type shifts at once -/

theorem zero_shiftTN (env : IEnv) (ke : KEnv) (σ : Ty) :
    ∀ ke₀ : KEnv, zeroableIn env (ke₀ ++ ke) (shiftTN ke₀.length σ) = zeroableIn env ke σ
  | [] => rfl
  | y :: ke₀ => by
      have e := (zero_shiftT (shiftTN ke₀.length σ) env 0 (ke₀ ++ ke) y (Nat.zero_le _)).1
      rw [insK_zero] at e
      simp only [List.cons_append, List.length_cons, shiftTN]
      rw [e]; exact zero_shiftTN env ke σ ke₀

theorem sens_shiftTN (ke : KEnv) (σ : Ty) :
    ∀ ke₀ : KEnv, Ty.sensitiveIn (ke₀ ++ ke) (shiftTN ke₀.length σ) = Ty.sensitiveIn ke σ
  | [] => rfl
  | y :: ke₀ => by
      have e := (sens_shiftT (shiftTN ke₀.length σ) 0 (ke₀ ++ ke) y (Nat.zero_le _))
      rw [insK_zero] at e
      simp only [List.cons_append, List.length_cons, shiftTN]
      rw [e]; exact sens_shiftTN ke σ ke₀

theorem coupled_shiftTN (ke : KEnv) (σ : Ty) :
    ∀ ke₀ : KEnv, Ty.coupledOKIn (ke₀ ++ ke) (shiftTN ke₀.length σ) = Ty.coupledOKIn ke σ
  | [] => rfl
  | y :: ke₀ => by
      have e := (coupled_shiftT (shiftTN ke₀.length σ) 0 (ke₀ ++ ke) y (Nat.zero_le _))
      rw [insK_zero] at e
      simp only [List.cons_append, List.length_cons, shiftTN]
      rw [e]; exact coupled_shiftTN ke σ ke₀

theorem noOwn_shiftTN (ke : KEnv) (σ : Ty) :
    ∀ ke₀ : KEnv, Ty.noOwnIn (ke₀ ++ ke) (shiftTN ke₀.length σ) = Ty.noOwnIn ke σ
  | [] => rfl
  | y :: ke₀ => by
      have e := (noOwn_shiftT (shiftTN ke₀.length σ) 0 (ke₀ ++ ke) y (Nat.zero_le _))
      rw [insK_zero] at e
      simp only [List.cons_append, List.length_cons, shiftTN]
      rw [e]; exact noOwn_shiftTN ke σ ke₀

theorem affine_shiftTN (ke : KEnv) (σ : Ty) :
    ∀ ke₀ : KEnv, Ty.affineIn (ke₀ ++ ke) (shiftTN ke₀.length σ) = Ty.affineIn ke σ
  | [] => rfl
  | y :: ke₀ => by
      have e := (affine_shiftT (shiftTN ke₀.length σ) 0 (ke₀ ++ ke) y (Nat.zero_le _))
      rw [insK_zero] at e
      simp only [List.cons_append, List.length_cons, shiftTN]
      rw [e]; exact affine_shiftTN ke σ ke₀

theorem shared_shiftTN (ke : KEnv) (σ : Ty) :
    ∀ ke₀ : KEnv, Ty.sharedOKIn (ke₀ ++ ke) (shiftTN ke₀.length σ) = Ty.sharedOKIn ke σ
  | [] => rfl
  | y :: ke₀ => by
      have e := (shared_shiftT (shiftTN ke₀.length σ) 0 (ke₀ ++ ke) y (Nat.zero_le _))
      rw [insK_zero] at e
      simp only [List.cons_append, List.length_cons, shiftTN]
      rw [e]; exact shared_shiftTN ke σ ke₀

theorem info_top_shiftTN : ∀ (c : Nat) (σ : Ty), info Ty.top (shiftTN c σ) = info Ty.top σ
  | 0, _ => rfl
  | c + 1, σ => by simp only [shiftTN, info_top_shiftT, info_top_shiftTN c σ]

/-! ## §B. Index shifts -/

theorem hasIni_shift (c : Nat) : ∀ ψ : Pred, (ψ.shift c).hasIni = ψ.hasIni
  | .and p q => by simp only [Pred.shift, Pred.hasIni, hasIni_shift c p, hasIni_shift c q]
  | .tt => rfl
  | .le _ _ => rfl
  | .eq _ _ => rfl
  | .ini _ => rfl

theorem payloadFree_shiftI (t : Ty) (c : Nat) : (t.shiftI c).payloadFree = t.payloadFree := by
  simp only [Ty.payloadFree, info_shiftI]

theorem zero_shiftI : ∀ (t : Ty) (c : Nat) (env' env : IEnv) (ke : KEnv), EnvSh c env' env →
    zeroableIn env' ke (t.shiftI c) = zeroableIn env ke t ∧
    ∀ sel : Ty → Bool, (∀ (u : Ty) (c' : Nat), sel (u.shiftI c') = sel u) →
      zeroArmP sel env' ke (t.shiftI c) = zeroArmP sel env ke t := by
  have pf : ∀ (u : Ty) (c' : Nat), Ty.payloadFree (u.shiftI c') = Ty.payloadFree u := payloadFree_shiftI
  have tr : ∀ (u : Ty) (c' : Nat), (fun _ : Ty => true) (u.shiftI c') = (fun _ : Ty => true) u := fun _ _ => rfl
  have leaf : ∀ (t : Ty) (c : Nat) (env' env : IEnv) (ke : KEnv) (sel : Ty → Bool),
      zeroableIn env' ke (t.shiftI c) = zeroableIn env ke t → sel (t.shiftI c) = sel t →
      zeroArmP sel env' ke (t.shiftI c) = (if sel (t.shiftI c) then some (zeroableIn env' ke (t.shiftI c)) else none) →
      zeroArmP sel env ke t = (if sel t then some (zeroableIn env ke t) else none) →
      zeroArmP sel env' ke (t.shiftI c) = zeroArmP sel env ke t := by
    intro t c env' env ke sel h hs e1 e2
    rw [e1, e2, h, hs]
  intro t
  induction t with
  | intS i =>
      intro c env' env ke h
      have e : zeroableIn env' ke ((Ty.intS i).shiftI c) = zeroableIn env ke (.intS i) := by
        simp only [Ty.shiftI, zeroableIn, evalIn_shift h]
      exact ⟨e, fun sel hs => leaf (.intS i) c env' env ke sel e (hs _ c) (by simp only [Ty.shiftI, zeroArmP] <;> rfl) (by simp only [zeroArmP])⟩
  | prod a b iha ihb =>
      intro c env' env ke h
      have e : zeroableIn env' ke ((Ty.prod a b).shiftI c) = zeroableIn env ke (.prod a b) := by
        simp only [Ty.shiftI, zeroableIn, (iha c env' env ke h).1, (ihb c env' env ke h).1]
      exact ⟨e, fun sel hs => leaf (.prod a b) c env' env ke sel e (hs _ c) (by simp only [Ty.shiftI, zeroArmP] <;> rfl) (by simp only [zeroArmP])⟩
  | sum a b iha ihb =>
      intro c env' env ke h
      have e := info_shiftI (.sum a b) c
      simp only [Ty.shiftI] at e
      refine ⟨?_, fun sel hs => ?_⟩
      · simp only [Ty.shiftI, zeroableIn, Ty.tier, e, (iha c env' env ke h).2 _ pf, (ihb c env' env ke h).2 _ pf,
          (iha c env' env ke h).2 (fun _ => true) tr, (ihb c env' env ke h).2 (fun _ => true) tr]
      · simp only [Ty.shiftI, zeroArmP, (iha c env' env ke h).2 sel hs, (ihb c env' env ke h).2 sel hs]
  | array i t ih =>
      intro c env' env ke h
      have e : zeroableIn env' ke ((Ty.array i t).shiftI c) = zeroableIn env ke (.array i t) := by
        simp only [Ty.shiftI, zeroableIn, (ih c env' env ke h).1]
      exact ⟨e, fun sel hs => leaf (.array i t) c env' env ke sel e (hs _ c) (by simp only [Ty.shiftI, zeroArmP] <;> rfl) (by simp only [zeroArmP])⟩
  | loc μ t ih =>
      intro c env' env ke h
      have e : zeroableIn env' ke ((Ty.loc μ t).shiftI c) = zeroableIn env ke (.loc μ t) := by
        cases t with
        | array i u => simp only [Ty.shiftI, zeroableIn, evalIn_shift h]
        | _ => simp only [Ty.shiftI, zeroableIn]
      exact ⟨e, fun sel hs => leaf (.loc μ t) c env' env ke sel e (hs _ c) (by simp only [Ty.shiftI, zeroArmP] <;> rfl) (by simp only [zeroArmP])⟩
  | mu t ih =>
      intro c env' env ke h
      have h' := ih c env' env (none :: ke) h
      exact ⟨by simp only [Ty.shiftI, zeroableIn, h'.1], fun sel hs => by simp only [Ty.shiftI, zeroArmP, h'.2 sel hs]⟩
  | tex κ t ih =>
      intro c env' env ke h
      have h' := ih c env' env (none :: ke) h
      exact ⟨by simp only [Ty.shiftI, zeroableIn], fun sel hs => by simp only [Ty.shiftI, zeroArmP, h'.2 sel hs]⟩
  | iall t ih =>
      intro c env' env ke h
      have h' := ih (c + 1) _ _ ke (h.cons none)
      exact ⟨by simp only [Ty.shiftI, zeroableIn, h'.1], fun sel hs => by simp only [Ty.shiftI, zeroArmP, h'.2 sel hs]⟩
  | iex t ih =>
      intro c env' env ke h
      have h' := ih (c + 1) _ _ ke (h.cons (some 0))
      exact ⟨by simp only [Ty.shiftI, zeroableIn, h'.1], fun sel hs => by simp only [Ty.shiftI, zeroArmP, h'.2 sel hs]⟩
  | refine t ψ ih =>
      intro c env' env ke h
      have h' := ih c env' env ke h
      exact ⟨by simp only [Ty.shiftI, zeroableIn, h'.1, zeroHolds_shift h],
        fun sel hs => by simp only [Ty.shiftI, zeroArmP, h'.2 sel hs, zeroHolds_shift h]⟩
  | void => intro c env' env ke h; exact ⟨by simp only [Ty.shiftI, zeroableIn], fun _ _ => by simp only [Ty.shiftI, zeroArmP]⟩
  | _ =>
      intro c env' env ke h
      refine ⟨by simp only [Ty.shiftI, zeroableIn], fun sel hs => ?_⟩
      exact leaf _ c env' env ke sel (by simp only [Ty.shiftI, zeroableIn]) (hs _ c) (by simp only [Ty.shiftI, zeroArmP] <;> rfl) (by simp only [zeroArmP])

theorem elemOf_shiftI (u : Ty) (c : Nat) : elemOf (u.shiftI c) = (elemOf u).shiftI c := by
  cases u <;> rfl

theorem pz_shiftI (t : Ty) (c : Nat) (ke : KEnv) :
    Ty.pointeeZeroableIn ke (t.shiftI c) = Ty.pointeeZeroableIn ke t := by
  cases t with
  | ptr μ u => simp only [Ty.shiftI, pz_ptr, elemOf_shiftI, (zero_shiftI _ c [] [] ke (EnvSh.nil c)).1]
  | ptrOpt μ u => simp only [Ty.shiftI, pz_ptrOpt, elemOf_shiftI, (zero_shiftI _ c [] [] ke (EnvSh.nil c)).1]
  | loc μ u => simp only [Ty.shiftI, pz_loc, elemOf_shiftI, (zero_shiftI _ c [] [] ke (EnvSh.nil c)).1]
  | _ => rfl

theorem fits_shiftI (t : Ty) (c : Nat) : (t.shiftI c).fitsGranule = t.fitsGranule := by
  simp only [Ty.fitsGranule, Ty.width, info_shiftI]
  cases (info Ty.top t).width <;> simp [closed_shift]

theorem sens_shiftI : ∀ (t : Ty) (c : Nat) (ke : KEnv),
    Ty.sensitiveIn ke (t.shiftI c) = Ty.sensitiveIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, iha, ihb]
  | sum a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, iha, ihb]
  | array i t ih => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, ih]
  | mu t ih => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, ih]
  | tex κ t ih => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, ih]
  | iall t ih => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, ih]
  | iex t ih => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, ih]
  | refine t ψ ih => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn, ih, pz_shiftI, hasIni_shift]
  | cap s r => intro c ke; cases s <;> simp only [Ty.shiftI, Ty.sensitiveIn]
  | _ => intro c ke; simp only [Ty.shiftI, Ty.sensitiveIn]

theorem coupled_shiftI : ∀ (t : Ty) (c : Nat) (ke : KEnv),
    Ty.coupledOKIn ke (t.shiftI c) = Ty.coupledOKIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.coupledOKIn, iha, ihb]
  | sum a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.coupledOKIn, iha, ihb]
  | array i t ih => intro c ke; simp only [Ty.shiftI, Ty.coupledOKIn, ih]
  | mu t ih => intro c ke; simp only [Ty.shiftI, Ty.coupledOKIn, ih]
  | tex κ t ih =>
      intro c ke
      have e := fits_shiftI (.tex κ t) c
      simp only [Ty.shiftI] at e
      simp only [Ty.shiftI, Ty.coupledOKIn, ih, countT_shiftI, e]
  | iall t ih => intro c ke; simp only [Ty.shiftI, Ty.coupledOKIn, ih]
  | iex t ih =>
      intro c ke
      have e := fits_shiftI (.iex t) c
      simp only [Ty.shiftI] at e
      simp only [Ty.shiftI, Ty.coupledOKIn, ih, countI_shiftI t (c + 1) 0 (by omega), e]
  | refine t ψ ih => intro c ke; simp only [Ty.shiftI, Ty.coupledOKIn, ih]
  | _ => intro c ke; simp only [Ty.shiftI, Ty.coupledOKIn]

theorem noOwn_shiftI : ∀ (t : Ty) (c : Nat) (ke : KEnv),
    Ty.noOwnIn ke (t.shiftI c) = Ty.noOwnIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, iha, ihb]
  | sum a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, iha, ihb]
  | array i t ih => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, ih]
  | ptr μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.noOwnIn, ih]
  | ptrOpt μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.noOwnIn, ih]
  | loc μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.noOwnIn, ih]
  | mu t ih => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, ih]
  | tex κ t ih => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, ih]
  | iall t ih => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, ih]
  | iex t ih => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, ih]
  | refine t ψ ih => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn, ih]
  | _ => intro c ke; simp only [Ty.shiftI, Ty.noOwnIn]

theorem affine_shiftI : ∀ (t : Ty) (c : Nat) (ke : KEnv),
    Ty.affineIn ke (t.shiftI c) = Ty.affineIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.affineIn, iha, ihb]
  | sum a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.affineIn, iha, ihb]
  | array i t ih => intro c ke; simp only [Ty.shiftI, Ty.affineIn, ih]
  | ptr μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.affineIn]
  | ptrOpt μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.affineIn]
  | loc μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.affineIn]
  | mu t ih => intro c ke; simp only [Ty.shiftI, Ty.affineIn, ih]
  | tex κ t ih => intro c ke; simp only [Ty.shiftI, Ty.affineIn, ih]
  | iall t ih => intro c ke; simp only [Ty.shiftI, Ty.affineIn, ih]
  | iex t ih => intro c ke; simp only [Ty.shiftI, Ty.affineIn, ih]
  | refine t ψ ih => intro c ke; simp only [Ty.shiftI, Ty.affineIn, ih]
  | _ => intro c ke; simp only [Ty.shiftI, Ty.affineIn]

theorem shared_shiftI : ∀ (t : Ty) (c : Nat) (ke : KEnv),
    Ty.sharedOKIn ke (t.shiftI c) = Ty.sharedOKIn ke t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, iha, ihb]
  | sum a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, iha, ihb]
  | code a b iha ihb => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, iha, ihb]
  | array i t ih => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, ih]
  | ptr μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.sharedOKIn, ih, coupled_shiftI, noOwn_shiftI]
  | ptrOpt μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.sharedOKIn, ih, coupled_shiftI, noOwn_shiftI]
  | loc μ t ih => intro c ke; cases μ <;> simp only [Ty.shiftI, Mode.shift, Ty.sharedOKIn, ih, coupled_shiftI, noOwn_shiftI]
  | mu t ih => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, ih]
  | tex κ t ih => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, ih]
  | iall t ih => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, ih]
  | iex t ih => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, ih]
  | refine t ψ ih => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn, ih]
  | _ => intro c ke; simp only [Ty.shiftI, Ty.sharedOKIn]

/-! ### Many index shifts at once -/

theorem zero_shiftIN (ke : KEnv) (t : Ty) : ∀ (d : Nat) (env : IEnv),
    zeroableIn env ke (shiftIN d t) = zeroableIn (env.drop d) ke t
  | 0, env => rfl
  | d + 1, env => by
      simp only [shiftIN, (zero_shiftI _ 0 env (env.drop 1) ke (EnvSh.drop env)).1,
        zero_shiftIN ke t d, List.drop_drop]
      congr 2; omega

theorem sens_shiftIN (ke : KEnv) (t : Ty) : ∀ d : Nat, Ty.sensitiveIn ke (shiftIN d t) = Ty.sensitiveIn ke t
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, sens_shiftI, sens_shiftIN ke t d]
theorem coupled_shiftIN (ke : KEnv) (t : Ty) : ∀ d : Nat, Ty.coupledOKIn ke (shiftIN d t) = Ty.coupledOKIn ke t
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, coupled_shiftI, coupled_shiftIN ke t d]
theorem noOwn_shiftIN (ke : KEnv) (t : Ty) : ∀ d : Nat, Ty.noOwnIn ke (shiftIN d t) = Ty.noOwnIn ke t
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, noOwn_shiftI, noOwn_shiftIN ke t d]
theorem affine_shiftIN (ke : KEnv) (t : Ty) : ∀ d : Nat, Ty.affineIn ke (shiftIN d t) = Ty.affineIn ke t
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, affine_shiftI, affine_shiftIN ke t d]
theorem shared_shiftIN (ke : KEnv) (t : Ty) : ∀ d : Nat, Ty.sharedOKIn ke (shiftIN d t) = Ty.sharedOKIn ke t
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, shared_shiftI, shared_shiftIN ke t d]

/-! ## §C. Knowing more index values keeps `Zeroable` -/

def EnvLe (env env' : IEnv) : Prop := ∀ (k v : Nat), env[k]?.join = some v → env'[k]?.join = some v

theorem EnvLe.nil (env' : IEnv) : EnvLe [] env' := by intro k v h; simp at h

theorem EnvLe.cons {env env' : IEnv} (h : EnvLe env env') (x : Option Nat) : EnvLe (x :: env) (x :: env') := by
  intro k v hk
  cases k with
  | zero => simpa using hk
  | succ k => simpa using h k v (by simpa using hk)

theorem evalIn_mono {env env' : IEnv} (h : EnvLe env env') :
    ∀ (i : Idx) (v : Nat), i.evalIn env = some v → i.evalIn env' = some v
  | .lit _, v, hv => hv
  | .var k, v, hv => h k v hv
  | .add i j, v, hv => by
      simp only [Idx.evalIn] at hv ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at hv
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at hv
          | some b => rw [evalIn_mono h i a hi, evalIn_mono h j b hj]; simpa [hi, hj] using hv
  | .sub i j, v, hv => by
      simp only [Idx.evalIn] at hv ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at hv
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at hv
          | some b => rw [evalIn_mono h i a hi, evalIn_mono h j b hj]; simpa [hi, hj] using hv
  | .smul n i, v, hv => by
      simp only [Idx.evalIn] at hv ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at hv
      | some a => rw [evalIn_mono h i a hi]; simpa [hi] using hv

theorem zeroHolds_mono {env env' : IEnv} (h : EnvLe env env') :
    ∀ ψ : Pred, ψ.zeroHolds env = true → ψ.zeroHolds env' = true
  | .tt, _ => rfl
  | .le i j, hv => by
      simp only [Pred.zeroHolds] at hv ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at hv
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at hv
          | some b => rw [evalIn_mono h i a hi, evalIn_mono h j b hj]; simpa [hi, hj] using hv
  | .eq i j, hv => by
      simp only [Pred.zeroHolds] at hv ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at hv
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at hv
          | some b => rw [evalIn_mono h i a hi, evalIn_mono h j b hj]; simpa [hi, hj] using hv
  | .and p q, hv => by
      simp only [Pred.zeroHolds, Bool.and_eq_true] at hv ⊢
      exact ⟨zeroHolds_mono h p hv.1, zeroHolds_mono h q hv.2⟩
  | .ini i, hv => by
      simp only [Pred.zeroHolds, beq_iff_eq] at hv ⊢
      exact evalIn_mono h i 0 hv

theorem zero_mono : ∀ (t : Ty) (env env' : IEnv) (ke : KEnv), EnvLe env env' →
    (zeroableIn env ke t = true → zeroableIn env' ke t = true) ∧
    ∀ sel : Ty → Bool,
      (zeroArmP sel env ke t = some true → zeroArmP sel env' ke t = some true) ∧
      (zeroArmP sel env ke t = none → zeroArmP sel env' ke t = none) := by
  have leaf : ∀ (t : Ty) (env env' : IEnv) (ke : KEnv) (sel : Ty → Bool),
      (zeroableIn env ke t = true → zeroableIn env' ke t = true) →
      zeroArmP sel env ke t = (if sel t then some (zeroableIn env ke t) else none) →
      zeroArmP sel env' ke t = (if sel t then some (zeroableIn env' ke t) else none) →
      (zeroArmP sel env ke t = some true → zeroArmP sel env' ke t = some true) ∧
      (zeroArmP sel env ke t = none → zeroArmP sel env' ke t = none) := by
    intro t env env' ke sel z e1 e2
    rw [e1, e2]
    cases sel t
    · exact ⟨fun hz => by simp at hz, fun _ => rfl⟩
    · refine ⟨fun hz => ?_, fun hz => by simp at hz⟩
      simp at hz ⊢; exact z hz
  intro t
  induction t with
  | intS i =>
      intro env env' ke h
      have z : zeroableIn env ke (.intS i) = true → zeroableIn env' ke (.intS i) = true := by
        simp only [zeroableIn, beq_iff_eq]; exact evalIn_mono h i 0
      exact ⟨z, fun sel => leaf _ env env' ke sel z (by simp only [zeroArmP] <;> rfl) (by simp only [zeroArmP] <;> rfl)⟩
  | prod a b iha ihb =>
      intro env env' ke h
      have z : zeroableIn env ke (.prod a b) = true → zeroableIn env' ke (.prod a b) = true := by
        simp only [zeroableIn, Bool.and_eq_true]
        exact fun hz => ⟨(iha env env' ke h).1 hz.1, (ihb env env' ke h).1 hz.2⟩
      exact ⟨z, fun sel => leaf _ env env' ke sel z (by simp only [zeroArmP] <;> rfl) (by simp only [zeroArmP] <;> rfl)⟩
  | sum a b iha ihb =>
      intro env env' ke h
      have arm : ∀ sel : Ty → Bool, (zeroArmP sel env ke a <|> zeroArmP sel env ke b) = some true →
          (zeroArmP sel env' ke a <|> zeroArmP sel env' ke b) = some true := by
        intro sel hz
        have za := (iha env env' ke h).2 sel
        have zb := (ihb env env' ke h).2 sel
        cases ha : zeroArmP sel env ke a with
        | none => rw [za.2 ha]; simp [ha] at hz ⊢; exact zb.1 hz
        | some x =>
            have hx : x = true := by simpa [ha] using hz
            subst hx; rw [za.1 ha]; simp
      refine ⟨?_, fun sel => ⟨?_, ?_⟩⟩
      · simp only [zeroableIn]
        split
        · simp only [beq_iff_eq]; exact arm _
        · simp only [beq_iff_eq]; exact arm _
        · exact id
      · simp only [zeroArmP]; exact arm sel
      · simp only [zeroArmP]; intro hz
        have za := (iha env env' ke h).2 sel
        have zb := (ihb env env' ke h).2 sel
        cases ha : zeroArmP sel env ke a with
        | none => rw [za.2 ha]; simp [ha] at hz ⊢; exact zb.2 hz
        | some x => simp [ha] at hz
  | array i t ih =>
      intro env env' ke h
      have z : zeroableIn env ke (.array i t) = true → zeroableIn env' ke (.array i t) = true := by
        simp only [zeroableIn]; exact (ih env env' ke h).1
      exact ⟨z, fun sel => leaf _ env env' ke sel z (by simp only [zeroArmP] <;> rfl) (by simp only [zeroArmP] <;> rfl)⟩
  | loc μ t ih =>
      intro env env' ke h
      have z : zeroableIn env ke (.loc μ t) = true → zeroableIn env' ke (.loc μ t) = true := by
        cases t with
        | array i u => simp only [zeroableIn, beq_iff_eq]; exact evalIn_mono h i 0
        | _ => simp only [zeroableIn]; exact id
      exact ⟨z, fun sel => leaf _ env env' ke sel z (by simp only [zeroArmP] <;> rfl) (by simp only [zeroArmP] <;> rfl)⟩
  | mu t ih =>
      intro env env' ke h
      have hi := ih env env' (none :: ke) h
      exact ⟨by simp only [zeroableIn]; exact hi.1, fun sel => by simp only [zeroArmP]; exact hi.2 sel⟩
  | iall t ih =>
      intro env env' ke h
      have hi := ih _ _ ke (h.cons none)
      exact ⟨by simp only [zeroableIn]; exact hi.1, fun sel => by simp only [zeroArmP]; exact hi.2 sel⟩
  | iex t ih =>
      intro env env' ke h
      have hi := ih _ _ ke (h.cons (some 0))
      exact ⟨by simp only [zeroableIn]; exact hi.1, fun sel => by simp only [zeroArmP]; exact hi.2 sel⟩
  | refine t ψ ih =>
      intro env env' ke h
      have z : zeroableIn env ke (.refine t ψ) = true → zeroableIn env' ke (.refine t ψ) = true := by
        simp only [zeroableIn, Bool.and_eq_true]
        exact fun hz => ⟨(ih env env' ke h).1 hz.1, zeroHolds_mono h ψ hz.2⟩
      refine ⟨z, fun sel => ?_⟩
      have hi := (ih env env' ke h).2 sel
      simp only [zeroArmP]
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · cases hx : zeroArmP sel env ke t with
        | none => simp [hx] at hz
        | some x =>
            simp only [hx, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hz
            rw [hi.1 (by rw [hx, hz.1])]
            simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true]
            exact ⟨trivial, zeroHolds_mono h ψ hz.2⟩
      · cases hx : zeroArmP sel env ke t with
        | none => rw [hi.2 hx]; rfl
        | some x => simp [hx] at hz
  | tex κ t ih =>
      intro env env' ke h
      have hi := (ih env env' (none :: ke) h)
      refine ⟨by simp only [zeroableIn]; exact id, fun sel => ?_⟩
      simp only [zeroArmP]
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · cases hx : zeroArmP sel env (none :: ke) t <;> simp [hx] at hz
      · cases hx : zeroArmP sel env (none :: ke) t with
        | none => rw [(hi.2 sel).2 hx]; rfl
        | some x => simp [hx] at hz
  | void => intro env env' ke h; exact ⟨by simp [zeroableIn], fun sel => ⟨by simp [zeroArmP], by simp [zeroArmP]⟩⟩
  | _ =>
      intro env env' ke h
      exact ⟨fun hz => by simpa only [zeroableIn] using hz, fun sel => leaf _ env env' ke sel
        (fun hz => by simpa only [zeroableIn] using hz) (by simp only [zeroArmP] <;> rfl) (by simp only [zeroArmP] <;> rfl)⟩

/-! ## §D. Substitution keeps every defined width and arm summary -/

theorem leaf_inv (w : Option Idx) : (Arms.leaf w).wide = 0 → (Arms.leaf w).maxW.isSome := by
  unfold Arms.leaf; split <;> simp_all

/-- In any `info`, an arm summary with no wide arm knows its largest width. -/
theorem arms_inv : ∀ (t : Ty) (ρ : Ctx), (info ρ t).arms.wide = 0 → (info ρ t).arms.maxW.isSome := by
  intro t
  induction t with
  | sum a b iha ihb =>
      intro ρ h
      have e : (info ρ (.sum a b)).arms = (info ρ a).arms.combine (info ρ b).arms := by
        simp only [info]; split <;> (try split) <;> rfl
      rw [e] at h ⊢
      simp only [Arms.combine] at h ⊢
      have ha := iha ρ (by omega); have hb := ihb ρ (by omega)
      cases h1 : (info ρ a).arms.maxW <;> cases h2 : (info ρ b).arms.maxW <;> simp_all
  | mu t ih => intro ρ h; exact ih _ h
  | tex κ t ih => intro ρ h; exact ih _ h
  | iall t ih => intro ρ h; exact ih _ h
  | iex t ih => intro ρ h; exact ih _ h
  | refine t ψ ih => intro ρ h; exact ih _ h
  | void => intro ρ h; rfl
  | ptr μ t _ => intro ρ h; rfl
  | ptrOpt μ t _ => intro ρ h; rfl
  | loc μ t _ => intro ρ h; rfl
  | _ => intro ρ h; exact leaf_inv _ h

theorem info_subst (σs : List Ty) : ∀ (t : Ty) (c d : Nat),
    ((info Ty.top t).width.isSome → (info Ty.top (substTs σs c d t)).width = (info Ty.top t).width) ∧
    ((info Ty.top t).arms.maxW.isSome → (info Ty.top (substTs σs c d t)).arms = (info Ty.top t).arms) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro c d
      have ha := iha c d; have hb := ihb c d
      simp only [substTs, info, Info.leaf]
      cases hwa : (info Ty.top a).width with
      | none => simp [Arms.leaf]
      | some wa =>
          cases hwb : (info Ty.top b).width with
          | none => simp [Arms.leaf]
          | some wb =>
              rw [ha.1 (by simp [hwa]), hb.1 (by simp [hwb]), hwa, hwb]
              exact ⟨fun _ => rfl, fun _ => rfl⟩
  | sum a b iha ihb =>
      intro c d
      have ha := iha c d; have hb := ihb c d
      cases hma : (info Ty.top a).arms.maxW with
      | none => simp [substTs, info, Arms.combine, hma]
      | some x =>
          cases hmb : (info Ty.top b).arms.maxW with
          | none => simp [substTs, info, Arms.combine, hma, hmb]
          | some y =>
              have ea := ha.2 (by simp [hma]); have eb := hb.2 (by simp [hmb])
              simp only [substTs, info, ea, eb]
              first | exact ⟨fun _ => rfl, fun _ => rfl⟩ | simp
  | mu t ih => intro c d; simp only [substTs, info, top_cons]; exact ih (c + 1) d
  | tex κ t ih => intro c d; simp only [substTs, info, top_cons]; exact ih (c + 1) d
  | iall t ih =>
      intro c d
      have h := ih c (d + 1)
      simp only [substTs, info, top_shiftI]
      cases hw : (info Ty.top t).width with
      | none =>
          refine ⟨by simp [lowerW], fun hm => ?_⟩
          exact h.2 hm
      | some w => rw [h.1 (by simp [hw]), hw]; exact ⟨fun _ => rfl, fun hm => h.2 hm⟩
  | iex t ih =>
      intro c d
      have h := ih c (d + 1)
      simp only [substTs, info, top_shiftI]
      cases hw : (info Ty.top t).width with
      | none =>
          refine ⟨by simp [lowerW], fun hm => ?_⟩
          exact h.2 hm
      | some w => rw [h.1 (by simp [hw]), hw]; exact ⟨fun _ => rfl, fun hm => h.2 hm⟩
  | refine t ψ ih => intro c d; simp only [substTs, info]; exact ih c d
  | tvar k => intro c d; simp [info, Info.leaf, Arms.leaf, Ty.top]
  | code a b _ _ => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | array i t _ => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | ptr μ t _ => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | ptrOpt μ t _ => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | loc μ t _ => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | _ => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem fits_subst (σs : List Ty) (t : Ty) (c d : Nat) (h : t.fitsGranule = true) :
    (substTs σs c d t).fitsGranule = true := by
  unfold Ty.fitsGranule Ty.width at *
  cases hw : (info Ty.top t).width with
  | none => simp [hw] at h
  | some w => rw [(info_subst σs t c d).1 (by simp [hw]), hw]; rw [hw] at h; exact h

/-! ## §E. The row-18 lemma

The callee is checked under `kd` (its type parameters' kinds, variable `k`
having kind `kd[k]`); the caller instantiates variable `k` at `σs[k]`, written
in the caller's kind environment `keC`, and `admitsIn` has checked each
`σs[k]` against `kd[k]`.  Under `ke₀` further binders (the `μ`s and `∃α`s
crossed so far, the same in both), and any number of index binders `d`. -/

/-- What `admitsIn` checks of one type argument, as far as these predicates go. -/
def AdmOK (keC : KEnv) (κ : Kind) (σ : Ty) : Prop :=
  Ty.sharedOKIn keC σ = true ∧
  (κ.zero = true → zeroableIn [] keC σ = true) ∧
  (κ.insens = true → Ty.sensitiveIn keC σ = false) ∧
  (κ.share = true → Ty.coupledOKIn keC σ = true) ∧
  (κ.noOwn = true → Ty.noOwnIn keC σ = true) ∧
  (κ.copy = true → Ty.affineIn keC σ = false) ∧
  (κ.noWord = true → Ty.wordFreeIn keC σ = true)

/-- Every type argument has what its parameter's kind asserts. -/
def Adm (keC : KEnv) (kd : List Kind) (σs : List Ty) : Prop :=
  kd.length = σs.length ∧ ∀ (k : Nat) (κ : Kind) (σ : Ty), kd[k]? = some κ → σs[k]? = some σ → AdmOK keC κ σ

section
variable {keC : KEnv} {kd : List Kind} {σs : List Ty}

theorem adm_some (h : Adm keC kd σs) {i : Nat} {σ : Ty} (hs : σs[i]? = some σ) :
    ∃ κ, kd[i]? = some κ ∧ AdmOK keC κ σ := by
  have hi : i < σs.length := by
    rcases List.getElem?_eq_some_iff.mp hs with ⟨hi, _⟩; exact hi
  have hk : i < kd.length := by rw [h.1]; exact hi
  exact ⟨kd[i], List.getElem?_eq_getElem hk, h.2 i _ σ (List.getElem?_eq_getElem hk) hs⟩

theorem adm_none (h : Adm keC kd σs) {i : Nat} (hs : σs[i]? = none) : kd[i]? = none := by
  apply List.getElem?_eq_none_iff.mpr
  rw [h.1]; exact List.getElem?_eq_none_iff.mp hs

end

theorem ask_low {ke₀ X Y : KEnv} {j : Nat} (hj : j < ke₀.length) (r : Bool) (f : Kind → Bool) :
    (ke₀ ++ X).ask j r f = (ke₀ ++ Y).ask j r f := by
  unfold KEnv.ask
  rw [List.getElem?_append_left hj, List.getElem?_append_left hj]

theorem ask_gen {ke₀ : KEnv} {kd : List Kind} {j : Nat} (hj : ¬ j < ke₀.length) (r : Bool) (f : Kind → Bool) :
    (ke₀ ++ kd.map some).ask j r f = match kd[j - ke₀.length]? with | some κ => f κ | none => false := by
  unfold KEnv.ask
  rw [List.getElem?_append_right (by omega), List.getElem?_map]
  cases kd[j - ke₀.length]? <;> rfl

theorem noOwn_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) :
    ∀ (t : Ty) (ke₀ : KEnv) (d : Nat), Ty.noOwnIn (ke₀ ++ kd.map some) t = true →
      Ty.noOwnIn (ke₀ ++ keC) (substTs σs ke₀.length d t) = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.noOwnIn, Bool.and_eq_true] at hg
      simp only [substTs, Ty.noOwnIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.and_self]
  | sum a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.noOwnIn, Bool.and_eq_true] at hg
      simp only [substTs, Ty.noOwnIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.and_self]
  | array i t ih => intro ke₀ d hg; simp only [Ty.noOwnIn] at hg; simp only [substTs, Ty.noOwnIn, ih ke₀ d hg]
  | ptr μ t ih => intro ke₀ d hg; cases μ <;> simp only [substTs, Ty.noOwnIn] at hg ⊢ <;> first | cases hg | exact ih ke₀ d hg | rfl
  | ptrOpt μ t ih => intro ke₀ d hg; cases μ <;> simp only [substTs, Ty.noOwnIn] at hg ⊢ <;> first | cases hg | exact ih ke₀ d hg | rfl
  | loc μ t ih => intro ke₀ d hg; cases μ <;> simp only [substTs, Ty.noOwnIn] at hg ⊢ <;> first | cases hg | exact ih ke₀ d hg | rfl
  | mu t ih =>
      intro ke₀ d hg; simp only [Ty.noOwnIn] at hg
      have := ih (none :: ke₀) d hg
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.noOwnIn, this]
  | tex κ t ih =>
      intro ke₀ d hg; simp only [Ty.noOwnIn, Bool.and_eq_true] at hg
      have := ih (some κ :: ke₀) d hg.2
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.noOwnIn, this, hg.1, Bool.and_self]
  | iall t ih => intro ke₀ d hg; simp only [Ty.noOwnIn] at hg; simp only [substTs, Ty.noOwnIn, ih ke₀ (d + 1) hg]
  | iex t ih => intro ke₀ d hg; simp only [Ty.noOwnIn] at hg; simp only [substTs, Ty.noOwnIn, ih ke₀ (d + 1) hg]
  | refine t ψ ih => intro ke₀ d hg; simp only [Ty.noOwnIn] at hg; simp only [substTs, Ty.noOwnIn, ih ke₀ d hg]
  | tvar j =>
      intro ke₀ d hg
      simp only [substTs]
      by_cases hj : j < ke₀.length
      · rw [if_pos hj]; simp only [Ty.noOwnIn] at hg ⊢; rwa [ask_low hj] at hg
      · rw [if_neg hj]
        split
        next _ σ hs =>
          obtain ⟨κ, hk, ha⟩ := adm_some h hs
          simp only [Ty.noOwnIn, ask_gen hj, hk] at hg
          rw [noOwn_shiftIN, noOwn_shiftTN]; exact ha.2.2.2.2.1 hg
        next _ hn =>
          simp only [Ty.noOwnIn, ask_gen hj, adm_none h hn] at hg; cases hg
  | _ => intro ke₀ d hg; rfl

theorem affine_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) :
    ∀ (t : Ty) (ke₀ : KEnv) (d : Nat), Ty.affineIn (ke₀ ++ kd.map some) t = false →
      Ty.affineIn (ke₀ ++ keC) (substTs σs ke₀.length d t) = false := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.affineIn, Bool.or_eq_false_iff] at hg
      simp only [substTs, Ty.affineIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.or_self]
  | sum a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.affineIn, Bool.or_eq_false_iff] at hg
      simp only [substTs, Ty.affineIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.or_self]
  | array i t ih => intro ke₀ d hg; simp only [Ty.affineIn] at hg; simp only [substTs, Ty.affineIn, ih ke₀ d hg]
  | ptr μ t ih => intro ke₀ d hg; cases μ <;> simp only [Ty.affineIn] at hg <;> simp only [substTs, Ty.affineIn] <;> first | cases hg | rfl
  | ptrOpt μ t ih => intro ke₀ d hg; cases μ <;> simp only [Ty.affineIn] at hg <;> simp only [substTs, Ty.affineIn] <;> first | cases hg | rfl
  | loc μ t ih => intro ke₀ d hg; cases μ <;> simp only [Ty.affineIn] at hg <;> simp only [substTs, Ty.affineIn] <;> first | cases hg | rfl
  | mu t ih =>
      intro ke₀ d hg; simp only [Ty.affineIn] at hg
      have := ih (none :: ke₀) d hg
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.affineIn, this]
  | tex κ t ih =>
      intro ke₀ d hg; simp only [Ty.affineIn] at hg
      have := ih (some κ :: ke₀) d hg
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.affineIn, this]
  | iall t ih => intro ke₀ d hg; simp only [Ty.affineIn] at hg; simp only [substTs, Ty.affineIn, ih ke₀ (d + 1) hg]
  | iex t ih => intro ke₀ d hg; simp only [Ty.affineIn] at hg; simp only [substTs, Ty.affineIn, ih ke₀ (d + 1) hg]
  | refine t ψ ih => intro ke₀ d hg; simp only [Ty.affineIn] at hg; simp only [substTs, Ty.affineIn, ih ke₀ d hg]
  | tvar j =>
      intro ke₀ d hg
      simp only [substTs]
      by_cases hj : j < ke₀.length
      · rw [if_pos hj]; simp only [Ty.affineIn] at hg ⊢; rwa [ask_low hj] at hg
      · rw [if_neg hj]
        split
        next _ σ hs =>
          obtain ⟨κ, hk, ha⟩ := adm_some h hs
          simp only [Ty.affineIn, ask_gen hj, hk, Bool.not_eq_false'] at hg
          rw [affine_shiftIN, affine_shiftTN]; exact ha.2.2.2.2.2.1 hg
        next _ hn =>
          simp only [Ty.affineIn, ask_gen hj, adm_none h hn] at hg; cases hg
  | _ => intro ke₀ d hg; exact hg

theorem coupled_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) :
    ∀ (t : Ty) (ke₀ : KEnv) (d : Nat), Ty.coupledOKIn (ke₀ ++ kd.map some) t = true →
      Ty.coupledOKIn (ke₀ ++ keC) (substTs σs ke₀.length d t) = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.coupledOKIn, Bool.and_eq_true] at hg
      simp only [substTs, Ty.coupledOKIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.and_self]
  | sum a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.coupledOKIn, Bool.and_eq_true] at hg
      simp only [substTs, Ty.coupledOKIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.and_self]
  | array i t ih => intro ke₀ d hg; simp only [Ty.coupledOKIn] at hg; simp only [substTs, Ty.coupledOKIn, ih ke₀ d hg]
  | mu t ih =>
      intro ke₀ d hg; simp only [Ty.coupledOKIn] at hg
      have := ih (none :: ke₀) d hg
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.coupledOKIn, this]
  | tex κ t ih =>
      intro ke₀ d hg; simp only [Ty.coupledOKIn, Bool.and_eq_true, Bool.or_eq_true] at hg
      have := ih (some κ :: ke₀) d hg.1
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.coupledOKIn, this, Bool.true_and, Bool.or_eq_true,
        countT_subst σs t (ke₀.length + 1) d 0 (by omega)]
      rcases hg.2 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (fits_subst σs (.tex κ t) ke₀.length d h1)
  | iall t ih => intro ke₀ d hg; simp only [Ty.coupledOKIn] at hg; simp only [substTs, Ty.coupledOKIn, ih ke₀ (d + 1) hg]
  | iex t ih =>
      intro ke₀ d hg; simp only [Ty.coupledOKIn, Bool.and_eq_true, Bool.or_eq_true] at hg
      simp only [substTs, Ty.coupledOKIn, ih ke₀ (d + 1) hg.1, Bool.true_and, Bool.or_eq_true,
        countI_subst σs t ke₀.length (d + 1) 0 (by omega)]
      rcases hg.2 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (fits_subst σs (.iex t) ke₀.length d h1)
  | refine t ψ ih => intro ke₀ d hg; simp only [Ty.coupledOKIn] at hg; simp only [substTs, Ty.coupledOKIn, ih ke₀ d hg]
  | tvar j =>
      intro ke₀ d hg
      simp only [substTs]
      by_cases hj : j < ke₀.length
      · rw [if_pos hj]; simp only [Ty.coupledOKIn] at hg ⊢; rwa [ask_low hj] at hg
      · rw [if_neg hj]
        split
        next _ σ hs =>
          obtain ⟨κ, hk, ha⟩ := adm_some h hs
          simp only [Ty.coupledOKIn, ask_gen hj, hk] at hg
          rw [coupled_shiftIN, coupled_shiftTN]; exact ha.2.2.2.1 hg
        next _ hn =>
          simp only [Ty.coupledOKIn, ask_gen hj, adm_none h hn] at hg; cases hg
  | _ => intro ke₀ d hg; rfl

theorem shared_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) :
    ∀ (t : Ty) (ke₀ : KEnv) (d : Nat), Ty.sharedOKIn (ke₀ ++ kd.map some) t = true →
      Ty.sharedOKIn (ke₀ ++ keC) (substTs σs ke₀.length d t) = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.sharedOKIn, Bool.and_eq_true] at hg
      simp only [substTs, Ty.sharedOKIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.and_self]
  | sum a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.sharedOKIn, Bool.and_eq_true] at hg
      simp only [substTs, Ty.sharedOKIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.and_self]
  | code a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.sharedOKIn, Bool.and_eq_true] at hg
      simp only [substTs, Ty.sharedOKIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.and_self]
  | array i t ih => intro ke₀ d hg; simp only [Ty.sharedOKIn] at hg; simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
  | ptr μ t ih =>
      intro ke₀ d hg
      cases μ <;> simp only [Ty.sharedOKIn, Bool.and_eq_true] at hg
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg.2, coupled_subst h t ke₀ d hg.1.1,
          noOwn_subst h t ke₀ d hg.1.2, Bool.and_self]
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
  | ptrOpt μ t ih =>
      intro ke₀ d hg
      cases μ <;> simp only [Ty.sharedOKIn, Bool.and_eq_true] at hg
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg.2, coupled_subst h t ke₀ d hg.1.1,
          noOwn_subst h t ke₀ d hg.1.2, Bool.and_self]
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
  | loc μ t ih =>
      intro ke₀ d hg
      cases μ <;> simp only [Ty.sharedOKIn, Bool.and_eq_true] at hg
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg.2, coupled_subst h t ke₀ d hg.1.1,
          noOwn_subst h t ke₀ d hg.1.2, Bool.and_self]
      · simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
  | mu t ih =>
      intro ke₀ d hg; simp only [Ty.sharedOKIn] at hg
      have := ih (none :: ke₀) d hg
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.sharedOKIn, this]
  | tex κ t ih =>
      intro ke₀ d hg; simp only [Ty.sharedOKIn] at hg
      have := ih (some κ :: ke₀) d hg
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.sharedOKIn, this]
  | iall t ih => intro ke₀ d hg; simp only [Ty.sharedOKIn] at hg; simp only [substTs, Ty.sharedOKIn, ih ke₀ (d + 1) hg]
  | iex t ih => intro ke₀ d hg; simp only [Ty.sharedOKIn] at hg; simp only [substTs, Ty.sharedOKIn, ih ke₀ (d + 1) hg]
  | refine t ψ ih => intro ke₀ d hg; simp only [Ty.sharedOKIn] at hg; simp only [substTs, Ty.sharedOKIn, ih ke₀ d hg]
  | tvar j =>
      intro ke₀ d hg
      simp only [substTs]
      by_cases hj : j < ke₀.length
      · rw [if_pos hj]; rfl
      · rw [if_neg hj]
        split
        next _ σ hs =>
          obtain ⟨κ, hk, ha⟩ := adm_some h hs
          rw [shared_shiftIN, shared_shiftTN]; exact ha.1
        next _ hn => rfl
  | _ => intro ke₀ d hg; rfl

/-! ### Zeroability under instantiation -/

theorem tier_niche {A : Arms} (h : A.tier = .niche) : A.wide = 0 := by
  unfold Arms.tier at h
  split at h
  · rename_i hc; exact hc.1
  · split at h <;> cases h

theorem tier_wide {A : Arms} (h : A.tier = .wide) : A.maxW.isSome := by
  unfold Arms.tier at h
  split at h
  · cases h
  · split at h
    · rename_i hc; cases hm : A.maxW <;> simp_all
    · cases h

theorem arms_sum (ρ : Ctx) (x y : Ty) :
    (info ρ (.sum x y)).arms = (info ρ x).arms.combine (info ρ y).arms := by
  simp only [info]; split <;> (try split) <;> rfl

theorem ms_sum {ρ : Ctx} {x y : Ty} (h : (info ρ (.sum x y)).arms.maxW.isSome) :
    (info ρ x).arms.maxW.isSome ∧ (info ρ y).arms.maxW.isSome := by
  rw [arms_sum] at h; simp only [Arms.combine] at h
  cases hx : (info ρ x).arms.maxW <;> cases hy : (info ρ y).arms.maxW <;> simp_all

/-- `sel` picks the same arms after a substitution, where that keeps the arm
summary (`info_subst`). -/
def SelSub (σs : List Ty) (sel : Ty → Bool) : Prop :=
  ∀ (u : Ty) (c d : Nat), (info Ty.top u).arms.maxW.isSome → sel (substTs σs c d u) = sel u

theorem selSub_pf (σs : List Ty) : SelSub σs Ty.payloadFree := fun u c d hm => by
  simp only [Ty.payloadFree, (info_subst σs u c d).2 hm]

theorem selSub_tr (σs : List Ty) : SelSub σs (fun _ => true) := fun _ _ _ _ => rfl

/-- `zero_subst` over any kind environment `keS` whose `Zeroable` variables
have `Zeroable` arguments (T3c-5b: the runtime's `KindsZ`, with `keC = []`). -/
theorem zero_subst_gen {keS keC : KEnv} {σs : List Ty}
    (hZ : ∀ k, keS.ask k false (·.zero) = true → ∃ σ, σs[k]? = some σ ∧ zeroableIn [] keC σ = true) :
    ∀ (t : Ty) (ke₀ : KEnv) (d : Nat) (env : IEnv),
    (zeroableIn env (ke₀ ++ keS) t = true →
      zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d t) = true) ∧
    ∀ sel : Ty → Bool, SelSub σs sel → (info Ty.top t).arms.maxW.isSome →
      (zeroArmP sel env (ke₀ ++ keS) t = some true →
        zeroArmP sel env (ke₀ ++ keC) (substTs σs ke₀.length d t) = some true) ∧
      (zeroArmP sel env (ke₀ ++ keS) t = none →
        zeroArmP sel env (ke₀ ++ keC) (substTs σs ke₀.length d t) = none) := by
  have leaf : ∀ (t t' : Ty) (env : IEnv) (K K' : KEnv) (sel : Ty → Bool), sel t' = sel t →
      (zeroableIn env K t = true → zeroableIn env K' t' = true) →
      zeroArmP sel env K t = (if sel t then some (zeroableIn env K t) else none) →
      zeroArmP sel env K' t' = (if sel t' then some (zeroableIn env K' t') else none) →
      (zeroArmP sel env K t = some true → zeroArmP sel env K' t' = some true) ∧
      (zeroArmP sel env K t = none → zeroArmP sel env K' t' = none) := by
    intro t t' env K K' sel hs z e1 e2
    rw [e1, e2, hs]
    cases sel t
    · exact ⟨fun hz => by simp at hz, fun _ => rfl⟩
    · refine ⟨fun hz => ?_, fun hz => by simp at hz⟩
      simp at hz ⊢; exact z hz
  intro t
  induction t with
  | sum a b iha ihb =>
      intro ke₀ d env
      have ha := iha ke₀ d env; have hb := ihb ke₀ d env
      -- The arms of `a + b`, if a word, survive; so do the arms' zeroability.
      have arm2 : ∀ sel : Ty → Bool, SelSub σs sel →
          (info Ty.top a).arms.maxW.isSome → (info Ty.top b).arms.maxW.isSome →
          (zeroArmP sel env (ke₀ ++ keS) a <|> zeroArmP sel env (ke₀ ++ keS) b) = some true →
          (zeroArmP sel env (ke₀ ++ keC) (substTs σs ke₀.length d a) <|>
            zeroArmP sel env (ke₀ ++ keC) (substTs σs ke₀.length d b)) = some true := by
        intro sel hsel ma mb hz
        cases hza : zeroArmP sel env (ke₀ ++ keS) a with
        | none =>
            simp [hza] at hz
            simp [(ha.2 sel hsel ma).2 hza, (hb.2 sel hsel mb).1 hz]
        | some v =>
            cases v
            · simp [hza] at hz
            · simp [(ha.2 sel hsel ma).1 hza]
      refine ⟨fun hz => ?_, fun sel hsel hms => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · have parm := (info_subst σs (.sum a b) ke₀.length d).2
        simp only [substTs] at parm ⊢
        simp only [zeroableIn] at hz ⊢
        split at hz
        next hn =>
          have hms := arms_inv (.sum a b) Ty.top (tier_niche hn)
          have et : (Ty.sum (substTs σs ke₀.length d a) (substTs σs ke₀.length d b)).tier = .niche := by
            unfold Ty.tier; rw [parm hms]; exact hn
          have ⟨ma, mb⟩ := ms_sum hms
          simp only [et, beq_iff_eq] at hz ⊢
          exact arm2 _ (selSub_pf σs) ma mb hz
        next hw =>
          have hms := tier_wide hw
          have et : (Ty.sum (substTs σs ke₀.length d a) (substTs σs ke₀.length d b)).tier = .wide := by
            unfold Ty.tier; rw [parm hms]; exact hw
          have ⟨ma, mb⟩ := ms_sum hms
          simp only [et, beq_iff_eq] at hz ⊢
          exact arm2 _ (selSub_tr σs) ma mb hz
        next => cases hz
      · have ⟨ma, mb⟩ := ms_sum hms
        simp only [substTs, zeroArmP] at hz ⊢
        exact arm2 sel hsel ma mb hz
      · have ⟨ma, mb⟩ := ms_sum hms
        simp only [substTs, zeroArmP] at hz ⊢
        cases hza : zeroArmP sel env (ke₀ ++ keS) a with
        | none => simp [hza] at hz; simp [(ha.2 sel hsel ma).2 hza, (hb.2 sel hsel mb).2 hz]
        | some v => simp [hza] at hz
  | tvar j =>
      intro ke₀ d env
      have p1 : zeroableIn env (ke₀ ++ keS) (.tvar j) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.tvar j)) = true := by
        intro hz
        simp only [substTs]
        by_cases hj : j < ke₀.length
        · rw [if_pos hj]; simp only [zeroableIn] at hz ⊢; rwa [ask_low hj] at hz
        · rw [if_neg hj]
          have hask : (ke₀ ++ keS).ask j false (·.zero) = keS.ask (j - ke₀.length) false (·.zero) := by
            unfold KEnv.ask; rw [List.getElem?_append_right (by omega)]
          simp only [zeroableIn] at hz
          rw [hask] at hz
          obtain ⟨σ, hs, hzσ⟩ := hZ _ hz
          simp only [hs]
          rw [zero_shiftIN, zero_shiftTN]
          exact (zero_mono σ [] (env.drop d) keC (EnvLe.nil _)).1 hzσ
      refine ⟨p1, fun sel _ hms => ?_⟩
      simp [info, Info.leaf, Arms.leaf, Ty.top] at hms
  | void =>
      intro ke₀ d env
      exact ⟨fun hz => by simp [zeroableIn] at hz, fun sel _ _ =>
        ⟨fun hz => by simp [zeroArmP] at hz, fun _ => by simp [substTs, zeroArmP]⟩⟩
  | prod a b iha ihb =>
      intro ke₀ d env
      have p1 : zeroableIn env (ke₀ ++ keS) (.prod a b) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.prod a b)) = true := by
        intro hz; simp only [zeroableIn, Bool.and_eq_true] at hz
        simp only [substTs, zeroableIn, (iha ke₀ d env).1 hz.1, (ihb ke₀ d env).1 hz.2, Bool.and_self]
      exact ⟨p1, fun sel hsel hms => leaf _ _ env _ _ sel (hsel _ _ _ hms) p1
        (by simp only [zeroArmP] <;> rfl) (by simp only [substTs, zeroArmP] <;> rfl)⟩
  | array i t ih =>
      intro ke₀ d env
      have p1 : zeroableIn env (ke₀ ++ keS) (.array i t) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.array i t)) = true := by
        intro hz; simp only [zeroableIn] at hz
        simp only [substTs, zeroableIn, (ih ke₀ d env).1 hz]
      exact ⟨p1, fun sel hsel hms => leaf _ _ env _ _ sel (hsel _ _ _ hms) p1
        (by simp only [zeroArmP] <;> rfl) (by simp only [substTs, zeroArmP] <;> rfl)⟩
  | loc μ t _ =>
      intro ke₀ d env
      have p1 : zeroableIn env (ke₀ ++ keS) (.loc μ t) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.loc μ t)) = true := by
        intro hz
        cases t with
        | array i u => simp only [substTs, zeroableIn] at hz ⊢; exact hz
        | _ => simp [zeroableIn] at hz
      exact ⟨p1, fun sel hsel hms => leaf _ _ env _ _ sel (hsel _ _ _ hms) p1
        (by simp only [zeroArmP] <;> rfl) (by simp only [substTs, zeroArmP] <;> rfl)⟩
  | mu t ih =>
      intro ke₀ d env
      have hi := ih (none :: ke₀) d env
      simp only [List.cons_append, List.length_cons] at hi
      have p1 : zeroableIn env (ke₀ ++ keS) (.mu t) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.mu t)) = true := by
        intro hz; simp only [zeroableIn] at hz
        simp only [substTs, zeroableIn, hi.1 hz]
      refine ⟨p1, fun sel hsel hms => ?_⟩
      simp only [info, top_cons] at hms
      simp only [substTs, zeroArmP]
      exact hi.2 sel hsel hms
  | tex κ t ih =>
      intro ke₀ d env
      have hi := ih (none :: ke₀) d env
      simp only [List.cons_append, List.length_cons] at hi
      refine ⟨fun hz => by simp [zeroableIn] at hz, fun sel hsel hms => ?_⟩
      simp only [info, top_cons] at hms
      have hj := hi.2 sel hsel hms
      simp only [substTs, zeroArmP]
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · cases hx : zeroArmP sel env (none :: (ke₀ ++ keS)) t <;> simp [hx] at hz
      · cases hx : zeroArmP sel env (none :: (ke₀ ++ keS)) t with
        | none => rw [hj.2 hx]; rfl
        | some x => simp [hx] at hz
  | iall t ih =>
      intro ke₀ d env
      have hi := ih ke₀ (d + 1) (none :: env)
      have p1 : zeroableIn env (ke₀ ++ keS) (.iall t) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.iall t)) = true := by
        intro hz; simp only [zeroableIn] at hz
        simp only [substTs, zeroableIn, hi.1 hz]
      refine ⟨p1, fun sel hsel hms => ?_⟩
      simp only [info, top_shiftI] at hms
      simp only [substTs, zeroArmP]
      exact hi.2 sel hsel hms
  | iex t ih =>
      intro ke₀ d env
      have hi := ih ke₀ (d + 1) (some 0 :: env)
      have p1 : zeroableIn env (ke₀ ++ keS) (.iex t) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.iex t)) = true := by
        intro hz; simp only [zeroableIn] at hz
        simp only [substTs, zeroableIn, hi.1 hz]
      refine ⟨p1, fun sel hsel hms => ?_⟩
      simp only [info, top_shiftI] at hms
      simp only [substTs, zeroArmP]
      exact hi.2 sel hsel hms
  | refine t ψ ih =>
      intro ke₀ d env
      have hi := ih ke₀ d env
      have p1 : zeroableIn env (ke₀ ++ keS) (.refine t ψ) = true →
          zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d (.refine t ψ)) = true := by
        intro hz; simp only [zeroableIn, Bool.and_eq_true] at hz
        simp only [substTs, zeroableIn, hi.1 hz.1, hz.2, Bool.and_self]
      refine ⟨p1, fun sel hsel hms => ?_⟩
      simp only [info] at hms
      have hj := hi.2 sel hsel hms
      simp only [substTs, zeroArmP]
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · cases hx : zeroArmP sel env (ke₀ ++ keS) t with
        | none => simp [hx] at hz
        | some x =>
            simp only [hx, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hz
            rw [hj.1 (by rw [hx, hz.1])]
            simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true]
            exact ⟨trivial, hz.2⟩
      · cases hx : zeroArmP sel env (ke₀ ++ keS) t with
        | none => rw [hj.2 hx]; rfl
        | some x => simp [hx] at hz
  | _ =>
      intro ke₀ d env
      refine ⟨fun hz => ?_, fun sel hsel hms => leaf _ _ env _ _ sel (hsel _ _ _ hms) (fun hz => ?_)
        (by simp only [zeroArmP] <;> rfl) (by simp only [substTs, zeroArmP] <;> rfl)⟩ <;>
        simp only [substTs, zeroableIn, Option.some.injEq] at hz ⊢ <;>
        first | exact hz | cases hz | skip

theorem zero_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) :
    ∀ (t : Ty) (ke₀ : KEnv) (d : Nat) (env : IEnv),
    (zeroableIn env (ke₀ ++ kd.map some) t = true →
      zeroableIn env (ke₀ ++ keC) (substTs σs ke₀.length d t) = true) ∧
    ∀ sel : Ty → Bool, SelSub σs sel → (info Ty.top t).arms.maxW.isSome →
      (zeroArmP sel env (ke₀ ++ kd.map some) t = some true →
        zeroArmP sel env (ke₀ ++ keC) (substTs σs ke₀.length d t) = some true) ∧
      (zeroArmP sel env (ke₀ ++ kd.map some) t = none →
        zeroArmP sel env (ke₀ ++ keC) (substTs σs ke₀.length d t) = none) :=
  zero_subst_gen (fun k hk => by
    cases hs : σs[k]? with
    | none => simp [KEnv.ask, List.getElem?_map, adm_none h hs] at hk
    | some σ =>
        obtain ⟨κ, hk', ha⟩ := adm_some h hs
        simp [KEnv.ask, List.getElem?_map, hk'] at hk
        exact ⟨σ, rfl, ha.2.1 hk⟩)

/-- (T3c-5b) **Static ⇒ runtime zeroability**: what the checker found
`Zeroable` under the frame's kinds is `Zeroable` once closed at type arguments
that respect the kinds' `zero` (`TermSound.KindsZ`). -/
theorem zero_close : ZeroCloseP := by
  intro ke σs σ hK hz
  exact (zero_subst_gen (keS := ke) (keC := []) hK σ [] 0 []).1 hz

/-! ### View-sensitivity under instantiation -/

theorem zero_elemOf (env : IEnv) (ke : KEnv) (u : Ty) :
    zeroableIn env ke (elemOf u) = zeroableIn env ke u := by
  cases u <;> simp [elemOf, zeroableIn]

theorem pz_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs)
    (t : Ty) (ke₀ : KEnv) (d : Nat) :
    Ty.pointeeZeroableIn (ke₀ ++ kd.map some) t = true →
      Ty.pointeeZeroableIn (ke₀ ++ keC) (substTs σs ke₀.length d t) = true := by
  intro hz
  cases t with
  | ptr μ u =>
      rw [pz_ptr, zero_elemOf] at hz; simp only [substTs]; rw [pz_ptr, zero_elemOf]
      exact (zero_subst h u ke₀ d []).1 hz
  | ptrOpt μ u =>
      rw [pz_ptrOpt, zero_elemOf] at hz; simp only [substTs]; rw [pz_ptrOpt, zero_elemOf]
      exact (zero_subst h u ke₀ d []).1 hz
  | loc μ u =>
      rw [pz_loc, zero_elemOf] at hz; simp only [substTs]; rw [pz_loc, zero_elemOf]
      exact (zero_subst h u ke₀ d []).1 hz
  | _ => simp [Ty.pointeeZeroableIn] at hz

theorem sens_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) :
    ∀ (t : Ty) (ke₀ : KEnv) (d : Nat), Ty.sensitiveIn (ke₀ ++ kd.map some) t = false →
      Ty.sensitiveIn (ke₀ ++ keC) (substTs σs ke₀.length d t) = false := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.sensitiveIn, Bool.or_eq_false_iff] at hg
      simp only [substTs, Ty.sensitiveIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.or_self]
  | sum a b iha ihb =>
      intro ke₀ d hg; simp only [Ty.sensitiveIn, Bool.or_eq_false_iff] at hg
      simp only [substTs, Ty.sensitiveIn, iha ke₀ d hg.1, ihb ke₀ d hg.2, Bool.or_self]
  | array i t ih => intro ke₀ d hg; simp only [Ty.sensitiveIn] at hg; simp only [substTs, Ty.sensitiveIn, ih ke₀ d hg]
  | mu t ih =>
      intro ke₀ d hg; simp only [Ty.sensitiveIn] at hg
      have := ih (none :: ke₀) d hg
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.sensitiveIn, this]
  | tex κ t ih =>
      intro ke₀ d hg; simp only [Ty.sensitiveIn, Bool.or_eq_false_iff] at hg
      have := ih (some κ :: ke₀) d hg.2
      simp only [List.cons_append, List.length_cons] at this
      simp only [substTs, Ty.sensitiveIn, this, hg.1, Bool.or_self]
  | iall t ih => intro ke₀ d hg; simp only [Ty.sensitiveIn] at hg; simp only [substTs, Ty.sensitiveIn, ih ke₀ (d + 1) hg]
  | iex t ih => intro ke₀ d hg; simp only [Ty.sensitiveIn] at hg; simp only [substTs, Ty.sensitiveIn, ih ke₀ (d + 1) hg]
  | refine t ψ ih =>
      intro ke₀ d hg; simp only [Ty.sensitiveIn, Bool.or_eq_false_iff] at hg
      simp only [substTs, Ty.sensitiveIn, ih ke₀ d hg.1, Bool.false_or]
      cases hψ : ψ.hasIni
      · rfl
      · simp only [hψ, Bool.true_and, Bool.not_eq_false'] at hg ⊢
        exact pz_subst h t ke₀ d hg.2
  | tvar j =>
      intro ke₀ d hg
      simp only [substTs]
      by_cases hj : j < ke₀.length
      · rw [if_pos hj]; simp only [Ty.sensitiveIn] at hg ⊢; rwa [ask_low hj] at hg
      · rw [if_neg hj]
        split
        next _ σ hs =>
          obtain ⟨κ, hk, ha⟩ := adm_some h hs
          simp only [Ty.sensitiveIn, ask_gen hj, hk, Bool.not_eq_false'] at hg
          rw [sens_shiftIN, sens_shiftTN]; exact ha.2.2.1 hg
        next _ hn =>
          simp only [Ty.sensitiveIn, ask_gen hj, adm_none h hn] at hg; cases hg
  | cap m r => intro ke₀ d hg; cases m <;> simp_all [substTs, Ty.sensitiveIn]
  | _ => intro ke₀ d hg; rfl

/-! ## Row 18's lemma

The checker's rule (CoreTerm's `instantiate`): a prenex `∀(αᵢ : κᵢ)` body is
checked once, each `αᵢ` answering from `κᵢ`; a call at `σs` then takes the
instance `substTs σs 0 0 t`.  If every `σᵢ` has what `κᵢ` asserts (`Adm`,
which `admitsIn` implies), every one-way property the generic check concluded
holds of the instance. -/

/-- `wordFreeIn` reads only the head (through refinements), so an instance's
head is an argument's, which `noWord` — or `copy`, a word being affine — kept
word-free. -/
theorem wordFree_subst {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) :
    ∀ t : Ty, Ty.wordFreeIn (kd.map some) t = true → Ty.wordFreeIn keC (substTs σs 0 0 t) = true := by
  intro t
  induction t with
  | tvar j =>
      intro hg
      simp only [substTs, Nat.not_lt_zero, if_false, Nat.sub_zero]
      split
      next _ σ hs =>
        obtain ⟨κ, hk, ha⟩ := adm_some h hs
        simp only [Ty.wordFreeIn, KEnv.ask, List.getElem?_map, hk, Option.map_some] at hg
        show Ty.wordFreeIn keC σ = true
        cases hn : κ.noWord
        · simp only [hn, Bool.false_or] at hg
          exact wordFreeIn_of_affine σ (ha.2.2.2.2.2.1 hg)
        · exact ha.2.2.2.2.2.2 hn
      next _ hn =>
        simp only [Ty.wordFreeIn, KEnv.ask, List.getElem?_map, adm_none h hn, Option.map_none] at hg
        cases hg
  | refine t ψ ih => intro hg; simp only [Ty.wordFreeIn] at hg; simp only [substTs, Ty.wordFreeIn]; exact ih hg
  | word r P => intro hg; simp [Ty.wordFreeIn] at hg
  | word2 r P => intro hg; simp [Ty.wordFreeIn] at hg
  | epair r P => intro hg; simp [Ty.wordFreeIn] at hg
  | _ => intro _; simp [substTs, Ty.wordFreeIn]

theorem row18_kinds {keC : KEnv} {kd : List Kind} {σs : List Ty} (h : Adm keC kd σs) (t : Ty) :
    (Ty.sharedOKIn (kd.map some) t = true → Ty.sharedOKIn keC (substTs σs 0 0 t) = true) ∧
    (Ty.coupledOKIn (kd.map some) t = true → Ty.coupledOKIn keC (substTs σs 0 0 t) = true) ∧
    (Ty.noOwnIn (kd.map some) t = true → Ty.noOwnIn keC (substTs σs 0 0 t) = true) ∧
    (Ty.sensitiveIn (kd.map some) t = false → Ty.sensitiveIn keC (substTs σs 0 0 t) = false) ∧
    (Ty.affineIn (kd.map some) t = false → Ty.affineIn keC (substTs σs 0 0 t) = false) ∧
    (zeroableIn [] (kd.map some) t = true → zeroableIn [] keC (substTs σs 0 0 t) = true) ∧
    (Ty.wordFreeIn (kd.map some) t = true → Ty.wordFreeIn keC (substTs σs 0 0 t) = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, wordFree_subst h t⟩
  · simpa using shared_subst h t [] 0
  · simpa using coupled_subst h t [] 0
  · simpa using noOwn_subst h t [] 0
  · simpa using sens_subst h t [] 0
  · simpa using affine_subst h t [] 0
  · simpa using (zero_subst h t [] 0 []).1

/-- The checker's `admitsIn` gives what `Adm` asks of each argument. -/
theorem admitsIn_ok (cx : Cx) (κ : Kind) (σ : Ty) (h : admitsIn cx κ σ = true) : AdmOK cx.ke κ σ := by
  simp only [admitsIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hsh⟩, _⟩, hz⟩, hi⟩, hs⟩, ho⟩, hc⟩, hw⟩, _⟩ := h
  refine ⟨hsh, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · simpa [e] using hz
  · simpa [e] using hi
  · simpa [e] using hs
  · simpa [e] using ho
  · simpa [e] using hc
  · simpa [e] using hw

/-! ### CoreLang §8's `coversInstances`, for every kind, body and instance -/

theorem shiftT_shiftI : ∀ (t : Ty) (c c' : Nat), (t.shiftI c').shiftT c = (t.shiftT c).shiftI c' := by
  intro t
  induction t with
  | tvar k => intro c c'; simp only [Ty.shiftT, Ty.shiftI]; split <;> rfl
  | _ => intro c c'; simp [Ty.shiftT, Ty.shiftI, *]

theorem shiftT_shiftIN (X : Ty) (c : Nat) : ∀ d : Nat, (shiftIN d X).shiftT c = shiftIN d (X.shiftT c)
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, shiftT_shiftI, shiftT_shiftIN X c d]

theorem substT_eq (σ : Ty) : ∀ (t : Ty) (j d : Nat),
    Ty.substT j (shiftIN d (shiftTN j σ)) t = substTs [σ] j d t := by
  intro t
  induction t with
  | tvar k =>
      intro j d
      simp only [Ty.substT, substTs]
      rcases Nat.lt_trichotomy k j with hk | hk | hk
      · have e1 : (k == j) = false := beq_false_of_ne (by omega)
        simp [e1, hk, show ¬ k > j by omega]
      · subst hk; simp
      · have e1 : (k == j) = false := beq_false_of_ne (by omega)
        have e2 : [σ][k - j]? = none := List.getElem?_eq_none_iff.mpr (by simp; omega)
        simp [e1, hk, e2, show ¬ k < j by omega]
  | mu t ih =>
      intro j d; simp only [Ty.substT, substTs, shiftT_shiftIN]; rw [← ih (j + 1) d]; rfl
  | tex κ t ih =>
      intro j d; simp only [Ty.substT, substTs, shiftT_shiftIN]; rw [← ih (j + 1) d]; rfl
  | iall t ih => intro j d; simp only [Ty.substT, substTs]; rw [← ih j (d + 1)]; rfl
  | iex t ih => intro j d; simp only [Ty.substT, substTs]; rw [← ih j (d + 1)]; rfl
  | _ => intro j d; simp [Ty.substT, substTs, *]

theorem imp_bool {p q : Bool} (h : p = true → q = true) : (!p || q) = true := by
  cases p <;> simp_all
theorem imp_bool' {p q : Bool} (h : p = false → q = false) : (p || !q) = true := by
  cases p <;> cases q <;> simp_all

/-- A closed type the kind admits has what the kind asserts. -/
theorem admits_ok (κ : Kind) (σ : Ty) (hA : κ.admits σ = true) : AdmOK [] κ σ := by
  simp only [Kind.admits, Bool.and_eq_true, Ty.zeroable, Ty.sensitive, Ty.coupledOK, Ty.noOwn,
    Ty.affine, Ty.wordFree] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨hk, hz⟩, hi⟩, hs⟩, ho⟩, hc⟩, hw⟩, _⟩ := hA
  have hsh : Ty.sharedOKIn [] σ = true := by
    simp only [Ty.kind, Ty.kindIn] at hk
    split at hk
    · rename_i hw; simp only [Bool.and_eq_true] at hw; exact hw.2
    · cases hk
  exact ⟨hsh, fun e => by simpa [e] using hz, fun e => by simpa [e] using hi,
     fun e => by simpa [e] using hs, fun e => by simpa [e] using ho, fun e => by simpa [e] using hc,
     fun e => by simpa [e] using hw⟩

theorem adm_single {κ : Kind} {σ : Ty} (hA : κ.admits σ = true) : Adm [] [κ] [σ] := by
  refine ⟨rfl, fun k κ' σ' h1 h2 => ?_⟩
  cases k with
  | zero => simp at h1 h2; subst h1; subst h2; exact admits_ok κ σ hA
  | succ k => simp at h1

/-- **Row 18's lemma for closed instances**: CoreLang §8's sampled `#guard`,
for every kind, every body and every instance. -/
theorem coversInstances_true (κ : Kind) (b σ : Ty) : coversInstances κ b σ = true := by
  simp only [coversInstances]
  cases hA : κ.admits σ
  · rfl
  have hadm : Adm [] [κ] [σ] := adm_single hA
  have et : Ty.substT 0 σ b = substTs [σ] 0 0 b := substT_eq σ b 0 0
  have r := row18_kinds hadm b
  simp only [List.map_cons, List.map_nil] at r
  rw [et]
  simp only [Bool.not_true, Bool.false_or, Ty.sharedOK, Ty.coupledOK, Ty.noOwn, Ty.sensitive,
    Ty.affine, Bool.and_eq_true]
  exact ⟨⟨⟨⟨imp_bool r.1, imp_bool r.2.1⟩, imp_bool r.2.2.1⟩, imp_bool' r.2.2.2.1⟩, imp_bool' r.2.2.2.2.1⟩

/-- **Row 18 for `wordFree`, closed instances**: CoreLang §8's sampled
`#guard` for `noWord`, for every kind, body and instance. -/
theorem wordFree_covers (κ : Kind) (b σ : Ty) (hA : κ.admits σ = true)
    (hb : b.wordFreeIn [some κ] = true) : (Ty.substT 0 σ b).wordFree = true := by
  have r := wordFree_subst (adm_single hA) b
  simp only [List.map_cons, List.map_nil] at r
  have et : Ty.substT 0 σ b = substTs [σ] 0 0 b := substT_eq σ b 0 0
  rw [et]
  exact r hb

end KindSound

#print axioms KindSound.row18_kinds
#print axioms KindSound.admitsIn_ok
#print axioms KindSound.coversInstances_true
#print axioms KindSound.wordFree_covers

#print axioms KindSound.zero_close
