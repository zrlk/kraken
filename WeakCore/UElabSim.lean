/-
# UElabSim — T2: the UnElab machine is the core machine on the elaborated program

* `focus_elab` (the crux): if `focus` finds a nested operation `o` at counter `k`, the elaboration starts with
  `let tmp k = o` and continues with the elaboration of the focused-and-plugged term at `k + 1`; `focus_none_elab`:
  otherwise it is the head with elaborated continuations.  Together: `elab_layer : elabT k e = (layer k e).core`.
* `tstep_elab` (L0): `tstep g mem pairs (toCoreTh th) = (ustep U g mem pairs th).map toCore3` when
  `g.p = elabProg U`, from `elab_layer` and `UTstep.tstep_head_subst` (and the hand-written call/`ret`/`tail` cases).
-/
import WeakCore.USem

set_option linter.unusedSimpArgs false

namespace UnElab
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep
open WeakMem (Memory Ts VState AllocLabel Address Val Arch)

/-! ## §1 Focus and elaboration -/

theorem peelArg_none {v : At} : ∀ {a : UArg}, peelArg v a = none → a = .at (atomOf a)
  | .at _, _ => rfl
  | .op h args, hp => by
      unfold peelArg at hp
      split at hp <;> simp at hp

mutual
theorem peelArgs_none {v : At} {k : Nat} : ∀ {as : List UArg}, peelArgs v as = none →
    elabArgs k as = ([], as.map atomOf, k)
  | [], _ => rfl
  | a :: rest, hp => by
      unfold peelArgs at hp
      split at hp
      · simp at hp
      · rename_i ha
        have hr : peelArgs v rest = none := by
          cases h : peelArgs v rest with
          | none => rfl
          | some r => rw [h] at hp; simp at hp
        have := peelArg_none ha
        rw [this]
        simp only [elabArgs, elabArg, peelArgs_none hr, List.nil_append, List.map_cons, atomOf]

theorem peelArg_elab {k : Nat} : ∀ {a : UArg} {o : Op} {a' : UArg},
    peelArg (.var (tmp k)) a = some (o, a') →
    elabArg k a = ((tmp k, o) :: (elabArg (k + 1) a').1, (elabArg (k + 1) a').2)
  | .at _, _, _, hp => by simp [peelArg] at hp
  | .op hd args, o, a', hp => by
      unfold peelArg at hp
      split at hp
      · rename_i r hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have h2 := peelArgs_elab (k := k) (o := r.1) (as' := r.2) hr
        simp only [elabArg, h2, List.cons_append]
      · rename_i hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        simp only [elabArg, peelArgs_none hr, List.nil_append]

theorem peelArgs_elab {k : Nat} : ∀ {as : List UArg} {o : Op} {as' : List UArg},
    peelArgs (.var (tmp k)) as = some (o, as') →
    elabArgs k as = ((tmp k, o) :: (elabArgs (k + 1) as').1, (elabArgs (k + 1) as').2)
  | [], _, _, hp => by simp [peelArgs] at hp
  | a :: rest, o, as', hp => by
      unfold peelArgs at hp
      split at hp
      · rename_i r hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have h2 := peelArg_elab (k := k) (o := r.1) (a' := r.2) hr
        simp only [elabArgs, h2, List.cons_append]
      · rename_i ha
        cases hr : peelArgs (.var (tmp k)) rest with
        | none => rw [hr] at hp; simp at hp
        | some r =>
          rw [hr] at hp
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          have h2 := peelArgs_elab (k := k) (o := r.1) (as' := r.2) hr
          have := peelArg_none ha
          rw [this]
          simp only [elabArgs, elabArg, h2, List.nil_append]
end

theorem peelArgs_length {v : At} : ∀ {as : List UArg} {o : Op} {as' : List UArg},
    peelArgs v as = some (o, as') → as'.length = as.length
  | [], _, _, hp => by simp [peelArgs] at hp
  | a :: rest, o, as', hp => by
      unfold peelArgs at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        rfl
      · cases hr : peelArgs v rest with
        | none => rw [hr] at hp; simp at hp
        | some r =>
          rw [hr] at hp
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          simp [peelArgs_length (as' := r.2) (o := r.1) hr]

theorem getD_two {α : Type} {l : List α} (d : α) (h : l.length = 2) : [l.getD 0 d, l.getD 1 d] = l := by
  match l, h with
  | [a, b], _ => rfl

theorem getD_three {α : Type} {l : List α} (d : α) (h : l.length = 3) :
    [l.getD 0 d, l.getD 1 d, l.getD 2 d] = l := by
  match l, h with
  | [a, b, c], _ => rfl

theorem getD_five {α : Type} {l : List α} (d : α) (h : l.length = 5) :
    [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d, l.getD 4 d] = l := by
  match l, h with
  | [a, b, c, e, f], _ => rfl

theorem lets_cons (x : String) (o : Op) (l : List (String × Op)) (e : Expr) :
    lets ((x, o) :: l) e = .let_ x o (lets l e) := rfl

/-- **`focus_elab`** (the crux): if `focus` finds the nested operation `o`
(leftmost-innermost, operands atoms) at counter `k`, the elaboration is `let tmp k = o` followed by the
elaboration, at `k + 1`, of the term with `o` replaced by `tmp k` — exactly the binder and counter `ustep` uses. -/
theorem focus_elab {k : Nat} {e : UExpr} {o : Op} {e' : UExpr} (hf : focus (.var (tmp k)) e = some (o, e')) :
    elabT k e = .let_ (tmp k) o (elabT (k + 1) e') := by
  cases e with
  | let_ x h args e =>
    cases hp : peelArgs (.var (tmp k)) args with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArgs_elab hp, lets_cons]
  | ifeq a b yes no =>
    cases hp : peelArgs (.var (tmp k)) [a, b] with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArgs_elab hp, lets_cons, getD_two _ (peelArgs_length hp)]
  | cas acq rel w e v t ok fail =>
    cases hp : peelArgs (.var (tmp k)) [w, e, v] with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArgs_elab hp, lets_cons, getD_three _ (peelArgs_length hp)]
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
    cases hp : peelArgs (.var (tmp k)) [w, e0, e1, v0, v1] with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArgs_elab hp, lets_cons, getD_five _ (peelArgs_length hp)]
  | split a p q e =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | unpack a i x e =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | unpackT a al x e =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | region a rn pn tn e =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | openPub a rn pn cn e =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | case a x e₁ y e₂ =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | ifnull a e₁ x e₂ =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | parity a kn ev od =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | ret a =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]
  | tail f is a ts =>
    cases hp : peelArg (.var (tmp k)) a with
    | none => simp [focus, hp] at hf
    | some r =>
      simp only [focus, hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [elabT, peelArg_elab hp, lets_cons]

/-- An operand `peelArg` does not enter is an atom, elaborated to itself with no lets. -/
theorem elabArg_none {v : At} {k : Nat} {a : UArg} (hp : peelArg v a = none) :
    elabArg k a = ([], atomOf a, k) := by
  rw [peelArg_none hp]; rfl

/-- The rest of a pattern after one split elaborates to `destr`'s continuation. -/
theorem elabT_wrap (j : Nat) (b : String) (p : UPat) (E : UExpr) :
    elabT j (wrap b p E) = destr j (.var b) p (fun j => elabT j E) := by
  cases p with
  | bind _ => rfl
  | pair p1 p2 => rfl

theorem pickE_S0 (a : Expr) (l : List Expr) : pickE (a :: l) S0 = a := by
  simp [pickE, S0]

theorem pickE_S1 (a b : Expr) (l : List Expr) : pickE (a :: b :: l) S1 = b := by
  simp [pickE, S1]

/-- **`focus_none_elab`**: with every head operand an atom, the elaboration is the head form with its
continuations elaborated (`headLayer`). -/
theorem focus_none_elab {k : Nat} {e : UExpr} (hf : focus (.var (tmp k)) e = none) :
    elabT k e = (headLayer k e).core := by
  cases e with
  | let_ x h args e =>
    have hp : peelArgs (.var (tmp k)) args = none := by
      cases h : peelArgs (.var (tmp k)) args with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, peelArgs_none hp]
    rfl
  | split a p q e =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, destr, mapHead, List.map_cons, List.map_nil,
      pickE_S0, elabT_wrap]
    rfl
  | ifeq a b yes no =>
    have hp : peelArgs (.var (tmp k)) [a, b] = none := by
      cases h : peelArgs (.var (tmp k)) [a, b] with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, peelArgs_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | cas acq rel w e v t ok fail =>
    have hp : peelArgs (.var (tmp k)) [w, e, v] = none := by
      cases h : peelArgs (.var (tmp k)) [w, e, v] with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, peelArgs_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
    have hp : peelArgs (.var (tmp k)) [w, e0, e1, v0, v1] = none := by
      cases h : peelArgs (.var (tmp k)) [w, e0, e1, v0, v1] with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, peelArgs_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | unpack a i x e =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | unpackT a al x e =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | region a rn pn tn e =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | openPub a rn pn cn e =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | case a x e₁ y e₂ =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | ifnull a e₁ x e₂ =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | parity a kn ev od =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | ret a =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl
  | tail f is a ts =>
    have hp : peelArg (.var (tmp k)) a = none := by
      cases h : peelArg (.var (tmp k)) a with
      | none => rfl
      | some _ => simp [focus, h] at hf
    simp only [elabT, headLayer, ULayer.core, elabArg_none hp, mapHead, List.map_cons, List.map_nil,
      pickE_S0, pickE_S1]
    rfl

/-- **`elab_layer`**: the elaboration of a term is its layer's core term. -/
theorem elab_layer (k : Nat) (e : UExpr) : elabT k e = (layer k e).core := by
  unfold layer
  cases hf : focus (.var (tmp k)) e with
  | some r => exact focus_elab hf
  | none => exact focus_none_elab hf

/-! ## §2 L0: one thread step -/

theorem toCoreTh_backTh (th : UTTh) (t : TTh) (e : UExpr) (j : Nat) :
    toCoreTh (backTh th t e j) = { t with term := elabT j e, stack := th.stack.map toCoreFr } := by
  cases t; rfl

theorem find_elabProg (U : UProg) (f : String) :
    (elabProg U).find? (·.name == f) = (U.find? (·.name == f)).map elabDecl := by
  simp only [elabProg, List.find?_map]
  rfl

theorem getElem_elabProg (U : UProg) (i : Nat) : (elabProg U)[i]? = U[i]?.map elabDecl := by
  simp [elabProg]

theorem getD_map {α β : Type} (f : α → β) (d : α) : ∀ (l : List α) (n : Nat),
    (l.map f).getD n (f d) = f (l.getD n d)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => getD_map f d l n

theorem elabT_pickU (j : Nat) (conts : List UExpr) (t : Expr) :
    elabT j (pickU conts t) = pickE (conts.map (elabT j)) t := by
  have hd : elabT j (.ret (.at .unit)) = .ret .unit := rfl
  unfold pickU pickE
  split
  · split <;> rw [← hd, getD_map]
  · rw [← hd, getD_map]

theorem layer_head {k : Nat} {e : UExpr} {h : Expr} {conts : List UExpr} {j : Nat}
    (hl : layer k e = .head h conts j) : IsHead h := by
  unfold layer at hl
  split at hl
  · simp at hl
  · cases e <;> simp only [headLayer, ULayer.head.injEq, reduceCtorEq] at hl <;>
      (obtain ⟨rfl, -, -⟩ := hl; trivial)

theorem notCall_of {o : Op} (h1 : ∀ f is a ts, o = .call f is a ts → False)
    (h2 : ∀ f a, o = .callc f a → False) : NotCall o := by
  unfold NotCall
  split
  · exact h1 _ _ _ _ rfl
  · exact h2 _ _ rfl
  · trivial

theorem enter_elab {U : UProg} {g : G} (hg : g.p = elabProg U) (th : UTTh) (f : String) (ts : List Ty) (a : At) :
    enter g (toCoreTh th) f ts a = (uEnter U th f ts a).map toCoreTh := by
  simp only [enter, uEnter, hg, find_elabProg]
  cases U.find? (·.name == f) with
  | none => rfl
  | some d =>
    simp only [Option.map_some, Option.bind_some, toCoreTh]
    cases evalAt th.env a with
    | none => rfl
    | some r => rfl

theorem callFrame_elab {U : UProg} {g : G} (hg : g.p = elabProg U) (th : UTTh) (f : String) (ts : List Ty)
    (x : String) (e : UExpr) (j : Nat) :
    callFrame g (toCoreTh th) f ts x (elabT j e) = (uCallFrame U th f ts x e j).map toCoreFr := by
  simp only [callFrame, uCallFrame, hg, find_elabProg]
  cases U.find? (·.name == f) with
  | none => rfl
  | some d => rfl

/-- **L0** (T2): on the image of a UnElab thread, the core thread step is the UnElab step
followed by the image — the same memory, pairs and outcomes, outcome for outcome. -/
theorem tstep_elab {U : UProg} {g : G} (hg : g.p = elabProg U) (mem : Memory) (pairs : List Ts) (th : UTTh) :
    tstep g mem pairs (toCoreTh th) =
      (ustep U g mem pairs th).map (fun r => (r.1, r.2.1, toCoreTh r.2.2)) := by
  have hl := elab_layer th.ctr th.term
  unfold ustep
  split
  · -- call
    rename_i x f is a ts j e heq
    rw [heq] at hl
    have ht : (toCoreTh th).term = .let_ x (.call f is a ts) (elabT j e) := hl
    unfold tstep
    rw [ht]
    simp only
    rw [callFrame_elab hg]
    cases uCallFrame U th f ts x e j with
    | none => rfl
    | some fr =>
      simp only [Option.map_some, Option.bind_some]
      have := enter_elab hg { th with stack := fr :: th.stack } f ts a
      simp only [toCoreTh, List.map_cons, hl, ULayer.core] at this
      erw [this]
      cases uEnter U { th with stack := fr :: th.stack } f ts a <;> rfl
  · -- callc
    rename_i x f a j e heq
    rw [heq] at hl
    have ht : (toCoreTh th).term = .let_ x (.callc f a) (elabT j e) := hl
    unfold tstep
    rw [ht]
    simp only
    have henv : (toCoreTh th).env = th.env := rfl
    rw [henv]
    rcases hf : evalAt th.env f with _ | ⟨tf, _ | ⟨w, _ | ⟨w', ws⟩⟩⟩ <;> try rfl
    simp only
    cases hw : w.val <;> try rfl
    rename_i i
    simp only
    rw [hg, getElem_elabProg]
    cases hd : U[i]? with
    | none => rfl
    | some d =>
      simp only [Option.map_some]
      have hc := callFrame_elab hg th d.name [] x e j
      simp only [elabDecl] at hc ⊢
      erw [hc]
      cases uCallFrame U th d.name [] x e j with
      | none => rfl
      | some fr =>
        simp only [Option.map_some, Option.bind_some]
        have := enter_elab hg { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack } d.name [] a
        simp only [toCoreTh, List.map_cons, hl, ULayer.core] at this
        erw [this]
        cases uEnter U { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack } d.name [] a <;> rfl
  · -- other let: `tstep` on the sentinel
    rename_i x o j e h1 h2 heq
    rw [heq] at hl
    have hop : NotCall o := notCall_of h1 h2
    have ht : toCoreTh th =
        { coreView th (.let_ x o S0) with
          term := mapHead (fun _ => elabT j e) (.let_ x o S0), stack := th.stack.map toCoreFr } := by
      simp only [toCoreTh, coreView, mapHead, hl, ULayer.core]
    rw [ht, tstep_head_subst (fun _ => elabT j e) (.let_ x o S0) hop, List.map_map]
    congr 1
  · -- head: `tstep` on the sentinel head
    rename_i h conts j heq
    rw [heq] at hl
    have hh : IsHead h := layer_head heq
    have ht : toCoreTh th =
        { coreView th h with
          term := mapHead (pickE (conts.map (elabT j))) h, stack := th.stack.map toCoreFr } := by
      simp only [toCoreTh, coreView, hl, ULayer.core]
    rw [ht, tstep_head_subst _ h hh, List.map_map]
    congr 1
    all_goals (funext r; simp only [Function.comp, reTerm, toCoreTh_backTh, elabT_pickU])
  · -- ret (design (iii))
    rename_i a heq
    rw [heq] at hl
    have ht : (toCoreTh th).term = .ret a := hl
    unfold tstep
    rw [ht]
    simp only [toCoreTh]
    cases th.stack with
    | nil => rfl
    | cons f rest =>
      simp only [List.map_cons]
      cases evalAt th.env a with
      | none => rfl
      | some r => rfl
  · -- tail (design (iii))
    rename_i f is a ts heq
    rw [heq] at hl
    have ht : (toCoreTh th).term = .tail f is a ts := hl
    unfold tstep
    rw [ht]
    simp only
    rw [enter_elab hg]
    cases uEnter U th f ts a <;> rfl

/-! ## §3 Done, progress -/

theorem layer_ret {k : Nat} {e : UExpr} {a : At} (hl : layer k e = .ret a) : e = .ret (.at a) := by
  unfold layer at hl
  split at hl
  · simp at hl
  · rename_i hf
    cases e <;> simp only [headLayer, ULayer.ret.injEq, reduceCtorEq] at hl
    rename_i a'
    have hp : peelArg (.var (tmp k)) a' = none := by
      cases h : peelArg (.var (tmp k)) a' with
      | none => rfl
      | some _ => simp [focus, h] at hf
    rw [peelArg_none hp, hl]

theorem layer_head_shape {k : Nat} {e : UExpr} {h : Expr} {conts : List UExpr} {j : Nat}
    (hl : layer k e = .head h conts j) (f : Expr → Expr) :
    (∀ x o e', mapHead f h ≠ .let_ x o e') ∧ (∀ a, mapHead f h ≠ .ret a) := by
  unfold layer at hl
  split at hl
  · simp at hl
  · cases e <;> simp only [headLayer, ULayer.head.injEq, reduceCtorEq] at hl <;>
      (obtain ⟨rfl, -, -⟩ := hl; exact ⟨fun _ _ _ h => by simp [mapHead] at h, fun _ h => by simp [mapHead] at h⟩)

/-- The image of a thread is done iff the thread is. -/
theorem isDone_elab (th : UTTh) : isDone (toCoreTh th) = uIsDone th := by
  unfold isDone uIsDone
  simp only [toCoreTh]
  by_cases hr : ∃ a, th.term = .ret (.at a)
  · obtain ⟨a, ha⟩ := hr
    rw [ha]
    cases th.stack <;> rfl
  · have hne : ∀ a, elabT th.ctr th.term ≠ .ret a := by
      intro a h
      rw [elab_layer] at h
      cases hl : layer th.ctr th.term with
      | letOp x o j e => rw [hl] at h; simp [ULayer.core] at h
      | head hd conts j => rw [hl] at h; exact (layer_head_shape hl _).2 a h
      | ret a' => exact hr ⟨a', layer_ret hl⟩
      | tail f is a' ts => rw [hl] at h; simp [ULayer.core] at h
    split <;> split <;> simp_all

/-- **Thread-level progress transfers** (from L0): a UnElab thread is stuck iff its image is. -/
theorem ustep_nil_iff {U : UProg} {g : G} (hg : g.p = elabProg U) (mem : Memory) (pairs : List Ts) (th : UTTh) :
    ustep U g mem pairs th = [] ↔ tstep g mem pairs (toCoreTh th) = [] := by
  rw [tstep_elab hg]
  simp

/-! ## §4 Configurations -/

@[simp] theorem toCoreCfg_mem (c : UCfg) : (toCoreCfg c).mem = c.mem := rfl
@[simp] theorem toCoreCfg_pairs (c : UCfg) : (toCoreCfg c).pairs = c.pairs := rfl
@[simp] theorem toCoreCfg_trace (c : UCfg) : (toCoreCfg c).trace = c.trace := rfl
@[simp] theorem toCoreCfg_cap (c : UCfg) : (toCoreCfg c).cap = c.cap := rfl
@[simp] theorem toCoreCfg_size (c : UCfg) : (toCoreCfg c).ths.size = c.ths.size := by simp [toCoreCfg]
theorem toCoreCfg_get (c : UCfg) (i : Nat) : (toCoreCfg c).ths[i]? = c.ths[i]?.map toCoreTh := by
  simp [toCoreCfg]

theorem lt_of_get {α : Type} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) : i < a.size := by
  rcases Nat.lt_or_ge i a.size with hi | hi
  · exact hi
  · simp [Array.getElem?_eq_none hi] at h

theorem get_of_get {α : Type} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) :
    a[i]'(lt_of_get h) = x := by
  rw [Array.getElem?_eq_getElem (lt_of_get h)] at h
  exact Option.some.inj h

theorem threadSteps_elab (U : UProg) (k : Promises.Knobs) (arch : Arch) (c : UCfg) (i : Nat) :
    threadSteps (elabProg U) k arch (toCoreCfg c) i = (uThreadSteps U k arch c i).map toCoreCfg := by
  unfold threadSteps uThreadSteps
  rw [toCoreCfg_get]
  cases c.ths[i]? with
  | none => rfl
  | some th =>
    simp only [Option.map_some]
    rw [show gOf (elabProg U) k arch (toCoreCfg c) i = gU U k arch c i from rfl, tstep_elab rfl, List.map_map,
      List.map_map]
    congr 1
    funext r
    simp [toCoreCfg, Array.set!]

theorem promise_elab (c : UCfg) (i : Nat) (a : Address) (v : Val) (w : Ts) :
    promise (toCoreCfg c) i a v w = toCoreCfg (uPromise c i a v w) := by
  unfold promise uPromise
  rw [toCoreCfg_get]
  cases h : c.ths[i]? with
  | none => rfl
  | some th =>
    have hi := lt_of_get h
    simp [promise, toCoreCfg, Array.set!, toCoreTh, h, hi, get_of_get h]

theorem noPromises_elab (c : UCfg) (i : Nat) : noPromises (toCoreCfg c) i = uNoPromises c i := by
  unfold noPromises uNoPromises
  rw [toCoreCfg_get]
  cases c.ths[i]? <;> rfl

theorem extCfg_elab {c : UCfg} {i : Nat} {th : UTTh} (hth : c.ths[i]? = some th) (x : String) (n : ExtName)
    (e : UExpr) (j : Nat) (ws rs : List Word) :
    toCoreCfg (uExtCfg c i th x n e j ws rs) = extCfg (toCoreCfg c) i (toCoreTh th) x n (elabT j e) ws rs := by
  have hi := lt_of_get hth
  unfold uExtCfg extCfg curCfg
  cases n <;> (try cases htl : th.tidLbl) <;>
    simp [toCoreCfg, Array.set!, toCoreTh, backTh, hi, htl]

theorem spawnCfg_elab (c : UCfg) (i : Nat) (th : UTTh) (x : String) (e : UExpr) (j : Nat) (f : String)
    (ts : List Ty) (T : Ty) (ws : List Word) :
    toCoreCfg (uSpawnCfg c i th x e j f ts T ws) = spawnCfg (toCoreCfg c) i (toCoreTh th) x (elabT j e) f ts T ws := by
  have hp : toCoreTh (backTh th (spawnPar (toCoreCfg c) i (toCoreTh th) x S0) e j) =
      spawnPar (toCoreCfg c) i (toCoreTh th) x (elabT j e) := rfl
  have hk : toCoreTh (fromCore0 (spawnKid (toCoreCfg c) i (toCoreTh th) f ts T ws) (.tail f [] (.at (.var "a")) ts)) =
      spawnKid (toCoreCfg c) i (toCoreTh th) f ts T ws := rfl
  have h : toCoreCfg (uSpawnCfg c i th x e j f ts T ws) =
      spawnT (toCoreCfg c) i (toCoreTh (backTh th (spawnPar (toCoreCfg c) i (toCoreTh th) x S0) e j))
        (toCoreTh (fromCore0 (spawnKid (toCoreCfg c) i (toCoreTh th) f ts T ws)
          (.tail f [] (.at (.var "a")) ts))) := by
    simp [uSpawnCfg, spawnT, toCoreCfg, Array.set!]
  rw [h, hp, hk]
  rfl

/-- The core `let` an image term starts with comes from a `letOp` layer. -/
theorem layer_let_inv {k : Nat} {t : UExpr} {x : String} {o : Op} {e : Expr}
    (h : elabT k t = .let_ x o e) : ∃ j e', layer k t = .letOp x o j e' ∧ e = elabT j e' := by
  rw [elab_layer] at h
  cases hL : layer k t with
  | letOp x' o' j e' =>
    rw [hL] at h
    simp only [ULayer.core, Expr.let_.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨j, e', rfl, rfl⟩
  | head hd conts j => rw [hL] at h; exact absurd h ((layer_head_shape hL _).1 _ _ _)
  | ret a => rw [hL] at h; simp [ULayer.core] at h
  | tail f is a ts => rw [hL] at h; simp [ULayer.core] at h

theorem extSteps_elab (c : UCfg) (i : Nat) : extSteps (toCoreCfg c) i = (uExtSteps c i).map toCoreCfg := by
  unfold extSteps uExtSteps
  rw [toCoreCfg_get]
  cases hth : c.ths[i]? with
  | none => rfl
  | some th =>
    simp only [Option.map_some]
    have ht : (toCoreTh th).term = (layer th.ctr th.term).core := elab_layer th.ctr th.term
    rw [ht]
    cases hL : layer th.ctr th.term with
    | letOp x o j e =>
      cases o <;> try rfl
      rename_i n a
      simp only [ULayer.core]
      split
      · rfl
      · have henv : (toCoreTh th).env = th.env := rfl
        rw [henv]
        cases evalAt th.env a with
        | none => rfl
        | some r => simp [extCfg_elab hth]
    | head hd conts j =>
      simp only [ULayer.core]
      split
      · rename_i heq; exact absurd heq ((layer_head_shape hL _).1 _ _ _)
      · rfl
    | ret a => rfl
    | tail f is a ts => rfl

/-! ## §5 The lifts (T2, both directions) -/

section Lifts
variable {U : UProg} {k : Promises.Knobs} {arch : Arch}

theorem mem_threadSteps_elab {c : UCfg} {i : Nat} {d : Cfg} :
    d ∈ threadSteps (elabProg U) k arch (toCoreCfg c) i ↔ ∃ c', c' ∈ uThreadSteps U k arch c i ∧ d = toCoreCfg c' := by
  rw [threadSteps_elab, List.mem_map]
  exact ⟨fun ⟨c', h, e⟩ => ⟨c', h, e.symm⟩, fun ⟨c', h, e⟩ => ⟨c', h, e.symm⟩⟩

theorem mem_extSteps_elab {c : UCfg} {i : Nat} {d : Cfg} :
    d ∈ extSteps (toCoreCfg c) i ↔ ∃ c', c' ∈ uExtSteps c i ∧ d = toCoreCfg c' := by
  rw [extSteps_elab, List.mem_map]
  exact ⟨fun ⟨c', h, e⟩ => ⟨c', h, e.symm⟩, fun ⟨c', h, e⟩ => ⟨c', h, e.symm⟩⟩

/-- `USolo` → `Solo` on the images. -/
theorem USolo.toCore {i : Nat} {c c' : UCfg} (h : USolo U k arch i c c') :
    Solo (elabProg U) k arch i (toCoreCfg c) (toCoreCfg c') := by
  induction h with
  | refl c => exact Solo.refl _
  | thread h _ ih => exact Solo.thread (mem_threadSteps_elab.mpr ⟨_, h, rfl⟩) ih
  | prom a v w hw _ ih =>
    refine Solo.prom a v w (by simpa using hw) ?_
    rw [promise_elab]; exact ih
  | ext h _ ih => exact Solo.ext (mem_extSteps_elab.mpr ⟨_, h, rfl⟩) ih

/-- `Solo` from an image ← a `USolo` whose image it ends at. -/
theorem USolo.ofCore {i : Nat} {d d' : Cfg} (h : Solo (elabProg U) k arch i d d') :
    ∀ c, d = toCoreCfg c → ∃ c', USolo U k arch i c c' ∧ d' = toCoreCfg c' := by
  induction h with
  | refl d => intro c hc; exact ⟨c, USolo.refl _, hc⟩
  | thread h _ ih =>
    intro c hc
    subst hc
    obtain ⟨c1, h1, rfl⟩ := mem_threadSteps_elab.mp h
    obtain ⟨c2, h2, rfl⟩ := ih c1 rfl
    exact ⟨c2, USolo.thread h1 h2, rfl⟩
  | prom a v w hw _ ih =>
    intro c hc
    subst hc
    obtain ⟨c2, h2, rfl⟩ := ih (uPromise c _ a v w) (promise_elab c _ a v w)
    exact ⟨c2, USolo.prom a v w (by simpa using hw) h2, rfl⟩
  | ext h _ ih =>
    intro c hc
    subst hc
    obtain ⟨c1, h1, rfl⟩ := mem_extSteps_elab.mp h
    obtain ⟨c2, h2, rfl⟩ := ih c1 rfl
    exact ⟨c2, USolo.ext h1 h2, rfl⟩

/-- **Certification is the same** on a configuration and its image. -/
theorem uCertified_iff {c : UCfg} {i : Nat} :
    UCertified U k arch c i ↔ Certified (elabProg U) k arch (toCoreCfg c) i := by
  constructor
  · rintro ⟨c', hs, hn⟩
    exact ⟨_, hs.toCore, by rw [noPromises_elab]; exact hn⟩
  · rintro ⟨d, hs, hn⟩
    obtain ⟨c', hs', rfl⟩ := USolo.ofCore hs c rfl
    exact ⟨c', hs', by rw [← noPromises_elab]; exact hn⟩

theorem UStep.toCore {c c' : UCfg} (h : UStep U k arch c c') :
    Step (elabProg U) k arch (toCoreCfg c) (toCoreCfg c') := by
  cases h with
  | thread i h hc => exact Step.thread i (mem_threadSteps_elab.mpr ⟨_, h, rfl⟩) (uCertified_iff.mp hc)
  | prom i a v w hi hw hc =>
    rw [← promise_elab]
    exact Step.prom i a v w (by simpa using hi) (by simpa using hw) (by rw [promise_elab]; exact uCertified_iff.mp hc)

theorem UStep.ofCore {c : UCfg} {d : Cfg} (h : Step (elabProg U) k arch (toCoreCfg c) d) :
    ∃ c', UStep U k arch c c' ∧ d = toCoreCfg c' := by
  cases h with
  | thread i h hc =>
    obtain ⟨c', h', rfl⟩ := mem_threadSteps_elab.mp h
    exact ⟨c', UStep.thread i h' (uCertified_iff.mpr hc), rfl⟩
  | prom i a v w hi hw hc =>
    refine ⟨uPromise c i a v w, UStep.prom i a v w (by simpa using hi) (by simpa using hw) ?_, promise_elab c i a v w⟩
    rw [uCertified_iff, ← promise_elab]; exact hc

theorem USpawn.toCore {cap : Nat} {c c' : UCfg} (h : USpawn U k arch cap c c') :
    Spawn (elabProg U) k arch cap (toCoreCfg c) (toCoreCfg c') := by
  cases h with
  | mk i x f a T ts j e th rt ws hth hl hp hcap hev =>
    rw [spawnCfg_elab]
    refine Spawn.mk i x f a T ts (elabT j e) (toCoreTh th) rt ws (by rw [toCoreCfg_get, hth]; rfl) ?_ hp
      (by simpa using hcap) hev
    show elabT th.ctr th.term = _
    rw [elab_layer, hl]; rfl

theorem USpawn.ofCore {cap : Nat} {c : UCfg} {d : Cfg} (h : Spawn (elabProg U) k arch cap (toCoreCfg c) d) :
    ∃ c', USpawn U k arch cap c c' ∧ d = toCoreCfg c' := by
  cases h with
  | mk i x f a T ts e th' rt ws hth hterm hp hcap hev =>
    rw [toCoreCfg_get] at hth
    cases hc : c.ths[i]? with
    | none => rw [hc] at hth; simp at hth
    | some th =>
      rw [hc] at hth
      simp only [Option.map_some, Option.some.injEq] at hth
      subst hth
      obtain ⟨j, e', hl, rfl⟩ := layer_let_inv hterm
      exact ⟨_, USpawn.mk i x f a T ts j e' th rt ws hc hl hp (by simpa using hcap) hev,
        (spawnCfg_elab c i th x e' j f ts T ws).symm⟩

theorem UExt.toCore {c c' : UCfg} (h : UExt U k arch c c') :
    Ext (elabProg U) k arch (toCoreCfg c) (toCoreCfg c') := by
  cases h with
  | mk i x n a j e th rt ws rs hth hl hp hev hadm hc =>
    rw [wake_elab, extCfg_elab hth]
    refine Ext.mk i x n a (elabT j e) (toCoreTh th) rt ws rs (by rw [toCoreCfg_get, hth]; rfl) ?_ hp hev hadm ?_
    · show elabT th.ctr th.term = _
      rw [elab_layer, hl]; rfl
    · rw [← extCfg_elab hth]; exact uCertified_iff.mp hc

theorem UExt.ofCore {c : UCfg} {d : Cfg} (h : Ext (elabProg U) k arch (toCoreCfg c) d) :
    ∃ c', UExt U k arch c c' ∧ d = toCoreCfg c' := by
  cases h with
  | mk i x n a e th' rt ws rs hth hterm hp hev hadm hc =>
    rw [toCoreCfg_get] at hth
    cases hcc : c.ths[i]? with
    | none => rw [hcc] at hth; simp at hth
    | some th =>
      rw [hcc] at hth
      simp only [Option.map_some, Option.some.injEq] at hth
      subst hth
      obtain ⟨j, e', hl, rfl⟩ := layer_let_inv hterm
      refine ⟨_, UExt.mk i x n a j e' th rt ws rs hcc hl hp hev hadm ?_, by rw [wake_elab, extCfg_elab hcc x n e' j ws rs]; rfl⟩
      rw [uCertified_iff, extCfg_elab hcc]; exact hc

/-- Runs lift forward, for any extra relation that does. -/
theorem StepsGU.toCore {SpU : UCfg → UCfg → Prop} {Sp : Cfg → Cfg → Prop}
    (hsp : ∀ c c', SpU c c' → Sp (toCoreCfg c) (toCoreCfg c')) {c c' : UCfg} (h : StepsGU U k arch SpU c c') :
    StepsG (elabProg U) k arch Sp (toCoreCfg c) (toCoreCfg c') := by
  induction h with
  | refl c => exact StepsG.refl _
  | step h _ ih =>
    rcases h with h | h
    · exact StepsG.step (Or.inl h.toCore) ih
    · exact StepsG.step (Or.inr (hsp _ _ h)) ih

/-- Runs from an image lift back, for any extra relation that does. -/
theorem StepsGU.ofCore {SpU : UCfg → UCfg → Prop} {Sp : Cfg → Cfg → Prop}
    (hsp : ∀ c d, Sp (toCoreCfg c) d → ∃ c', SpU c c' ∧ d = toCoreCfg c') {d d' : Cfg}
    (h : StepsG (elabProg U) k arch Sp d d') :
    ∀ c, d = toCoreCfg c → ∃ c', StepsGU U k arch SpU c c' ∧ d' = toCoreCfg c' := by
  induction h with
  | refl d => intro c hc; exact ⟨c, StepsGU.refl _, hc⟩
  | step h _ ih =>
    intro c hc
    subst hc
    rcases h with h | h
    · obtain ⟨c1, h1, rfl⟩ := UStep.ofCore h
      obtain ⟨c2, h2, rfl⟩ := ih c1 rfl
      exact ⟨c2, StepsGU.step (Or.inl h1) h2, rfl⟩
    · obtain ⟨c1, h1, rfl⟩ := hsp _ _ h
      obtain ⟨c2, h2, rfl⟩ := ih c1 rfl
      exact ⟨c2, StepsGU.step (Or.inr h1) h2, rfl⟩

/-- **T2, forward**: every UnElab run (machine, spawn and extern steps) is a core run of the
elaborated program between the images — same memory, pairs, promises, thread count and trace
(`toCoreCfg_mem`, `toCoreCfg_pairs`, `toCoreCfg_trace`, `toCoreCfg_size`), step for step. -/
theorem T2_fwd {cap : Nat} {c0 c : UCfg} (h : StepsU U k arch cap c0 c) :
    StepsE (elabProg U) k arch cap (toCoreCfg c0) (toCoreCfg c) :=
  StepsGU.toCore (fun _ _ h => h.elim (fun h => Or.inl h.toCore) (fun h => Or.inr h.toCore)) h

/-- **T2, backward**: every core run of the elaborated program from the image of a UnElab
configuration is the image of a UnElab run.  (The form "`StepsE` between two images ↔ `StepsU`" with both ends
images would need `toCoreCfg` injective, which it is not in general — the counter is invisible in the image; that
is the optional [K2] isomorphism.) -/
theorem T2_bwd {cap : Nat} {c0 : UCfg} {d : Cfg} (h : StepsE (elabProg U) k arch cap (toCoreCfg c0) d) :
    ∃ c, StepsU U k arch cap c0 c ∧ d = toCoreCfg c :=
  StepsGU.ofCore (fun _ _ h => h.elim
    (fun h => (USpawn.ofCore h).elim fun c' ⟨h1, h2⟩ => ⟨c', Or.inl h1, h2⟩)
    (fun h => (UExt.ofCore h).elim fun c' ⟨h1, h2⟩ => ⟨c', Or.inr h1, h2⟩)) h c0 rfl

end Lifts

/-! ## §6 The premise predicates, UnElab versions -/

mutual
/-- No spawn in an operand. -/
def argNoSpawn : UArg → Bool
  | .at _ => true
  | .op h args => opNoSpawn h && argsNoSpawn args

def argsNoSpawn : List UArg → Bool
  | [] => true
  | a :: rest => argNoSpawn a && argsNoSpawn rest
end

/-- No spawn anywhere in a UnElab term (operands included). -/
def uExprNoSpawn : UExpr → Bool
  | .let_ _ h args e => opNoSpawn h && argsNoSpawn args && uExprNoSpawn e
  | .split a _ _ e | .unpack a _ _ e | .unpackT a _ _ e | .region a _ _ _ e | .openPub a _ _ _ e =>
      argNoSpawn a && uExprNoSpawn e
  | .case a _ e₁ _ e₂ | .ifnull a e₁ _ e₂ | .parity a _ e₁ e₂ => argNoSpawn a && uExprNoSpawn e₁ && uExprNoSpawn e₂
  | .ifeq a b e₁ e₂ => argsNoSpawn [a, b] && uExprNoSpawn e₁ && uExprNoSpawn e₂
  | .cas _ _ w e v _ ok fail => argsNoSpawn [w, e, v] && uExprNoSpawn ok && uExprNoSpawn fail
  | .casp _ _ w e0 e1 v0 v1 _ ok fail =>
      argsNoSpawn [w, e0, e1, v0, v1] && uExprNoSpawn ok && uExprNoSpawn fail
  | .ret a | .tail _ _ a _ => argNoSpawn a

/-- A spawn-free UnElab program. -/
def UNoSpawnP (U : UProg) : Prop := ∀ d ∈ U, uExprNoSpawn d.body = true

theorem opNoSpawn_setAts (h : Op) (as : List At) : opNoSpawn (setAts h as) = opNoSpawn h := by
  cases h <;> simp only [setAts] <;> (try split) <;> rfl

theorem exprNoSpawn_lets (L : List (String × Op)) (e : Expr) :
    exprNoSpawn (lets L e) = (L.all (fun b => opNoSpawn b.2) && exprNoSpawn e) := by
  induction L with
  | nil => simp [lets]
  | cons b L ih => simp [lets, exprNoSpawn, ih, Bool.and_assoc]

mutual
theorem elabArg_noSpawn (k : Nat) : ∀ a : UArg,
    (elabArg k a).1.all (fun b => opNoSpawn b.2) = argNoSpawn a
  | .at _ => rfl
  | .op h args => by
      simp [elabArg, argNoSpawn, elabArgs_noSpawn k args, opNoSpawn_setAts, Bool.and_comm]

theorem elabArgs_noSpawn (k : Nat) : ∀ as : List UArg,
    (elabArgs k as).1.all (fun b => opNoSpawn b.2) = argsNoSpawn as
  | [] => rfl
  | a :: rest => by
      simp [elabArgs, argsNoSpawn, elabArg_noSpawn k a, elabArgs_noSpawn _ rest]
end

theorem destr_noSpawn (b : Bool) : ∀ (p : UPat) (k : Nat) (s : At) (c : Nat → Expr),
    (∀ j, exprNoSpawn (c j) = b) → exprNoSpawn (destr k s p c) = b
  | .bind _, k, s, c, h => h k
  | .pair p q, k, s, c, h => by
      simp only [destr, exprNoSpawn]
      exact destr_noSpawn b p _ _ _ fun j => destr_noSpawn b q _ _ _ h

theorem exprNoSpawn_elab : ∀ (e : UExpr) (k : Nat), exprNoSpawn (elabT k e) = uExprNoSpawn e := by
  intro e
  induction e with
  | let_ x h args e ih =>
    intro k; simp [elabT, exprNoSpawn_lets, exprNoSpawn, elabArgs_noSpawn, uExprNoSpawn, opNoSpawn_setAts, ih,
      Bool.and_assoc, Bool.and_left_comm]
  | split a p q e ih =>
    intro k
    simp only [elabT, exprNoSpawn_lets, elabArg_noSpawn, uExprNoSpawn]
    rw [destr_noSpawn (uExprNoSpawn e) (.pair p q) _ _ _ (fun j => ih j)]
  | ifeq a b yes no ih1 ih2 =>
    intro k; simp [elabT, exprNoSpawn_lets, exprNoSpawn, elabArgs_noSpawn, uExprNoSpawn, ih1, ih2, Bool.and_assoc]
  | cas acq rel w e v t ok fail ih1 ih2 =>
    intro k; simp [elabT, exprNoSpawn_lets, exprNoSpawn, elabArgs_noSpawn, uExprNoSpawn, ih1, ih2, Bool.and_assoc]
  | casp acq rel w e0 e1 v0 v1 t ok fail ih1 ih2 =>
    intro k; simp [elabT, exprNoSpawn_lets, exprNoSpawn, elabArgs_noSpawn, uExprNoSpawn, ih1, ih2, Bool.and_assoc]
  | ret a => intro k; simp [elabT, exprNoSpawn_lets, exprNoSpawn, elabArg_noSpawn, uExprNoSpawn]
  | tail f is a ts => intro k; simp [elabT, exprNoSpawn_lets, exprNoSpawn, elabArg_noSpawn, uExprNoSpawn]
  | _ => intro k; simp_all [elabT, exprNoSpawn_lets, exprNoSpawn, elabArg_noSpawn, uExprNoSpawn, Bool.and_assoc]

/-- `NoSpawnP` of the elaboration is `UNoSpawnP`. -/
theorem uNoSpawnP_iff (U : UProg) : UNoSpawnP U ↔ NoSpawnP (elabProg U) := by
  simp [UNoSpawnP, NoSpawnP, elabProg, elabDecl, exprNoSpawn_elab]

/-- A UnElab thread at a spawn: its layer is a spawn `let`. -/
def UAtSite (th : UTTh) : Prop := ∃ x f a T ts j e, layer th.ctr th.term = .letOp x (.spawn f a T ts) j e

/-- A UnElab thread at an extern call. -/
def UExtSite (th : UTTh) : Prop := ∃ x n a j e, layer th.ctr th.term = .letOp x (.ext n a) j e

/-- Every UnElab thread at a spawn has no promises. -/
def USiteNoProm (c : UCfg) : Prop := ∀ (i : Nat) (th : UTTh), c.ths[i]? = some th → UAtSite th → th.promises = []

theorem uAtSite_iff (th : UTTh) : UAtSite th ↔ AtSite (toCoreTh th) := by
  constructor
  · rintro ⟨x, f, a, T, ts, j, e, hl⟩
    exact ⟨x, f, a, T, ts, elabT j e, show elabT th.ctr th.term = _ by rw [elab_layer, hl]; rfl⟩
  · rintro ⟨x, f, a, T, ts, e, he⟩
    obtain ⟨j, e', hl, -⟩ := layer_let_inv (show elabT th.ctr th.term = _ from he)
    exact ⟨x, f, a, T, ts, j, e', hl⟩

theorem uExtSite_iff (th : UTTh) : UExtSite th ↔ ExtSite (toCoreTh th) := by
  constructor
  · rintro ⟨x, n, a, j, e, hl⟩
    exact ⟨x, n, a, elabT j e, show elabT th.ctr th.term = _ by rw [elab_layer, hl]; rfl⟩
  · rintro ⟨x, n, a, e, he⟩
    obtain ⟨j, e', hl, -⟩ := layer_let_inv (show elabT th.ctr th.term = _ from he)
    exact ⟨x, n, a, j, e', hl⟩

theorem uSiteNoProm_iff (c : UCfg) : USiteNoProm c ↔ SiteNoProm (toCoreCfg c) := by
  constructor
  · intro h i th' hth hs
    rw [toCoreCfg_get] at hth
    cases hc : c.ths[i]? with
    | none => rw [hc] at hth; simp at hth
    | some th =>
      rw [hc] at hth
      simp only [Option.map_some, Option.some.injEq] at hth
      subst hth
      exact h i th hc ((uAtSite_iff th).mpr hs)
  · intro h i th hth hs
    have := h i (toCoreTh th) (by rw [toCoreCfg_get, hth]; rfl) ((uAtSite_iff th).mp hs)
    exact this

end UnElab

#print axioms UnElab.focus_elab
#print axioms UnElab.elab_layer
#print axioms UnElab.tstep_elab
#print axioms UnElab.ustep_nil_iff
#print axioms UnElab.uCertified_iff
#print axioms UnElab.UStep.toCore
#print axioms UnElab.UStep.ofCore
#print axioms UnElab.T2_fwd
#print axioms UnElab.T2_bwd
#print axioms UnElab.uNoSpawnP_iff
#print axioms UnElab.uAtSite_iff
#print axioms UnElab.uExtSite_iff
#print axioms UnElab.uSiteNoProm_iff
