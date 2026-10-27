import Spike.Lib.Src.NJLB

/-!
**The walk facts of an `Accepted2` body's induction** (ISA-neutral): the
side conditions of the node invariant's per-construct lemmas (`NJB.*`,
`Spike/Lib/Src/NJLB.lean`) that the invariant does not give itself, stated
at the points of the two walks the induction follows. All are facts about
the source program only; they are discharged from `Accepted2`'s conjuncts
separately.

- `headAtoms t`: the atoms the construct at the head of `t` reads;
- `LitPt q`, at a point `q` of the literal walk (`litWalk2`): every atom
  the head reads is bound in the walk's layouts (`InLits`); a `pack`'s
  target is compatible with its operand's layout (`Compat`, for
  `NJB.pack`); an `asLanes` operand is one word (a `.leaf`, for a variable
  operand of `asLanes`);
- `EnvTy2 q`, at a point `q` of the lowering's walk (`lowerEnvs2`): every
  binding's type has `shapeOf`'s exact layout (`simpleTy`), a word count
  (`valWords`) and no refined product (`noRefProd`). This gives a `split`
  its literal product (`prodOf` sees through refinements, `NJB.split` asks
  `.prod`) and its left part's access paths (`accsPl_of_valWords`);
- `GrpL env`, at a point of the lowering's walk: every binding a lookup
  finds groups into placements (`Form.group`), for the symbolic environment
  `ofEnv2`.

Where they come from: `LitPt`'s `InLits` from `body2`'s scopes and the
walk's start (`params2`), its `Compat` and `.leaf` from `layoutOk2`;
`EnvTy2` from `decls2`'s types, `layoutOk2` (`pack`), `refOk2`, and the
types the lowering binds (`newBufTy`, an element `elem2`, a call's result);
`GrpL` from the walk's bindings against the literal walk's (`RelE`, its
layouts compatible).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV litAt Env)

/-- **The atoms the construct at the head of `t` reads.** -/
def headAtoms : Expr → List At
  | .let_ _ op _ =>
    match op with
    | .atom a | .nameI a | .pack a _ _ | .asLanes _ _ a | .call _ _ a _ | .newBuf a _ => [a]
    | .pair a b | .add a b | .sub a b => [a, b]
    | .xchgAt b i v => [b, i, v]
    | _ => []
  | .split a _ _ _ | .unpack a _ _ _ | .ret a => [a]
  | .ifeq a b _ _ => [a, b]
  | _ => []

/-- **The literal walk's facts at a point** `q` (term, layouts): the head's
atoms bound in the layouts, a `pack`'s target compatible with its operand's
layout, an `asLanes` operand one word, the head's literals below `2 ^ 64`. -/
def LitPt (q : Expr × List (String × LitV)) : Prop :=
  (∀ a ∈ headAtoms q.1, InLits q.2 a) ∧
    (∀ x a w τ e, q.1 = .let_ x (.pack a w τ) e → Compat τ (litAt q.2 a) = true) ∧
    (∀ x sg w a e, q.1 = .let_ x (.asLanes sg w a) e → ∃ o, litAt q.2 a = .leaf o) ∧
    (∀ n, At.lit n ∈ headAtoms q.1 → n < 2 ^ 64)

/-- An atom bound in the layouts, as a `Bool`. -/
def inLitsB (lits : List (String × LitV)) : At → Bool
  | .var x => (lits.lookup x).isSome
  | _ => true

/-- A literal atom below `2 ^ 64`, as a `Bool`. -/
def litLtB : At → Bool
  | .lit n => decide (n < 2 ^ 64)
  | _ => true

/-- **`LitPt` as a `Bool`** (for walks over `litWalks2` with a `Bool`
predicate). -/
def litPtB (q : Expr × List (String × LitV)) : Bool :=
  (headAtoms q.1).all (inLitsB q.2) && (headAtoms q.1).all litLtB &&
    match q.1 with
    | .let_ _ (.pack a _ τ) _ => Compat τ (litAt q.2 a)
    | .let_ _ (.asLanes _ _ a) _ => match litAt q.2 a with | .leaf _ => true | _ => false
    | _ => true

theorem inLits_of_B {lits : List (String × LitV)} {a : At} (h : inLitsB lits a = true) : InLits lits a := by
  intro x hx
  subst hx
  exact h

theorem litPt_of_B {q : Expr × List (String × LitV)} (h : litPtB q = true) : LitPt q := by
  obtain ⟨t, lits⟩ := q
  simp only [litPtB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨ha, hl⟩, hm⟩ := h
  refine ⟨fun a hm' => inLits_of_B (ha a hm'), ?_, ?_, fun n hn => by simpa [litLtB] using hl _ hn⟩
  · rintro x a w τ e rfl
    simpa using hm
  · rintro x sg w a e rfl
    simp only at hm
    split at hm
    · exact ⟨_, ‹_›⟩
    · cases hm

/-- **The lowering walk's type facts at a point** `q` (term, environment,
counter): every binding's type is a `simpleTy` with a word count and no
refined product. -/
def EnvTy2 (q : Expr × Env × Nat) : Prop :=
  ∀ b ∈ q.2.1, Scc.Lower.simpleTy b.2.1 = true ∧ (Scc.Obj.valWords b.2.1).isSome = true ∧
    Scc.Lower.noRefProd b.2.1 = true

/-- **The lowering walk's bindings group** (at a point's environment):
every binding a lookup finds has its words grouped into placements
(`Form.group`), so that `ofEnv2` places it (`ofEnv2_cons`, `sevalAt` at
`ofEnv2`). Shadowed bindings are not asked. -/
def GrpL (env : Env) : Prop :=
  ∀ x b, env.find? (·.1 == x) = some b → (Spike.Lib.Form.group b.2.1 b.2.2).isSome = true

/-- Under `noRefProd`, `prodOf` finds a literal product. -/
theorem prodOf_noRefProd {t u w : Ty} (hn : Scc.Lower.noRefProd t = true) (hp : Scc.Lower.prodOf t = some (u, w)) :
    t = .prod u w := by
  cases t with
  | prod a b => simp [Scc.Lower.prodOf] at hp; obtain ⟨rfl, rfl⟩ := hp; rfl
  | refine t _ =>
    simp only [Scc.Lower.noRefProd, Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
    simp [Scc.Lower.prodOf, hn.1] at hp
  | _ => simp [Scc.Lower.prodOf] at hp

end Spike.Lib.LowerNode
