/-
**Prototype: the immediate table keyed by control point** (ISA-neutral;
touches no existing definition).

Today `Layout.imms` is keyed by a frame's remaining term, so two control
points with the same remaining term must agree on their constants, and
`Accepted1` refuses programs where they do not (`immsCoherent`). Here the
table is keyed by the term **and a variant number** the witness chooses per
frame (`EnvImmPt`): the points with one term are numbered, and a frame's
constants are all read from its one variant.

- `variants`, `imms1V`: the variants of a term are the points of the
  program's literal walk with its key, in walk order; variant `j` of `t`
  gives the literal bindings of the `j`-th;
- `imms1V_of_mem`, `immIn_imms1V`: every point of the lowering's walk of a
  code block of **any** program (no coherence) has its immediates in one
  variant of its term;
- `EnvImmTerm`, `EnvImmPt`, `envImmPt_ofTerm`: today's `env_imm` for one
  thread and the variant-keyed one; a term-keyed table is the variant-keyed
  table that ignores the variant, for any choice of variants (by `Iff.rfl`);
- `EnvImmEx`, `envImmEx_iff`: the clause with the variant existential per
  frame (no witness field) is the one with a chosen variant per frame;
- `twoDecls`: two code blocks binding `x` to `3` and `4` at the same term
  `ret x`: refused by `immsCoherent`, no term-keyed table serves both
  frames (`no_term_table`), the variant table does (`pt_table`).
-/
import Spike.Lib.LowerEnvImmC1Of

namespace Spike.Lib.Proto.D2Imms

open CoreLang CoreTerm
open Scc.Lower (litWalk litWalks litOf termKey decls1 immsCoherent)
open Scc.Lower.Inv (env1)
open Spike.Lib.LowerNode (lowerEnvsC walkC_lits litRel_env1 ImmIn ofEnv imm_of_ofEnv)

/-! ## The variant table -/

/-- **The variants of a term**: the points of `p`'s literal walk with its
key (`termKey`), in walk order. -/
def variants (p : Prog) (t : Expr) : List (Expr × List (String × Option Nat)) :=
  (litWalks p).filter fun q => termKey q.1 == termKey t

/-- **The variant-keyed immediate table of a program**: at term `t`,
variant `j`, word 0 of `x`, the literal `x` is bound to at the `j`-th point
with `t`'s key. -/
def imms1V (p : Prog) (t : Expr) (j : Nat) (x : String) (k : Nat) : Option Nat :=
  if k = 0 then ((variants p t)[j]?).bind fun q => (q.2.lookup x).join else none

/-- **A point of the literal walk is a variant of its term**: some variant
gives exactly its literal bindings. -/
theorem imms1V_of_mem {p : Prog} {t : Expr} {lits : List (String × Option Nat)} (h : (t, lits) ∈ litWalks p) :
    ∃ j, ∀ x, imms1V p t j x 0 = (lits.lookup x).join := by
  have hm : (t, lits) ∈ variants p t := List.mem_filter.mpr ⟨h, by simp⟩
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hm
  exact ⟨j, fun x => by simp [imms1V, List.getElem?_eq_getElem hj, hget]⟩

/-- **The lowering's immediates are in one variant**: at each point of the
walk with calls of a code block of `p` (any program: no `immsCoherent`),
the lowering's environment has its immediates in one variant of the
point's term. -/
theorem immIn_imms1V {p : Prog} {d : Decl} (hd : d ∈ p) (frames : Option Nat) :
    ∀ q ∈ lowerEnvsC frames (env1 d) 0 d.body, ∃ j, ImmIn (fun t => imms1V p t j) (ofEnv q.2.1) q.1 := by
  intro q hq
  obtain ⟨lits, hl, hr⟩ := walkC_lits frames d.body (env1 d) 0 _ (litRel_env1 d _) q hq
  have hw : (q.1, lits) ∈ litWalks p := by
    simp only [litWalks, List.mem_flatMap]
    exact ⟨d, hd, hl⟩
  obtain ⟨j, hj⟩ := imms1V_of_mem hw
  refine ⟨j, fun x k v h => ?_⟩
  obtain ⟨rfl, hn⟩ := hr x k v (imm_of_ofEnv h)
  exact (hj x).trans hn

/-! ## The clause, for one thread -/

/-- **Today's `env_imm`** for one thread: frame `d`'s remaining term is
`terms[d]`, and a word it places at an immediate is the table's at that
term. -/
def EnvImmTerm {R : Type} (imms : Expr → String → Nat → Option Nat) (terms : List Expr)
    (env : Nat → String → Nat → Option (Scc.Sem.WordPlace R)) : Prop :=
  ∀ d e x k n, terms[d]? = some e → env d x k = some (.imm n) → imms e x k = some n

/-- **The variant-keyed `env_imm`** for one thread: the witness chooses a
variant `pt d` per frame, and every immediate of the frame is the table's
at its term and that variant. -/
def EnvImmPt {R : Type} (imms : Expr → Nat → String → Nat → Option Nat) (pt : Nat → Nat) (terms : List Expr)
    (env : Nat → String → Nat → Option (Scc.Sem.WordPlace R)) : Prop :=
  ∀ d e x k n, terms[d]? = some e → env d x k = some (.imm n) → imms e (pt d) x k = some n

/-- **A term-keyed table is a variant-keyed one** that ignores the variant,
whatever the witness chooses: the clauses are the same proposition, so every
existing proof of `env_imm` carries over unchanged. -/
theorem envImmPt_ofTerm {R : Type} (i : Expr → String → Nat → Option Nat) (pt : Nat → Nat) (terms : List Expr)
    (env : Nat → String → Nat → Option (Scc.Sem.WordPlace R)) :
    EnvImmTerm i terms env ↔ EnvImmPt (fun e _ => i e) pt terms env := Iff.rfl

/-- **The variant-keyed `env_imm`, variant existential**: each frame has
some variant holding all its immediates. The witness needs no new field. -/
def EnvImmEx {R : Type} (imms : Expr → Nat → String → Nat → Option Nat) (terms : List Expr)
    (env : Nat → String → Nat → Option (Scc.Sem.WordPlace R)) : Prop :=
  ∀ d, ∃ j, ∀ e x k n, terms[d]? = some e → env d x k = some (.imm n) → imms e j x k = some n

/-- **The two forms agree**: a choice of variants gives the existential
form, and the existential form gives a choice. -/
theorem envImmEx_iff {R : Type} (imms : Expr → Nat → String → Nat → Option Nat) (terms : List Expr)
    (env : Nat → String → Nat → Option (Scc.Sem.WordPlace R)) :
    EnvImmEx imms terms env ↔ ∃ pt, EnvImmPt imms pt terms env := by
  constructor
  · intro h
    exact ⟨fun d => Classical.choose (h d), fun d e x k n hd hx => Classical.choose_spec (h d) e x k n hd hx⟩
  · rintro ⟨pt, h⟩ d
    exact ⟨pt d, fun e x k n hd hx => h d e x k n hd hx⟩

/-! ## Example: one term, two constants -/

/-- `let x = n  ret x` as a code block `name`. -/
def litDecl (name : String) (n : Nat) : Decl :=
  { name, idx := [], arg := "n", argTy := .int, retTy := .int, body := .let_ "x" (.atom (.lit n)) (.ret (.var "x")) }

/-- Two code blocks binding `x` to `a` and `b` at `ret x`, and `main`
calling both. -/
def twoDecls (a b : Nat) : Prog :=
  [litDecl "f" a, litDecl "g" b,
   { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "r" (.call "f" [] (.lit 0)) <| .let_ "s" (.call "g" [] (.var "r")) (.ret (.var "s")) }]

/-- The shared term. -/
def retX : Expr := .ret (.var "x")

-- Refused today: well-formed code blocks, but not coherent.
#guard decls1 [] (twoDecls 3 4) && !immsCoherent (twoDecls 3 4)

-- The variant table: `ret x` has two variants, `x` is 3 in the first, 4 in
-- the second, nothing in a third; no other word.
#guard (variants (twoDecls 3 4) retX).length == 2
#guard imms1V (twoDecls 3 4) retX 0 "x" 0 == some 3
#guard imms1V (twoDecls 3 4) retX 1 "x" 0 == some 4
#guard imms1V (twoDecls 3 4) retX 2 "x" 0 == none
#guard imms1V (twoDecls 3 4) retX 0 "x" 1 == none

/-- A frame at `ret x` placing `x` at the immediate `n`. -/
def immEnv (n : Nat) : Nat → String → Nat → Option (Scc.Sem.WordPlace Unit) :=
  fun d y k => if d = 0 ∧ y = "x" ∧ k = 0 then some (.imm n) else none

/-- **No term-keyed table serves both frames**: one at `ret x` with `x` at
3 (in `f`), one with `x` at 4 (in `g`). -/
theorem no_term_table :
    ¬ ∃ i : Expr → String → Nat → Option Nat, EnvImmTerm i [retX] (immEnv 3) ∧ EnvImmTerm i [retX] (immEnv 4) := by
  rintro ⟨i, h3, h4⟩
  have e3 := h3 0 retX "x" 0 3 rfl (by simp [immEnv])
  have e4 := h4 0 retX "x" 0 4 rfl (by simp [immEnv])
  rw [e3] at e4
  cases e4

/-- **The variant table serves both**, the witness choosing variant 0 for
`f`'s frame and 1 for `g`'s. -/
theorem pt_table :
    EnvImmPt (imms1V (twoDecls 3 4)) (fun _ => 0) [retX] (immEnv 3) ∧
      EnvImmPt (imms1V (twoDecls 3 4)) (fun _ => 1) [retX] (immEnv 4) := by
  constructor
  all_goals
    intro d e x k n hd hx
    simp only [immEnv] at hx
    split at hx
    · rename_i h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases hd
      cases hx
      decide
    · cases hx

end Spike.Lib.Proto.D2Imms
