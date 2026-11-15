import WeakCore.CoreTerm

/-!
# TermDyDefs — the type-test cleanliness premise (CHECKED r3)

`TaintClosed` and `HidClean` (moved verbatim from TermSound, same names `TermSound.*`, so that the
classes `TermTv.ProgRetIall` / `TermA4.ProgCkWC` upstream of TermSound can carry `DyClean`) and the
headline premise `DyClean`, which replaces `checkProg p = .ok ()` beside `CoreTyping.ProgT`.
-/

namespace TermSound
open CoreLang CoreTerm

/-- A set of (callee, tainted type parameters) closed under the walk: no refused allocation, and
every tainted call edge stays in the set. -/
def TaintClosed (p : Prog) (ann : Op → Option Ty) (tg : List Ty) (S : List (String × List Nat)) : Prop :=
  ∀ g b, (g, b) ∈ S → ∀ d, p.find? (·.name == g) = some d →
    (scan ann tg b d.body).1 = [] ∧ ∀ e ∈ (scan ann tg b d.body).2, e.2 ≠ [] → e ∈ S

/-- A term with hidden positions `H` refuses nothing, and its tainted calls are in `S`. -/
def HidClean (ann : Op → Option Ty) (tg : List Ty) (S : List (String × List Nat)) (H : List Nat)
    (e : Expr) : Prop :=
  (scan ann tg H e).1 = [] ∧ ∀ c ∈ (scan ann tg H e).2, c.2 ≠ [] → c ∈ S

/-- **The program is clean for type tests.** This is a declarative closure over the checker's syntactic
scan of each block. There is one set of calls whose type parameters may hide a type, closed under the
program's calls, under which no block allocates, inside an opened type package, a value whose type
mentions the hidden type and could later be tested against it. It states what the checker's
type-scope pass establishes, without that pass's search bound. Every program the checker accepts meets it
(`TermSound.typed_dy_of_checked`); it would be revisited if the accepted language is widened beyond `DyClean`. -/
def DyClean (p : Prog) : Prop :=
  ∃ S, TaintClosed p annNew (progTgts p) S ∧ ∀ d ∈ p, HidClean annNew (progTgts p) S [] d.body

end TermSound
