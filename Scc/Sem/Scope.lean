/-
`exprFv` and `opVars` (`Scc/Sem/Correct.lean`) against WeakCore's
syntactic scope check (`WeakCore/TermScope.lean`): `x ∈ exprFv e` iff
`TermScope.freeB x e`, and `opVars` reads what `TermScope.opAts` lists. A
separate module so that the statement does not import the scope check.
-/
import Scc.Sem.Correct
import WeakCore.TermScope

namespace Scc.Sem

theorem mem_atVars {x : String} {a : CoreTerm.At} : x ∈ atVars a ↔ TermScope.freeA x a = true := by
  cases a <;> simp [atVars, TermScope.freeA]

/-- `opVars` reads what WeakCore's `TermScope.opAts` lists (`validate`'s
variable included). -/
theorem mem_opVars {x : String} {op : CoreTerm.Op} :
    x ∈ opVars op ↔ (TermScope.opAts op).any (TermScope.freeA x) = true := by
  cases op <;> simp [opVars, opAts, TermScope.opAts, mem_atVars, TermScope.freeA]

/-- **`exprFv` is WeakCore's free-variable test**: `x ∈ exprFv e` iff
`TermScope.freeB x e`. -/
theorem mem_exprFv {x : String} {e : CoreTerm.Expr} : x ∈ exprFv e ↔ TermScope.freeB x e = true := by
  induction e <;> simp [exprFv, TermScope.freeB, mem_atVars, mem_opVars, *] <;> grind

end Scc.Sem
