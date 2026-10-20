/-
**The same-location tree shapes of the no-fault-at-declarations proofs**: `EvTree.AtLocD l t`
(every access of `t` at `l`) and `EvTree.RootSameD t` (every access after
the root access at the root's location), moved verbatim from
`EnvG/X64NoFaultDMpIncl.lean` (same names). A module of their own, so that
their auto-generated equation lemmas keep their own `match` auxiliaries.
Used by `EnvG/X64NoFaultD.lean`.

ISA-neutral (it imports only `EnvG/A64DeclsCommon.lean`, no longer
`X64DeclsLink`), so that `EnvG/NoFaultDCommon.lean` can state the generic
`noFault_reresolve_rootSameD` for both ISAs.
-/
import Kraken.Promising.SLR.EnvG.A64DeclsCommon

namespace Kraken.Promising.EvTree

/-- **Every access of the tree is at `l`.** -/
def AtLocD {σ : Type} (l : Loc) : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, AtLocD l (k i)
  | .fence _ ret => AtLocD l (ret ())
  | .load _ _ l' ret => l' = l ∧ ∀ v, AtLocD l (ret v)
  | .store _ _ l' _ ret => l' = l ∧ ∀ b, AtLocD l (ret b)
  | .rmw _ _ l' _ ret => l' = l ∧ ∀ v, AtLocD l (ret v)

/-- **Every access after the root access is at the root's location.** -/
def RootSameD {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, RootSameD (k i)
  | .fence _ ret => RootSameD (ret ())
  | .load _ _ l ret => ∀ v, AtLocD l (ret v)
  | .store _ _ l _ ret => ∀ b, AtLocD l (ret b)
  | .rmw _ _ l _ ret => ∀ v, AtLocD l (ret v)

end Kraken.Promising.EvTree
