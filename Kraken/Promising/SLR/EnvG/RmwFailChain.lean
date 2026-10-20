/-
The failing-RMW route's open chain link, closed.

`Theorem1FChain` (`EnvG/RmwFailRule.lean`) is Theorem 1′ for per-thread
`NPSafeF` tokens (`NPSafe` whose step conjunct also assumes `StepFul`). The
existing Theorem 1′ chain is now generic in a step guard `S`
(`SLR/NPSafeP.lean`, `StepGuard`, `NPSafePS`), discharged at its two
`stepAt` sites (`caseNow'`, `caseD1'`) from `StepFulP`; `theorem1IIPureS'`
(`SLR/Theorem1Final.lean`) is the generic theorem.

- `stepFul_eq`: the failing-RMW route's `StepFul` is the chain's `StepFulP`.
- `npSafeF_eq`: `NPSafeF` is `NPSafePF` (`NPSafePS` at `StepGuard.ful`) at
  the existing guard `G₀` and frame `K2₀`, definitionally.
- `theorem1FChain`: **`Theorem1FChain` holds** for every `A` and `fuel`
  (`theorem1IIPureS'` at `G₀`, `GRF`, `K2₀`, `StepGuard.ful`).

ISA-neutral.
-/
import Kraken.Promising.SLR.EnvG.RmwFailRule
import Kraken.Promising.SLR.Theorem1Final

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- The failing-RMW route's step condition is the chain's (`rfl`). -/
theorem stepFul_eq (M : ResModel I) : StepFul M = StepFulP M := rfl

unseal NPSafeF NPSafePS in
/-- **`NPSafeF` is `NPSafePS` at the fulfilling step guard**, at the existing
prepay guard `G₀` and K2 frame `K2₀`: `rfl` once the two well-founded
definitions are unsealed (as `NPSafeP_G₀_K₀`). -/
theorem npSafeF_eq (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat) :
    NPSafeF M A B tid = NPSafePF M A B tid G₀ (K2₀ M) := rfl

/-- `npSafeF_eq`, applied (for rewriting). -/
theorem npSafeF_eq_apply (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid n m : Nat)
    (cl : Prop) (c : Config I) (r : M.R) (g : M.Ghost) :
    NPSafeF M A B tid n m cl c r g = NPSafePF M A B tid G₀ (K2₀ M) n m cl c r g := by
  rw [npSafeF_eq M A B tid]

/-- **Theorem 1′ for `NPSafeF`** (the failing-RMW route's open link, now proved):
`theorem1IIPureS'` at the existing guards `G₀`/`GRF`, the existing frame `K2₀`
and the fulfilling step guard `StepGuard.ful`. -/
theorem theorem1FChain [I.LawfulState] (A : Arch) (fuel : Nat) : Theorem1FChain (I := I) A fuel :=
  fun B states initMem rF g hNT E hp hpure hs =>
    theorem1IIPureS' (S := StepGuard.ful (model I)) guardOK_G₀ guardOK_GRF (fun _ _ _ _ _ h => G₀_le_GRF h)
      (k2OK_K2₀ _) A fuel B states initMem rF g hNT E hp hpure
      (fun tid htid n m => Eq.mp (npSafeF_eq_apply (model I) A B tid n m True _ _ _) (hs tid htid n m))

#print axioms theorem1FChain

end Kraken.Promising.SLR.EnvG
