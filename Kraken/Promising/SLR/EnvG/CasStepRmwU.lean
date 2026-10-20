/-
**`StepRmwU` is a theorem** (the claim fix).

`CasVC.lean` states the CAS worker's `casa` VC under the explicit
hypothesis `StepRmwU` (`step_rmwFacts` with the unclaimed read added), since
`RmwFacts` did not expose that the message an RMW reads is unclaimed. With the
claim fix (`RmwOut`/`RmwFacts`' success disjunct ends in
`¬ σ'.g.Claimed (l, tr)`, produced by `ErAt.not_claimed_rmw`), it follows from
`step_rmwFacts` for every arch, thread and plan: `stepRmwU`.
-/
import Kraken.Promising.SLR.EnvG.CasVC

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG

/-- `RmwFacts` implies the strengthened `RmwFactsU`. -/
theorem rmwFactsU_of_rmwFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {old : Val} (h : RmwFacts A tid pl σ σ' k l op old) :
    RmwFactsU A tid pl σ σ' k l op old := by
  obtain ⟨c, tr, hA, hR, hV, hcl, -, -, -, hacq, hbr⟩ := h
  refine ⟨c, tr, hA, hR, hV, hcl, hacq, ?_⟩
  rcases hbr with ⟨hop, -, hr⟩ | ⟨new, tw, hop, htw, -, -, hwb, hcoh, -, -, hr, hun⟩
  · exact .inl ⟨hop, hr⟩
  · exact .inr ⟨new, tw, hop, htw, hun, hwb, hcoh, hr⟩

/-- **`StepRmwU` holds** (the claim fix): the CAS lock proof's hypothesis on `casWorker_envG`
and `vc_casa` is discharged by `step_rmwFacts`. -/
theorem stepRmwU (A : Arch) (tid : Nat) (pl : Plan) : StepRmwU A tid pl :=
  fun _ _ _ _ _ _ _ h => rmwFactsU_of_rmwFacts (step_rmwFacts h)

end Kraken.Promising.SLR.EnvG.CasSmoke
