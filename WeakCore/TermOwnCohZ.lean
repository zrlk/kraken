import WeakCore.TermCut

/-!
# TermOwnCohZ: the `SysInvN` clause `ownCoh`

`OwnCohZ E s`: at every own private cell of `E` (owned by `E.tid`, no frontier), at the
offsets inside the cell, the thread's coherence is at most its `vWr`.  This is
`TermCohLe.OwnCohInv`, stated here (before `TermMainDefs`) so that `SysInvN` can carry
it; `TermOwnCoh.ownCohZ_iff` identifies the two.
-/

namespace TermOwnCohZ
open CoreLang CoreTerm TermRun TermClose TermSound TermMem TermStep
open WeakMem (Address Ts AllocLabel)

/-- The thread's coherence at its own private cells is at most its `vWr`. -/
def OwnCohZ (E : TEnv) (s : St) : Prop :=
  ∀ l c, E.sto l = some c → c.owner = some E.tid → E.pfr l = none →
    ∀ o, (∃ (E0 : TEnv) (n : Nat) (vals : List Word), CellOK E0 n c.ty vals ∧ o < vals.length) →
    s.vs.coh ⟨l, o⟩ ≤ s.vs.vWr

end TermOwnCohZ
