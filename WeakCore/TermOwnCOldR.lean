import WeakCore.TermOwnCOld

/-! # TermOwnCOldR: `overCr_old` with the stepper's re-pin items (ownC)

`overCr_oldR`: as `TermOwnCOld.overCr_old`, with `KeepQRS`'s re-pin items `RS` (pool form,
`RepinQh`) as a third source of cover: a post-demand is a pre-demand, a zero item, or covered by
an item of `RS` at the label.  Credits: a kept holder's old credit plus its re-pin credit, and any
re-pin credit, lie within the new credits.
-/

namespace TermOwnCOldR

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)


#print axioms le_rpSum


#print axioms overCr_oldR

end TermOwnCOldR
