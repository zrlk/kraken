import WeakCore.TermGranW

/-!
# FootNCE (the statement text, for a verbatim diff against the two goal statements and the (X) export)

The two conjuncts that `FootNC` (`TermPtrKey`) adds to the footprint's `∃ E'`, stated about a
single step result `r` with pre-env `E` (`= CE η`) and post-env `E'`.  Conjunct order and binder
order match `FootNC` verbatim (NC4 carries `v ∉ r.2.2.promises`).
-/

namespace TermPtrRtsK

open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep TermSys TermPtrRts
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (staging) **NC ∧ NC4** at one step result. -/
def FootNCE (E E' : TEnv) (r : Memory × List Ts × TTh) : Prop :=
  (∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → E'.sto m0.loc.label = some cl →
    E.sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset) ∧
  ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
    E'.sto mv.loc.label = some cl → E.sto mv.loc.label = none → mv.loc.offset = o + 1 →
    TwoAtT cl.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1

end TermPtrRtsK
