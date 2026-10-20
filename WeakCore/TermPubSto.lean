import WeakCore.TermStep

/-! # (D+, L4) `pubSto_of_typed`: a typed `publish` names an own cell of the store

A `publish a` types only at an `own` handle (`OpT.publish`: `.ptr .own u`; `OpT.publishBuf`: `.loc .own (.array n u)`), whose value
(`VR` at `.ptr .own` / `.loc .own`, via `use_FInv`) is a location of a cell of `η.sto` owned by `η.tid` (`ModeOK` at
`.own`).  So the published label is never a box label (box labels hold no cell) nor a freed one; the same
destructuring as `TermStep.tstepM_publish`.  Needs only the typing and `FInv` (no `MemInv`). -/

namespace TermPubSto

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem pubSto_of_typed {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {x : String} {a : At}
    {e : Expr} {rt : Ty} {ws : List Word} {ad : Address} (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hterm : th.term = .let_ x (.publish a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0]) :
    ∃ c, (CE η).sto ad.label = some c ∧ c.owner = some (CE η).tid := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨-, rt', ws', hea', hv, -⟩ := use_FInv hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VR] at hv
    obtain ⟨ad', c, hws', -, hsto, -, hmode, -⟩ := hv
    rw [hws] at hws'
    have had : ad = ad' := by simpa using hws'
    subst had
    exact ⟨c, hsto, hmode⟩
  | publishBuf hu hsh hb =>
    obtain ⟨-, rt', ws', hea', hvb, -⟩ := use_FInv hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VR] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -⟩ | ⟨ad', c, U, hws', hsto, -, -, hmode, -⟩
    · rw [hws] at hnull; simp at hnull
    · rw [hws] at hws'
      have had : ad = ad' := by simpa using hws'
      subst had
      exact ⟨c, hsto, hmode⟩

end TermPubSto

#print axioms TermPubSto.pubSto_of_typed
