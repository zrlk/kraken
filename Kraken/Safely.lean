/-
Partial correctness for a step relation in `Eventually`'s shape (design
note `Kraken/Promising/EnvWP.md` §8).

`Eventually trans post x` is total correctness: every run from `x` reaches
`post` in finitely many steps. A retry loop over a shared location does not
terminate by a variant in general (another thread may keep winning, and an
AArch64 store-exclusive may fail spuriously even in the one-thread
environment). `Safely trans post x` is the partial-correctness twin: there is
an invariant holding at `x` such that every invariant state either satisfies
`post` or takes a step whose every outcome is again in the invariant. A run
that never reaches `post` is allowed; a run that stops (no step) is in `post`.

ISA-free: it mentions only the step relation, so both ISAs and the Promising
link import it. The link (`Kraken.Promising.SeqLinkSafe`) needs only one case
analysis per step, which `Safely` gives just as `Eventually` does.
-/
import Kraken.OmniSemantics

/-- Partial correctness by an invariant: `Inv` holds at `x`, and from every
`Inv` state either `post` holds, or a `trans` step is possible whose outcomes
are all in `Inv`. -/
def Safely {State : Type} (trans : State → (State → Prop) → Prop) (post : State → Prop) (x : State) : Prop :=
  ∃ Inv : State → Prop, Inv x ∧
    ∀ y, Inv y → post y ∨ ∃ R : State → Prop, trans y R ∧ ∀ z, R z → Inv z

namespace Safely

variable {State : Type} {trans : State → (State → Prop) → Prop} {post post' : State → Prop}

/-- Unfold one step: `post` now, or a step into states that are again
`Safely`. -/
theorem unfold {x : State} (h : Safely trans post x) :
    post x ∨ ∃ R : State → Prop, trans x R ∧ ∀ z, R z → Safely trans post z := by
  obtain ⟨Inv, hx, hInv⟩ := h
  rcases hInv x hx with hp | ⟨R, hT, hR⟩
  · exact .inl hp
  · exact .inr ⟨R, hT, fun z hz => ⟨Inv, hR z hz, hInv⟩⟩

/-- Fold one step (the coinduction principle with `Safely` itself as the
invariant). -/
theorem fold {x : State}
    (h : post x ∨ ∃ R : State → Prop, trans x R ∧ ∀ z, R z → Safely trans post z) :
    Safely trans post x :=
  ⟨fun y => post y ∨ ∃ R : State → Prop, trans y R ∧ ∀ z, R z → Safely trans post z, h,
    fun _ hy => hy.imp id fun ⟨R, hT, hR⟩ => ⟨R, hT, fun z hz => (hR z hz).unfold⟩⟩

theorem mono (hp : ∀ x, post x → post' x) {x : State} (h : Safely trans post x) :
    Safely trans post' x := by
  obtain ⟨Inv, hx, hInv⟩ := h
  exact ⟨Inv, hx, fun y hy => (hInv y hy).imp (hp y) id⟩

/-- Total correctness implies partial correctness. -/
theorem of_eventually {x : State} (h : Eventually trans post x) : Safely trans post x :=
  ⟨Eventually trans post, h, fun _ hy => by
    cases hy with
    | done _ hp => exact .inl hp
    | step _ mid hT hmid => exact .inr ⟨mid, hT, hmid⟩⟩

/-- Sequencing: a total run into states from which the rest is partially
correct. -/
theorem of_eventually_safely {x : State} {mid : State → Prop} (h : Eventually trans mid x)
    (hk : ∀ y, mid y → Safely trans post y) : Safely trans post x := by
  induction h with
  | done y hm => exact hk y hm
  | step y m hT _ ih => exact fold (.inr ⟨m, hT, ih⟩)

/-- At a state with no step, `Safely` is `post`. -/
theorem post_of_stuck {x : State} (h : Safely trans post x) (hs : ∀ R, ¬ trans x R) : post x :=
  h.unfold.resolve_right fun ⟨R, hT, _⟩ => hs R hT

/-- A simulation carries `Safely` along: if every `trans₁` step from a
related state gives a `trans₂` step into related states, `Safely trans₁`
gives `Safely trans₂` of the related post. -/
theorem sim {State₂ : Type} {trans₂ : State₂ → (State₂ → Prop) → Prop} (Rel : State → State₂ → Prop)
    (hsim : ∀ x y R, Rel x y → trans x R → trans₂ y (fun y' => ∃ x', Rel x' y' ∧ R x'))
    {x : State} {y : State₂} (hxy : Rel x y) (h : Safely trans post x) :
    Safely trans₂ (fun y' => ∃ x', Rel x' y' ∧ post x') y := by
  obtain ⟨Inv, hx, hInv⟩ := h
  refine ⟨fun y' => ∃ x', Rel x' y' ∧ Inv x', ⟨x, hxy, hx⟩, ?_⟩
  rintro y' ⟨x', hr, hi⟩
  rcases hInv x' hi with hp | ⟨R, hT, hR⟩
  · exact .inl ⟨x', hr, hp⟩
  · exact .inr ⟨_, hsim x' y' R hr hT, fun z ⟨x'', hr'', hR''⟩ => ⟨x'', hr'', hR x'' hR''⟩⟩

end Safely
