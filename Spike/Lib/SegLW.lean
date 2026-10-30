/-
**Segments with the load-or-stutter row inside a state predicate**
(`SegLW`).

`SegL p lbl ms P Q` (`Spike/Lib/SegLd.lean`) hides its invariant, as `Seg`
does: nothing is known of its pairs beyond their `OutL` rows. `SegLW W` is
`SegL` with the hidden invariant inside `W`, as `SegW W` is `Seg`'s
(`Spike/Lib/SegW.lean`; no outside moves: a path with the load-or-stutter
row holds no take). wake's main after the spawn needs it for
`WakeM0.MSide.off` (`W` the states off the `writeErr` and `threads` abort
sites).

Combinators: `step`, `seq`, `loop`, `mono_pre`, `mono_post`, `mono_W`,
`or_pre`, `cfg`, `exists_pre`; `toL` forgets `W`; `ofSegW` lifts a `SegW W`
segment with no outside moves; `closed` names the invariant (a `SegLW` to
the empty fragment gives an invariant inside `W` closed under the rows).
-/
import Spike.Lib.SegLd
import Spike.Lib.SegW

namespace Spike.Lib

open Kraken.Promising

/-- **`SegL` inside `W`**: every pair of `P` lies in an invariant inside `W`
whose pairs step (`OutL`) to the invariant or the exit `Q`. -/
def SegLW {I : ISA} (W : Frag I) (p : CoreTerm.Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I)
    (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧ (∀ s c, inv s c → W s c) ∧
    ∀ s c, inv s c → OutL p lbl ms (fun s c => inv s c ∨ Q s c) s c

namespace SegLW

variable {I : ISA} {W W' : Frag I} {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {P P' Q Q' R : Frag I}

/-- Forget `W`. -/
theorem toL (h : SegLW W p lbl ms P Q) : SegL p lbl ms P Q :=
  let ⟨i, hs, _, ho⟩ := h
  ⟨i, hs, ho⟩

/-- A `SegW` segment with no outside moves is one with the
load-or-stutter row. -/
theorem ofSegW (h : SegW W (fun _ _ => False) p lbl ms P Q) : SegLW W p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c hi => .out ((ho s c hi).1 fun _ h => h)⟩

/-- **One instruction** from every pair of `P`, inside `W`, into `Q`. -/
theorem step (hW : ∀ s c, P s c → W s c) (h : ∀ s c, P s c → OutL p lbl ms Q s c) : SegLW W p lbl ms P Q :=
  ⟨P, fun _ _ h => h, hW, fun s c hp => (h s c hp).mono fun _ _ h => .inr h⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegLW W p lbl ms P Q) (h₂ : SegLW W p lbl ms Q R) : SegLW W p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h),
    fun s c h => h.elim (hw₁ s c) (hw₂ s c), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) .inr

/-- **A tail-call loop.** -/
theorem loop {H X : Frag I} (h : SegLW W p lbl ms H (fun s c => H s c ∨ X s c)) : SegLW W p lbl ms H X := by
  obtain ⟨i, hs, hw, ho⟩ := h
  refine ⟨i, hs, hw, fun s c hi => (ho s c hi).mono fun s c h => ?_⟩
  rcases h with h | h | h
  · exact .inl h
  · exact .inl (hs s c h)
  · exact .inr h

theorem mono_pre (h : SegLW W p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegLW W p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), hw, ho⟩

theorem mono_post (h : SegLW W p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegLW W p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h => (ho s c h).mono fun s c h => h.imp_right (hQ s c)⟩

/-- A weaker predicate. -/
theorem mono_W (h : SegLW W p lbl ms P Q) (hW : ∀ s c, W s c → W' s c) : SegLW W' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c h => hW s c (hw s c h), ho⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegLW W p lbl ms P Q) (h' : SegLW W p lbl ms P' Q) :
    SegLW W p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  obtain ⟨i', hs', hw', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c),
    fun s c h => h.elim (hw s c) (hw' s c), ?_⟩
  rintro s c (h | h)
  · exact (ho s c h).mono fun s c h => h.imp_left .inl
  · exact (ho' s c h).mono fun s c h => h.imp_left .inr

/-- **A control-flow graph** of nodes `N i`, each a segment inside `W` to
some node or the exit `X`. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, SegLW W p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    SegLW W p lbl ms (fun s c => ∃ i, N i s c) X := by
  let Inv : Frag I := fun s c => ∃ i, ∃ J : Frag I, (∀ s c, N i s c → J s c) ∧ (∀ s c, J s c → W s c) ∧
      (∀ s c, J s c → OutL p lbl ms (fun s c => J s c ∨ ((∃ j, N j s c) ∨ X s c)) s c) ∧ J s c
  refine ⟨Inv, ?_, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨J, hs, hw, ho⟩ := h i
    exact ⟨i, J, hs, hw, ho, hs s c hi⟩
  · rintro s c ⟨i, J, -, hw, -, hJ⟩
    exact hw s c hJ
  · rintro s c ⟨i, J, hs, hw, ho, hJ⟩
    refine (ho s c hJ).mono fun s c h => ?_
    rcases h with h | ⟨j, hj⟩ | h
    · exact .inl ⟨i, J, hs, hw, ho, h⟩
    · obtain ⟨J', hs', hw', ho'⟩ := h j
      exact .inl ⟨j, J', hs', hw', ho', hs' s c hj⟩
    · exact .inr h

/-- **Ghost parameters.** -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, SegLW W p lbl ms (P g) X) :
    SegLW W p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

/-- **The invariant of a `SegLW` to nothing**: it contains `P`, lies inside
`W`, and is closed under the rows. -/
theorem closed (h : SegLW W p lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧ (∀ s c, inv s c → W s c) ∧
      ∀ s c, inv s c → OutL p lbl ms inv s c := by
  obtain ⟨inv, hP, hw, hi⟩ := h
  exact ⟨inv, hP, hw, fun s c h => (hi s c h).mono fun _ _ h => h.resolve_right id⟩

end SegLW

end Spike.Lib
