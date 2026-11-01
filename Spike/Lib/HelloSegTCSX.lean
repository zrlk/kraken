/-
**The worker's segments at any call depth, with a fact at every landing pair** (hello.w, row 5j-wit-W; the
landing-placed variant of `Spike/Lib/HelloSegTCS.lean`'s `SegTCS`): a segment whose rows land, with a pending
frame run, in its invariant or exit, **and** in a fragment `X` at the landing pair itself; its invariant inside
`X`. `SegTCS.closed`'s invariant `Pend p inv` only knows `S` at the end of each pending run; here the closed
invariant `X ∧ Pend p inv` lies inside `X` (for `X := PlacedSE …`, the worker's invariant places every frame,
`HelloPostWit.post_wit_hello`'s `hplW`).

- `SegTCSX S X p lbl ms P Q`: the invariant inside `S` and `X`, each row into `X ∧ Pend p (inv ∨ Q)`.
- `toS`: the plain `SegTCS` (forgetting `X`); `ofS`: a plain `SegTCS` at `X := True`.
- `ofTC`, `liftL` (flat segments, the invariant and the exit in `X`), `step`, `seq`, `mono_pre`, `mono_post`,
  `mono_S`, `or_pre`, `empty`, `cfg`, `exists_pre`, `pre_run` (the entry's pairs in `X`), `post_run`, `conjS`:
  as `SegTCS`'s.
- `closedX`, `closed_conjSX`: the closed invariant of a segment to the empty fragment, inside `X`.
-/
import Spike.Lib.HelloSegTCS

namespace Spike.Lib.HelloSegTCSX

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib Spike.Lib.HelloSegThrS Spike.Lib.HelloSegTCS

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}

/-- **A segment whose invariant lies inside `S` and `X`, each row landing in `X`** with a pending frame run in
the invariant or `Q`. -/
def SegTCSX (S X : FragS I) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide I)
    (P Q : FragS I) : Prop :=
  ∃ inv : FragS I, (∀ s c fs, P s c fs → inv s c fs) ∧ (∀ s c fs, inv s c fs → S s c fs) ∧
    (∀ s c fs, inv s c fs → X s c fs) ∧
    ∀ s c fs, inv s c fs → OutTS p lbl ms (fun s c fs => X s c fs ∧ Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs)
      s c fs

namespace SegTCSX

variable {S S' X : FragS I} {P P' Q Q' R : FragS I}

/-- The plain segment. -/
theorem toS (h : SegTCSX S X p lbl ms P Q) : SegTCS S p lbl ms P Q :=
  let ⟨inv, hs, hw, _, ho⟩ := h
  ⟨inv, hs, hw, fun s c fs h => (ho s c fs h).mono fun _ _ _ h => h.2⟩

/-- **A plain segment is a segment landing in the trivial fragment** (`toS`'s converse at `X := True`): its
invariant and every landing pair lie in `fun _ _ _ => True`. The consumers stated over `SegTCSX` take a plain
`SegTCS` segment through this. -/
theorem ofS (h : SegTCS S p lbl ms P Q) : SegTCSX S (fun _ _ _ => True) p lbl ms P Q :=
  let ⟨inv, hs, hw, ho⟩ := h
  ⟨inv, hs, hw, fun _ _ _ _ => trivial, fun s c fs h => (ho s c fs h).mono fun _ _ _ h => ⟨trivial, h⟩⟩

/-- **A flat segment at depth `0`**, its fragment and exit in `X` at no frames. -/
theorem ofTC {S₀ P₀ Q₀ : Frag I} (h : SegTC S₀ p lbl (ms []) P₀ Q₀) (hS : ∀ s c, S₀ s c → S s c [])
    (hX : ∀ s c, S₀ s c → X s c []) (hQ : ∀ s c, Q₀ s c → X s c []) :
    SegTCSX S X p lbl ms (P₀.at []) (Q₀.at []) := by
  obtain ⟨inv, hP, hiS, ho⟩ := h
  refine ⟨inv.at [], fun s c fs ⟨h, e⟩ => ⟨hP s c h, e⟩, fun s c fs ⟨h, e⟩ => e ▸ hS s c (hiS s c h),
    fun s c fs ⟨h, e⟩ => e ▸ hX s c (hiS s c h), ?_⟩
  rintro s c fs ⟨hi, rfl⟩
  refine OutTS.ofT ((ho s c hi).mono fun s c h => ⟨h.elim (fun h => hX s c (hiS s c h)) (hQ s c), ?_⟩)
  exact Pend.of (h.imp (fun h => ⟨h, rfl⟩) fun h => ⟨h, rfl⟩)

/-- **A flat segment at frames `fs`**, its fragment's pairs `NoTop`, its fragment and exit in `X` at `fs`. -/
theorem liftL {S₀ P₀ Q₀ : Frag I} (fs : List TermRun.Frame) (h : SegTC S₀ p lbl (ms fs) P₀ Q₀)
    (hS : ∀ s c, S₀ s c → S s c fs) (hn : ∀ s c, S₀ s c → NoTop (ms fs) s c)
    (hX : ∀ s c, S₀ s c → X s c fs) (hQ : ∀ s c, Q₀ s c → X s c fs) :
    SegTCSX S X p lbl ms (P₀.at fs) (Q₀.at fs) := by
  obtain ⟨inv, hP, hiS, ho⟩ := h
  refine ⟨inv.at fs, fun s c fs' ⟨h, e⟩ => ⟨hP s c h, e⟩, fun s c fs' ⟨h, e⟩ => e ▸ hS s c (hiS s c h),
    fun s c fs' ⟨h, e⟩ => e ▸ hX s c (hiS s c h), ?_⟩
  rintro s c fs' ⟨hi, rfl⟩
  refine OutT.toTS ((ho s c hi).mono fun s c h => ⟨h.elim (fun h => hX s c (hiS s c h)) (hQ s c), ?_⟩)
    (hn s c (hiS s c hi))
  exact Pend.of (h.imp (fun h => ⟨h, rfl⟩) fun h => ⟨h, rfl⟩)

/-- **One instruction** from every pair of `P`, inside `S` and `X`, into `X ∧ Q`. -/
theorem step (hS : ∀ s c fs, P s c fs → S s c fs) (hX : ∀ s c fs, P s c fs → X s c fs)
    (h : ∀ s c fs, P s c fs → OutTS p lbl ms (fun s c fs => X s c fs ∧ Q s c fs) s c fs) :
    SegTCSX S X p lbl ms P Q :=
  ⟨P, fun _ _ _ h => h, hS, hX, fun s c fs hp => (h s c fs hp).mono fun _ _ _ h => ⟨h.1, Pend.of (.inr h.2)⟩⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegTCSX S X p lbl ms P Q) (h₂ : SegTCSX S X p lbl ms Q R) : SegTCSX S X p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, hx₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, hx₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), fun s c fs h => h.elim (hx₁ s c fs) (hx₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact (ho₁ s c fs h).mono fun s c fs h => ⟨h.1, h.2.mono fun s c fs h =>
      h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c fs h))⟩
  · exact (ho₂ s c fs h).mono fun s c fs h => ⟨h.1, h.2.mono fun s c fs h => h.elim (fun h => .inl (.inr h)) .inr⟩

theorem mono_pre (h : SegTCSX S X p lbl ms P Q) (hP : ∀ s c fs, P' s c fs → P s c fs) :
    SegTCSX S X p lbl ms P' Q :=
  let ⟨i, hs, hw, hx, ho⟩ := h
  ⟨i, fun s c fs h => hs s c fs (hP s c fs h), hw, hx, ho⟩

theorem mono_post (h : SegTCSX S X p lbl ms P Q) (hQ : ∀ s c fs, Q s c fs → Q' s c fs) :
    SegTCSX S X p lbl ms P Q' :=
  let ⟨i, hs, hw, hx, ho⟩ := h
  ⟨i, hs, hw, hx, fun s c fs h => (ho s c fs h).mono fun _ _ _ h =>
    ⟨h.1, h.2.mono fun s c fs h => h.imp_right (hQ s c fs)⟩⟩

/-- A weaker fragment `S`. -/
theorem mono_S (h : SegTCSX S X p lbl ms P Q) (hS : ∀ s c fs, S s c fs → S' s c fs) : SegTCSX S' X p lbl ms P Q :=
  let ⟨i, hs, hw, hx, ho⟩ := h
  ⟨i, hs, fun s c fs h => hS s c fs (hw s c fs h), hx, ho⟩

/-- A weaker landing fragment `X`. -/
theorem mono_X {X' : FragS I} (h : SegTCSX S X p lbl ms P Q) (hX : ∀ s c fs, X s c fs → X' s c fs) :
    SegTCSX S X' p lbl ms P Q :=
  let ⟨i, hs, hw, hx, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h => hX s c fs (hx s c fs h), fun s c fs h => (ho s c fs h).mono fun s c fs h =>
    ⟨hX s c fs h.1, h.2⟩⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegTCSX S X p lbl ms P Q) (h' : SegTCSX S X p lbl ms P' Q) :
    SegTCSX S X p lbl ms (fun s c fs => P s c fs ∨ P' s c fs) Q := by
  obtain ⟨i, hs, hw, hx, ho⟩ := h
  obtain ⟨i', hs', hw', hx', ho'⟩ := h'
  refine ⟨fun s c fs => i s c fs ∨ i' s c fs, fun s c fs h => h.imp (hs s c fs) (hs' s c fs),
    fun s c fs h => h.elim (hw s c fs) (hw' s c fs), fun s c fs h => h.elim (hx s c fs) (hx' s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact (ho s c fs h).mono fun _ _ _ h => ⟨h.1, h.2.mono fun _ _ _ h => h.imp_left .inl⟩
  · exact (ho' s c fs h).mono fun _ _ _ h => ⟨h.1, h.2.mono fun _ _ _ h => h.imp_left .inr⟩

/-- A segment from nowhere. -/
theorem empty (h : ∀ s c fs, ¬ P s c fs) : SegTCSX S X p lbl ms P Q :=
  ⟨fun _ _ _ => False, fun s c fs hP => h s c fs hP, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim,
    fun _ _ _ h => h.elim⟩

/-- **A control-flow graph** of nodes `N i`, each a segment to some node or the exit `E`. -/
theorem cfg {ι : Sort _} (N : ι → FragS I) {E : FragS I}
    (h : ∀ i, SegTCSX S X p lbl ms (N i) (fun s c fs => (∃ j, N j s c fs) ∨ E s c fs)) :
    SegTCSX S X p lbl ms (fun s c fs => ∃ i, N i s c fs) E := by
  let Inv : FragS I := fun s c fs => ∃ i, ∃ J : FragS I, (∀ s c fs, N i s c fs → J s c fs) ∧
      (∀ s c fs, J s c fs → S s c fs) ∧ (∀ s c fs, J s c fs → X s c fs) ∧
      (∀ s c fs, J s c fs → OutTS p lbl ms (fun s c fs => X s c fs ∧
        Pend p (fun s c fs => J s c fs ∨ ((∃ j, N j s c fs) ∨ E s c fs)) s c fs) s c fs) ∧
      J s c fs
  refine ⟨Inv, ?_, ?_, ?_, ?_⟩
  · rintro s c fs ⟨i, hi⟩
    obtain ⟨J, hs, hw, hx, ho⟩ := h i
    exact ⟨i, J, hs, hw, hx, ho, hs s c fs hi⟩
  · rintro s c fs ⟨i, J, -, hw, -, -, hJ⟩
    exact hw s c fs hJ
  · rintro s c fs ⟨i, J, -, -, hx, -, hJ⟩
    exact hx s c fs hJ
  · rintro s c fs ⟨i, J, hs, hw, hx, ho, hJ⟩
    refine (ho s c fs hJ).mono fun s c fs hx' => ⟨hx'.1, hx'.2.mono fun s c fs hx' => ?_⟩
    rcases hx' with hx' | ⟨j, hj⟩ | hx'
    · exact .inl ⟨i, J, hs, hw, hx, ho, hx'⟩
    · obtain ⟨J', hs', hw', hx'', ho'⟩ := h j
      exact .inl ⟨j, J', hs', hw', hx'', ho', hs' s c fs hj⟩
    · exact .inr hx'

/-- **Ghost parameters.** -/
theorem exists_pre {γ : Sort _} {P : γ → FragS I} (h : ∀ g, SegTCSX S X p lbl ms (P g) Q) :
    SegTCSX S X p lbl ms (fun s c fs => ∃ g, P g s c fs) Q :=
  cfg P fun g => (h g).mono_post fun _ _ _ h => .inr h

/-- **A frame run before a segment, at the entry**: every pair of `P` inside `S` and `X`, with a pending frame
run to `P'`. -/
theorem pre_run (h : SegTCSX S X p lbl ms P' Q)
    (hP : ∀ s c fs, P s c fs → S s c fs ∧ X s c fs ∧ Pend p P' s c fs) : SegTCSX S X p lbl ms P Q := by
  obtain ⟨inv, hs, hw, hx, ho⟩ := h
  refine ⟨fun s c fs => inv s c fs ∨ P s c fs, fun s c fs h => .inr h,
    fun s c fs h => h.elim (hw s c fs) fun h => (hP s c fs h).1,
    fun s c fs h => h.elim (hx s c fs) fun h => (hP s c fs h).2.1, ?_⟩
  have hX : ∀ s c fs, X s c fs ∧ Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs →
      X s c fs ∧ Pend p (fun s c fs => (inv s c fs ∨ P s c fs) ∨ Q s c fs) s c fs :=
    fun s c fs h => ⟨h.1, h.2.mono fun _ _ _ h => h.imp_left .inl⟩
  rintro s c fs (h | h)
  · exact (ho s c fs h).mono hX
  · obtain ⟨c', fs', hr, h'⟩ := (hP s c fs h).2.2
    exact ((ho s c' fs' (hs s c' fs' h')).run hr).mono hX

/-- **A frame run after a segment**: a segment to the pairs with a pending frame run to `Q` is one to `Q`. -/
theorem post_run (h : SegTCSX S X p lbl ms P (Pend p Q)) : SegTCSX S X p lbl ms P Q :=
  let ⟨inv, hs, hw, hx, ho⟩ := h
  ⟨inv, hs, hw, hx, fun s c fs hi => (ho s c fs hi).mono fun _ _ _ h => ⟨h.1, h.2.or_pend⟩⟩

/-- **A kept state predicate along a segment.** -/
theorem conjS {S' : I.State → Prop} (h : SegTCSX S X p lbl ms P Q) (hE : ExecKeeps I S')
    (hK : ∀ fs, KernKeeps (ms fs) S') :
    SegTCSX (fun s c fs => S s c fs ∧ S' s) X p lbl ms (fun s c fs => P s c fs ∧ S' s)
      (fun s c fs => Q s c fs ∧ S' s) := by
  obtain ⟨i, hs, hw, hx, ho⟩ := h
  refine ⟨fun s c fs => i s c fs ∧ S' s, fun s c fs h => ⟨hs s c fs h.1, h.2⟩,
    fun s c fs h => ⟨hw s c fs h.1, h.2⟩, fun s c fs h => hx s c fs h.1, fun s c fs h => ?_⟩
  refine ((ho s c fs h.1).conjS h.2 hE hK).mono fun s c fs ⟨⟨hX, c', fs', hr, h⟩, hS⟩ => ?_
  exact ⟨hX, c', fs', hr, h.imp (fun h => ⟨h, hS⟩) fun h => ⟨h, hS⟩⟩

/-- **The closed invariant inside `X`** of a segment to the empty fragment: the pairs in `X` with a pending
frame run into the hidden invariant, closed under the rows (`OutTS.run`), each with a pending frame run into
`S`. -/
theorem closedX (h : SegTCSX S X p lbl ms P (fun _ _ _ => False)) :
    ∃ Wi : FragS I, (∀ s c fs, P s c fs → Wi s c fs) ∧
      (∀ s c fs, Wi s c fs → Pend p S s c fs ∧ X s c fs) ∧ ∀ s c fs, Wi s c fs → OutTS p lbl ms Wi s c fs := by
  obtain ⟨inv, hP, hS, hX, ho⟩ := h
  refine ⟨fun s c fs => X s c fs ∧ Pend p inv s c fs,
    fun s c fs h => ⟨hX s c fs (hP s c fs h), Pend.of (hP s c fs h)⟩,
    fun s c fs h => ⟨h.2.mono hS, h.1⟩, ?_⟩
  rintro s c fs ⟨-, c', fs', hr, hi⟩
  exact ((ho s c' fs' hi).run hr).mono fun _ _ _ h => ⟨h.1, h.2.mono fun _ _ _ h => h.resolve_right id⟩

/-- **The closed invariant inside `X` with a kept state predicate `S'`**, from the entry's pairs in `S'`. -/
theorem closed_conjSX {S' : I.State → Prop} (h : SegTCSX S X p lbl ms P (fun _ _ _ => False))
    (hE : ExecKeeps I S') (hK : ∀ fs, KernKeeps (ms fs) S') :
    ∃ Wi : FragS I, (∀ s c fs, P s c fs → S' s → Wi s c fs) ∧
      (∀ s c fs, Wi s c fs → Pend p S s c fs ∧ S' s ∧ X s c fs) ∧
      ∀ s c fs, Wi s c fs → OutTS p lbl ms Wi s c fs := by
  obtain ⟨Wi, hP, hS, ho⟩ := ((h.conjS hE hK).mono_post fun _ _ _ h => h.1).closedX
  exact ⟨Wi, fun s c fs h h' => hP s c fs ⟨h, h'⟩, fun s c fs h =>
    ⟨(hS s c fs h).1.mono fun _ _ _ h => h.1, Pend.state ((hS s c fs h).1.mono fun _ _ _ h => h.2),
      (hS s c fs h).2⟩, ho⟩

end SegTCSX

end Spike.Lib.HelloSegTCSX

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.closedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.closedX

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.closed_conjSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.closed_conjSX

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.pre_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.pre_run

/-- info: 'Spike.Lib.HelloSegTCSX.SegTCSX.cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegTCSX.SegTCSX.cfg
