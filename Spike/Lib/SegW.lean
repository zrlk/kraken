/-
**Segments with a state predicate on the hidden invariant** (`SegW`).

`Seg p lbl ms P Q` (`Spike/Lib/Seg.lean`) hides its invariant: nothing is
known of the pairs inside the segment beyond their `Out` rows. The one-thread
consumer's node obligations (`Nodes`: no pair at `ret`, single-word cells,
the environment placed, no pair at the release site, the owned words kept)
are facts about *every* pair of the fragment, so a whole-program fragment
built as the hidden invariant of one composed segment needs them of the
hidden pairs too, including a block's internal states and a callee's.

`SegW W K p lbl ms P Q` is `Seg` with the hidden invariant inside `W` and
closed under the **outside moves** `K`: a relation on machine states, a
step the thread takes instead of its instruction (the kernel's take of a
stack range at the take site: the range copied into private memory, the
`nop` skipped). From every pair of the invariant, every `K`-successor of
its state lands, after a local run of the source, in the invariant or the
exit (`KOut`), and a pair `K` does not move steps (`Out`) there; at a state
`K` moves, its instruction is not run and no `Out` is asked. A segment none
of whose pairs `K` moves (`step`: `∀ s', ¬ K s s'` with `W`) is a `Seg`
step; a node at which `K` does move (the take) gives the landing itself
(`stepK`).

Its combinators are `Seg`'s (`step`, `seq`, `loop`, `seq_left`, `cfg`,
`exists_pre`, monotonicity) with `W` and `K` fixed; `SegW.toSeg` forgets
`W` with no outside moves, `SegW.ofSeg` makes a `Seg` one at `W := True`,
`K := False`,
and `SegW.inv` names the invariant with its properties (the fragment a
consumer takes).
-/
import Spike.Lib.Seg

namespace Spike.Lib

open Kraken.Promising

/-- **Every outside move lands in `X`**: every `K`-successor `s'` of `s`
is in `X`, with the source control after a local run from `c`. -/
def KOut {I : ISA} (K : I.State → I.State → Prop) (p : CoreTerm.Prog) (X : Frag I) (s : I.State) (c : Ctl) :
    Prop :=
  ∀ s', K s s' → ∃ c', LocalRun p c c' ∧ X s' c'

theorem KOut.mono {I : ISA} {K : I.State → I.State → Prop} {p : CoreTerm.Prog} {X Y : Frag I} {s : I.State}
    {c : Ctl} (h : KOut K p X s c) (hXY : ∀ s c, X s c → Y s c) : KOut K p Y s c :=
  fun s' hk => let ⟨c', hr, hx⟩ := h s' hk; ⟨c', hr, hXY _ _ hx⟩

/-- No outside move from `s`. -/
theorem KOut.none {I : ISA} {K : I.State → I.State → Prop} {p : CoreTerm.Prog} {X : Frag I} {s : I.State}
    {c : Ctl} (h : ∀ s', ¬ K s s') : KOut K p X s c :=
  fun s' hk => (h s' hk).elim

/-- **Segment simulation inside `W`, closed under `K`**: every pair of `P`
lies in an invariant inside `W` whose every outside move (`K`) lands in the
invariant or the exit `Q` (`KOut`), and whose pairs `K` does not move step
(`Out`) there. -/
def SegW {I : ISA} (W : Frag I) (K : I.State → I.State → Prop) (p : CoreTerm.Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧ (∀ s c, inv s c → W s c) ∧
    ∀ s c, inv s c → ((∀ s', ¬ K s s') → Out p lbl ms (fun s c => inv s c ∨ Q s c) s c) ∧
      KOut K p (fun s c => inv s c ∨ Q s c) s c

/-- The closure of a `SegW` invariant, moved along `X ⊆ Y`. -/
theorem kout_out_mono {I : ISA} {K : I.State → I.State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {X Y : Frag I} {s : I.State} {c : Ctl}
    (h : ((∀ s', ¬ K s s') → Out p lbl ms X s c) ∧ KOut K p X s c) (hXY : ∀ s c, X s c → Y s c) :
    ((∀ s', ¬ K s s') → Out p lbl ms Y s c) ∧ KOut K p Y s c :=
  ⟨fun hk => (h.1 hk).mono hXY, h.2.mono hXY⟩

namespace SegW

variable {I : ISA} {W W' : Frag I} {K K' : I.State → I.State → Prop} {p : CoreTerm.Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {P P' Q Q' R : Frag I}

/-- Forget `W`, with no outside moves. -/
theorem toSeg (h : SegW W (fun _ _ => False) p lbl ms P Q) : Seg p lbl ms P Q :=
  let ⟨i, hs, _, ho⟩ := h
  ⟨i, hs, fun s c h => (ho s c h).1 fun _ h => h⟩

/-- A segment is one inside the trivial predicate, with no outside moves. -/
theorem ofSeg (h : Seg p lbl ms P Q) : SegW (fun _ _ => True) (fun _ _ => False) p lbl ms P Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun _ _ _ => trivial, fun s c h => ⟨fun _ => ho s c h, KOut.none fun _ h => h⟩⟩

/-- **One instruction, with its outside moves**: from every pair of `P`,
inside `W`, every outside move lands in `Q`, and where there is none the
instruction does. -/
theorem stepK (hW : ∀ s c, P s c → W s c)
    (h : ∀ s c, P s c → ((∀ s', ¬ K s s') → Out p lbl ms Q s c) ∧ KOut K p Q s c) :
    SegW W K p lbl ms P Q :=
  ⟨P, fun _ _ h => h, hW, fun s c hp => kout_out_mono (h s c hp) fun _ _ h => .inr h⟩

/-- **One instruction** from every pair of `P`, inside `W` and not moved by
`K`, into `Q`. -/
theorem step (hW : ∀ s c, P s c → W s c ∧ ∀ s', ¬ K s s') (h : ∀ s c, P s c → Out p lbl ms Q s c) :
    SegW W K p lbl ms P Q :=
  stepK (fun s c hp => (hW s c hp).1) fun s c hp => ⟨fun _ => h s c hp, KOut.none (hW s c hp).2⟩

/-- **Sequencing.** -/
theorem seq (h₁ : SegW W K p lbl ms P Q) (h₂ : SegW W K p lbl ms Q R) : SegW W K p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), fun s c h => h.elim (hw₁ s c) (hw₂ s c), ?_⟩
  have m₁ : ∀ s c, (i₁ s c ∨ Q s c) → (i₁ s c ∨ i₂ s c) ∨ R s c :=
    fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  have m₂ : ∀ s c, (i₂ s c ∨ R s c) → (i₁ s c ∨ i₂ s c) ∨ R s c :=
    fun s c h => h.elim (fun h => .inl (.inr h)) .inr
  rintro s c (h | h)
  · exact kout_out_mono (ho₁ s c h) m₁
  · exact kout_out_mono (ho₂ s c h) m₂

/-- **A tail-call loop.** -/
theorem loop {H X : Frag I} (h : SegW W K p lbl ms H (fun s c => H s c ∨ X s c)) : SegW W K p lbl ms H X := by
  obtain ⟨i, hs, hw, ho⟩ := h
  have m : ∀ s c, (i s c ∨ H s c ∨ X s c) → i s c ∨ X s c := fun s c h => by
    rcases h with h | h | h
    · exact .inl h
    · exact .inl (hs s c h)
    · exact .inr h
  exact ⟨i, hs, hw, fun s c hi => kout_out_mono (ho s c hi) m⟩

/-- **A segment from no state.** -/
theorem empty (h : ∀ s c, ¬ P s c) : SegW W K p lbl ms P Q :=
  ⟨fun _ _ => False, fun s c hP => h s c hP, fun _ _ h => h.elim, fun _ _ h => h.elim⟩

theorem mono_pre (h : SegW W K p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegW W K p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), hw, ho⟩

theorem mono_post (h : SegW W K p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegW W K p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h => kout_out_mono (ho s c h) fun s c h => h.imp_right (hQ s c)⟩

/-- A weaker predicate. -/
theorem mono_W (h : SegW W K p lbl ms P Q) (hW : ∀ s c, W s c → W' s c) : SegW W' K p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, fun s c h => hW s c (hw s c h), ho⟩

/-- The same outside moves, at the invariant's states (`K'` moves a state
of `W` exactly as `K` does). -/
theorem mono_K (h : SegW W K p lbl ms P Q) (hK : ∀ s c, W s c → ∀ s', K' s s' ↔ K s s') :
    SegW W K' p lbl ms P Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c h =>
    ⟨fun hn => (ho s c h).1 fun s' hk => hn s' ((hK s c (hw s c h) s').2 hk),
      fun s' hk => (ho s c h).2 s' ((hK s c (hw s c h) s').1 hk)⟩⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegW W K p lbl ms P Q) (h' : SegW W K p lbl ms P' Q) :
    SegW W K p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  obtain ⟨i', hs', hw', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c),
    fun s c h => h.elim (hw s c) (hw' s c), ?_⟩
  rintro s c (h | h)
  · exact kout_out_mono (ho s c h) fun s c h => h.imp_left .inl
  · exact kout_out_mono (ho' s c h) fun s c h => h.imp_left .inr

/-- Continue the normal exit `Q` with a segment to `R`, keeping a second
exit `E` as it is. -/
theorem seq_left {E : Frag I} (h₁ : SegW W K p lbl ms P (fun s c => Q s c ∨ E s c)) (h₂ : SegW W K p lbl ms Q R) :
    SegW W K p lbl ms P (fun s c => R s c ∨ E s c) := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), fun s c h => h.elim (hw₁ s c) (hw₂ s c), ?_⟩
  have m₁ : ∀ s c, (i₁ s c ∨ Q s c ∨ E s c) → (i₁ s c ∨ i₂ s c) ∨ R s c ∨ E s c := fun s c h => by
    rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr (hs₂ s c h))
    · exact .inr (.inr h)
  have m₂ : ∀ s c, (i₂ s c ∨ R s c) → (i₁ s c ∨ i₂ s c) ∨ R s c ∨ E s c :=
    fun s c h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)
  rintro s c (h | h)
  · exact kout_out_mono (ho₁ s c h) m₁
  · exact kout_out_mono (ho₂ s c h) m₂

/-- **A control-flow graph** of nodes `N i`, each a segment inside `W`
closed under `K` to some node or the exit `X`. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, SegW W K p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    SegW W K p lbl ms (fun s c => ∃ i, N i s c) X := by
  let Y : Frag I → Frag I := fun J s c => J s c ∨ ((∃ j, N j s c) ∨ X s c)
  let Inv : Frag I := fun s c => ∃ i, ∃ J : Frag I, (∀ s c, N i s c → J s c) ∧ (∀ s c, J s c → W s c) ∧
      (∀ s c, J s c → ((∀ s', ¬ K s s') → Out p lbl ms (Y J) s c) ∧ KOut K p (Y J) s c) ∧ J s c
  refine ⟨Inv, ?_, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨J, hs, hw, ho⟩ := h i
    exact ⟨i, J, hs, hw, ho, hs s c hi⟩
  · rintro s c ⟨i, J, -, hw, -, hJ⟩
    exact hw s c hJ
  · rintro s c ⟨i, J, hs, hw, ho, hJ⟩
    have m : ∀ s c, Y J s c → Inv s c ∨ X s c := fun s c h => by
      rcases h with h | ⟨j, hj⟩ | h
      · exact .inl ⟨i, J, hs, hw, ho, h⟩
      · obtain ⟨J', hs', hw', ho'⟩ := h j
        exact .inl ⟨j, J', hs', hw', ho', hs' s c hj⟩
      · exact .inr h
    exact kout_out_mono (ho s c hJ) m

/-- **Ghost parameters.** -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, SegW W K p lbl ms (P g) X) :
    SegW W K p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

/-- **The invariant of a segment to nowhere**: a fragment containing `P`,
inside `W`, every outside move of it landing in it and every pair of it `K`
does not move stepping into it. This is the fragment a whole-program proof takes
(`Nodes.out` with the other node obligations read off `W`). -/
theorem inv (h : SegW W K p lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧ (∀ s c, inv s c → W s c) ∧
      ∀ s c, inv s c → ((∀ s', ¬ K s s') → Out p lbl ms inv s c) ∧ KOut K p inv s c := by
  obtain ⟨i, hs, hw, ho⟩ := h
  exact ⟨i, hs, hw, fun s c h => kout_out_mono (ho s c h) fun _ _ h => h.elim id False.elim⟩

end SegW

end Spike.Lib
