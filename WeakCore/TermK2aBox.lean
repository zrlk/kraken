import WeakCore.TermK2aLd

/-!
# TermK2aBox: (R) through boxes (conditional on)

A boxed `case` binds payload words loaded from a box, whose label is not in the store typing, so
`LoadW` does not cover them.  `BoxSep` (the BoxPlantSep, pre-state, staged) bounds the messages
carrying a box payload word naming `a` whose view reaches `a`'s frontier; `BoxLW` is the matching new-word disjunct, and
`StepBX`/`StepOKX` the step contract with it.  `NewW`/`StepB`/`StepOK` are unchanged.
-/

namespace TermK2aBox

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermK2a TermK2aLd
open TermCut (GEnv)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `w` names only labels a payload word `w0` of a box names, `w0`'s view reaches `a`'s frontier when
`w` names `a`, and a message carrying `w0` at its box slot has index `≤ w.rts`. -/
def BoxLW (E : TEnv) (mem : Memory) (a : AllocLabel) (w : Word) : Prop :=
  Names a w → ∃ l B o w0, E.box l = some B ∧ B.pay[o]? = some w0 ∧ Names a w0 ∧
    (∃ f, E.pfr a = some f ∧ f ≤ w0.view) ∧
    ∃ u m, mem[u]? = some m ∧ m.loc = ⟨l, o + 1⟩ ∧ m.val = w0.val ∧ u ≤ w.rts

/-- The binding contract for (R) with box loads. -/
def StepBX (E : TEnv) (sto : Sto) (s : St) (a : AllocLabel) (th th' : TTh) : Prop :=
  ∀ b ∈ Binds th', b ∈ Binds th ∨ ∀ w ∈ pubWords b.2.1 b.2.2,
    OldW a th w ∨ LoadW sto s.mem s.pairs th.promises w ∨ BoxLW E s.mem a w

/-- The step contract with box loads: `StepBX` and `StepOK`'s label half. -/
def StepOKX (E : TEnv) (sto : Sto) (s : St) (a : AllocLabel) (Gl : AllocLabel → Prop) (th th' : TTh) : Prop :=
  StepBX E sto s a th th' ∧
    ∀ b ∈ Binds th', b ∈ Binds th ∨ ∀ w ∈ pubWords b.2.1 b.2.2, ∀ l, Names l w → LblNew Gl th l

theorem stepOKX_of_stepOK {E : TEnv} {sto : Sto} {s : St} {a : AllocLabel} {N Gl : AllocLabel → Prop}
    {th th' : TTh} (h : StepOK sto s a N Gl th th') : StepOKX E sto s a Gl th th' := by
  refine ⟨fun b hb => ?_, h.2⟩
  rcases h.1 b hb with h0 | h1
  · exact .inl h0
  · exact .inr fun w hw => ((h1 w hw).1).elim .inl fun h => .inr (.inl h)

/-- (R) across a step meeting `StepBX`. -/
theorem thRts_of_stepBX {E : TEnv} {sto : Sto} {s : St} {th th' : TTh} {t : Ts} {a : AllocLabel}
    (hR : ThRts t a th) (hC : MemRtsC sto t a s.mem s.pairs th.promises) (hX : BoxSep E t a s.mem)
    (hB : StepBX E sto s a th th') : ThRts t a th' := by
  have hold : ∀ b ∈ Binds th, ∀ w ∈ pubWords b.2.1 b.2.2, Names a w → t ≤ w.rts := by
    intro b hb w hw hn
    unfold Binds at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hR.1 _ _ _ hb w hw hn
    · obtain ⟨f, hf, hbf⟩ := List.mem_flatMap.1 hb
      exact hR.2 f hf _ _ _ hbf w hw hn
  have hall : ∀ b ∈ Binds th', ∀ w ∈ pubWords b.2.1 b.2.2, Names a w → t ≤ w.rts := by
    intro b hb w hw hn
    rcases hB b hb with hb0 | hnew
    · exact hold b hb0 w hw hn
    · rcases hnew w hw with hO | ⟨u, m, cl, hmu, hnp, hcl, hval, hrts, hslot⟩ |
          hBL
      · obtain ⟨b0, hb0, w0, hw0, hn0, hle⟩ := hO hn
        exact Nat.le_trans (hold b0 hb0 w0 hw0 hn0) hle
      · exact Nat.le_trans (hC u m cl hmu hnp hcl (hval a hn) hslot) hrts
      · obtain ⟨l, B, o, w0, hB0, hw0, hn0, ⟨f, hf, hv⟩, u, m, hmu, hloc, hval, hrts⟩ := hBL hn
        rcases hX l B hB0 o w0 hw0 hn0 f hf with h | h
        · exact absurd hv (Nat.not_le_of_gt h)
        · exact Nat.le_trans (h u m hmu hloc hval) hrts
  exact ⟨fun x rt ws hm => hall _ (mem_binds_env hm), fun f hf x rt ws hm => hall _ (mem_binds_stack hf hm)⟩

/-- `ThLbl` across a step meeting `StepOKX`. -/
theorem thLbl_of_stepOKX {E : TEnv} {sto : Sto} {s : St} {a : AllocLabel} {th th' : TTh} {Eg' : GEnv}
    (hL : ThLbl Eg' th) (hB : StepOKX E sto s a (fun l => Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none) th th') :
    ThLbl Eg' th' := by
  have hold : ∀ b ∈ Binds th, ∀ w ∈ pubWords b.2.1 b.2.2, ∀ l, Names l w →
      Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro b hb w hw l hn
    unfold Binds at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hL.1 _ _ _ hb w hw l hn
    · obtain ⟨f, hf, hbf⟩ := List.mem_flatMap.1 hb
      exact hL.2 f hf _ _ _ hbf w hw l hn
  have hall : ∀ b ∈ Binds th', ∀ w ∈ pubWords b.2.1 b.2.2, ∀ l, Names l w →
      Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro b hb w hw l hn
    rcases hB.2 b hb with hb0 | hnew
    · exact hold b hb0 w hw l hn
    · rcases hnew w hw l hn with h | ⟨b0, hb0, w0, hw0, hn0⟩
      · exact h
      · exact hold b0 hb0 w0 hw0 l hn0
  exact ⟨fun x rt ws hm => hall _ (mem_binds_env hm), fun f hf x rt ws hm => hall _ (mem_binds_stack hf hm)⟩

end TermK2aBox

#print axioms TermK2aBox.stepOKX_of_stepOK
#print axioms TermK2aBox.thRts_of_stepBX
#print axioms TermK2aBox.thLbl_of_stepOKX
