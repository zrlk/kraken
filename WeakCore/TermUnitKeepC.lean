import WeakCore.TermPlant

/-! # TermUnitKeepC: an own-path op leaves the untouched units' coherence alone

`unitKeepC_tstep`: at an op with an op atom (`opAtomP`), a step that leaves memory unchanged
moves the coherence view only at units carrying a promise the step discharges.
-/

namespace TermUnitKeepC
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPiece TermPlant
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `loadUnits` leaves coherence alone off the words it reads. -/
theorem loadUnits_cohOff {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      ∀ b, (∀ j, j < nWords us → b ≠ offs a (k + j)) → r.1.vs.coh b = s.vs.coh b
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; intros; rfl
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      intro b hb
      have g := loadUnits_cohOff us (k + 1) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] }
        (s', ws) hmem b fun j hj => by
          have := hb (j + 1) (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega)
          rw [show k + (j + 1) = k + 1 + j by omega] at this; exact this
      refine g.trans ?_
      have hb0 : b ≠ offs a k := by
        have := hb 0 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega)
        rw [Nat.add_zero] at this; exact this
      exact stepLoad_cohOther hth b hb0
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      intro b hb
      have g := loadUnits_cohOff us (k + 2)
        { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] } (s', ws) hmem b
        fun j hj => by
          have := hb (j + 2) (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega)
          rw [show k + (j + 2) = k + 2 + j by omega] at this; exact this
      refine g.trans ?_
      have hb0 : b ≠ offs a k := by
        have := hb 0 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega)
        rw [Nat.add_zero] at this; exact this
      have hb1 : b ≠ (offs a k).next := by
        have := hb 1 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega)
        intro e; apply this; rw [e]; rfl
      exact stepLoadPair_cohOther hth b hb0 hb1
#print axioms TermUnitKeepC.loadUnits_cohOff

/-- `loadUnits` keeps memory and promises. -/
theorem loadUnits_keepMP {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.mem = s.mem ∧ r.1.promises = s.promises
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; exact ⟨rfl, rfl⟩
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_keepMP us (k + 1) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] } (s', ws) hmem
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      exact loadUnits_keepMP us (k + 2) { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] } (s', ws) hmem
#print axioms TermUnitKeepC.loadUnits_keepMP

/-- The shape of an own-path op's outcome: an optional read of the units, then a store of
them. -/
def LS (s s' : St) : Prop :=
  ∃ (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool) (us : List Acc) (ws : List Word) (s1 : St),
    s1.mem = s.mem ∧ s1.promises = s.promises ∧
    (∀ b, (∀ j, j < nWords us → b ≠ offs a (0 + j)) → s1.vs.coh b = s.vs.coh b) ∧
    s' ∈ storeUnits k arch pw a rel us ws 0 s1

theorem LS_store {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} {us : List Acc}
    {ws : List Word} {s s' : St} (h : s' ∈ storeUnits k arch pw a rel us ws 0 s) : LS s s' :=
  ⟨k, arch, pw, a, rel, us, ws, s, rfl, rfl, fun _ _ => rfl, h⟩

theorem LS_rmw {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} {us : List Acc}
    {ws : List Word} {s s' : St} {r1 : St × List Word} (h1 : r1 ∈ loadUnits arch pw a false us 0 s)
    (h : s' ∈ storeUnits k arch pw a rel us ws 0 r1.1) : LS s s' := by
  obtain ⟨e1, e3⟩ := loadUnits_keepMP us 0 s r1 h1
  exact ⟨k, arch, pw, a, rel, us, ws, r1.1, e1, e3, loadUnits_cohOff us 0 s r1 h1, h⟩

/-- **Coherence of the untouched units**: in the `LS` shape, with memory unchanged, the
coherence view moves only at units carrying a discharged promise. -/
theorem LS_cohKeep {s s' : St} (h : LS s s') (hnd : s.promises.Nodup) (hmem : s'.mem = s.mem) :
    ∀ b, (∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ b) →
      s'.vs.coh b = s.vs.coh b := by
  obtain ⟨k, arch, pw, a, rel, us, ws, s1, e1, e2, hc1, hs⟩ := h
  have hnd1 : s1.promises.Nodup := by rw [e2]; exact hnd
  obtain ⟨-, -, F, hFl, -, hco, -, hFj⟩ := storeUnits_fulAll us ws 0 s1 s' hnd1 hs
    (by rw [hmem, e1]; exact Nat.le_refl _)
  intro b hb
  have hoff : ∀ j, j < nWords us → b ≠ offs a (0 + j) := by
    intro j hj e
    obtain ⟨t, ht⟩ : ∃ t, F[j]? = some t := ⟨F[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨h1, h2, m, w, hm, -, hl, -⟩ := hFj j t ht
    rw [e2] at h1
    rw [e1] at hm
    exact hb t m h1 h2 hm (hl.trans e.symm)
  rw [hco b hoff, hc1 b hoff]
#print axioms TermUnitKeepC.LS_cohKeep

theorem opAtom_shapes {t : Expr} (h : (opAtomP t).isSome = true) :
    ∃ x op e, t = .let_ x op e ∧ ((∃ a v, op = .xchg a v) ∨ (∃ b i v, op = .xchgAt b i v) ∨
      (∃ b i q v, op = .xchgAtF b i q v) ∨ (∃ b wi jl v, op = .stlw b wi jl v) ∨ (∃ b i v, op = .stl b i v) ∨
      (∃ b i v, op = .bufInit b i v) ∨ (∃ rel a v tok, op = .store rel a v tok)) := by
  unfold opAtomP at h
  split at h
  · exact ⟨_, _, _, rfl, .inl ⟨_, _, rfl⟩⟩
  · exact ⟨_, _, _, rfl, .inr (.inl ⟨_, _, _, rfl⟩)⟩
  · exact ⟨_, _, _, rfl, .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))⟩
  · exact ⟨_, _, _, rfl, .inr (.inr (.inr (.inl ⟨_, _, _, _, rfl⟩)))⟩
  · exact ⟨_, _, _, rfl, .inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))⟩
  · exact ⟨_, _, _, rfl, .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))))⟩
  · exact ⟨_, _, _, rfl, .inr (.inr (.inr (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩)))))⟩
  · cases h
#print axioms TermUnitKeepC.opAtom_shapes

/-- **The outcome shape of an op-atom step**: a read (or nothing) then a store. -/
theorem tstep_LS {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hq : (opAtomP th.term).isSome = true) (hr : r ∈ tstep g mem pairs th) :
    ∃ s', LS (stOf mem pairs th) s' ∧ r.1 = s'.mem ∧ r.2.2.vs = s'.vs ∧ r.2.2.promises = s'.promises := by
  obtain ⟨x, op, e, ht, hop⟩ := opAtom_shapes hq
  have hr' : r ∈ (evalOp g th.env th.σs (stOf mem pairs th) op).map fun (s', t, ws) =>
      (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    rcases hop with ⟨a, v, rfl⟩ | ⟨b, i, v, rfl⟩ | ⟨b, i, q, v, rfl⟩ | ⟨b, wi, jl, v, rfl⟩ | ⟨b, i, v, rfl⟩ |
        ⟨b, i, v, rfl⟩ | ⟨rel, a, v, tok, rfl⟩ <;>
      (simp only [tstep, ht] at hr; exact hr)
  rw [List.mem_map] at hr'
  obtain ⟨⟨s', t', ws'⟩, hin, rfl⟩ := hr'
  refine ⟨s', ?_, rfl, rfl, rfl⟩
  rcases hop with ⟨a, v, rfl⟩ | ⟨b, i, v, rfl⟩ | ⟨b, i, q, v, rfl⟩ | ⟨b, wi, jl, v, rfl⟩ | ⟨b, i, v, rfl⟩ |
      ⟨b, i, v, rfl⟩ | ⟨rel, a, v, tok, rfl⟩ <;>
    simp only [evalOp] at hin <;>
    repeat' (split at hin)
  all_goals first
    | (simp at hin; done)
    | (obtain ⟨s2, h2, he⟩ := List.mem_map.1 hin; cases he; exact LS_store h2)
    | (obtain ⟨⟨s1, old⟩, h1, hin2⟩ := List.mem_flatMap.1 hin
       obtain ⟨s2, h2, he⟩ := List.mem_map.1 hin2; cases he; exact LS_rmw h1 h2)
    | (obtain ⟨⟨s1, old⟩, h1, hin2⟩ := List.mem_flatMap.1 hin
       simp only at hin2
       split at hin2
       · obtain ⟨s2, h2, he⟩ := List.mem_map.1 hin2; cases he; exact LS_rmw h1 h2
       · simp at hin2)
#print axioms TermUnitKeepC.tstep_LS

end TermUnitKeepC
