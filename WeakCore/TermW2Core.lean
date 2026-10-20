import WeakCore.TermPlantS

namespace W2Core

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem nWords_take_succ_one {us : List Acc} {i : Nat} (hi : us[i]? = some .one) :
    nWords (us.take (i + 1)) = nWords (us.take i) + 1 := by
  rw [List.take_add_one, hi]
  simp [nWords, Acc.size]

/-- The double splice replacing unit `i` (a `.one` unit) of `wsA` by `wsB`'s word, by index. -/
theorem splice1_get {wsA wsB : List Word} {o : Nat} (lA : wsA.length = wsB.length) (ho : o < wsA.length)
    (k : Nat) (w : Word) (h : (TermTear.splice (o + 1) (TermTear.splice o wsA wsB) wsA)[k]? = some w) :
    (k = o ∧ wsB[o]? = some w) ∨ (k ≠ o ∧ wsA[k]? = some w) := by
  simp only [TermTear.splice] at h
  have hl1 : (wsA.take o ++ wsB.drop o).length = wsA.length := by
    simp [List.length_take, List.length_drop]; omega
  rw [List.getElem?_append] at h
  split at h
  · rename_i hk
    rw [List.length_take, hl1] at hk
    rw [List.getElem?_take] at h
    split at h
    · rename_i hk2
      rw [List.getElem?_append] at h
      split at h
      · rename_i hk3
        rw [List.length_take] at hk3
        rw [List.getElem?_take] at h
        split at h
        · right; exact ⟨by omega, h⟩
        · cases h
      · rename_i hk3
        rw [List.length_take] at hk3
        rw [List.getElem?_drop] at h
        have hko : k = o := by omega
        left
        refine ⟨hko, ?_⟩
        have e : o + (k - (List.take o wsA).length) = o := by rw [List.length_take]; omega
        rw [e] at h
        exact h
    · omega
  · rename_i hk
    rw [List.length_take, hl1] at hk
    rw [List.getElem?_drop, List.length_take, hl1] at h
    right
    refine ⟨by omega, ?_⟩
    have e : o + 1 + (k - min (o + 1) wsA.length) = k := by omega
    rw [e] at h
    exact h

/-- **Unit splice**: in one environment, replacing a `.one` unit of a value of a tear-OK
segment type by the same unit of another value gives a value. -/
theorem splice_unit {E : TEnv} {S : Ty} {us : List Acc} {wsA wsB : List Word} {i : Nat}
    (hT : TearOK S) (hu : accs S = some us) (hi : us[i]? = some .one)
    (hA : ValOf E S wsA) (hB : ValOf E S wsB) (lA : wsA.length = nWords us) (lB : wsB.length = nWords us) :
    ValOf E S (TermTear.splice (nWords (us.take i) + 1) (TermTear.splice (nWords (us.take i)) wsA wsB) wsA) ∧
      (TermTear.splice (nWords (us.take i) + 1) (TermTear.splice (nWords (us.take i)) wsA wsB) wsA).length =
        nWords us := by
  have hb0 : TermTear.Bnd us (nWords (us.take i)) := ⟨i, rfl⟩
  have hb1 : TermTear.Bnd us (nWords (us.take i) + 1) := ⟨i + 1, (nWords_take_succ_one hi).symm⟩
  have l1 : (TermTear.splice (nWords (us.take i)) wsA wsB).length = nWords us := by
    rw [TermTear.splice_length (lA.trans lB.symm)]; exact lB
  have h1 : ValOf E S (TermTear.splice (nWords (us.take i)) wsA wsB) :=
    ⟨hT E.unsee us _ wsA wsB hu hb0 hA.1 hB.1 lA lB, TermTear.Valid_tear hu hb0 hA.2 hB.2 lA lB⟩
  refine ⟨⟨hT E.unsee us _ _ wsA hu hb1 h1.1 hA.1 l1 lA, TermTear.Valid_tear hu hb1 h1.2 hA.2 l1 lA⟩, ?_⟩
  rw [TermTear.splice_length (l1.trans lA.symm)]; exact lA

theorem TwoAt_cons {us : List Acc} {x : Nat} (u : Acc) (h : TwoAt us x) : TwoAt (u :: us) (x + u.size) := by
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨i + 1, by simpa using hi, ?_⟩
  simp [nWords, Nat.add_comm]

/-- A word of a layout that starts no two-word unit and is no second word of one starts a
`.one` unit. -/
theorem oneAt_of_noTwo : ∀ {us : List Acc} {o : Nat}, o < nWords us →
    (∀ x, TwoAt us x → o ≠ x ∧ o ≠ x + 1) → ∃ i, us[i]? = some .one ∧ o = nWords (us.take i)
  | [], o, ho, _ => by simp [nWords] at ho
  | .one :: us, o, ho, hn => by
    cases o with
    | zero => exact ⟨0, rfl, by simp [nWords]⟩
    | succ o =>
      have ho' : o < nWords us := by
        have e : nWords (Acc.one :: us) = 1 + nWords us := by simp [nWords, Acc.size]
        omega
      obtain ⟨i, hi, e⟩ := oneAt_of_noTwo ho' fun x hx => by
        have := hn (x + 1) (by simpa [Acc.size] using TwoAt_cons .one hx); omega
      refine ⟨i + 1, by simpa using hi, ?_⟩
      simp [nWords, Acc.size] at e ⊢; omega
  | .two :: us, o, ho, hn => by
    have h0 : TwoAt (.two :: us) 0 := ⟨0, rfl, by simp [nWords]⟩
    have := hn 0 h0
    obtain ⟨o, rfl⟩ : ∃ o', o = o' + 2 := ⟨o - 2, by omega⟩
    have ho' : o < nWords us := by
      have e : nWords (Acc.two :: us) = 2 + nWords us := by simp [nWords, Acc.size]
      omega
    obtain ⟨i, hi, e⟩ := oneAt_of_noTwo ho' fun x hx => by
      have := hn (x + 2) (by simpa [Acc.size] using TwoAt_cons .two hx); omega
    refine ⟨i + 1, by simpa using hi, ?_⟩
    simp [nWords, Acc.size] at e ⊢; omega

/-- The same, from the cell-level `TwoAtT` exclusion at a segment. -/
theorem oneAt_of_noTwoT {T S : Ty} {b o : Nat} {us : List Acc} (hseg : SegOf T b S) (hu : accs S = some us)
    (hb : b ≤ o) (ho : o < b + nWords us) (hn : ∀ x, TwoAtT T x → o ≠ x ∧ o ≠ x + 1) :
    ∃ i, us[i]? = some .one ∧ o - b = nWords (us.take i) :=
  oneAt_of_noTwo (by omega) fun x hx => by
    have := hn (b + x) ⟨b, S, us, x, hseg, hu, hx, rfl⟩; omega

theorem ValOf_ext {E0 E2 : TEnv} (hx : Ext E0 E2) {T : Ty} {ws : List Word} (h : ValOf E0 T ws) :
    ValOf E2 T ws :=
  ValOf_mono hx.2.2.1.symm hx.2.2.2.1.symm hx.2.2.2.2.1 hx.2.2.2.2.2.1 h hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1
    hx.2.2.2.2.2.2.2.2.1 hx.rini

/-- Two segments of a cell covering one offset are the same segment. -/
theorem seg_uniq {T S S2 : Ty} {b b2 o : Nat} {us us2 : List Acc} (h1 : SegOf T b S) (h2 : SegOf T b2 S2)
    (hu : accs S = some us) (hu2 : accs S2 = some us2) (hb : b ≤ o) (ho : o < b + nWords us)
    (hb2 : b2 ≤ o) (ho2 : o < b2 + nWords us2) : b = b2 ∧ S = S2 := by
  rcases h1 with ⟨rfl, rfl, hA⟩ | ⟨N, us', j, rfl, hus', hj, rfl⟩
  · rcases h2 with ⟨rfl, rfl, -⟩ | ⟨N, us', j, rfl, -, -, -⟩
    · exact ⟨rfl, rfl⟩
    · simp [accs] at hA
  · rcases h2 with ⟨rfl, rfl, hA⟩ | ⟨N2, us'', j2, hT, hus'', hj2, rfl⟩
    · simp [accs] at hA
    · simp only [Ty.array.injEq, Idx.lit.injEq] at hT
      obtain ⟨-, rfl⟩ := hT
      rw [hu] at hus'; cases hus'
      rw [hu] at hu2; cases hu2
      rw [hu] at hus''; cases hus''
      have e : j = j2 := by
        rcases Nat.lt_trichotomy j j2 with hlt | e | hgt
        · have := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt hlt)
          rw [Nat.succ_mul] at this; omega
        · exact e
        · have := Nat.mul_le_mul_right (nWords us) (Nat.succ_le_of_lt hgt)
          rw [Nat.succ_mul] at this; omega
      subst e; exact ⟨rfl, rfl⟩

/-- **The rebuild**: a `WordOK` word `w` at offset `o` of a cell type `T` in `E2`, at a
`.one` unit of a tear-OK segment, together with a value `wsE` of the segment at an
environment `E0` that `E2` extends, gives a value of the segment in `E2` whose words are
`wsE`'s except for the unit at `o`, which holds the `WordOK` witness word. -/
theorem rebuild {E0 E2 : TEnv} {T S : Ty} {b o : Nat} {us : List Acc} {w : Word} {wsE : List Word}
    (hx : Ext E0 E2) (hseg : SegOf T b S) (hu : accs S = some us) (hb : b ≤ o) (ho : o < b + nWords us)
    (hT : TearOK S) (hn : ∀ x, TwoAtT T x → o ≠ x ∧ o ≠ x + 1)
    (hE : ValOf E0 S wsE) (lE : wsE.length = nWords us) (hw : WordOK E2 T o w) :
    ∃ ws w0, ValOf E2 S ws ∧ ws.length = nWords us ∧ ws[o - b]? = some w0 ∧ WLe1 w0 w ∧
      ∀ x ∈ ws, x ∈ wsE ∨ x = w0 := by
  obtain ⟨b2, S2, ws2, o2, w0, hseg2, ⟨hv2, hsh2⟩, hw0, hle, hbo2⟩ := hw
  obtain ⟨us2, hus2⟩ : ∃ us2, accs S2 = some us2 := by
    rcases hseg2 with ⟨-, rfl, hA⟩ | ⟨N, us2, jj, -, hus2, -, -⟩
    · exact Option.ne_none_iff_exists'.1 hA
    · exact ⟨us2, hus2⟩
  have hl2 : ws2.length = nWords us2 := hsh2 us2 hus2
  have ho2 : o2 < ws2.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨rfl, rfl⟩ := seg_uniq hseg hseg2 hu hus2 hb ho (by omega) (by omega)
  rw [hu] at hus2; cases hus2
  have eo : o2 = o - b := by omega
  subst eo
  obtain ⟨i, hi, ei⟩ := oneAt_of_noTwoT hseg hu hb ho hn
  have hE2 := ValOf_ext hx hE
  obtain ⟨hV, hL⟩ := splice_unit hT hu hi hE2 hv2 lE hl2
  rw [← ei] at hV hL
  refine ⟨_, w0, hV, hL, ?_, hle, fun x hx' => ?_⟩
  · simp only [TermTear.splice]
    have hl1 : (wsE.take (o - b) ++ ws2.drop (o - b)).length = nWords us := by
      simp [List.length_take, List.length_drop]; omega
    rw [List.getElem?_append_left (by rw [List.length_take, hl1]; omega), List.getElem?_take_of_lt (by omega),
      List.getElem?_append_right (by rw [List.length_take]; omega), List.getElem?_drop]
    have e : o - b + (o - b - (List.take (o - b) wsE).length) = o - b := by rw [List.length_take]; omega
    rw [e]; exact hw0
  · obtain ⟨k, hk⟩ := List.getElem?_of_mem hx'
    rcases splice1_get (lE.trans hl2.symm) (by omega) k x hk with ⟨-, h⟩ | ⟨-, h⟩
    · rw [hw0] at h; cases h; exact .inr rfl
    · exact .inl (List.mem_of_getElem? h)

/-- An initialised offset of a segment makes the segment initialised. -/
theorem iniSeg_of_initR {E : TEnv} {c : Cell} {l : AllocLabel} {S : Ty} {b o : Nat} {us : List Acc}
    (hseg : SegOf c.ty b S) (hu : accs S = some us) (hb : b ≤ o) (hI : InitR E c l o) : IniSeg E c l b := by
  intro N e hT
  rcases hseg with ⟨-, -, hA⟩ | ⟨N', us', jj, hT', hus', -, rfl⟩
  · rw [hT] at hA; simp [accs] at hA
  · rw [hT] at hT'
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
    obtain ⟨-, rfl⟩ := hT'
    rw [hu] at hus'; cases hus'
    have h := hI N e us hT hu
    exact ⟨us, jj, hu, Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hb h), rfl⟩

end W2Core

#print axioms W2Core.splice1_get
#print axioms W2Core.splice_unit
#print axioms W2Core.oneAt_of_noTwoT
#print axioms W2Core.rebuild
