import WeakCore.TermCntEmb

/-!
# TermPubPos: a counted word naming a label is a counted position's word (K-2a loads)

`pubWords_pos`: a word of `pubWords R ws` naming `x` has the read timestamp of the word at a counted
position `i ∈ cntIdx R ws`, which names `x` too (a niche sum's payload re-encodes the slot word, keeping
its label and read timestamp; the synthesised `cst .null` names nothing).
-/

namespace TermPubPos
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermCntLoc TermCntEmb

/-- Every word of `l` naming a label has the read timestamp of a word of `ws` naming it. -/
def NR (ws l : List Word) : Prop := ∀ w ∈ l, ∀ x, Names x w → ∃ w0 ∈ ws, w0.rts = w.rts ∧ Names x w0

theorem nr_refl (ws : List Word) : NR ws ws := fun w hw _ hn => ⟨w, hw, rfl, hn⟩

theorem nr_nil (ws : List Word) : NR ws [] := fun _ h => by simp at h

theorem nr_trans {a b c : List Word} (h1 : NR a b) (h2 : NR b c) : NR a c := by
  intro w hw x hn
  obtain ⟨w1, hw1, e1, hn1⟩ := h2 w hw x hn
  obtain ⟨w0, hw0, e0, hn0⟩ := h1 w1 hw1 x hn1
  exact ⟨w0, hw0, e0.trans e1, hn0⟩

theorem nr_take (ws : List Word) (n : Nat) : NR ws (ws.take n) :=
  fun w hw _ hn => ⟨w, List.mem_of_mem_take hw, rfl, hn⟩

theorem nr_drop (ws : List Word) (n : Nat) : NR ws (ws.drop n) :=
  fun w hw _ hn => ⟨w, List.mem_of_mem_drop hw, rfl, hn⟩

theorem nr_append {ws a b : List Word} (h1 : NR ws a) (h2 : NR ws b) : NR ws (a ++ b) := by
  intro w hw
  rcases List.mem_append.1 hw with h | h
  · exact h1 w h
  · exact h2 w h

/-- The decoded payload's naming words carry the last word's read timestamp and label. -/
theorem decodeArm_nr {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : decodeArm tr as ws = some (j, p)) : NR ws p := by
  cases tr with
  | boxed => simp [decodeArm] at h
  | niche =>
      rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · simp [decodeArm] at h
      · simp only [decodeArm] at h
        cases hw : w.val with
        | loc a g =>
            rw [hw] at h
            cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
            | none => simp [h1, bind, Option.bind] at h
            | some pr =>
                simp [h1, bind, Option.bind, pure] at h
                obtain ⟨rfl, rfl⟩ := h
                intro y hy x hn
                simp at hy; subst hy
                obtain ⟨a', g', hv, hl⟩ := hn
                simp only [WeakMem.Val.loc.injEq] at hv
                obtain ⟨rfl, -⟩ := hv
                exact ⟨w, List.mem_singleton_self _, rfl, a, g, hw, hl⟩
        | num k =>
            rw [hw] at h
            simp only [bind, Option.bind] at h
            cases h1 : as[k]? with
            | none => simp [h1] at h
            | some arm =>
                simp only [h1] at h
                intro y hy x hn
                cases hk : armK arm <;> simp [hk, pure] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
                  simp at hy
                subst hy
                obtain ⟨a', g', hv, -⟩ := hn
                exact absurd hv (by intro h; cases h)
        | _ => rw [hw] at h; simp at h
      · simp [decodeArm] at h
  | wide =>
      rcases ws with _ | ⟨t, _ | ⟨w, _ | ⟨w3, rest⟩⟩⟩
      · simp [decodeArm] at h
      · simp [decodeArm] at h
      · simp only [decodeArm] at h
        cases ht : t.val with
        | num k =>
            rw [ht] at h
            cases h1 : as[k]? with
            | none => simp [h1, bind, Option.bind] at h
            | some a =>
                simp only [h1, bind, Option.bind] at h
                intro y hy x hn
                by_cases hr : a.rawWords = some 0
                · simp [hr, pure] at h; obtain ⟨rfl, rfl⟩ := h; simp at hy
                · simp [hr, pure] at h; obtain ⟨rfl, rfl⟩ := h
                  simp at hy; subst hy
                  exact ⟨y, by simp, rfl, hn⟩
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

/-- The counted words naming a label carry an input word's read timestamp and label. -/
theorem pubWords_nr : ∀ (R : Ty), (∀ ws, NR ws (pubWords R ws)) ∧ (∀ j p, NR p (pubArm R j p)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws, NR ws (pubWords (.prod a b) ws) := by
        intro ws
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs]; exact nr_refl ws
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact nr_append (nr_trans (nr_take ws _) (iha.1 _)) (nr_trans (nr_drop ws _) (ihb.1 _))
          · exact nr_nil ws
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p, NR p (pubArm (.sum a b) j p) := by
        intro j p
        simp only [pubArm]
        split
        · exact iha.2 _ _
        · exact ihb.2 _ _
      refine ⟨fun ws => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs]; exact nr_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact nr_refl ws
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none => exact nr_nil ws
          | some x =>
            obtain ⟨j, p⟩ := x
            have hp : NR ws p := decodeArm_nr hd
            simp only []
            split
            · exact nr_trans hp (iha.2 _ _)
            · exact nr_trans hp (ihb.2 _ _)
  | refine t ψ ih =>
      exact ⟨fun ws => by rw [pubWords_refine]; exact ih.1 _, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
  | iall t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs]; exact nr_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | iex t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs]; exact nr_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | mu t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs]; exact nr_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | tex κ t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs]; exact nr_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | _ =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only []
        split
        · exact nr_refl ws
        · exact nr_nil ws
      · simp only [pubArm]; rw [pubWords.eq_def]; simp only []
        split
        · exact nr_refl p
        · exact nr_nil p

/-- `ws` with each word's read timestamp encoding its position and its own read timestamp. -/
def enc (N : Nat) (ws : List Word) : List Word :=
  ws.mapIdx fun i w => { w with rts := (i + 1) + N * (w.rts : Nat) }

theorem enc_get (N : Nat) (ws : List Word) (i : Nat) :
    (enc N ws)[i]? = ws[i]?.map fun w => { w with rts := (i + 1) + N * (w.rts : Nat) } := by
  simp [enc, List.getElem?_mapIdx]

theorem div_enc {N a b : Nat} (h : a < N) : (a + N * b) / N = b := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt h, Nat.zero_add]

theorem mod_enc {N a b : Nat} (h : a < N) : (a + N * b) % N = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem enc_relab_div (ws : List Word) : (enc (ws.length + 1) ws).map (relab (· / (ws.length + 1))) = ws := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, enc_get]
  rcases Nat.lt_or_ge i ws.length with h | h
  · rw [List.getElem?_eq_getElem h]
    simp only [Option.map_some, relab]
    congr 1
    show { ws[i] with rts := ((i + 1) + (ws.length + 1) * (ws[i].rts : Nat)) / (ws.length + 1) } = ws[i]
    rw [div_enc (by omega)]
  · rw [List.getElem?_eq_none h]; rfl

theorem enc_relab_mod (ws : List Word) : (enc (ws.length + 1) ws).map (relab (· % (ws.length + 1))) = tag 0 ws := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, enc_get, tag_get]
  rcases Nat.lt_or_ge i ws.length with h | h
  · rw [List.getElem?_eq_getElem h]
    simp only [Option.map_some, relab]
    congr 1
    show { ws[i] with rts := ((i + 1) + (ws.length + 1) * (ws[i].rts : Nat)) % (ws.length + 1) } =
      { ws[i] with rts := i + 0 + 1 }
    rw [mod_enc (by omega)]
  · rw [List.getElem?_eq_none h]; rfl

theorem names_relab {f : Nat → Nat} {x : WeakMem.AllocLabel} {w : Word} : Names x (relab f w) ↔ Names x w := Iff.rfl

/-- **A counted word naming `x` is a counted position's word**: same read timestamp, naming `x`. -/
theorem pubWords_pos {R : Ty} {ws : List Word} {w : Word} (hw : w ∈ pubWords R ws) {x : WeakMem.AllocLabel}
    (hn : Names x w) : ∃ i w0, i ∈ cntIdx R ws ∧ ws[i]? = some w0 ∧ Names x w0 ∧ w0.rts = w.rts := by
  have hf : (fun n : Nat => n / (ws.length + 1)) 0 = 0 := Nat.zero_div _
  have hg : (fun n : Nat => n % (ws.length + 1)) 0 = 0 := Nat.zero_mod _
  have e1 := (pubWords_relab (f := fun n : Nat => n / (ws.length + 1)) hf R).1 (enc (ws.length + 1) ws)
  have e2 := (pubWords_relab (f := fun n : Nat => n % (ws.length + 1)) hg R).1 (enc (ws.length + 1) ws)
  rw [enc_relab_div] at e1
  rw [enc_relab_mod] at e2
  rw [e1] at hw
  obtain ⟨w2, hw2, rfl⟩ := List.mem_map.1 hw
  obtain ⟨w0, hw0, er, hn0⟩ := (pubWords_nr R).1 _ w2 hw2 x hn
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hw0
  have hi' : i < ws.length := by simpa [enc] using hi
  have hg0 : (enc (ws.length + 1) ws)[i]? = some w0 := by rw [List.getElem?_eq_getElem hi, e]
  rw [enc_get, List.getElem?_eq_getElem hi'] at hg0
  simp only [Option.map_some, Option.some.injEq] at hg0
  subst hg0
  refine ⟨i, ws[i], ?_, List.getElem?_eq_getElem hi', hn0, ?_⟩
  · rw [cntIdx_eq]
    unfold cntK
    rw [e2]
    refine List.mem_filterMap.2 ⟨i + 1, List.mem_map.2 ⟨relab (· % (ws.length + 1)) w2,
      List.mem_map_of_mem hw2, ?_⟩, ?_⟩
    · show (w2.rts : Nat) % (ws.length + 1) = i + 1
      rw [← er]
      exact mod_enc (by omega)
    · simp [TermCntLoc.rf]
  · show (ws[i].rts : Nat) = (w2.rts : Nat) / (ws.length + 1)
    rw [← er]
    exact (div_enc (by omega)).symm

end TermPubPos

#print axioms TermPubPos.pubWords_nr
#print axioms TermPubPos.pubWords_pos
