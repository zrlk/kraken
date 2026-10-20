import WeakCore.TermK2aLd

/-!
# K-2a sums and `publish`: per-operation binding contracts (K1c)

A non-boxed `inl`/`inr`/`case` reads no memory: the result's counted words are (re-encoded) payload
words of the operand, each naming a label some counted word of the operand names, at no smaller
`rts` (`cntOld_inj`, `cntOld_proj`).  So the result is old-covered (`CntOld`).
-/

namespace TermK2aSum

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermK2aLd
open TermOwnG0Defs (PubAt)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## 1. `rts`-tracking label inclusion -/

/-- Every label a word of `wsP` names is named by a word of `ws` of no larger `rts`. -/
def RtsSub (wsP ws : List Word) : Prop :=
  ∀ w ∈ wsP, ∀ l, Names l w → ∃ w0 ∈ ws, Names l w0 ∧ w0.rts ≤ w.rts

theorem rtsSub_refl (ws : List Word) : RtsSub ws ws := fun w hw _ hn => ⟨w, hw, hn, Nat.le_refl _⟩

theorem rtsSub_nil (ws : List Word) : RtsSub [] ws := fun _ hw => by cases hw

theorem rtsSub_trans {a b c : List Word} (h1 : RtsSub a b) (h2 : RtsSub b c) : RtsSub a c := by
  intro w hw l hn
  obtain ⟨w1, hw1, hn1, hr1⟩ := h1 w hw l hn
  obtain ⟨w2, hw2, hn2, hr2⟩ := h2 w1 hw1 l hn1
  exact ⟨w2, hw2, hn2, Nat.le_trans hr2 hr1⟩

theorem rtsSub_of_sub {a b : List Word} (h : ∀ w ∈ a, w ∈ b) : RtsSub a b :=
  fun w hw _ hn => ⟨w, h w hw, hn, Nat.le_refl _⟩

theorem rtsSub_append {a b c d : List Word} (h1 : RtsSub a c) (h2 : RtsSub b d) : RtsSub (a ++ b) (c ++ d) := by
  intro w hw l hn
  rcases List.mem_append.1 hw with hw | hw
  · obtain ⟨w0, h0, hn0, hr⟩ := h1 w hw l hn
    exact ⟨w0, List.mem_append_left _ h0, hn0, hr⟩
  · obtain ⟨w0, h0, hn0, hr⟩ := h2 w hw l hn
    exact ⟨w0, List.mem_append_right _ h0, hn0, hr⟩

theorem not_names_null (l : AllocLabel) : ¬ Names l (cst .null) := by
  rintro ⟨aP, gP, hvP, -⟩
  have e : (cst .null).val = WeakMem.Val.null := rfl
  rw [e] at hvP; cases hvP

theorem not_names_num (n : Nat) (l : AllocLabel) : ¬ Names l (cst (.num n)) := by
  rintro ⟨aP, gP, hvP, -⟩
  have e : (cst (.num n)).val = WeakMem.Val.num n := rfl
  rw [e] at hvP; cases hvP

/-! ## 2. Pointwise value-equal, `rts`-dominated word lists -/

/-- `wP` has `w`'s value, and if it names a label, no smaller `rts`. -/
def WR (wP w : Word) : Prop := wP.val = w.val ∧ ∀ l, Names l wP → w.rts ≤ wP.rts

/-- Pointwise `WR`. -/
def Rel : List Word → List Word → Prop
  | [], [] => True
  | a :: as, b :: bs => WR a b ∧ Rel as bs
  | _, _ => False

theorem wr_refl (w : Word) : WR w w := ⟨rfl, fun _ _ => Nat.le_refl _⟩

theorem rel_refl : ∀ (ws : List Word), Rel ws ws
  | [] => trivial
  | w :: ws => ⟨wr_refl w, rel_refl ws⟩

theorem rel_take : ∀ (wsP ws : List Word) (n : Nat), Rel wsP ws → Rel (wsP.take n) (ws.take n)
  | [], [], _, _ => by simp [Rel]
  | _ :: _, [], _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | a :: as, b :: bs, 0, _ => by simp [Rel]
  | a :: as, b :: bs, n + 1, h => ⟨h.1, rel_take as bs n h.2⟩

theorem rel_drop : ∀ (wsP ws : List Word) (n : Nat), Rel wsP ws → Rel (wsP.drop n) (ws.drop n)
  | [], [], _, _ => by simp [Rel]
  | _ :: _, [], _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | a :: as, b :: bs, 0, h => h
  | a :: as, b :: bs, n + 1, h => rel_drop as bs n h.2

theorem rel_rtsSub : ∀ (wsP ws : List Word), Rel wsP ws → RtsSub wsP ws
  | [], _, _ => rtsSub_nil _
  | _ :: _, [], h => h.elim
  | a :: as, b :: bs, h => by
      intro w hw l hn
      rcases List.mem_cons.1 hw with rfl | hw
      · obtain ⟨aP, gP, hv, hl⟩ := hn
        exact ⟨b, List.mem_cons_self .., ⟨aP, gP, h.1.1 ▸ hv, hl⟩, h.1.2 l ⟨aP, gP, hv, hl⟩⟩
      · obtain ⟨w0, h0, hn0, hr⟩ := rel_rtsSub as bs h.2 w hw l hn
        exact ⟨w0, List.mem_cons_of_mem _ h0, hn0, hr⟩

theorem rel_one {wP : Word} {ws : List Word} (h : Rel [wP] ws) : ∃ w, ws = [w] ∧ WR wP w := by
  match ws, h with
  | [w], h => exact ⟨w, rfl, h.1⟩
  | [], h => exact h.elim
  | _ :: _ :: _, h => exact h.2.elim

theorem rel_two {tP wP : Word} {ws : List Word} (h : Rel [tP, wP] ws) :
    ∃ t w, ws = [t, w] ∧ WR tP t ∧ WR wP w := by
  match ws, h with
  | [t, w], h => exact ⟨t, w, rfl, h.1, h.2.1⟩
  | [], h => exact h.elim
  | [_], h => exact h.2.elim
  | _ :: _ :: _ :: _, h => exact h.2.2.elim

theorem decodeArm_rel {tr : Tier} {as : List Ty} {wsP ws : List Word} {j : Nat} {pP : List Word}
    (e : Rel wsP ws) (h : decodeArm tr as wsP = some (j, pP)) :
    ∃ p, decodeArm tr as ws = some (j, p) ∧ Rel pP p := by
  cases tr with
  | boxed => simp [decodeArm] at h
  | niche =>
      rcases wsP with _ | ⟨wP, _ | ⟨w2, rest⟩⟩
      · simp [decodeArm] at h
      · obtain ⟨w, rfl, ew, er⟩ := rel_one e
        simp only [decodeArm] at h ⊢
        rw [← ew]
        cases hw : wP.val with
        | loc a g =>
            rw [hw] at h
            cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
            | none => simp [h1, bind, Option.bind] at h
            | some pr =>
                simp [h1, bind, Option.bind, pure] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨[{ w with val := .loc a 0 }], by simp [h1, bind, Option.bind, pure], ⟨rfl, ?_⟩, trivial⟩
                intro l hn
                obtain ⟨aP, gP, hvP, hl⟩ := hn
                simp only at hvP
                cases hvP
                exact er l ⟨a, g, hw, hl⟩
        | num k =>
            rw [hw] at h
            exact ⟨pP, h, rel_refl _⟩
        | _ => rw [hw] at h; simp at h
      · simp [decodeArm] at h
  | wide =>
      rcases wsP with _ | ⟨tP, _ | ⟨wP, _ | ⟨w3, rest⟩⟩⟩
      · simp [decodeArm] at h
      · simp [decodeArm] at h
      · obtain ⟨t, w, rfl, et, ew⟩ := rel_two e
        simp only [decodeArm] at h ⊢
        rw [← et.1]
        cases ht : tP.val with
        | num k =>
            rw [ht] at h
            cases h1 : as[k]? with
            | none => simp [h1, bind, Option.bind] at h
            | some a =>
                simp only [h1, bind, Option.bind] at h ⊢
                by_cases hr : a.rawWords = some 0
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], ⟨rfl, rfl⟩, trivial⟩
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨[w], ⟨rfl, rfl⟩, ew, trivial⟩
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

/-! ## 3. Counted words follow `Rel` -/

/-- The counted words of a `Rel`-smaller value name labels of the counted words of the larger. -/
theorem pubWords_rel : ∀ (R : Ty),
    (∀ wsP ws, Rel wsP ws → RtsSub (pubWords R wsP) (pubWords R ws)) ∧
    (∀ j pP p, Rel pP p → RtsSub (pubArm R j pP) (pubArm R j p)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ wsP ws, Rel wsP ws → RtsSub (pubWords (.prod a b) wsP) (pubWords (.prod a b) ws) := by
        intro wsP ws e
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact rel_rtsSub _ _ e
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact rtsSub_append (iha.1 _ _ (rel_take _ _ _ e)) (ihb.1 _ _ (rel_drop _ _ _ e))
          · exact rtsSub_nil _
      exact ⟨h1, fun j pP p e => by simp only [pubArm]; exact h1 pP p e⟩
  | sum a b iha ihb =>
      have h2 : ∀ j pP p, Rel pP p → RtsSub (pubArm (.sum a b) j pP) (pubArm (.sum a b) j p) := by
        intro j pP p e
        simp only [pubArm]
        split
        · exact iha.2 _ _ _ e
        · exact ihb.2 _ _ _ e
      refine ⟨fun wsP ws e => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact rel_rtsSub _ _ e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact rel_rtsSub _ _ e
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) wsP with
          | none => exact rtsSub_nil _
          | some x =>
            obtain ⟨j, pP⟩ := x
            obtain ⟨p, hp, ep⟩ := decodeArm_rel e hd
            simp only [hp]
            split
            · exact iha.2 _ _ _ ep
            · exact ihb.2 _ _ _ ep
  | refine t ψ ih =>
      exact ⟨fun wsP ws e => by rw [pubWords_refine, pubWords_refine]; exact ih.1 _ _ e,
        fun j pP p e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
  | iall t ih =>
      refine ⟨fun wsP ws e => ?_, fun j pP p e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact rel_rtsSub _ _ e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | iex t ih =>
      refine ⟨fun wsP ws e => ?_, fun j pP p e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact rel_rtsSub _ _ e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | mu t ih =>
      refine ⟨fun wsP ws e => ?_, fun j pP p e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact rel_rtsSub _ _ e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | tex κ t ih =>
      refine ⟨fun wsP ws e => ?_, fun j pP p e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact rel_rtsSub _ _ e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | _ =>
      refine ⟨fun wsP ws e => ?_, fun j pP p e => ?_⟩
      · rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact rel_rtsSub _ _ e
        · exact rtsSub_nil _
      · simp only [pubArm]; rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact rel_rtsSub _ _ e
        · exact rtsSub_nil _

/-- Under a shallow-pub type every payload word counts. -/
theorem pubArm_sNo : ∀ (t : Ty), sNo t = true → ∀ j p, pubArm t j p = p := by
  intro t
  induction t with
  | sum a b iha ihb =>
      intro h j p
      simp only [sNo, Bool.and_eq_true] at h
      simp only [pubArm]; split
      · exact iha h.1 _ _
      · exact ihb h.2 _ _
  | refine t ψ ih => intro h j p; simp only [pubArm]; exact ih h j p
  | iall t ih => intro h j p; simp only [pubArm]; exact ih h j p
  | iex t ih => intro h j p; simp only [pubArm]; exact ih h j p
  | mu t ih => intro h j p; simp only [pubArm]; exact ih h j p
  | tex κ t ih =>
      intro h j p; simp only [sNo, Bool.and_eq_true] at h; simp only [pubArm]; exact ih h.2 j p
  | _ => intro h j p; simp only [pubArm]; exact pubWords_of_sNo h p

/-- The wrappers count their body's words. -/
theorem pubWords_wrap (t : Ty) (ws : List Word) :
    pubWords (.iall t) ws = pubWords t ws ∧ pubWords (.iex t) ws = pubWords t ws ∧
      pubWords (.mu t) ws = pubWords t ws ∧ ∀ κ, pubWords (.tex κ t) ws = pubWords t ws := by
  refine ⟨?_, ?_, ?_, fun κ => ?_⟩
  · by_cases h : sNo (.iall t) = true
    · rw [pubWords_of_sNo h, pubWords_of_sNo (by simpa [sNo] using h)]
    · simp only [pubWords, h, Bool.false_eq_true, ite_false]
  · by_cases h : sNo (.iex t) = true
    · rw [pubWords_of_sNo h, pubWords_of_sNo (by simpa [sNo] using h)]
    · simp only [pubWords, h, Bool.false_eq_true, ite_false]
  · by_cases h : sNo (.mu t) = true
    · rw [pubWords_of_sNo h, pubWords_of_sNo (by simpa [sNo] using h)]
    · simp only [pubWords, h, Bool.false_eq_true, ite_false]
  · by_cases h : sNo (.tex κ t) = true
    · have hb : sNo t = true := by simp only [sNo, Bool.and_eq_true] at h; exact h.2
      rw [pubWords_of_sNo h, pubWords_of_sNo hb]
    · simp only [pubWords, h, Bool.false_eq_true, ite_false]

/-! ## 4. Encoding and decoding keep labels and `rts` -/

theorem decodeArm_rtsSub {tr : Tier} {as : List Ty} {ws p : List Word} {j : Nat}
    (h : decodeArm tr as ws = some (j, p)) : RtsSub p ws := by
  have h0 : Rel ws ws := rel_refl ws
  cases tr with
  | boxed => simp [decodeArm] at h
  | niche =>
      rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · simp [decodeArm] at h
      · simp only [decodeArm] at h
        cases hw : w.val with
        | loc a g =>
            rw [hw] at h
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨_, _, h⟩ := h
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            intro wP hwP l hn
            simp only [List.mem_singleton] at hwP
            subst hwP
            obtain ⟨aP, gP, hvP, hl⟩ := hn
            simp only at hvP
            cases hvP
            exact ⟨w, List.mem_singleton_self _, ⟨a, g, hw, hl⟩, Nat.le_refl _⟩
        | num k =>
            rw [hw] at h
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨arm, -, h⟩ := h
            split at h <;> simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
            · obtain ⟨-, rfl⟩ := h; exact rtsSub_nil _
            · obtain ⟨-, rfl⟩ := h
              intro wP hwP l hn
              simp only [List.mem_singleton] at hwP
              subst hwP
              exact absurd hn (not_names_null l)
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
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨arm, -, h⟩ := h
            split at h <;> simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
            · obtain ⟨-, rfl⟩ := h; exact rtsSub_nil _
            · obtain ⟨-, rfl⟩ := h
              exact rtsSub_of_sub (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp)
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

/-- Encoding takes a payload of at most one word, and keeps its labels and `rts`. -/
theorem encodeArm_rtsSub {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (h : encodeArm tr as j p = some q) : RtsSub q p ∧ (p = [] ∨ ∃ w, p = [w]) := by
  cases tr with
  | boxed => simp [encodeArm] at h
  | wide =>
      simp only [encodeArm] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨fun w hw l hn => ?_, .inl rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact absurd hn (not_names_num _ l)
        · exact absurd hn (not_names_num _ l)
      · simp only [Option.some.injEq] at h; subst h
        rename_i w
        refine ⟨fun x hx l hn => ?_, .inr ⟨w, rfl⟩⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact absurd hn (not_names_num _ l)
        · exact ⟨x, List.mem_singleton_self _, hn, Nat.le_refl _⟩
      · cases h
  | niche =>
      simp only [encodeArm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, h⟩ := h
      split at h
      · rename_i w _
        refine ⟨?_, .inr ⟨w, rfl⟩⟩
        split at h
        · rename_i a g hv
          simp only [Option.some.injEq] at h; subst h
          intro x hx l hn
          simp only [List.mem_singleton] at hx; subst hx
          obtain ⟨aP, gP, hvP, hl⟩ := hn
          simp only at hvP; cases hvP
          exact ⟨w, List.mem_singleton_self _, ⟨a, g, hv, hl⟩, Nat.le_refl _⟩
        · split at h
          · simp only [Option.some.injEq] at h; subst h
            intro x hx l hn
            simp only [List.mem_singleton] at hx; subst hx
            exact absurd hn (not_names_num _ l)
          · cases h
        · cases h
      · rename_i w _
        refine ⟨?_, .inr ⟨w, rfl⟩⟩
        split at h
        · rename_i a g hv
          simp only [Option.some.injEq] at h; subst h
          intro x hx l hn
          simp only [List.mem_singleton] at hx; subst hx
          obtain ⟨aP, gP, hvP, hl⟩ := hn
          simp only at hvP; cases hvP
          exact ⟨w, List.mem_singleton_self _, ⟨a, g, hv, hl⟩, Nat.le_refl _⟩
        · split at h
          · simp only [Option.some.injEq] at h; subst h
            intro x hx l hn
            simp only [List.mem_singleton] at hx; subst hx
            exact absurd hn (not_names_num _ l)
          · cases h
        · cases h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨fun x hx l hn => ?_, .inl rfl⟩
        simp only [List.mem_singleton] at hx; subst hx
        exact absurd hn (not_names_num _ l)
      · cases h

/-- A payload decoded back from its encoding is `Rel`-below the original. -/
theorem rel_dec_enc {tr : Tier} {as bs : List Ty} {j jP : Nat} {p q pP : List Word}
    (he : encodeArm tr as j p = some q) (hd : decodeArm tr bs q = some (jP, pP)) (e : VEq p pP) :
    Rel pP p := by
  obtain ⟨hq, hp⟩ := encodeArm_rtsSub he
  have hs := rtsSub_trans (decodeArm_rtsSub hd) hq
  rcases hp with rfl | ⟨w, rfl⟩
  · cases pP with
    | nil => trivial
    | cons _ _ => simp [VEq] at e
  · match pP, e with
    | [wP], e =>
        simp only [VEq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
        refine ⟨⟨e.symm, fun l hn => ?_⟩, trivial⟩
        obtain ⟨w0, h0, -, hr⟩ := hs wP (List.mem_singleton_self _) l hn
        rw [List.mem_singleton] at h0; subst h0; exact hr
    | [], e => simp [VEq] at e
    | _ :: _ :: _, e => simp [VEq] at e

theorem asArm_rtsSub {t : Ty} {ws p : List Word} {j : Nat} (h : asArm t ws = some (j, p)) : RtsSub p ws := by
  unfold asArm at h
  split at h
  · exact decodeArm_rtsSub h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact rtsSub_refl _

/-! ## 5. Arms: projection and injection -/

/-- **Projection**: a payload `Rel`-below the projected arm counts only labels the value counts. -/
theorem cnt_proj : ∀ (rt : Ty) {ws p pP : List Word} {j : Nat}, rt.tier ≠ .boxed →
    asArm rt ws = some (j, p) → Rel pP p → RtsSub (pubArm rt j pP) (pubWords rt ws) := by
  intro rt
  induction rt with
  | sum a b _ _ =>
      intro ws p pP j ht ha e
      have hd : decodeArm (Ty.sum a b).tier (armsOf (.sum a b)) ws = some (j, p) := by
        simpa [asArm, sumHead] using ha
      by_cases hs : sNo (.sum a b) = true
      · rw [pubArm_sNo _ hs, pubWords_of_sNo hs]
        exact rtsSub_trans (rel_rtsSub _ _ e) (decodeArm_rtsSub hd)
      · have hdP := decodeArm_mono (arms_lnorm (.sum a b)) hd
        simp only [pubWords, hs, Bool.false_eq_true, ite_false, ht, hdP]
        have h := (pubWords_rel (.sum a b)).2 j pP p e
        simp only [pubArm] at h ⊢
        exact h
  | refine t ψ ih =>
      intro ws p pP j ht ha e
      obtain ⟨e1, -⟩ := @asArm_congr (.refine t ψ) t rfl (tier_refine t ψ) rfl
      rw [e1] at ha
      simp only [pubArm]; rw [pubWords_refine]
      exact ih (tier_refine t ψ ▸ ht) ha e
  | iall t ih =>
      intro ws p pP j ht ha e
      obtain ⟨e1, -⟩ := @asArm_congr (.iall t) t rfl (tier_iall t) rfl
      rw [e1] at ha
      simp only [pubArm]; rw [(pubWords_wrap t ws).1]
      exact ih (tier_iall t ▸ ht) ha e
  | iex t ih =>
      intro ws p pP j ht ha e
      obtain ⟨e1, -⟩ := @asArm_congr (.iex t) t rfl (tier_iex t) rfl
      rw [e1] at ha
      simp only [pubArm]; rw [(pubWords_wrap t ws).2.1]
      exact ih (tier_iex t ▸ ht) ha e
  | mu t ih =>
      intro ws p pP j ht ha e
      obtain ⟨e1, -⟩ := @asArm_congr (.mu t) t rfl (tier_mu t) rfl
      rw [e1] at ha
      simp only [pubArm]; rw [(pubWords_wrap t ws).2.2.1]
      exact ih (tier_mu t ▸ ht) ha e
  | tex κ t ih =>
      intro ws p pP j ht ha e
      obtain ⟨e1, -⟩ := @asArm_congr (.tex κ t) t rfl (tier_tex κ t) rfl
      rw [e1] at ha
      simp only [pubArm]; rw [(pubWords_wrap t ws).2.2.2 κ]
      exact ih (tier_tex κ t ▸ ht) ha e
  | _ =>
      intro ws p pP j _ ha e
      simp only [asArm, sumHead, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      simp only [pubArm]
      exact (pubWords_rel _).1 _ _ e

/-- **Injection**: a fitting payload, injected, counts only labels its arm counts. -/
theorem cnt_inj : ∀ (t : Ty) {p q : List Word} {j : Nat} {arm : Ty}, ofArm t j p = some q →
    (armsOf t)[j]? = some arm → PayOK arm p → RtsSub (pubWords t q) (pubArm t j p) := by
  intro t
  induction t with
  | sum a b _ _ =>
      intro p q j arm ho ha hp
      have he : encodeArm (Ty.sum a b).tier (armsOf (.sum a b)) j p = some q := by
        simpa [ofArm, sumHead] using ho
      have ht : (Ty.sum a b).tier ≠ .boxed := by
        intro hb; rw [hb] at he; simp [encodeArm] at he
      by_cases hs : sNo (.sum a b) = true
      · rw [pubArm_sNo _ hs, pubWords_of_sNo hs]
        exact (encodeArm_rtsSub he).1
      · obtain ⟨pP, hd, ep⟩ := roundtrip ht ha hp he
        have hdP := decodeArm_mono (arms_lnorm (.sum a b)) hd
        simp only [pubWords, hs, Bool.false_eq_true, ite_false, ht, hdP]
        have h := (pubWords_rel (.sum a b)).2 j pP p (rel_dec_enc he hd ep)
        simp only [pubArm] at h ⊢
        exact h
  | refine t ψ ih =>
      intro p q j arm ho ha hp
      obtain ⟨-, e2⟩ := @asArm_congr (.refine t ψ) t rfl (tier_refine t ψ) rfl
      rw [e2] at ho
      simp only [pubArm]; rw [pubWords_refine]
      exact ih ho ha hp
  | iall t ih =>
      intro p q j arm ho ha hp
      obtain ⟨-, e2⟩ := @asArm_congr (.iall t) t rfl (tier_iall t) rfl
      rw [e2] at ho
      simp only [pubArm]; rw [(pubWords_wrap t q).1]
      exact ih ho ha hp
  | iex t ih =>
      intro p q j arm ho ha hp
      obtain ⟨-, e2⟩ := @asArm_congr (.iex t) t rfl (tier_iex t) rfl
      rw [e2] at ho
      simp only [pubArm]; rw [(pubWords_wrap t q).2.1]
      exact ih ho ha hp
  | mu t ih =>
      intro p q j arm ho ha hp
      obtain ⟨-, e2⟩ := @asArm_congr (.mu t) t rfl (tier_mu t) rfl
      rw [e2] at ho
      simp only [pubArm]; rw [(pubWords_wrap t q).2.2.1]
      exact ih ho ha hp
  | tex κ t ih =>
      intro p q j arm ho ha hp
      obtain ⟨-, e2⟩ := @asArm_congr (.tex κ t) t rfl (tier_tex κ t) rfl
      rw [e2] at ho
      simp only [pubArm]; rw [(pubWords_wrap t q).2.2.2 κ]
      exact ih ho ha hp
  | _ =>
      intro p q j arm ho _ _
      simp only [ofArm, sumHead, Bool.false_eq_true, ite_false] at ho
      split at ho
      · simp only [Option.some.injEq] at ho; subst ho
        simp only [pubArm]; exact rtsSub_refl _
      · cases ho

/-! ## 6. Old-covered results -/

/-- Every label a word of `ws` names is named by a counted word of an old binding, of no larger
`rts` (the `CntOld`). -/
def CntOld (th : TTh) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∀ l, Names l w → ∃ b ∈ TermK2a.Binds th, ∃ w0 ∈ pubWords b.2.1 b.2.2, Names l w0 ∧ w0.rts ≤ w.rts

theorem cntOld_of_rtsSub {th : TTh} {ws wsP : List Word} (hs : RtsSub wsP ws) (h : CntOld th ws) :
    CntOld th wsP := by
  intro w hw l hn
  obtain ⟨w1, h1, hn1, hr1⟩ := hs w hw l hn
  obtain ⟨b, hb, w0, h0, hn0, hr0⟩ := h w1 h1 l hn1
  exact ⟨b, hb, w0, h0, hn0, Nat.le_trans hr0 hr1⟩

/-- An atom's value is a binding's (a variable) or names nothing (a literal, unit). -/
theorem cntOld_evalAt {th : TTh} {v : At} {rt : Ty} {ws : List Word} (h : evalAt th.env v = some (rt, ws)) :
    CntOld th (pubWords rt ws) := by
  cases v with
  | var x =>
    have hm := TermNoFul.lookupE_mem h
    exact fun w hw _ hn => ⟨(x, rt, ws), TermK2a.mem_binds_env hm, w, hw, hn, Nat.le_refl _⟩
  | lit n =>
    simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine cntOld_of_rtsSub (rtsSub_trans ?_ (rtsSub_refl [cst (.num n)])) (fun w hw l hn => ?_)
    · rw [pubWords.eq_def]; simp only []; split
      · exact rtsSub_refl _
      · exact rtsSub_nil _
    · rw [List.mem_singleton] at hw; subst hw; exact absurd hn (not_names_num n l)
  | unit =>
    simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun w hw => by
      rw [pubWords.eq_def] at hw; simp only [] at hw; split at hw <;> cases hw

/-- **A one-binding step with an old-covered result satisfies the contract.** -/
theorem stepOK_of_cntOld {sto : Sto} {s : St} {a : AllocLabel} {N Gl : AllocLabel → Prop} {th thP : TTh}
    {x : String} {rt : Ty} {ws : List Word}
    (he : thP.env = (x, rt, ws) :: th.env) (hst : thP.stack = th.stack) (h : CntOld th (pubWords rt ws)) :
    StepOK sto s a N Gl th thP := by
  have hv : TermK2a.ValB sto s a N th rt ws := by
    intro w hw
    refine ⟨.inl fun hn => h w hw a hn, .inl fun l hn => ?_⟩
    obtain ⟨b, hb, w0, h0, hn0, -⟩ := h w hw l hn
    exact ⟨b, hb, w0, h0, hn0⟩
  refine ⟨TermK2a.stepB_let he hst hv, fun b hb => ?_⟩
  unfold TermK2a.Binds at hb
  rw [he, hst] at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_cons.1 hb with e | hb
    · subst e
      refine .inr fun w hw l hn => .inr ?_
      obtain ⟨b, hb, w0, h0, hn0, -⟩ := h w hw l hn
      exact ⟨b, hb, w0, h0, hn0⟩
    · exact .inl (TermK2a.mem_binds_env hb)
  · exact .inl (List.mem_append_right _ hb)

/-! ## 7. The non-boxed sum contracts -/

/-- **`inl`, non-boxed** (mirrors `tstepM_inl`). -/
theorem sum_inl {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum t τ)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (sto : Sto) (Gl : AllocLabel → Prop) (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
      cases hop with
      | inl _ hu _ =>
          obtain ⟨-, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
          have hS : (Ty.sum rt (close th.σs τ)).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum _ τ)) (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, -, -⟩ := inl_value hv hl hS
          have hta := (tier_sum hS).1
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine stepOK_of_cntOld rfl rfl (cntOld_of_rtsSub ?_ (cntOld_evalAt hea))
          obtain ⟨jP, pP, arm, hasP, harm, hp, -⟩ := asArm_valid rt ws hl.2.2.2.1 hl.1 hta
          rw [has] at hasP
          simp only [Option.some.injEq, Prod.mk.injEq] at hasP
          obtain ⟨rfl, rfl⟩ := hasP
          have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
          have harmS : (armsOf (.sum rt (close th.σs τ)))[j]? = some arm := by
            simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
          have h1 := cnt_inj _ hq harmS hp
          simp only [pubArm, hj, ite_true] at h1
          exact rtsSub_trans h1 (cnt_proj rt hta has (rel_refl _))

/-- **`inr`, non-boxed** (mirrors `tstepM_inr`). -/
theorem sum_inr {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum τ t)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (sto : Sto) (Gl : AllocLabel → Prop) (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
      cases hop with
      | inr _ hu _ =>
          obtain ⟨-, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
          have hS : (Ty.sum (close th.σs τ) rt).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum τ _)) (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, -, -⟩ := inr_value hv hl hS
          have hta := (tier_sum hS).2
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine stepOK_of_cntOld rfl rfl (cntOld_of_rtsSub ?_ (cntOld_evalAt hea))
          obtain ⟨jP, pP, arm, hasP, harm, hp, -⟩ := asArm_valid rt ws hl.2.2.2.1 hl.1 hta
          rw [has] at hasP
          simp only [Option.some.injEq, Prod.mk.injEq] at hasP
          obtain ⟨rfl, rfl⟩ := hasP
          generalize hm : (armsOf (close th.σs τ)).length = m at hq
          have harmS : (armsOf (.sum (close th.σs τ) rt))[m + j]? = some arm := by
            simp only [armsOf]; rw [List.getElem?_append_right (by omega)]
            rw [hm, Nat.add_sub_cancel_left]; exact harm
          have h1 := cnt_inj _ hq harmS hp
          have hnl : ¬ m + j < m := by omega
          simp only [pubArm, hm, Nat.add_sub_cancel_left, hnl, ite_false] at h1
          exact rtsSub_trans h1 (cnt_proj rt hta has (rel_refl _))

/-- **`case`, non-boxed** (mirrors `tstepM_case`). -/
theorem sum_case {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs t).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (htv : TvOK cx)
    (sto : Sto) (Gl : AllocLabel → Prop) (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  obtain ⟨ra, rb, ws, j, pP, hea, hS, has, hA, hB⟩ := case_step hT hi hnb htv
  obtain ⟨hta, htb⟩ := tier_sum hS
  -- the scrutinee's payload fits its arm
  obtain ⟨arm, harm, hp⟩ : ∃ arm, (armsOf (.sum ra rb))[j]? = some arm ∧ PayOK arm pP := by
    cases hT with
    | case hu _ _ _ _ =>
      obtain ⟨-, rt, ws0, hea0, -, hl⟩ := use_FInv hu hi
      rw [hea] at hea0
      simp only [Option.some.injEq, Prod.mk.injEq] at hea0
      obtain ⟨rfl, rfl⟩ := hea0
      obtain ⟨jP, p0, arm, hasP, harm, hp, -⟩ := asArm_valid _ ws hl.2.2.2.1 hl.1 hS
      rw [has] at hasP
      simp only [Option.some.injEq, Prod.mk.injEq] at hasP
      obtain ⟨rfl, rfl⟩ := hasP
      exact ⟨arm, harm, hp⟩
  have hold := cnt_proj (.sum ra rb) hS has (rel_refl pP)
  have hco := cntOld_evalAt (th := th) hea
  by_cases hj : j < (armsOf ra).length
  · obtain ⟨q, hq, -⟩ := hA hj
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_true, injM_nb hta, hq, List.map_cons, List.map_nil,
      List.append_nil]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine stepOK_of_cntOld rfl rfl (cntOld_of_rtsSub ?_ hco)
    have harmP : (armsOf ra)[j]? = some arm := by
      simp only [armsOf] at harm; rwa [List.getElem?_append_left hj] at harm
    simp only [pubArm, hj, ite_true] at hold
    exact rtsSub_trans (cnt_inj ra hq harmP hp) hold
  · obtain ⟨q, hq, -⟩ := hB (by omega)
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_false, injM_nb htb, hq, List.map_cons, List.map_nil,
      List.append_nil]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine stepOK_of_cntOld rfl rfl (cntOld_of_rtsSub ?_ hco)
    have harmP : (armsOf rb)[j - (armsOf ra).length]? = some arm := by
      simp only [armsOf] at harm; rwa [List.getElem?_append_right (by omega)] at harm
    simp only [pubArm, hj, ite_false] at hold
    exact rtsSub_trans (cnt_inj rb hq harmP hp) hold

/-! ## 8. Regions: the new bindings count no words -/

theorem pubWords_rgn (u : Ty) (ws : List Word) : pubWords (.ptr (.rgn (.lit 0)) u) ws = [] := by
  simp [pubWords, sNo, mPub]

theorem pubWords_rgnLoc (u : Ty) (ψ : Pred) (ws : List Word) :
    pubWords (.refine (.loc (.rgn (.lit 0)) u) ψ) ws = [] := by
  rw [pubWords_refine]; simp [pubWords, sNo, mPub]

/-- Two new bindings counting no words. -/
theorem stepOK_of_nil2 {sto : Sto} {s : St} {a : AllocLabel} {N Gl : AllocLabel → Prop} {th thP : TTh}
    {b1 b2 : String × Ty × List Word}
    (he : thP.env = b1 :: b2 :: th.env) (hst : thP.stack = th.stack)
    (h1 : pubWords b1.2.1 b1.2.2 = []) (h2 : pubWords b2.2.1 b2.2.2 = []) :
    StepOK sto s a N Gl th thP := by
  have hb : ∀ b ∈ TermK2a.Binds thP, b ∈ TermK2a.Binds th ∨ pubWords b.2.1 b.2.2 = [] := by
    intro b hb
    unfold TermK2a.Binds at hb
    rw [he, hst] at hb
    rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_cons.1 hb with e | hb
      · subst e; exact .inr h1
      · rcases List.mem_cons.1 hb with e | hb
        · subst e; exact .inr h2
        · exact .inl (TermK2a.mem_binds_env hb)
    · exact .inl (List.mem_append_right _ hb)
  refine ⟨fun b hbb => ?_, fun b hbb => ?_⟩
  · rcases hb b hbb with h | h
    · exact .inl h
    · exact .inr fun w hw => by rw [h] at hw; cases hw
  · rcases hb b hbb with h | h
    · exact .inl h
    · exact .inr fun w hw => by rw [h] at hw; cases hw

/-- **`region`** (mirrors `tstepM_region`): a region pointer and a token, neither counted. -/
theorem rgn_region {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e)
    (sto : Sto) (Gl : AllocLabel → Prop) (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  intro r hr
  simp only [tstep, hterm] at hr
  split at hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact stepOK_of_nil2 rfl rfl (by rw [pubWords.eq_def]; simp) (pubWords_rgn _ _)
  · simp only [List.mem_singleton] at hr; subst hr
    exact stepOK_of_nil2 rfl rfl (by rw [pubWords.eq_def]; simp) (pubWords_rgnLoc _ _ _)
  · cases hr

/-- **`openPub`** (mirrors `tstepM_openPub`): a region pointer and a capability, neither counted. -/
theorem rgn_openPub {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {a : At} {rn pn cn : String} {e : Expr}
    (hterm : th.term = .openPub a rn pn cn e)
    (sto : Sto) (Gl : AllocLabel → Prop) (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  intro r hr
  simp only [tstep, hterm] at hr
  split at hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact stepOK_of_nil2 rfl rfl (by rw [pubWords.eq_def]; simp) (pubWords_rgn _ _)
  · cases hr

/-! ## 9. `publish` -/

/-- A word of a one-reference value names only the reference's label. -/
theorem names_of_map {ws : List Word} {ad : Address} (h : ws.map (·.val) = [.loc ad 0]) :
    ∀ w ∈ ws, ∀ l, Names l w → l = ad.label := by
  intro w hw l hn
  match ws, h with
  | [w0], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      rw [List.mem_singleton] at hw; subst hw
      obtain ⟨aP, gP, hv, hl⟩ := hn
      rw [h] at hv; cases hv; exact hl.symm
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

theorem not_names_of_null {ws : List Word} (h : ws.map (·.val) = [.null]) : ∀ w ∈ ws, ∀ l, ¬ Names l w := by
  intro w hw l hn
  match ws, h with
  | [w0], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      rw [List.mem_singleton] at hw; subst hw
      obtain ⟨aP, gP, hv, -⟩ := hn
      rw [h] at hv; cases hv
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

/-- **`publish`** (mirrors `tstepM_publish`, both typing rules).  The published reference's words
are counted only now: for (R) the gated label is not the published one (`hnp`, the Solo
discipline); for `ThLbl` and `N` the published label is in the new frontier (`hNp`, `hGp`). -/
theorem pub_publish {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.publish a) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    (hnp : ¬ PubAt th ga) (hNp : ∀ l, PubAt th l → N l) (hGp : ∀ l, PubAt th l → Gl l) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  -- every word of the operand names only the published label
  have hW : ∀ rt ws, evalAt th.env a = some (rt, ws) → ∀ w ∈ ws, ∀ l, Names l w → PubAt th l := by
    intro rt0 ws0 hea0 w hw l hn
    rw [hterm] at hT
    cases hT with
    | let_ hop _ =>
    cases hop with
    | publish hu _ _ =>
      obtain ⟨-, rt, ws, hea, hv, -⟩ := use_FInv hu hi
      rw [hea0] at hea; simp only [Option.some.injEq, Prod.mk.injEq] at hea; obtain ⟨rfl, rfl⟩ := hea
      simp only [VR] at hv
      obtain ⟨ad, c, hws, -⟩ := hv
      exact ⟨x, a, e, rt0, ws0, ad, hterm, hea0, hws, (names_of_map hws w hw l hn).symm⟩
    | publishBuf hu _ _ =>
      obtain ⟨-, rt, ws, hea, hv, -⟩ := use_FInv hu hi
      rw [hea0] at hea; simp only [Option.some.injEq, Prod.mk.injEq] at hea; obtain ⟨rfl, rfl⟩ := hea
      simp only [VR] at hv
      rcases hv.1 with ⟨hnull, -⟩ | ⟨ad, c, U, hws, -⟩
      · exact absurd hn (not_names_of_null hnull w hw l)
      · exact ⟨x, a, e, rt0, ws0, ad, hterm, hea0, hws, (names_of_map hws w hw l hn).symm⟩
  have fin : ∀ thP rt ws, thP.env = (x, rt, ws) :: th.env → thP.stack = th.stack →
      (∀ w ∈ pubWords rt ws, ∀ l, Names l w → PubAt th l) →
      StepOK sto (stOf mem pairs th) ga N Gl th thP := by
    intro thP rt ws he hst hP
    have hv : TermK2a.ValB sto (stOf mem pairs th) ga N th rt ws := fun w hw =>
      ⟨.inl fun hn => absurd (hP w hw ga hn) hnp, .inr (.inr fun l hn => hNp l (hP w hw l hn))⟩
    refine ⟨TermK2a.stepB_let he hst hv, fun b hb => ?_⟩
    unfold TermK2a.Binds at hb
    rw [he, hst] at hb
    rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_cons.1 hb with e | hb
      · subst e; exact .inr fun w hw l hn => .inl (hGp l (hP w hw l hn))
      · exact .inl (TermK2a.mem_binds_env hb)
    · exact .inl (List.mem_append_right _ hb)
  intro r hr
  simp only [tstep, hterm, evalOp] at hr
  cases hea : evalAt th.env a with
  | none => simp [hea, ol] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    have hWP := hW t ws hea
    simp only [hea, bind, Option.bind] at hr
    split at hr
    · simp only [ol, pure, Option.toList, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨_, rfl, rfl⟩ := hr
      refine fin _ _ _ rfl rfl fun w hw => hWP w ?_
      rwa [pubWords_of_sNo (by rfl)] at hw
    · simp only [ol, pure, Option.toList, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨_, rfl, rfl⟩ := hr
      refine fin _ _ _ rfl rfl fun w hw => hWP w ?_
      rwa [pubWords_refine, pubWords_of_sNo (by rfl)] at hw
    · simp [ol] at hr

/-! ## 10. Injection into a boxed sum: a fresh box reference -/

/-- A step binding one new value whose counted words name only labels of `Q`, with `Q` excluding the
gated label and inside `N` and `Gl`, satisfies the contract. -/
theorem stepOK_of_new {sto : Sto} {s : St} {a : AllocLabel} {N Gl Q : AllocLabel → Prop} {th thP : TTh}
    {x : String} {rt : Ty} {ws : List Word}
    (he : thP.env = (x, rt, ws) :: th.env) (hst : thP.stack = th.stack)
    (hP : ∀ w ∈ pubWords rt ws, ∀ l, Names l w → Q l) (hna : ¬ Q a) (hN : ∀ l, Q l → N l)
    (hG : ∀ l, Q l → Gl l) : StepOK sto s a N Gl th thP := by
  have hv : TermK2a.ValB sto s a N th rt ws := fun w hw =>
    ⟨.inl fun hn => absurd (hP w hw a hn) hna, .inr (.inr fun l hn => hN l (hP w hw l hn))⟩
  refine ⟨TermK2a.stepB_let he hst hv, fun b hb => ?_⟩
  unfold TermK2a.Binds at hb
  rw [he, hst] at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_cons.1 hb with e | hb
    · subst e; exact .inr fun w hw l hn => .inl (hG l (hP w hw l hn))
    · exact .inl (TermK2a.mem_binds_env hb)
  · exact .inl (List.mem_append_right _ hb)

/-- A boxed injection's result is the fresh box's reference, and the allocation bumps `nalloc`. -/
theorem injM_boxW {g : G} {s : St} {t : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (hb : isBoxed t = true) (h : r ∈ injM g s t j p) :
    ∃ pw, r.2 = [pw] ∧ (∀ l, Names l pw → l = freshLabel g.lbase g.n g.i s.nalloc) ∧
      r.1.nalloc = s.nalloc + 1 := by
  simp only [injM, hb, ite_true] at h
  split at h
  · rw [List.mem_map] at h
    obtain ⟨⟨sP, pw⟩, hal, rfl⟩ := h
    simp only [alloc, List.mem_map] at hal
    obtain ⟨s0, hs0, e⟩ := hal
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hn := TermTyped.storeUnits_nallocT _ _ _ _ s0 hs0
    refine ⟨_, rfl, fun l hn => ?_, ?_⟩
    · obtain ⟨aP, gP, hv, hl⟩ := hn
      have e : (cst (.loc ⟨freshLabel g.lbase g.n g.i s.nalloc, 0⟩ 0)).val =
          .loc ⟨freshLabel g.lbase g.n g.i s.nalloc, 0⟩ 0 := rfl
      rw [e] at hv; cases hv; exact hl.symm
    · dsimp only at hn ⊢
      split <;> simp [fenceS, hn]
  · cases h

/-- A boxed sum counts all its words (the box reference). -/
theorem pubWords_boxedSum {a b : Ty} (h : (Ty.sum a b).tier = .boxed) (ws : List Word) :
    pubWords (.sum a b) ws = ws := by
  simp only [pubWords, h, ite_true]; split <;> rfl

/-- **A boxed injection's binding** (per result): its only counted label is the fresh box's, which
is `FreshIn` the step and named by the new binding; so the per-result fresh-label hypotheses give
the contract. -/
theorem freshArm {mem : Memory} {pairs : List Ts} {g : G} {th : TTh} {sto : Sto} {Gl N : AllocLabel → Prop}
    {ga : AllocLabel} {s1 : St} (hn1 : s1.nalloc = th.nalloc) {ty : Ty} {j : Nat} {p : List Word}
    (hb : isBoxed ty = true) {r2 : St × List Word} (h3 : r2 ∈ injM g s1 ty j p) {x : String} {e : Expr}
    (hfa : ∀ l, FreshIn g th.nalloc r2.1.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r2.1.nalloc l →
      (∃ b ∈ (x, ty, r2.2) :: th.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r2.1.nalloc l →
      (∃ b ∈ (x, ty, r2.2) :: th.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th
      (withS { th with term := e, env := (x, ty, r2.2) :: th.env } r2.1) := by
  obtain ⟨pw, hq, hpw, hnl⟩ := injM_boxW hb h3
  refine stepOK_of_new (Q := fun l => FreshIn g th.nalloc r2.1.nalloc l ∧
      ∃ b ∈ (x, ty, r2.2) :: th.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) rfl rfl ?_
    (fun h => hfa ga h.1 rfl) (fun l h => hNf l h.1 h.2) (fun l h => hGf l h.1 h.2)
  intro w hw l hn
  refine ⟨?_, ⟨(x, ty, r2.2), List.mem_cons_self .., w, hw, hn⟩⟩
  have hw0 := hw
  rw [hq] at hw0
  obtain ⟨w0, h0, hn0⟩ := (pubWords_lblSub ty).1 [pw] w hw0 l hn
  rw [List.mem_singleton] at h0; subst h0
  refine ⟨th.nalloc, Nat.le_refl _, by omega, ?_⟩
  rw [← hn1]; exact hpw l hn0

/-- **`inl` into a boxed sum**, per result (mirrors `tstepM_inlB` and `tstepM_inlBB`). -/
theorem sum_inlBR {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {τ : Ty} {a : At} {e : Expr}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inl τ a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed)
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hSb : isBoxed (Ty.sum rt (close th.σs τ)) = true := by simp [isBoxed, sumHead, hS]
  simp only [tstep, hterm, evalOp, hea, List.mem_map, List.mem_flatMap] at hr
  obtain ⟨_, ⟨⟨s1, j, p⟩, h1, ⟨s2, q⟩, h2, rfl⟩, rfl⟩ := hr
  exact freshArm (TermStepper.projM_nalloc h1) hSb h2 hfa hNf hGf

/-- **`inr` into a boxed sum**, per result (mirrors `tstepM_inrB` and `tstepM_inrBB`). -/
theorem sum_inrBR {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {τ : Ty} {a : At} {e : Expr}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inr τ a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed)
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hSb : isBoxed (Ty.sum (close th.σs τ) rt) = true := by simp [isBoxed, sumHead, hS]
  simp only [tstep, hterm, evalOp, hea, List.mem_map, List.mem_flatMap] at hr
  obtain ⟨_, ⟨⟨s1, j, p⟩, h1, ⟨s2, q⟩, h2, rfl⟩, rfl⟩ := hr
  exact freshArm (TermStepper.projM_nalloc h1) hSb h2 hfa hNf hGf

/-- **`inl`, every tier**, per result (mirrors `tstepM_inlT`). -/
theorem sum_inlTR {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | inl _ hu _ =>
      obtain ⟨-, rt, ws, hea, -, hl⟩ := use_FInv hu hi
      have hsk : (Ty.sum rt (close th.σs τ)).tier = (close th.σs (.sum _ τ)).tier :=
        tier_of_eskel (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)
      by_cases hS : (Ty.sum rt (close th.σs τ)).tier = .boxed
      · exact sum_inlBR hterm hea hS sto hr hfa hNf hGf
      · refine sum_inl hterm (fun tP c₁P huP => ?_) hT hi sto Gl ga N r hr
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at huP; obtain ⟨rfl, rfl⟩ := huP
        rw [← hsk]; exact hS

/-- **`inr`, every tier**, per result (mirrors `tstepM_inrT`). -/
theorem sum_inrTR {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | inr _ hu _ =>
      obtain ⟨-, rt, ws, hea, -, hl⟩ := use_FInv hu hi
      have hsk : (Ty.sum (close th.σs τ) rt).tier = (close th.σs (.sum τ _)).tier :=
        tier_of_eskel (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)
      by_cases hS : (Ty.sum (close th.σs τ) rt).tier = .boxed
      · exact sum_inrBR hterm hea hS sto hr hfa hNf hGf
      · refine sum_inr hterm (fun tP c₁P huP => ?_) hT hi sto Gl ga N r hr
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at huP; obtain ⟨rfl, rfl⟩ := huP
        rw [← hsk]; exact hS

/-! ## 11. `case` on a boxed scrutinee -/

/-- **The missing box-load contract** (open): the payload projected out of the scrutinee's box
into a non-boxed summand is new-fine and its labels are new-fine.  Stated as a premise; the fixed
`NewW` has no box-load disjunct. -/
def BoxArmOK (g : G) (s : St) (sto : Sto) (ga : AllocLabel) (N Gl : AllocLabel → Prop) (th : TTh)
    (S : Ty) (ws : List Word) : Prop :=
  ∀ s1 j p, (s1, j, p) ∈ projM g s S ws → ∀ ty jP q, isBoxed ty = false → ofArm ty jP p = some q →
    TermK2a.ValB sto s ga N th ty q ∧ ∀ w ∈ pubWords ty q, ∀ l, Names l w → LblNew Gl th l

theorem stepOK_of_valB {sto : Sto} {s : St} {a : AllocLabel} {N Gl : AllocLabel → Prop} {th thP : TTh}
    {x : String} {rt : Ty} {ws : List Word}
    (he : thP.env = (x, rt, ws) :: th.env) (hst : thP.stack = th.stack) (hv : TermK2a.ValB sto s a N th rt ws)
    (hl : ∀ w ∈ pubWords rt ws, ∀ l, Names l w → LblNew Gl th l) : StepOK sto s a N Gl th thP := by
  refine ⟨TermK2a.stepB_let he hst hv, fun b hb => ?_⟩
  unfold TermK2a.Binds at hb
  rw [he, hst] at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_cons.1 hb with e | hb
    · subst e; exact .inr hl
    · exact .inl (TermK2a.mem_binds_env hb)
  · exact .inl (List.mem_append_right _ hb)

/-- One arm of a boxed `case`, per result: re-boxed (fresh reference) or rebuilt from the box
payload. -/
theorem caseB_arm {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {sto : Sto} {Gl N : AllocLabel → Prop}
    {ga : AllocLabel} {S : Ty} {ws : List Word} {s1 : St} {j : Nat} {p : List Word}
    (h1 : (s1, j, p) ∈ projM g (stOf mem pairs th) S ws)
    (hArm : BoxArmOK g (stOf mem pairs th) sto ga N Gl th S ws)
    {ty : Ty} {jP : Nat} {x : String} {e : Expr} {r2 : St × List Word} (h3 : r2 ∈ injM g s1 ty jP p)
    (hfa : ∀ l, FreshIn g th.nalloc r2.1.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r2.1.nalloc l →
      (∃ b ∈ (x, ty, r2.2) :: th.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r2.1.nalloc l →
      (∃ b ∈ (x, ty, r2.2) :: th.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th
      (withS { th with term := e, env := (x, ty, r2.2) :: th.env } r2.1) := by
  cases hb : isBoxed ty with
  | true => exact freshArm (TermStepper.projM_nalloc h1) hb h3 hfa hNf hGf
  | false =>
    rw [injM_nbB hb] at h3
    simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h3
    obtain ⟨q, hq, rfl⟩ := h3
    obtain ⟨hv, hl⟩ := hArm s1 j p h1 ty jP q hb hq
    exact stepOK_of_valB rfl rfl hv hl

/-- **`case` on a boxed scrutinee**, per result (mirrors `tstepM_caseB`); the non-boxed-summand
subcase under the open box-load premise `hArm`. -/
theorem sum_caseBR {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {a : At} {x y : String} {e₁ e₂ : Expr}
    {ra rb : Ty} {ws : List Word} (hterm : th.term = .case a x e₁ y e₂)
    (hea : evalAt th.env a = some (.sum ra rb, ws))
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    (hArm : BoxArmOK g (stOf mem pairs th) sto ga N Gl th (.sum ra rb) ws)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  simp only [tstep, hterm, hea, List.mem_flatMap] at hr
  obtain ⟨⟨s1, j, p⟩, h1, h2⟩ := hr
  by_cases hj : j < (armsOf ra).length
  · simp only [hj, ite_true, List.mem_map] at h2
    obtain ⟨r2, h3, rfl⟩ := h2
    exact caseB_arm h1 hArm h3 hfa hNf hGf
  · simp only [hj, ite_false, List.mem_map] at h2
    obtain ⟨r2, h3, rfl⟩ := h2
    exact caseB_arm h1 hArm h3 hfa hNf hGf

/-- **`case`, every tier**, per result (mirrors `tstepM_caseT`): non-boxed by `sum_case`, boxed by
`sum_caseBR` under the open box-load premise. -/
theorem sum_caseTR {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (htv : TvOK cx)
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    (hArm : ∀ ra rb ws, evalAt th.env a = some (.sum ra rb, ws) → (Ty.sum ra rb).tier = .boxed →
      BoxArmOK g (stOf mem pairs th) sto ga N Gl th (.sum ra rb) ws)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | case hu _ _ _ _ =>
    obtain ⟨-, rt, ws, hea, -, hl⟩ := use_FInv hu hi
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · exact sum_caseBR hterm hea sto (hArm ra rb ws hea hS) hr hfa hNf hGf
    · refine sum_case hterm (fun tP c₁P huP => ?_) hT hi htv sto Gl ga N r hr
      rw [hu, Except.ok.injEq, Prod.mk.injEq] at huP; obtain ⟨rfl, rfl⟩ := huP
      rw [← tier_of_eskel hl.2.1]; exact hS

end TermK2aSum

#print axioms TermK2aSum.sum_inl
#print axioms TermK2aSum.sum_inr
#print axioms TermK2aSum.sum_case
#print axioms TermK2aSum.sum_inlBR
#print axioms TermK2aSum.sum_inrBR
#print axioms TermK2aSum.sum_inlTR
#print axioms TermK2aSum.sum_inrTR
#print axioms TermK2aSum.sum_caseBR
#print axioms TermK2aSum.sum_caseTR
#print axioms TermK2aSum.pub_publish
#print axioms TermK2aSum.rgn_region
#print axioms TermK2aSum.rgn_openPub
