import WeakCore.TermPtrRts

/-!
# TermCntLoc: unit-locality of the counted positions

Whether position `i` of a value of a layout type `S` is counted (`cntIdx`) depends only on the
values at the positions of `i`'s access unit up to `i` (`cnt_window`): `i` alone at a one-word
unit or at the first word of a granule, both words at a granule's second.  So the untyped
`CntOK`/`CntPairOK` (any value of the right shape) agree with the typed reading (`MemOKP`'s
witness).
-/

namespace TermCntLoc
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts
open WeakMem (Ts)

/-! ## 1. Values and read timestamps -/

/-- Equal values and read timestamps, pointwise. -/
def VR (ws ws' : List Word) : Prop := ws.map (fun w => (w.val, w.rts)) = ws'.map (fun w => (w.val, w.rts))

theorem vr_rts {ws ws' : List Word} (e : VR ws ws') : ws.map (·.rts) = ws'.map (·.rts) := by
  have := congrArg (List.map Prod.snd) e
  simp only [List.map_map] at this
  exact this

theorem vr_veq {ws ws' : List Word} (e : VR ws ws') : VEq ws ws' := by
  have := congrArg (List.map Prod.fst) e
  simp only [List.map_map] at this
  exact this

theorem vr_take {ws ws' : List Word} (e : VR ws ws') (n : Nat) : VR (ws.take n) (ws'.take n) := by
  simp only [VR, List.map_take]; rw [e]

theorem vr_drop {ws ws' : List Word} (e : VR ws ws') (n : Nat) : VR (ws.drop n) (ws'.drop n) := by
  simp only [VR, List.map_drop]; rw [e]

theorem vr_append {a b a' b' : List Word} (h1 : VR a a') (h2 : VR b b') : VR (a ++ b) (a' ++ b') := by
  simp only [VR, List.map_append]; rw [h1, h2]

theorem vr_one {w : Word} {ws' : List Word} (e : VR [w] ws') :
    ∃ w', ws' = [w'] ∧ w'.val = w.val ∧ w'.rts = w.rts := by
  match ws', e with
  | [w'], e => simp [VR] at e; exact ⟨w', rfl, e.1.symm, e.2.symm⟩
  | [], e => simp [VR] at e
  | _ :: _ :: _, e => simp [VR] at e

theorem vr_two {t w : Word} {ws' : List Word} (e : VR [t, w] ws') :
    ∃ t' w', ws' = [t', w'] ∧ t'.val = t.val ∧ w'.val = w.val ∧ w'.rts = w.rts := by
  match ws', e with
  | [t', w'], e => simp [VR] at e; exact ⟨t', w', rfl, e.1.1.symm, e.2.1.symm, e.2.2.symm⟩
  | [], e => simp [VR] at e
  | [_], e => simp [VR] at e
  | _ :: _ :: _ :: _, e => simp [VR] at e

theorem decodeArm_vr {tr : Tier} {as : List Ty} {ws ws' : List Word} {j : Nat} {p : List Word}
    (e : VR ws ws') (h : decodeArm tr as ws = some (j, p)) :
    ∃ p', decodeArm tr as ws' = some (j, p') ∧ VR p p' := by
  cases tr with
  | boxed => simp [decodeArm] at h
  | niche =>
      rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · simp [decodeArm] at h
      · obtain ⟨w', rfl, ew, er⟩ := vr_one e
        simp only [decodeArm] at h ⊢
        rw [ew]
        cases hw : w.val with
        | loc a g =>
            rw [hw] at h
            cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
            | none => simp [h1, bind, Option.bind] at h
            | some pr =>
                simp [h1, bind, Option.bind, pure] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨[{ w' with val := .loc a 0 }], by simp [h1, bind, Option.bind, pure], by simp [VR, er]⟩
        | num k =>
            rw [hw] at h
            exact ⟨p, h, rfl⟩
        | _ => rw [hw] at h; simp at h
      · simp [decodeArm] at h
  | wide =>
      rcases ws with _ | ⟨t, _ | ⟨w, _ | ⟨w3, rest⟩⟩⟩
      · simp [decodeArm] at h
      · simp [decodeArm] at h
      · obtain ⟨t', w', rfl, et, ew, er⟩ := vr_two e
        simp only [decodeArm] at h ⊢
        rw [et]
        cases ht : t.val with
        | num k =>
            rw [ht] at h
            cases h1 : as[k]? with
            | none => simp [h1, bind, Option.bind] at h
            | some a =>
                simp only [h1, bind, Option.bind] at h ⊢
                by_cases hr : a.rawWords = some 0
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; simp [VR]
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; simp [VR, ew, er]
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

/-- The counted words read only values and read timestamps. -/
theorem pubWords_vr : ∀ (R : Ty),
    (∀ ws ws', VR ws ws' → VR (pubWords R ws) (pubWords R ws')) ∧
    (∀ j p p', VR p p' → VR (pubArm R j p) (pubArm R j p')) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws ws', VR ws ws' → VR (pubWords (.prod a b) ws) (pubWords (.prod a b) ws') := by
        intro ws ws' e
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact vr_append (iha.1 _ _ (vr_take e _)) (ihb.1 _ _ (vr_drop e _))
          · rfl
      exact ⟨h1, fun j p p' e => by simp only [pubArm]; exact h1 p p' e⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p p', VR p p' → VR (pubArm (.sum a b) j p) (pubArm (.sum a b) j p') := by
        intro j p p' e
        simp only [pubArm]
        split
        · exact iha.2 _ _ _ e
        · exact ihb.2 _ _ _ e
      refine ⟨fun ws ws' e => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact e
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none =>
            cases hd' : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws' with
            | none => rfl
            | some x =>
              obtain ⟨j, p⟩ := x
              obtain ⟨p', hp', -⟩ := decodeArm_vr e.symm hd'
              rw [hd] at hp'; cases hp'
          | some x =>
            obtain ⟨j, p⟩ := x
            obtain ⟨p', hp', ep⟩ := decodeArm_vr e hd
            simp only [hp']
            split
            · exact iha.2 _ _ _ ep
            · exact ihb.2 _ _ _ ep
  | refine t ψ ih =>
      exact ⟨fun ws ws' e => by rw [pubWords_refine, pubWords_refine]; exact ih.1 _ _ e,
        fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
  | iall t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | iex t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | mu t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | tex κ t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | _ =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => ?_⟩
      · rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact e
        · rfl
      · simp only [pubArm]; rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact e
        · rfl

/-! ## 2. Where counted words come from -/

/-- Every word of `l` has read timestamp `0` or one of `ws`'s. -/
def RtsIn (ws l : List Word) : Prop := ∀ w ∈ l, w.rts = 0 ∨ w.rts ∈ ws.map (·.rts)

theorem rtsIn_refl (ws : List Word) : RtsIn ws ws := fun _ hw => .inr (List.mem_map_of_mem hw)

theorem rtsIn_nil (ws : List Word) : RtsIn ws [] := fun _ h => by simp at h

theorem rtsIn_trans {a b c : List Word} (h1 : RtsIn a b) (h2 : RtsIn b c) : RtsIn a c := by
  intro w hw
  rcases h2 w hw with h | h
  · exact .inl h
  · obtain ⟨w', hw', e⟩ := List.mem_map.1 h
    rw [← e]; exact h1 w' hw'

theorem rtsIn_take (ws : List Word) (n : Nat) : RtsIn ws (ws.take n) :=
  fun _ hw => .inr (List.mem_map_of_mem (List.mem_of_mem_take hw))

theorem rtsIn_drop (ws : List Word) (n : Nat) : RtsIn ws (ws.drop n) :=
  fun _ hw => .inr (List.mem_map_of_mem (List.mem_of_mem_drop hw))

theorem rtsIn_append {ws a b : List Word} (h1 : RtsIn ws a) (h2 : RtsIn ws b) : RtsIn ws (a ++ b) := by
  intro w hw
  rcases List.mem_append.1 hw with h | h
  · exact h1 w h
  · exact h2 w h

/-- The decoded payload's non-synthetic words are the last word's. -/
theorem decodeArm_rts {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : decodeArm tr as ws = some (j, p)) :
    ∀ w ∈ p, w.rts = 0 ∨ ∃ w0, ws[ws.length - 1]? = some w0 ∧ w0.rts = w.rts := by
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
                intro x hx
                simp at hx; subst hx
                exact .inr ⟨w, rfl, rfl⟩
        | num k =>
            rw [hw] at h
            simp only [bind, Option.bind] at h
            cases h1 : as[k]? with
            | none => simp [h1] at h
            | some arm =>
                simp only [h1] at h
                intro x hx
                cases hk : armK arm <;> simp [hk, pure] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
                  simp at hx
                subst hx; exact .inl rfl
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
                intro x hx
                by_cases hr : a.rawWords = some 0
                · simp [hr, pure] at h; obtain ⟨rfl, rfl⟩ := h; simp at hx
                · simp [hr, pure] at h; obtain ⟨rfl, rfl⟩ := h
                  simp at hx; subst hx; exact .inr ⟨x, rfl, rfl⟩
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

/-- The counted words' read timestamps are `0` or the input's. -/
theorem pubWords_rts : ∀ (R : Ty), (∀ ws, RtsIn ws (pubWords R ws)) ∧ (∀ j p, RtsIn p (pubArm R j p)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws, RtsIn ws (pubWords (.prod a b) ws) := by
        intro ws
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs]; exact rtsIn_refl ws
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact rtsIn_append (rtsIn_trans (rtsIn_take ws _) (iha.1 _))
              (rtsIn_trans (rtsIn_drop ws _) (ihb.1 _))
          · exact rtsIn_nil ws
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p, RtsIn p (pubArm (.sum a b) j p) := by
        intro j p
        simp only [pubArm]
        split
        · exact iha.2 _ _
        · exact ihb.2 _ _
      refine ⟨fun ws => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs]; exact rtsIn_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact rtsIn_refl ws
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none => exact rtsIn_nil ws
          | some x =>
            obtain ⟨j, p⟩ := x
            have hp : RtsIn ws p := by
              intro w hw
              rcases decodeArm_rts hd w hw with h | ⟨w0, h0, e⟩
              · exact .inl h
              · exact .inr (List.mem_map.2 ⟨w0, List.mem_of_getElem? h0, e⟩)
            simp only []
            split
            · exact rtsIn_trans hp (iha.2 _ _)
            · exact rtsIn_trans hp (ihb.2 _ _)
  | refine t ψ ih =>
      exact ⟨fun ws => by rw [pubWords_refine]; exact ih.1 _, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
  | iall t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs]; exact rtsIn_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | iex t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs]; exact rtsIn_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | mu t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs]; exact rtsIn_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | tex κ t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs]; exact rtsIn_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | _ =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only []
        split
        · exact rtsIn_refl ws
        · exact rtsIn_nil ws
      · simp only [pubArm]; rw [pubWords.eq_def]; simp only []
        split
        · exact rtsIn_refl p
        · exact rtsIn_nil p

/-! ## 3. Positions -/

/-- A word's read timestamp, as a `Nat` (for `omega`). -/
def rn (w : Word) : Nat := w.rts

/-- `ws` with each word's read timestamp set to its position past `k`, plus one. -/
def tag (k : Nat) (ws : List Word) : List Word := ws.mapIdx fun i w => { w with rts := i + k + 1 }

/-- Undo `tag`'s shift (`0`: a synthesised word). -/
def rf (n : Nat) : Option Nat := if n = 0 then none else some (n - 1)

/-- The counted positions, offset by `k`. -/
def cntK (S : Ty) (k : Nat) (ws : List Word) : List Nat := ((pubWords S (tag k ws)).map (·.rts)).filterMap rf

theorem cntIdx_eq (S : Ty) (ws : List Word) : cntIdx S ws = cntK S 0 ws := by
  unfold cntIdx cntK tag
  rw [List.filterMap_map]
  simp only [Nat.add_zero]
  rfl

theorem tag_nil (k : Nat) : tag k [] = [] := rfl

theorem tag_cons (k : Nat) (w : Word) (ws : List Word) :
    tag k (w :: ws) = { w with rts := k + 1 } :: tag (k + 1) ws := by
  simp only [tag, List.mapIdx_cons, Nat.zero_add]
  congr 1
  congr 1
  funext i x
  rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega]

theorem tag_length (k : Nat) (ws : List Word) : (tag k ws).length = ws.length := by
  simp [tag]

theorem tag_take : ∀ (k n : Nat) (ws : List Word), (tag k ws).take n = tag k (ws.take n)
  | _, _, [] => by simp [tag_nil]
  | _, 0, _ :: _ => by simp [tag_nil]
  | k, n + 1, w :: ws => by rw [tag_cons, List.take_succ_cons, List.take_succ_cons, tag_cons, tag_take]

theorem tag_drop : ∀ (k n : Nat) (ws : List Word), (tag k ws).drop n = tag (k + n) (ws.drop n)
  | _, _, [] => by simp [tag_nil]
  | _, 0, _ :: _ => by simp
  | k, n + 1, w :: ws => by
      rw [tag_cons, List.drop_succ_cons, List.drop_succ_cons, tag_drop]
      rw [show k + 1 + n = k + (n + 1) by omega]

theorem tag_rts_eq : ∀ (k : Nat) (ws ws2 : List Word), ws.length = ws2.length →
    (tag k ws).map (·.rts) = (tag k ws2).map (·.rts)
  | _, [], [], _ => rfl
  | k, w :: ws, w2 :: ws2, h => by
      rw [tag_cons, tag_cons, List.map_cons, List.map_cons, tag_rts_eq (k + 1) ws ws2 (by simpa using h)]
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

theorem tag_vr : ∀ (k : Nat) (ws ws2 : List Word), VEq ws ws2 → VR (tag k ws) (tag k ws2)
  | _, [], [], _ => rfl
  | k, w :: ws, w2 :: ws2, h => by
      simp only [VEq, List.map_cons, List.cons.injEq] at h
      have ih := tag_vr (k + 1) ws ws2 h.2
      simp only [VR] at ih ⊢
      rw [tag_cons, tag_cons, List.map_cons, List.map_cons, ih, h.1]
  | _, [], _ :: _, h => by simp [VEq] at h
  | _, _ :: _, [], h => by simp [VEq] at h

theorem tag_get (k : Nat) (ws : List Word) (m : Nat) :
    (tag k ws)[m]? = ws[m]?.map fun w => { w with rts := m + k + 1 } := by
  simp [tag, List.getElem?_mapIdx]

theorem mem_tag_rts {k : Nat} {ws : List Word} {w : Word} (h : w ∈ tag k ws) :
    k + 1 ≤ rn w ∧ rn w ≤ k + ws.length := by
  obtain ⟨m, hm, e⟩ := List.getElem_of_mem h
  have h2 : (tag k ws)[m]? = some w := by rw [List.getElem?_eq_getElem hm, e]
  rw [tag_get] at h2
  have hm' : m < ws.length := by rw [tag_length] at hm; exact hm
  rw [List.getElem?_eq_getElem hm'] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  subst h2
  show k + 1 ≤ m + k + 1 ∧ m + k + 1 ≤ k + ws.length
  omega

theorem cntK_range {S : Ty} {k : Nat} {ws : List Word} {x : Nat} (h : x ∈ cntK S k ws) :
    k ≤ x ∧ x < k + ws.length := by
  unfold cntK at h
  obtain ⟨n, hn, hr⟩ := List.mem_filterMap.1 h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hn
  unfold rf at hr
  split at hr
  · cases hr
  · cases hr
    rcases (pubWords_rts S).1 _ w hw with h0 | h1
    · contradiction
    · obtain ⟨w0, hw0, e⟩ := List.mem_map.1 h1
      have e1 : rn w0 = rn w := e
      have h2 := mem_tag_rts hw0
      have h3 : rn w ≠ 0 := by assumption
      show k ≤ rn w - 1 ∧ rn w - 1 < k + ws.length
      omega

theorem cntK_of_veq (S : Ty) (k : Nat) {ws ws2 : List Word} (e : VEq ws ws2) : cntK S k ws = cntK S k ws2 := by
  unfold cntK; rw [vr_rts ((pubWords_vr S).1 _ _ (tag_vr k ws ws2 e))]

theorem cntK_of_id {S : Ty} {k : Nat} {ws ws2 : List Word} (hl : ws.length = ws2.length)
    (h : ∀ L, pubWords S L = L) : cntK S k ws = cntK S k ws2 := by
  unfold cntK; rw [h, h, tag_rts_eq k ws ws2 hl]

theorem cntK_of_sNo {S : Ty} {k : Nat} {ws ws2 : List Word} (hl : ws.length = ws2.length) (hs : sNo S = true) :
    cntK S k ws = cntK S k ws2 :=
  cntK_of_id hl fun L => pubWords_of_sNo hs L

theorem cntK_congr {S S' : Ty} (h : ∀ L, pubWords S L = pubWords S' L) (k : Nat) (ws : List Word) :
    cntK S k ws = cntK S' k ws := by
  unfold cntK; rw [h]

theorem cntK_prod {a b : Ty} {n : Nat} (hs : ¬ sNo (.prod a b) = true) (hn : wc a = some n) (k : Nat)
    (ws : List Word) : cntK (.prod a b) k ws = cntK a k (ws.take n) ++ cntK b (k + n) (ws.drop n) := by
  unfold cntK
  simp only [pubWords, hs, Bool.false_eq_true, ite_false, hn]
  rw [tag_take, tag_drop, List.map_append, List.filterMap_append]

theorem cntK_prod_none {a b : Ty} (hs : ¬ sNo (.prod a b) = true) (hn : wc a = none) (k : Nat)
    (ws : List Word) : cntK (.prod a b) k ws = [] := by
  unfold cntK
  simp only [pubWords, hs, Bool.false_eq_true, ite_false, hn]
  rfl

/-- A non-shallow, non-boxed sum counts only its last word. -/
theorem cntK_sum_last {a b : Ty} (hs : ¬ sNo (.sum a b) = true) (hb : ¬ (Ty.sum a b).tier = .boxed) {k : Nat}
    {ws : List Word} {i : Nat} (hi : i + 1 < ws.length) : i + k ∉ cntK (.sum a b) k ws := by
  intro h
  unfold cntK at h
  obtain ⟨n, hn, hr⟩ := List.mem_filterMap.1 h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hn
  unfold rf at hr
  split at hr
  · cases hr
  rename_i hw0
  have hx := Option.some.inj hr
  simp only [pubWords, hs, hb, Bool.false_eq_true, ite_false] at hw
  cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) (tag k ws) with
  | none => rw [hd] at hw; simp at hw
  | some x =>
    obtain ⟨j, p⟩ := x
    rw [hd] at hw
    simp only [] at hw
    have hp : w.rts = 0 ∨ w.rts ∈ p.map (·.rts) := by
      split at hw
      · exact (pubWords_rts a).2 _ _ w hw
      · exact (pubWords_rts b).2 _ _ w hw
    rcases hp with h0 | h1
    · exact hw0 h0
    · obtain ⟨w1, hw1, e1⟩ := List.mem_map.1 h1
      rcases decodeArm_rts hd w1 hw1 with h2 | ⟨w2, h3, e2⟩
      · rw [h2] at e1; exact hw0 e1.symm
      · rw [tag_get, tag_length] at h3
        have hl : ws.length - 1 < ws.length := by omega
        rw [List.getElem?_eq_getElem hl] at h3
        simp only [Option.map_some, Option.some.injEq] at h3
        have f1 : rn w1 = rn w := e1
        have f2 : rn w2 = rn w1 := e2
        have f3 : rn w2 = ws.length - 1 + k + 1 := by rw [← h3]; rfl
        have f4 : rn w - 1 = i + k := hx
        have f5 : rn w ≠ 0 := hw0
        omega

/-! ## 4. Prefix-locality -/

/-- **Prefix-locality**: whether position `i` is counted depends only on the values at
positions `≤ i`. -/
theorem cnt_prefix : ∀ (S : Ty) (k : Nat) (ws ws2 : List Word) (i : Nat), ws.length = ws2.length →
    VEq (ws.take (i + 1)) (ws2.take (i + 1)) → (i + k ∈ cntK S k ws ↔ i + k ∈ cntK S k ws2) := by
  intro S
  induction S with
  | prod a b iha ihb =>
      intro k ws ws2 i hl he
      by_cases hs : sNo (.prod a b) = true
      · rw [cntK_of_sNo hl hs]
      cases hn : wc a with
      | none => rw [cntK_prod_none hs hn, cntK_prod_none hs hn]
      | some n =>
        rw [cntK_prod hs hn, cntK_prod hs hn, List.mem_append, List.mem_append]
        by_cases hi : i < n
        · have hr : ∀ (L : List Word), i + k ∉ cntK b (k + n) (L.drop n) := fun L h => by
            have := (cntK_range h).1; omega
          have e1 : (ws.take n).take (i + 1) = ws.take (i + 1) := by
            rw [List.take_take]; congr 1; omega
          have e2 : (ws2.take n).take (i + 1) = ws2.take (i + 1) := by
            rw [List.take_take]; congr 1; omega
          have := iha k (ws.take n) (ws2.take n) i (by simp [hl]) (by rw [e1, e2]; exact he)
          constructor
          · rintro (h | h)
            · exact .inl (this.1 h)
            · exact absurd h (hr ws)
          · rintro (h | h)
            · exact .inl (this.2 h)
            · exact absurd h (hr ws2)
        · have hlft : ∀ (L : List Word), i + k ∉ cntK a k (L.take n) := fun L h => by
            have := (cntK_range h).2; simp at this; omega
          have e1 : ∀ (L : List Word), (L.drop n).take (i - n + 1) = (L.take (i + 1)).drop n := fun L => by
            rw [List.drop_take]; congr 1; omega
          have := ihb (k + n) (ws.drop n) (ws2.drop n) (i - n) (by simp [hl])
            (by rw [e1, e1]; exact veq_drop he n)
          rw [show i - n + (k + n) = i + k by omega] at this
          constructor
          · rintro (h | h)
            · exact absurd h (hlft ws)
            · exact .inr (this.1 h)
          · rintro (h | h)
            · exact absurd h (hlft ws2)
            · exact .inr (this.2 h)
  | sum a b _ _ =>
      intro k ws ws2 i hl he
      by_cases hs : sNo (.sum a b) = true
      · rw [cntK_of_sNo hl hs]
      by_cases hb : (Ty.sum a b).tier = .boxed
      · rw [cntK_of_id hl fun L => by simp only [pubWords, hs, hb, Bool.false_eq_true, ite_false, ite_true]]
      by_cases hw : ws.length ≤ i + 1
      · have e : VEq ws ws2 := by
          rw [List.take_of_length_le hw, List.take_of_length_le (by omega)] at he; exact he
        rw [cntK_of_veq _ _ e]
      · exact ⟨fun h => absurd h (cntK_sum_last hs hb (by omega)),
          fun h => absurd h (cntK_sum_last hs hb (by omega))⟩
  | refine t ψ ih =>
      intro k ws ws2 i hl he
      rw [cntK_congr (fun L => pubWords_refine t ψ L), cntK_congr (fun L => pubWords_refine t ψ L)]
      exact ih k ws ws2 i hl he
  | iall t ih =>
      intro k ws ws2 i hl he
      by_cases hs : sNo (.iall t) = true
      · rw [cntK_of_sNo hl hs]
      have hc : ∀ L, pubWords (.iall t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih k ws ws2 i hl he
  | iex t ih =>
      intro k ws ws2 i hl he
      by_cases hs : sNo (.iex t) = true
      · rw [cntK_of_sNo hl hs]
      have hc : ∀ L, pubWords (.iex t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih k ws ws2 i hl he
  | mu t ih =>
      intro k ws ws2 i hl he
      by_cases hs : sNo (.mu t) = true
      · rw [cntK_of_sNo hl hs]
      have hc : ∀ L, pubWords (.mu t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih k ws ws2 i hl he
  | tex κ t ih =>
      intro k ws ws2 i hl he
      by_cases hs : sNo (.tex κ t) = true
      · rw [cntK_of_sNo hl hs]
      have hc : ∀ L, pubWords (.tex κ t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih k ws ws2 i hl he
  | _ =>
      intro k ws ws2 i hl _
      unfold cntK
      rw [pubWords.eq_def, pubWords.eq_def]; simp only []
      split
      · rw [tag_rts_eq k ws ws2 hl]
      · exact Iff.rfl

/-! ## 5. Units -/

theorem nWords_cons (u : Acc) (us : List Acc) : nWords (u :: us) = u.size + nWords us := by
  simp [nWords]

theorem nWords_append (us vs : List Acc) : nWords (us ++ vs) = nWords us + nWords vs := by
  simp [nWords, List.map_append, List.sum_append]

theorem unitAt_bound : ∀ (us : List Acc) (i : Nat) {u : Acc} {d : Nat}, UnitAt us i = some (u, d) →
    d ≤ i ∧ d < u.size ∧ i - d + u.size ≤ nWords us
  | [], _, _, _, h => by simp [UnitAt] at h
  | v :: us, i, u, d, h => by
      simp only [UnitAt] at h
      rw [nWords_cons]
      split at h
      · cases h; omega
      · have := unitAt_bound us _ h; omega

theorem unitAt_append : ∀ (us vs : List Acc) (i : Nat),
    UnitAt (us ++ vs) i = if i < nWords us then UnitAt us i else UnitAt vs (i - nWords us)
  | [], vs, i => by simp [nWords]
  | v :: us, vs, i => by
      simp only [List.cons_append, UnitAt, nWords_cons]
      rw [unitAt_append us vs]
      by_cases h1 : i < v.size
      · simp [h1, show i < v.size + nWords us by omega]
      · simp only [h1, ite_false]
        by_cases h2 : i - v.size < nWords us
        · simp [h2, show i < v.size + nWords us by omega]
        · simp only [h2, ite_false, show ¬ i < v.size + nWords us by omega]
          congr 1; omega

theorem unitAt_short {us : List Acc} (h : us.length ≤ 1) {i d : Nat} {u : Acc} (hu : UnitAt us i = some (u, d)) :
    d = i := by
  match us, h, hu with
  | [], _, hu => simp [UnitAt] at hu
  | [v], _, hu =>
      simp only [UnitAt] at hu
      split at hu
      · cases hu; rfl
      · simp at hu

/-- A short layout: the window is the prefix. -/
theorem cnt_window_short {S : Ty} {us : List Acc} (h : us.length ≤ 1) {k : Nat} {ws ws2 : List Word} {i d : Nat}
    {u : Acc} (hl : ws2.length = ws.length) (hu : UnitAt us i = some (u, d))
    (he : VEq ((ws.drop (i - d)).take (d + 1)) ((ws2.drop (i - d)).take (d + 1))) :
    i + k ∈ cntK S k ws ↔ i + k ∈ cntK S k ws2 := by
  obtain rfl := unitAt_short h hu
  simp only [Nat.sub_self, List.drop_zero] at he
  exact cnt_prefix S k ws ws2 d hl.symm he

theorem accs_prod {a b : Ty} {us : List Acc} (h : accs (.prod a b) = some us) :
    ∃ ua ub, accs a = some ua ∧ accs b = some ub ∧ us = ua ++ ub := by
  cases ha : accs a with
  | none => simp [accs, ha, bind, Option.bind] at h
  | some ua =>
    cases hb : accs b with
    | none => simp [accs, ha, hb, bind, Option.bind] at h
    | some ub =>
      simp [accs, ha, hb, bind, Option.bind, pure] at h
      exact ⟨ua, ub, rfl, rfl, h.symm⟩

/-- **Unit-locality**: whether position `i` is counted depends only on the values of its access
unit up to `i`. -/
theorem cnt_window : ∀ (S : Ty) (us : List Acc), accs S = some us → ∀ (k : Nat) (ws ws2 : List Word)
    (i d : Nat) (u : Acc), ws.length = nWords us → ws2.length = ws.length → UnitAt us i = some (u, d) →
    VEq ((ws.drop (i - d)).take (d + 1)) ((ws2.drop (i - d)).take (d + 1)) →
    (i + k ∈ cntK S k ws ↔ i + k ∈ cntK S k ws2) := by
  intro S
  induction S with
  | prod a b iha ihb =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      by_cases hs : sNo (.prod a b) = true
      · rw [cntK_of_sNo hl2.symm hs]
      obtain ⟨ua, ub, ha, hb, rfl⟩ := accs_prod hus
      have hn : wc a = some (nWords ua) := by simp [wc, ha]
      rw [cntK_prod hs hn, cntK_prod hs hn, List.mem_append, List.mem_append]
      rw [nWords_append] at hl
      rw [unitAt_append] at hu
      split at hu
      · rename_i hi
        obtain ⟨hd1, hd2, hd3⟩ := unitAt_bound ua i hu
        have hr : ∀ (L : List Word), i + k ∉ cntK b (k + nWords ua) (L.drop (nWords ua)) := fun L h => by
          have := (cntK_range h).1; omega
        have e1 : ∀ (L : List Word), ((L.take (nWords ua)).drop (i - d)).take (d + 1) =
            (L.drop (i - d)).take (d + 1) := fun L => by
          rw [List.drop_take, List.take_take]; congr 1; omega
        have := iha ua ha k (ws.take (nWords ua)) (ws2.take (nWords ua)) i d u (by simp; omega)
          (by simp [hl2]) hu (by rw [e1, e1]; exact he)
        constructor
        · rintro (h | h)
          · exact .inl (this.1 h)
          · exact absurd h (hr ws)
        · rintro (h | h)
          · exact .inl (this.2 h)
          · exact absurd h (hr ws2)
      · rename_i hi
        obtain ⟨hd1, hd2, hd3⟩ := unitAt_bound ub _ hu
        have hlft : ∀ (L : List Word), i + k ∉ cntK a k (L.take (nWords ua)) := fun L h => by
          have := (cntK_range h).2; simp at this; omega
        have e1 : ∀ (L : List Word), ((L.drop (nWords ua)).drop (i - nWords ua - d)).take (d + 1) =
            (L.drop (i - d)).take (d + 1) := fun L => by
          rw [List.drop_drop]; congr 2; omega
        have := ihb ub hb (k + nWords ua) (ws.drop (nWords ua)) (ws2.drop (nWords ua)) (i - nWords ua) d u
          (by simp; omega) (by simp [hl2]) hu (by rw [e1, e1]; exact he)
        rw [show i - nWords ua + (k + nWords ua) = i + k by omega] at this
        constructor
        · rintro (h | h)
          · exact absurd h (hlft ws)
          · exact .inr (this.1 h)
        · rintro (h | h)
          · exact absurd h (hlft ws2)
          · exact .inr (this.2 h)
  | sum a b _ _ =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      have h1 : us.length ≤ 1 := by
        simp only [accs] at hus; split at hus <;> cases hus <;> simp
      exact cnt_window_short h1 hl2 hu he
  | refine t ψ ih =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      rw [cntK_congr (fun L => pubWords_refine t ψ L), cntK_congr (fun L => pubWords_refine t ψ L)]
      exact ih us hus k ws ws2 i d u hl hl2 hu he
  | iall t ih =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      by_cases hs : sNo (.iall t) = true
      · rw [cntK_of_sNo hl2.symm hs]
      have hc : ∀ L, pubWords (.iall t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih us hus k ws ws2 i d u hl hl2 hu he
  | mu t ih =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      by_cases hs : sNo (.mu t) = true
      · rw [cntK_of_sNo hl2.symm hs]
      have hc : ∀ L, pubWords (.mu t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih us hus k ws ws2 i d u hl hl2 hu he
  | iex t ih =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      have hor : us.length ≤ 1 ∨ accs t = some us := by
        simp only [accs] at hus
        split at hus
        · split at hus
          · cases hus; left; simp
          · cases hus; left; simp
          · cases hus; left; simp
          · right; exact hus
        · right; exact hus
      rcases hor with h1 | h1
      · exact cnt_window_short h1 hl2 hu he
      by_cases hs : sNo (.iex t) = true
      · rw [cntK_of_sNo hl2.symm hs]
      have hc : ∀ L, pubWords (.iex t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih us h1 k ws ws2 i d u hl hl2 hu he
  | tex κ t ih =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      have hor : us.length ≤ 1 ∨ accs t = some us := by
        simp only [accs] at hus
        split at hus
        · split at hus
          · cases hus; left; simp
          · cases hus; left; simp
          · cases hus; left; simp
          · right; exact hus
        · right; exact hus
      rcases hor with h1 | h1
      · exact cnt_window_short h1 hl2 hu he
      by_cases hs : sNo (.tex κ t) = true
      · rw [cntK_of_sNo hl2.symm hs]
      have hc : ∀ L, pubWords (.tex κ t) L = pubWords t L := fun L => by
        simp only [pubWords, hs, Bool.false_eq_true, ite_false]
      rw [cntK_congr hc, cntK_congr hc]; exact ih us h1 k ws ws2 i d u hl hl2 hu he
  | _ =>
      intro us hus k ws ws2 i d u hl hl2 hu he
      have h1 : us.length ≤ 1 := by
        revert hus; simp only [accs]
        first
          | (intro hus; cases hus; simp)
          | (split <;> intro hus <;> cases hus <;> simp)
          | (intro hus; cases hus)
      exact cnt_window_short h1 hl2 hu he

/-! ## 6. The untyped counted slots are the typed ones -/

theorem unitAt_some : ∀ (us : List Acc) (i : Nat), i < nWords us → ∃ u d, UnitAt us i = some (u, d)
  | [], _, h => by simp [nWords] at h
  | v :: us, i, h => by
      simp only [UnitAt]
      rw [nWords_cons] at h
      split
      · exact ⟨v, i, rfl⟩
      · exact unitAt_some us _ (by omega)

theorem acc_size_le (u : Acc) : u.size ≤ 2 := by cases u <;> simp [Acc.size]

theorem take_drop_one {l : List Word} {i : Nat} {x : Word} (h : l[i]? = some x) : (l.drop i).take 1 = [x] := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.drop_eq_getElem_cons hi, e]; rfl

theorem take_drop_two {l : List Word} {i : Nat} {x y : Word} (h1 : l[i]? = some x) (h2 : l[i + 1]? = some y) :
    (l.drop i).take 2 = [x, y] := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hi2, e2⟩ := List.getElem?_eq_some_iff.1 h2
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hi2, e, e2]; rfl

theorem segOf_accs {T S : Ty} {b : Nat} (h : SegOf T b S) : ∃ L, accs S = some L := by
  rcases h with ⟨-, rfl, hA⟩ | ⟨N, us, j, -, hus, -, -⟩
  · cases e : accs S with
    | none => exact absurd e hA
    | some L => exact ⟨L, rfl⟩
  · exact ⟨us, hus⟩

/-- **A one-word counted slot is counted under the typed value**: the untyped `CntOK` and the typed
`WordOK` witness are of one segment (`SegOf_unique`), and the slot's unit is read from the word
alone (it is not a granule's second word, `hU`), so unit-locality transfers the count. -/
theorem cntOK_typed {E : TEnv} {T : Ty} {o : Nat} {w : Word} (hC : CntOK T o w) (hW : WordOK E T o w)
    (hU : NotSnd T o) :
    ∃ b S ws oo w0, SegOf T b S ∧ ValOfS E S ws ∧ ws[oo]? = some w0 ∧ WLe1 w0 w ∧ b + oo = o ∧
      oo ∈ cntIdx S ws := by
  obtain ⟨b, S, ws, oo, h1, hsh, hw, ho, hc⟩ := hC
  obtain ⟨b1, S1, ws1, o1, w0, h2, hv, hw0, hle, ho1⟩ := hW
  obtain ⟨L, hL⟩ := segOf_accs h1
  have hlen : ws.length = nWords L := hsh L hL
  have hlt : oo < ws.length := (List.getElem?_eq_some_iff.1 hw).1
  have hlt1 : o1 < ws1.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨rfl, rfl⟩ := SegOf_unique (o := oo) (o' := o1) h1 hL (by omega) h2 hv hlt1 (by omega)
  obtain rfl : oo = o1 := by omega
  have hlen1 : ws1.length = nWords L := hv.2 L hL
  obtain ⟨u, d, hu⟩ := unitAt_some L oo (by omega)
  obtain rfl := hU b S L oo u d h1 hL ho hu
  refine ⟨b, S, ws1, oo, w0, h1, hv, hw0, hle, ho, ?_⟩
  rw [cntIdx_eq] at hc ⊢
  have hwin : VEq ((ws.drop (oo - 0)).take (0 + 1)) ((ws1.drop (oo - 0)).take (0 + 1)) := by
    simp only [Nat.sub_zero, Nat.zero_add]
    rw [take_drop_one hw, take_drop_one hw0]
    simp [VEq, hle.1]
  have := cnt_window S L hL 0 ws ws1 oo 0 u hlen (by omega) hu hwin
  simpa using this.1 (by simpa using hc)

/-- **A pair store's second word, counted, is counted under the typed value** (no unit condition:
the window of the second word is within the pair). -/
theorem cntPairOK_typed {E : TEnv} {T : Ty} {o : Nat} {w0 w1 : Word} (hC : CntPairOK T o w0 w1)
    (hW : PairOK E T o w0 w1) :
    ∃ b S ws oo x0 x1, SegOf T b S ∧ ValOfS E S ws ∧ ws[oo]? = some x0 ∧ ws[oo + 1]? = some x1 ∧
      WLe1 x0 w0 ∧ WLe1 x1 w1 ∧ b + oo = o ∧ oo + 1 ∈ cntIdx S ws := by
  obtain ⟨b, S, ws, oo, h1, hsh, hw, hw', ho, hc⟩ := hC
  obtain ⟨b1, S1, ws1, o1, x0, x1, h2, hv, hx0, hx1, hle0, hle1, ho1⟩ := hW
  obtain ⟨L, hL⟩ := segOf_accs h1
  have hlen : ws.length = nWords L := hsh L hL
  have hlt : oo + 1 < ws.length := (List.getElem?_eq_some_iff.1 hw').1
  have hlt1 : o1 < ws1.length := (List.getElem?_eq_some_iff.1 hx0).1
  obtain ⟨rfl, rfl⟩ := SegOf_unique (o := oo) (o' := o1) h1 hL (by omega) h2 hv hlt1 (by omega)
  obtain rfl : oo = o1 := by omega
  have hlen1 : ws1.length = nWords L := hv.2 L hL
  obtain ⟨u, d, hu⟩ := unitAt_some L (oo + 1) (by omega)
  obtain ⟨hd1, hd2, -⟩ := unitAt_bound L _ hu
  have hs2 := acc_size_le u
  refine ⟨b, S, ws1, oo, x0, x1, h1, hv, hx0, hx1, hle0, hle1, ho, ?_⟩
  rw [cntIdx_eq] at hc ⊢
  have hwin : VEq ((ws.drop (oo + 1 - d)).take (d + 1)) ((ws1.drop (oo + 1 - d)).take (d + 1)) := by
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · simp only [Nat.sub_zero, Nat.zero_add]
      rw [take_drop_one hw', take_drop_one hx1]
      simp [VEq, hle1.1]
    · simp only [Nat.add_sub_cancel, show (1 : Nat) + 1 = 2 from rfl]
      rw [take_drop_two hw hw', take_drop_two hx0 hx1]
      simp [VEq, hle0.1, hle1.1]
  have := cnt_window S L hL 0 ws ws1 (oo + 1) d u hlen (by omega) hu hwin
  simpa using this.1 (by simpa using hc)

end TermCntLoc

#print axioms TermCntLoc.pubWords_vr
#print axioms TermCntLoc.pubWords_rts
#print axioms TermCntLoc.cnt_prefix
#print axioms TermCntLoc.cnt_window
#print axioms TermCntLoc.cntOK_typed
#print axioms TermCntLoc.cntPairOK_typed
