import WeakCore.TermPubPos

/-!
# TermCntPub: a counted position's word is a counted word (converse of `pubWords_pos`)

`cnt_pubWords`: if `i ∈ cntIdx R ws` and `ws[i]` names `x`, some word of `pubWords R ws` names `x`
and carries `ws[i]`'s read timestamp.
-/

namespace TermCntPub
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermCntLoc TermCntEmb
  TermPubPos

/-- Every nonzero-timestamped word of `l` has the read timestamp of a word of `ws` whose labels it names. -/
def NB (ws l : List Word) : Prop :=
  ∀ w ∈ l, w.rts ≠ 0 → ∃ w0 ∈ ws, w0.rts = w.rts ∧ ∀ x, Names x w0 → Names x w

theorem nb_refl (ws : List Word) : NB ws ws := fun w hw _ => ⟨w, hw, rfl, fun _ h => h⟩

theorem nb_nil (ws : List Word) : NB ws [] := fun _ h => by simp at h

theorem nb_trans {a b c : List Word} (h1 : NB a b) (h2 : NB b c) : NB a c := by
  intro w hw hz
  obtain ⟨w1, hw1, e1, hn1⟩ := h2 w hw hz
  obtain ⟨w0, hw0, e0, hn0⟩ := h1 w1 hw1 (by rw [e1]; exact hz)
  exact ⟨w0, hw0, e0.trans e1, fun x h => hn1 x (hn0 x h)⟩

theorem nb_take (ws : List Word) (n : Nat) : NB ws (ws.take n) :=
  fun w hw _ => ⟨w, List.mem_of_mem_take hw, rfl, fun _ h => h⟩

theorem nb_drop (ws : List Word) (n : Nat) : NB ws (ws.drop n) :=
  fun w hw _ => ⟨w, List.mem_of_mem_drop hw, rfl, fun _ h => h⟩

theorem nb_append {ws a b : List Word} (h1 : NB ws a) (h2 : NB ws b) : NB ws (a ++ b) := by
  intro w hw
  rcases List.mem_append.1 hw with h | h
  · exact h1 w h
  · exact h2 w h

theorem decodeArm_nb {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : decodeArm tr as ws = some (j, p)) : NB ws p := by
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
                intro y hy _
                simp at hy; subst hy
                refine ⟨w, List.mem_singleton_self _, rfl, fun x hn => ?_⟩
                obtain ⟨a', g', hv, hl⟩ := hn
                rw [hw] at hv
                simp only [WeakMem.Val.loc.injEq] at hv
                obtain ⟨rfl, -⟩ := hv
                exact ⟨_, 0, rfl, hl⟩
        | num k =>
            rw [hw] at h
            simp only [bind, Option.bind] at h
            cases h1 : as[k]? with
            | none => simp [h1] at h
            | some arm =>
                simp only [h1] at h
                intro y hy hz
                cases hk : armK arm <;> simp [hk, pure] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
                  simp at hy
                subst hy
                exact absurd rfl hz
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
                intro y hy _
                by_cases hr : a.rawWords = some 0
                · simp [hr, pure] at h; obtain ⟨rfl, rfl⟩ := h; simp at hy
                · simp [hr, pure] at h; obtain ⟨rfl, rfl⟩ := h
                  simp at hy; subst hy
                  exact ⟨y, by simp, rfl, fun _ h => h⟩
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

theorem pubWords_nb : ∀ (R : Ty), (∀ ws, NB ws (pubWords R ws)) ∧ (∀ j p, NB p (pubArm R j p)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws, NB ws (pubWords (.prod a b) ws) := by
        intro ws
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs]; exact nb_refl ws
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact nb_append (nb_trans (nb_take ws _) (iha.1 _)) (nb_trans (nb_drop ws _) (ihb.1 _))
          · exact nb_nil ws
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p, NB p (pubArm (.sum a b) j p) := by
        intro j p
        simp only [pubArm]
        split
        · exact iha.2 _ _
        · exact ihb.2 _ _
      refine ⟨fun ws => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs]; exact nb_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact nb_refl ws
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none => exact nb_nil ws
          | some x =>
            obtain ⟨j, p⟩ := x
            have hp : NB ws p := decodeArm_nb hd
            simp only []
            split
            · exact nb_trans hp (iha.2 _ _)
            · exact nb_trans hp (ihb.2 _ _)
  | refine t ψ ih =>
      exact ⟨fun ws => by rw [pubWords_refine]; exact ih.1 _, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
  | iall t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs]; exact nb_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | iex t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs]; exact nb_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | mu t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs]; exact nb_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | tex κ t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs]; exact nb_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | _ =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only []
        split
        · exact nb_refl ws
        · exact nb_nil ws
      · simp only [pubArm]; rw [pubWords.eq_def]; simp only []
        split
        · exact nb_refl p
        · exact nb_nil p

theorem rf_some {n i : Nat} (h : TermCntLoc.rf n = some i) : n = i + 1 := by
  unfold TermCntLoc.rf at h
  by_cases hc : n = 0
  · simp [hc] at h
  · simp [hc] at h; omega

/-- **A counted position's word is a counted word**: naming the same labels, same read timestamp. -/
theorem cnt_pubWords {R : Ty} {ws : List Word} {i : Nat} {w0 : Word} (hi : i ∈ cntIdx R ws)
    (h0 : ws[i]? = some w0) {x : WeakMem.AllocLabel} (hn : Names x w0) :
    ∃ w ∈ pubWords R ws, Names x w ∧ w.rts = w0.rts := by
  have hf : (fun n : Nat => n / (ws.length + 1)) 0 = 0 := Nat.zero_div _
  have hg : (fun n : Nat => n % (ws.length + 1)) 0 = 0 := Nat.zero_mod _
  have e1 := (pubWords_relab (f := fun n : Nat => n / (ws.length + 1)) hf R).1 (enc (ws.length + 1) ws)
  have e2 := (pubWords_relab (f := fun n : Nat => n % (ws.length + 1)) hg R).1 (enc (ws.length + 1) ws)
  rw [enc_relab_div] at e1
  rw [enc_relab_mod] at e2
  rw [cntIdx_eq] at hi
  unfold cntK at hi
  rw [e2] at hi
  obtain ⟨n, hnm, hrf⟩ := List.mem_filterMap.1 hi
  obtain ⟨w1, hw1, rfl⟩ := List.mem_map.1 hnm
  obtain ⟨w2, hw2, rfl⟩ := List.mem_map.1 hw1
  have hn1 : ((w2.rts : Nat) % (ws.length + 1)) = i + 1 := by
    have := rf_some hrf
    exact this
  have hz : w2.rts ≠ 0 := by
    intro h; rw [h] at hn1; simp at hn1
  obtain ⟨w3, hw3, er, hnb⟩ := (pubWords_nb R).1 _ w2 hw2 hz
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hw3
  have hk' : k < ws.length := by simpa [enc] using hk
  have hg0 : (enc (ws.length + 1) ws)[k]? = some w3 := by rw [List.getElem?_eq_getElem hk, e]
  rw [enc_get, List.getElem?_eq_getElem hk'] at hg0
  simp only [Option.map_some, Option.some.injEq] at hg0
  subst hg0
  have hki : k = i := by
    have er' : ((k + 1) + (ws.length + 1) * (ws[k].rts : Nat)) = (w2.rts : Nat) := er
    have hm : (w2.rts : Nat) % (ws.length + 1) = k + 1 := by
      rw [← er']; exact mod_enc (by omega)
    exact Nat.succ.inj (hm.symm.trans hn1)
  subst hki
  rw [List.getElem?_eq_getElem hk', Option.some.injEq] at h0
  subst h0
  refine ⟨relab (· / (ws.length + 1)) w2, ?_, ?_, ?_⟩
  · rw [e1]; exact List.mem_map_of_mem hw2
  · exact hnb x hn
  · show (w2.rts : Nat) / (ws.length + 1) = (ws[k].rts : Nat)
    have er' : ((k + 1) + (ws.length + 1) * (ws[k].rts : Nat)) = (w2.rts : Nat) := er
    rw [← er']
    exact div_enc (by omega)

end TermCntPub

#print axioms TermCntPub.pubWords_nb
#print axioms TermCntPub.cnt_pubWords
