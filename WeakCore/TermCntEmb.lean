import WeakCore.TermCntLoc
import WeakCore.TermPubOnly

/-!
# TermCntEmb: counted positions across a component

`pubWords` at a recursive type equals `pubWords` at its unfolding (`pubWords_cl_guard`: the
recursion variable occurs only under references, which `cnt` never enters), and a position counted
in a component `U` of a layout type `T` (`AtOff T o U`) is counted in `T` at `o` plus it, and back
(`cnt_atOff`).
-/

namespace TermCntEmb
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermCntLoc
open TermClose (cl clM clI Clo)

theorem mPub_clM (ρ : Nat → Nat) (d : Nat) (μ : Mode) : mPub (clM ρ d μ) = mPub μ := by
  cases μ <;> rfl

section Guard
variable {ρ : Nat → Nat} {W W1 : Nat → Ty}

theorem cl_tvar_guard (hW : ∀ k, W1 (k + 1) = W k) {j c : Nat} (d : Nat) (hk : j ≠ c) :
    cl ρ W1 c d (.tvar j) = cl ρ W (c + 1) d (.tvar j) := by
  by_cases h1 : j < c
  · simp [cl, h1, show j < c + 1 by omega]
  · have h2 : ¬ j < c + 1 := by omega
    have e : j - c = (j - (c + 1)) + 1 := by omega
    simp only [cl, h1, h2, ite_false]; rw [e, hW]

theorem sNo_cl_guard (hW : ∀ k, W1 (k + 1) = W k) :
    ∀ (t : Ty) (c d : Nat), t.unguarded c = false → sNo (cl ρ W1 c d t) = sNo (cl ρ W (c + 1) d t) := by
  intro t
  induction t with
  | tvar j =>
      intro c d hg
      rw [cl_tvar_guard hW d (by simpa [Ty.unguarded] using hg)]
  | ptr μ t _ => intro c d _; simp only [cl, sNo, mPub_clM]
  | ptrOpt μ t _ => intro c d _; simp only [cl, sNo, mPub_clM]
  | loc μ t _ => intro c d _; simp only [cl, sNo, mPub_clM]
  | prod a b iha ihb =>
      intro c d hg
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [cl, sNo, iha c d hg.1, ihb c d hg.2]
  | sum a b iha ihb =>
      intro c d hg
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [cl, sNo, iha c d hg.1, ihb c d hg.2]
  | mu t ih => intro c d hg; simp only [cl, sNo]; exact ih (c + 1) d (by simpa [Ty.unguarded] using hg)
  | tex κ t ih =>
      intro c d hg; simp only [cl, sNo]; rw [ih (c + 1) d (by simpa [Ty.unguarded] using hg)]
  | iall t ih => intro c d hg; simp only [cl, sNo]; exact ih c (d + 1) (by simpa [Ty.unguarded] using hg)
  | iex t ih => intro c d hg; simp only [cl, sNo]; exact ih c (d + 1) (by simpa [Ty.unguarded] using hg)
  | refine t ψ ih => intro c d hg; simp only [cl, sNo]; exact ih c d (by simpa [Ty.unguarded] using hg)
  | array i t ih => intro c d hg; simp only [cl, sNo]; exact ih c d (by simpa [Ty.unguarded] using hg)
  | _ => intro c d _; simp [cl, sNo]

theorem lnorm_cl_guard (hW : ∀ k, W1 (k + 1) = W k) :
    ∀ (t : Ty) (c d : Nat), t.unguarded c = false → lnorm (cl ρ W1 c d t) = lnorm (cl ρ W (c + 1) d t) := by
  intro t
  induction t with
  | tvar j =>
      intro c d hg
      rw [cl_tvar_guard hW d (by simpa [Ty.unguarded] using hg)]
  | prod a b iha ihb =>
      intro c d hg
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [cl, lnorm, iha c d hg.1, ihb c d hg.2]
  | sum a b iha ihb =>
      intro c d hg
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [cl, lnorm, iha c d hg.1, ihb c d hg.2]
  | mu t ih => intro c d hg; simp only [cl, lnorm]; rw [ih (c + 1) d (by simpa [Ty.unguarded] using hg)]
  | tex κ t ih => intro c d hg; simp only [cl, lnorm]; rw [ih (c + 1) d (by simpa [Ty.unguarded] using hg)]
  | iall t ih => intro c d hg; simp only [cl, lnorm]; rw [ih c (d + 1) (by simpa [Ty.unguarded] using hg)]
  | iex t ih => intro c d hg; simp only [cl, lnorm]; rw [ih c (d + 1) (by simpa [Ty.unguarded] using hg)]
  | refine t ψ ih => intro c d hg; simp only [cl, lnorm]; exact ih c d (by simpa [Ty.unguarded] using hg)
  | _ => intro c d _; simp [cl, lnorm]

theorem armsOf_len_cl_guard (hW : ∀ k, W1 (k + 1) = W k) :
    ∀ (t : Ty) (c d : Nat), t.unguarded c = false →
      (armsOf (cl ρ W1 c d t)).length = (armsOf (cl ρ W (c + 1) d t)).length := by
  intro t
  induction t with
  | tvar j =>
      intro c d hg
      rw [cl_tvar_guard hW d (by simpa [Ty.unguarded] using hg)]
  | sum a b iha ihb =>
      intro c d hg
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [cl, armsOf, List.length_append, iha c d hg.1, ihb c d hg.2]
  | mu t ih => intro c d hg; simp only [cl, armsOf]; exact ih (c + 1) d (by simpa [Ty.unguarded] using hg)
  | tex κ t ih => intro c d hg; simp only [cl, armsOf]; exact ih (c + 1) d (by simpa [Ty.unguarded] using hg)
  | iall t ih => intro c d hg; simp only [cl, armsOf]; exact ih c (d + 1) (by simpa [Ty.unguarded] using hg)
  | iex t ih => intro c d hg; simp only [cl, armsOf]; exact ih c (d + 1) (by simpa [Ty.unguarded] using hg)
  | refine t ψ ih => intro c d hg; simp only [cl, armsOf]; exact ih c d (by simpa [Ty.unguarded] using hg)
  | _ => intro c d _; simp [cl, armsOf]

/-- **Counted words under a guarded variable**: closing the variable at `c` by `W1 0` or leaving it
open gives the same counted words (it occurs only under references). -/
theorem pubWords_cl_guard (hW : ∀ k, W1 (k + 1) = W k) (hXT : ∀ m, (W1 0).tyMentions m = false)
    (hXI : ∀ m, (W1 0).idxMentions m = false) :
    ∀ (t : Ty) (c d : Nat), t.unguarded c = false →
      (∀ ws, pubWords (cl ρ W1 c d t) ws = pubWords (cl ρ W (c + 1) d t) ws) ∧
      (∀ j p, pubArm (cl ρ W1 c d t) j p = pubArm (cl ρ W (c + 1) d t) j p) := by
  intro t
  induction t with
  | tvar j =>
      intro c d hg
      rw [cl_tvar_guard hW d (by simpa [Ty.unguarded] using hg)]
      exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | prod a b iha ihb =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.prod a b) c d hg
      have hwa : wc (cl ρ W1 c d a) = wc (cl ρ W (c + 1) d a) := by
        simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
        simp only [wc, accs_cl_guard (ρ := ρ) hW hXT hXI a c d hg.1]
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      simp only [cl] at hs hwa ⊢
      have h1 : ∀ ws, pubWords (.prod (cl ρ W1 c d a) (cl ρ W1 c d b)) ws =
          pubWords (.prod (cl ρ W (c + 1) d a) (cl ρ W (c + 1) d b)) ws := by
        intro ws
        simp only [pubWords, hs, hwa, (iha c d hg.1).1, (ihb c d hg.2).1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.sum a b) c d hg
      have ht := TermStep.tier_of_sig (sig_cl_guard (ρ := ρ) hW (.sum a b) c d hg)
      have hl := lnorm_cl_guard (ρ := ρ) hW (.sum a b) c d hg
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      have hal := armsOf_len_cl_guard (ρ := ρ) hW a c d hg.1
      simp only [cl] at hs ht hl ⊢
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, (iha c d hg.1).2, (ihb c d hg.2).2]
      · simp only [pubArm, hal, (iha c d hg.1).2, (ihb c d hg.2).2]
  | refine t ψ ih =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.refine t ψ) c d hg
      have hg1 : t.unguarded c = false := by simpa [Ty.unguarded] using hg
      simp only [cl] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih c d hg1).1],
        fun j p => by simp only [pubArm, (ih c d hg1).2]⟩
  | iall t ih =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.iall t) c d hg
      have hg1 : t.unguarded c = false := by simpa [Ty.unguarded] using hg
      simp only [cl] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih c (d + 1) hg1).1],
        fun j p => by simp only [pubArm, (ih c (d + 1) hg1).2]⟩
  | iex t ih =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.iex t) c d hg
      have hg1 : t.unguarded c = false := by simpa [Ty.unguarded] using hg
      simp only [cl] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih c (d + 1) hg1).1],
        fun j p => by simp only [pubArm, (ih c (d + 1) hg1).2]⟩
  | mu t ih =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.mu t) c d hg
      have hg1 : t.unguarded (c + 1) = false := by simpa [Ty.unguarded] using hg
      simp only [cl] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih (c + 1) d hg1).1],
        fun j p => by simp only [pubArm, (ih (c + 1) d hg1).2]⟩
  | tex κ t ih =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.tex κ t) c d hg
      have hg1 : t.unguarded (c + 1) = false := by simpa [Ty.unguarded] using hg
      simp only [cl] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, (ih (c + 1) d hg1).1],
        fun j p => by simp only [pubArm, (ih (c + 1) d hg1).2]⟩
  | array i e ih =>
      intro c d hg
      have hs := sNo_cl_guard (ρ := ρ) hW (.array i e) c d hg
      simp only [cl] at hs ⊢
      have h1 : ∀ ws, pubWords (.array (clI ρ d i) (cl ρ W1 c d e)) ws =
          pubWords (.array (clI ρ d i) (cl ρ W (c + 1) d e)) ws := by
        intro ws
        rw [pubWords.eq_def, pubWords.eq_def]
        simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ =>
      intro c d _
      exact ⟨fun ws => by simp only [cl, pubWords, sNo, mPub_clM],
        fun j p => by simp only [cl, pubArm, pubWords, sNo, mPub_clM]⟩
  | ptrOpt μ u _ =>
      intro c d _
      exact ⟨fun ws => by simp only [cl, pubWords, sNo, mPub_clM],
        fun j p => by simp only [cl, pubArm, pubWords, sNo, mPub_clM]⟩
  | loc μ u _ =>
      intro c d _
      exact ⟨fun ws => by simp only [cl, pubWords, sNo, mPub_clM],
        fun j p => by simp only [cl, pubArm, pubWords, sNo, mPub_clM]⟩
  | code a b _ _ =>
      intro c d _
      exact ⟨fun ws => by simp only [cl, pubWords, sNo], fun j p => by simp only [cl, pubArm, pubWords, sNo]⟩
  | _ => intro c d _; exact ⟨fun ws => by simp [cl, pubWords, sNo], fun j p => by simp [cl, pubArm, pubWords, sNo]⟩

end Guard

/-- **Unfolding** keeps the counted words. -/
theorem pubWords_cl_unfold {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (hg : s.unguarded 0 = false) (ws : List Word) :
    pubWords (cl ρ W 0 0 (unfold1 (.mu s))) ws = pubWords (cl ρ W 0 0 (.mu s)) ws := by
  rw [TermPubOnly.cl_unfold_eq]
  have hX := Clo_cl0 (ρ := ρ) hW (.mu s)
  have e := (pubWords_cl_guard (ρ := ρ) (W := W) (W1 := wcons (cl ρ W 0 0 (.mu s)) W)
    (fun k => by simp [wcons]) (fun m => by simpa [wcons] using hX.1 m) (fun m => by simpa [wcons] using hX.2 m)
    s 0 0 hg).1 ws
  rw [e]
  by_cases hs : sNo (cl ρ W 0 0 (.mu s)) = true
  · rw [pubWords_of_sNo hs]
    have : sNo (cl ρ W (0 + 1) 0 s) = true := by simpa [cl, sNo] using hs
    exact pubWords_of_sNo this ws
  · have hs' : ¬ sNo (.mu (cl ρ W (0 + 1) 0 s)) = true := by simpa [cl] using hs
    simp only [cl]
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]


/-- At a type without sums every position is counted. -/
theorem cntK_sNo_mem {S : Ty} (hs : sNo S = true) (k : Nat) (ws : List Word) (x : Nat) :
    x ∈ cntK S k ws ↔ k ≤ x ∧ x < k + ws.length := by
  unfold cntK
  rw [pubWords_of_sNo hs]
  have key : ∀ (ws : List Word) (k : Nat), ((tag k ws).map (·.rts)).filterMap rf = List.range' k ws.length := by
    intro ws
    induction ws with
    | nil => intro k; simp [tag_nil]
    | cons w ws ih =>
        intro k
        rw [tag_cons, List.map_cons, List.filterMap_cons, ih (k + 1)]
        simp [TermCntLoc.rf, List.range'_succ]
  rw [key, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨x - k, by omega, by simp; omega⟩

/-- `sNo` passes to a component. -/
theorem sNo_atOff {T U : Ty} {o : Nat} (h : AtOff T o U) : sNo T = true → sNo U = true := by
  induction h with
  | here _ => exact id
  | fst _ ih => intro hs; simp only [sNo, Bool.and_eq_true] at hs; exact ih hs.1
  | snd _ _ ih => intro hs; simp only [sNo, Bool.and_eq_true] at hs; exact ih hs.2
  | elem _ _ _ ih => intro hs; simp only [sNo] at hs; exact ih hs
  | mu _ _ _ ih => intro hs; exact ih (TermPubOnly.sNo_unfold hs)
  | fold _ _ _ _ ih => intro hs; exact TermPubOnly.sNo_fold (ih hs)

theorem take_drop_take {ws : List Word} {o m n : Nat} (h : o + m ≤ n) :
    ((ws.take n).drop o).take m = (ws.drop o).take m := by
  rw [List.drop_take, List.take_take]; congr 1; omega

/-- **Counted positions across a component**: position `i` of a component `U` at offset `o` of a
layout type `T` is counted in `U` (at the component's window) iff `o + i` is counted in `T`. -/
theorem cnt_atOff {T U : Ty} {o : Nat} (h : AtOff T o U) :
    ∀ {L us : List Acc}, accs T = some L → accs U = some us → ∀ (k : Nat) (ws : List Word),
      ws.length = nWords L → ∀ i, i < nWords us →
      (o + i + k ∈ cntK T k ws ↔ o + i + k ∈ cntK U (o + k) ((ws.drop o).take (nWords us))) := by
  induction h with
  | here _ =>
      intro L us hL hu k ws hl i hi
      rw [hL] at hu; cases hu
      simp only [List.drop_zero, Nat.zero_add]
      rw [List.take_of_length_le (by omega)]
  | @fst a b u o hau ih =>
      intro L us hL hu k ws hl i hi
      obtain ⟨La, Lb, ha, hb, rfl⟩ := accs_prod hL
      obtain ⟨pre, post, e, hn⟩ := AtOff_embed hau ha hu
      have hLa : nWords La = nWords pre + nWords us + nWords post := by rw [e, TermCntLoc.nWords_append, TermCntLoc.nWords_append]
      rw [TermCntLoc.nWords_append] at hl
      by_cases hs : sNo (.prod a b) = true
      · have hsu := sNo_atOff (.fst hau) hs
        rw [cntK_sNo_mem hs, cntK_sNo_mem hsu]
        simp only [List.length_take, List.length_drop]
        constructor <;> intro _ <;> constructor <;> omega
      · rw [cntK_prod hs (show wc a = some (nWords La) by simp [wc, ha]), List.mem_append]
        have ih1 := ih ha hu k (ws.take (nWords La)) (by simp; omega) i hi
        rw [take_drop_take (by omega)] at ih1
        rw [← ih1]
        constructor
        · rintro (h1 | h1)
          · exact h1
          · have := cntK_range h1; omega
        · exact .inl
  | @snd a b u o ua hua hbu ih =>
      intro L us hL hu k ws hl i hi
      obtain ⟨La, Lb, ha, hb, rfl⟩ := accs_prod hL
      rw [hua] at ha; cases ha
      obtain ⟨pre, post, e, hn⟩ := AtOff_embed hbu hb hu
      have hLb : nWords Lb = nWords pre + nWords us + nWords post := by rw [e, TermCntLoc.nWords_append, TermCntLoc.nWords_append]
      rw [TermCntLoc.nWords_append] at hl
      by_cases hs : sNo (.prod a b) = true
      · have hsu := sNo_atOff (.snd hua hbu) hs
        rw [cntK_sNo_mem hs, cntK_sNo_mem hsu]
        simp only [List.length_take, List.length_drop]
        constructor <;> intro _ <;> constructor <;> omega
      · rw [cntK_prod hs (show wc a = some (nWords ua) by simp [wc, hua]), List.mem_append]
        have ih1 := ih hb hu (k + nWords ua) (ws.drop (nWords ua)) (by simp; omega) i hi
        rw [List.drop_drop] at ih1
        rw [show o + i + (k + nWords ua) = nWords ua + o + i + k by omega,
          show o + (k + nWords ua) = nWords ua + o + k by omega] at ih1
        rw [← ih1]
        constructor
        · rintro (h1 | h1)
          · have := cntK_range h1; simp at this; omega
          · exact h1
        · exact .inr
  | elem _ _ _ _ => intro L us hL; simp [accs] at hL
  | @mu ρ W s u o hW hg _ ih =>
      intro L us hL hu k ws hl i hi
      rw [cntK_congr (fun ws => (pubWords_cl_unfold hW hg ws).symm)]
      exact ih (by rw [accs_cl_unfold_eq hW hg]; exact hL) hu k ws hl i hi
  | @fold ρ W s T o hW hg _ _ ih =>
      intro L us hL hu k ws hl i hi
      rw [cntK_congr (S := cl ρ W 0 0 (.mu s)) (fun ws => (pubWords_cl_unfold hW hg ws).symm)]
      exact ih hL (by rw [accs_cl_unfold_eq hW hg]; exact hu) k ws hl i hi


/-! ## Relabelling read timestamps -/

/-- Relabel a word's read timestamp. -/
def relab (f : Nat → Nat) (w : Word) : Word := { w with rts := f w.rts }

theorem decodeArm_relab {f : Nat → Nat} (hf : f 0 = 0) (tr : Tier) (as : List Ty) (ws : List Word) :
    decodeArm tr as (ws.map (relab f)) = (decodeArm tr as ws).map (fun x => (x.1, x.2.map (relab f))) := by
  rcases ws with _ | ⟨w, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> cases tr <;> simp only [decodeArm, List.map] <;>
    try rfl
  · cases hv : w.val <;> (try simp only [relab, hv])
    all_goals first
      | rfl
      | (rename_i g; cases ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? <;> rfl)
      | (rename_i j
         cases as[j]? with
         | none => rfl
         | some arm =>
             simp only [bind, Option.bind]
             generalize armK arm = K
             cases K <;> simp [cst, Promises.TVal.mk0, hf, relab])
  · cases hv : w.val <;> (try simp only [relab, hv])
    all_goals first
      | rfl
      | (rename_i j
         cases as[j]? with
         | none => rfl
         | some arm =>
             simp only [bind, Option.bind]
             split <;> rfl)

theorem pubWords_relab {f : Nat → Nat} (hf : f 0 = 0) : ∀ (R : Ty),
    (∀ ws, pubWords R (ws.map (relab f)) = (pubWords R ws).map (relab f)) ∧
    (∀ j p, pubArm R j (p.map (relab f)) = (pubArm R j p).map (relab f)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws, pubWords (.prod a b) (ws.map (relab f)) = (pubWords (.prod a b) ws).map (relab f) := by
        intro ws
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · rw [← List.map_take, ← List.map_drop, (iha.1 _), (ihb.1 _), List.map_append]
          · rfl
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p, pubArm (.sum a b) j (p.map (relab f)) = (pubArm (.sum a b) j p).map (relab f) := by
        intro j p
        simp only [pubArm]
        split
        · exact iha.2 _ _
        · exact ihb.2 _ _
      refine ⟨fun ws => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · rfl
        · rw [decodeArm_relab hf]
          cases decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none => rfl
          | some x =>
              obtain ⟨j, p⟩ := x
              simp only [Option.map_some]
              split
              · exact iha.2 _ _
              · exact ihb.2 _ _
  | refine t ψ ih =>
      exact ⟨fun ws => by rw [pubWords_refine, pubWords_refine]; exact ih.1 _,
        fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
  | iall t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | iex t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | mu t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | tex κ t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | _ =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · rfl
        · rfl
      · simp only [pubArm]; rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · rfl
        · rfl

theorem tag_relab (k : Nat) : ∀ (ws : List Word) (m : Nat),
    tag (m + k) ws = (tag m ws).map (relab fun n => if n = 0 then 0 else n + k)
  | [], m => by simp [tag_nil]
  | w :: ws, m => by
      rw [tag_cons, tag_cons, List.map_cons, ← tag_relab k ws (m + 1), show m + 1 + k = m + k + 1 by omega]
      simp only [relab, List.cons.injEq, and_true]
      congr 1
      rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.succ_ne_zero m))]; exact Nat.add_right_comm m k 1

theorem filterMap_relab (k : Nat) : ∀ (L : List Word),
    ((L.map (relab fun n => if n = 0 then 0 else n + k)).map (·.rts)).filterMap TermCntLoc.rf =
      (((L.map (·.rts)).filterMap TermCntLoc.rf)).map (· + k)
  | [] => rfl
  | w :: L => by
      simp only [List.map_cons, List.filterMap_cons, filterMap_relab k L]
      by_cases h : w.rts = 0
      · simp [relab, h, TermCntLoc.rf]
      · have h2 : (w.rts : Nat) ≠ 0 := h
        simp [relab, h, TermCntLoc.rf]
        have h3 : ∀ x : Nat, x ≠ 0 → x + k - 1 = x - 1 + k := fun x hx => by omega
        exact h3 _ h2

/-- **Shift**: the counted positions past `k` are those past `0`, moved by `k`. -/
theorem cntK_shift (S : Ty) (k : Nat) (ws : List Word) : cntK S k ws = (cntK S 0 ws).map (· + k) := by
  unfold cntK
  have e := tag_relab k ws 0
  rw [Nat.zero_add] at e
  rw [e, (pubWords_relab (by simp) S).1, filterMap_relab]

theorem mem_cntK_shift {S : Ty} {k x : Nat} {ws : List Word} : x + k ∈ cntK S k ws ↔ x ∈ cntK S 0 ws := by
  rw [cntK_shift, List.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩; rw [show x = y by omega]; exact hy
  · intro h; exact ⟨x, h, rfl⟩


/-! ## A component's value inside a segment value -/

/-- **Padding a component value** to a value of the segment: same words at the component, and the
same counted positions there. -/
theorem pad_comp {S U : Ty} {o : Nat} {L us : List Acc} (hat : AtOff S o U) (hL : accs S = some L)
    (hu : accs U = some us) {wsU : List Word} (hl : wsU.length = nWords us) (w : Word) :
    ∃ wsS : List Word, ShapeC S wsS ∧ (∀ j, j < nWords us → wsS[o + j]? = wsU[j]?) ∧
      ∀ j, j < nWords us → (o + j ∈ cntIdx S wsS ↔ j ∈ cntIdx U wsU) := by
  obtain ⟨pre, post, e, hn⟩ := AtOff_embed hat hL hu
  refine ⟨List.replicate o w ++ wsU ++ List.replicate (nWords post) w, ?_, ?_, ?_⟩
  · intro L2 hL2
    rw [hL] at hL2; cases hL2
    simp [e, TermCntLoc.nWords_append, hn, hl]
  · intro j hj
    rw [List.append_assoc, List.getElem?_append_right (by simp), List.length_replicate,
      Nat.add_sub_cancel_left, List.getElem?_append_left (by omega)]
  · intro j hj
    have hlen : (List.replicate o w ++ wsU ++ List.replicate (nWords post) w).length = nWords L := by
      simp [e, TermCntLoc.nWords_append, hn, hl]
    have h1 := cnt_atOff hat hL hu 0 _ hlen j hj
    have hwin : ((List.replicate o w ++ wsU ++ List.replicate (nWords post) w).drop o).take (nWords us) = wsU := by
      rw [List.append_assoc, List.drop_append_of_le_length (by simp), List.drop_replicate, Nat.sub_self,
        List.replicate_zero, List.nil_append, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    rw [hwin, Nat.add_zero, Nat.add_zero, show o + j = j + o by omega, mem_cntK_shift] at h1
    rw [cntIdx_eq, cntIdx_eq, show o + j = j + o by omega]
    exact h1

/-- **`CntOK` from a counted position of a component value.** -/
theorem cntOK_of_comp {T S U : Ty} {b o : Nat} {L us : List Acc} (hseg : SegOf T b S) (hL : accs S = some L)
    (hat : AtOff S o U) (hu : accs U = some us) {wsU : List Word} (hl : wsU.length = nWords us) {i : Nat}
    (hc : i ∈ cntIdx U wsU) {w : Word} (hw : wsU[i]? = some w) : CntOK T (b + o + i) w := by
  have hi : i < nWords us := by have := (List.getElem?_eq_some_iff.1 hw).1; omega
  obtain ⟨wsS, hsh, hget, hcnt⟩ := pad_comp hat hL hu hl w
  exact ⟨b, S, wsS, o + i, hseg, hsh, by rw [hget i hi]; exact hw, by omega, (hcnt i hi).2 hc⟩

/-- **`CntPairOK` from a counted granule second word of a component value.** -/
theorem cntPairOK_of_comp {T S U : Ty} {b o : Nat} {L us : List Acc} (hseg : SegOf T b S)
    (hL : accs S = some L) (hat : AtOff S o U) (hu : accs U = some us) {wsU : List Word}
    (hl : wsU.length = nWords us) {i : Nat} (hc : i + 1 ∈ cntIdx U wsU) {w0 w1 : Word}
    (hw0 : wsU[i]? = some w0) (hw1 : wsU[i + 1]? = some w1) : CntPairOK T (b + o + i) w0 w1 := by
  have hi : i + 1 < nWords us := by have := (List.getElem?_eq_some_iff.1 hw1).1; omega
  obtain ⟨wsS, hsh, hget, hcnt⟩ := pad_comp hat hL hu hl w0
  exact ⟨b, S, wsS, o + i, hseg, hsh, by rw [hget i (by omega)]; exact hw0,
    by rw [show o + i + 1 = o + (i + 1) by omega, hget (i + 1) hi]; exact hw1, by omega,
    by rw [show o + i + 1 = o + (i + 1) by omega]; exact (hcnt (i + 1) hi).2 hc⟩

end TermCntEmb

#print axioms TermCntEmb.pubWords_cl_guard
#print axioms TermCntEmb.pubWords_cl_unfold
#print axioms TermCntEmb.cnt_atOff
#print axioms TermCntEmb.cntK_shift
#print axioms TermCntEmb.cntOK_of_comp
#print axioms TermCntEmb.cntPairOK_of_comp
