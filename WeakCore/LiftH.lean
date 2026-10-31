import WeakCore.LiftE
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! Lift helpers: `rlI` algebra and arm re-encoding facts. -/

section
variable {G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel}

theorem rlI_cst (g : WeakMem.AllocLabel → WeakMem.AllocLabel) : ∀ ws : List Word, rlI (fun _ => g) ws = ws.map (rl g)
  | [] => rfl
  | w :: ws => by simp only [rlI_cons, List.map_cons]; rw [rlI_cst g ws]

theorem single_of_vals {ws : List Word} {v : WeakMem.Val} (h : ws.map (·.val) = [v]) :
    ∃ w, ws = [w] ∧ w.val = v := by
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩ <;> simp at h; exact ⟨w, rfl, h⟩

theorem rlI_single {ws : List Word} {v : WeakMem.Val} (h : ws.map (·.val) = [v]) :
    rlI G ws = ws.map (rl (G 0)) := by
  obtain ⟨w, rfl, -⟩ := single_of_vals h; rfl

theorem rlI_one (w : Word) : rlI G [w] = [rl (G 0) w] := rfl

theorem vals_rlI_loc_inv {ws : List Word} {b : WeakMem.Address} {g : Nat}
    (h : (rlI G ws).map (·.val) = [.loc b g]) :
    ∃ a : WeakMem.Address, ws.map (·.val) = [.loc a g] ∧ b = ⟨G 0 a.label, a.offset⟩ := by
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
  · simp at h
  · rw [rlI_one] at h
    exact vals_rl_loc_inv (f := G 0) (ws := [w]) h
  · simp at h

theorem vals_rlI_num {ws : List Word} {n : Nat} :
    (rlI G ws).map (·.val) = [.num n] ↔ ws.map (·.val) = [.num n] := by
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
  · simp
  · rw [rlI_one]; exact vals_rl_num (ws := [w])
  · simp

theorem vals_rlI_pair {ws : List Word} {n0 n1 : Nat} :
    (rlI G ws).map (·.val) = [.num n0, .num n1] ↔ ws.map (·.val) = [.num n0, .num n1] := by
  rcases ws with _ | ⟨w, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩
  · simp
  · simp
  · simp [rl, rlv_num]
  · simp

theorem rlI_views {q : WeakMem.Ts} : ∀ (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) {ws : List Word},
    (∀ w ∈ ws, q ≤ w.view) → ∀ w ∈ rlI G ws, q ≤ w.view
  | _, [], _ => by simp
  | G, w :: ws, h => by
    intro w' hw'
    simp only [rlI_cons, List.mem_cons] at hw'
    rcases hw' with rfl | hw'
    · exact h w (by simp)
    · exact rlI_views (fun i => G (i + 1)) (fun w hw => h w (List.mem_cons_of_mem _ hw)) w' hw'

theorem rl_noloc {g : WeakMem.AllocLabel → WeakMem.AllocLabel} {w : Word} (h : ∀ a k, w.val ≠ .loc a k) :
    rl g w = w := rl_of_fix (fun a k e => absurd e (h a k))

theorem rlI_congr : ∀ (G₁ G₂ : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (ws : List Word),
    (∀ i w a g, ws[i]? = some w → w.val = .loc a g → G₁ i = G₂ i) → rlI G₁ ws = rlI G₂ ws
  | _, _, [], _ => rfl
  | G₁, G₂, w :: ws, h => by
    simp only [rlI_cons]
    congr 1
    · by_cases hl : ∃ a g, w.val = .loc a g
      · obtain ⟨a, g, hv⟩ := hl; rw [h 0 w a g rfl hv]
      · have hl' : ∀ a k, w.val ≠ .loc a k := fun a k e => hl ⟨a, k, e⟩
        rw [rl_noloc hl', rl_noloc hl']
    · exact rlI_congr _ _ ws (fun i w' a g h1 h2 => h (i + 1) w' a g h1 h2)

theorem rlI_congr_lt (G₁ G₂ : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (ws : List Word)
    (h : ∀ i, i < ws.length → G₁ i = G₂ i) : rlI G₁ ws = rlI G₂ ws :=
  rlI_congr G₁ G₂ ws (fun i w _ _ hw _ => h i (by
    rcases Nat.lt_or_ge i ws.length with hi | hi
    · exact hi
    · rw [List.getElem?_eq_none hi] at hw; cases hw))

theorem rlI_noloc (G₁ : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (ws : List Word)
    (h : ∀ w ∈ ws, ∀ a k, w.val ≠ .loc a k) : rlI G₁ ws = ws := by
  induction ws generalizing G₁ with
  | nil => rfl
  | cons w ws ih =>
    simp only [rlI_cons]; rw [rl_noloc (h w (by simp)), ih _ (fun w' hw' => h w' (by simp [hw']))]

theorem cst_noloc (v : WeakMem.Val) (hv : ∀ a k, v ≠ .loc a k) : ∀ a k, (cst v).val ≠ .loc a k := by
  intro a k e; apply hv a k; simpa [cst, Promises.TVal.mk0] using e

theorem ofArm_nil_noloc {t : Ty} {j : Nat} {q : List Word} (hq : ofArm t j [] = some q) :
    ∀ w ∈ q, ∀ a k, w.val ≠ .loc a k := by
  unfold ofArm at hq
  by_cases hs : sumHead t = true
  · simp only [hs, if_true] at hq
    cases htr : t.tier <;> rw [htr] at hq <;> simp only [encodeArm] at hq
    · cases hx : (armsOf t)[j]? <;> simp [hx] at hq
      split at hq
      · rename_i _ h2; simp at h2
      · rename_i _ h2; simp at h2
      · simp at hq; subst hq; intro w hw; simp at hw; subst hw; exact cst_noloc _ (by intro a k e; cases e)
      · simp at hq
    · simp at hq; subst hq; intro w hw; simp at hw
      rcases hw with rfl | rfl <;> exact cst_noloc _ (by intro a k e; cases e)
    · simp at hq
  · simp only [hs, if_false, Bool.false_eq_true] at hq
    split at hq
    · simp at hq; subst hq; simp
    · simp at hq

theorem shI_unI (tr : Tier) (H : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) : shI tr (unI tr H) = H := by
  cases tr <;> funext i <;> simp [shI, unI]

theorem unA_shI_cst (t : Ty) (tr : Tier) (g : WeakMem.AllocLabel → WeakMem.AllocLabel) :
    unA t (shI tr (fun _ => g)) = fun _ => g := by
  unfold unA; split <;> cases tr <;> cases t.tier <;> rfl

/-- At a loc position of an encoded arm, `unA` after `shIA` is the identity. -/
theorem unA_shIA_loc {t : Ty} {j : Nat} {p q : List Word} (hq : ofArm t j p = some q)
    (H : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) :
    ∀ i w a g, q[i]? = some w → w.val = .loc a g → unA t (shIA t H) i = H i := by
  intro i w a g hw hv
  unfold unA shIA
  by_cases hs : sumHead t = true
  · simp only [hs, if_true]
    unfold ofArm at hq; simp only [hs, if_true] at hq
    cases htr : t.tier <;> simp only [unI, shI]
    rw [htr] at hq; simp only [encodeArm] at hq
    rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩ <;> simp at hq <;> subst hq
    · rcases i with _ | _ | i <;> simp at hw
      · subst hw; exact absurd hv (cst_noloc _ (by intro a k e; cases e) a g)
      · subst hw; exact absurd hv (cst_noloc _ (by intro a k e; cases e) a g)
    · rcases i with _ | i
      · simp at hw; subst hw; exact absurd hv (cst_noloc _ (by intro a k e; cases e) a g)
      · simp
  · simp only [hs, if_false, Bool.false_eq_true]

theorem IniR_rlI {ρ : Nat → Nat} {i₁ i₂ : WeakMem.AllocLabel → Nat} :
    ∀ (ψ : Pred) (ws : List Word), IniR ρ i₁ ψ ws →
      (∀ a : WeakMem.Address, ws.map (·.val) = [.loc a 0] → i₁ a.label ≤ i₂ (G 0 a.label)) →
      IniR ρ i₂ ψ (rlI G ws)
  | .ini k, ws, h, hl => by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := vals_rlI_loc_inv hb
    exact Nat.le_trans (h a ha) (hl a ha)
  | .and p q, ws, h, hl => ⟨IniR_rlI p ws h.1 hl, IniR_rlI q ws h.2 hl⟩
  | .tt, _, _, _ => trivial
  | .le _ _, _, _, _ => trivial
  | .eq _ _, _, _, _ => trivial

theorem pre_push0 : ∀ (P : List Ty) (η : TEnv) (s : Ty), TEnv.pre P (η.push0 s) = TEnv.pre (P ++ [s]) η
  | [], _, _ => rfl
  | s' :: P, η, s => by simp only [TEnv.pre, List.cons_append]; rw [pre_push0 P η s]

end
end TermSound.Flat
