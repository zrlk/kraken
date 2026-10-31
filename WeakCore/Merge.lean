import WeakCore.MergeH
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

section
variable {l' l : WeakMem.AllocLabel}

theorem lr_of_ne {w : Word} (h : ∀ a g, w.val = .loc a g → a.label ≠ l') : lr l' l w = w := by
  cases w with
  | mk v vw rt =>
    cases v with
    | loc a g => have := h a g rfl; simp [lr, lrv, this]
    | _ => simp [lr, lrv]

theorem map_lrv_single_num {vs : List WeakMem.Val} {n : Nat} :
    vs.map (lrv l' l) = [.num n] ↔ vs = [.num n] := by
  rcases vs with _ | ⟨v, _ | ⟨v2, vs⟩⟩ <;> simp [lrv_num]

theorem map_lrv_pair_num {vs : List WeakMem.Val} {n0 n1 : Nat} :
    vs.map (lrv l' l) = [.num n0, .num n1] ↔ vs = [.num n0, .num n1] := by
  rcases vs with _ | ⟨v, _ | ⟨v2, _ | ⟨v3, vs⟩⟩⟩ <;> simp [lrv_num]

theorem map_lrv_null {vs : List WeakMem.Val} : vs.map (lrv l' l) = [.null] ↔ vs = [.null] := by
  rcases vs with _ | ⟨v, _ | ⟨v2, vs⟩⟩ <;> simp [lrv_null]

theorem vals_lr_num {ws : List Word} {n : Nat} :
    (ws.map (lr l' l)).map (·.val) = [.num n] ↔ ws.map (·.val) = [.num n] := by
  rw [vals_lr]; exact map_lrv_single_num

theorem vals_lr_pair {ws : List Word} {n0 n1 : Nat} :
    (ws.map (lr l' l)).map (·.val) = [.num n0, .num n1] ↔ ws.map (·.val) = [.num n0, .num n1] := by
  rw [vals_lr]; exact map_lrv_pair_num

theorem vals_lr_null {ws : List Word} :
    (ws.map (lr l' l)).map (·.val) = [.null] ↔ ws.map (·.val) = [.null] := by
  rw [vals_lr]; exact map_lrv_null

theorem WordHolds_lr {P : Proto} {ws : List Word} :
    WordHolds P ((ws.map (lr l' l)).map (·.val)) ↔ WordHolds P (ws.map (·.val)) := by
  constructor
  · rintro ⟨hg, n, c, cl, k, hv, h⟩; exact ⟨hg, n, c, cl, k, vals_lr_num.1 hv, h⟩
  · rintro ⟨hg, n, c, cl, k, hv, h⟩; exact ⟨hg, n, c, cl, k, vals_lr_num.2 hv, h⟩

theorem Word2Holds_lr {P : Proto2} {ws : List Word} :
    Word2Holds P ((ws.map (lr l' l)).map (·.val)) ↔ Word2Holds P (ws.map (·.val)) := by
  constructor
  · rintro ⟨n0, n1, c, cl, k0, k1, hv, h⟩; exact ⟨n0, n1, c, cl, k0, k1, vals_lr_pair.1 hv, h⟩
  · rintro ⟨n0, n1, c, cl, k0, k1, hv, h⟩; exact ⟨n0, n1, c, cl, k0, k1, vals_lr_pair.2 hv, h⟩

/-- A single reference word after the merge. -/
theorem vals_lr_loc {ws : List Word} {a : WeakMem.Address} {g : Nat} (h : ws.map (·.val) = [.loc a g]) :
    (ws.map (lr l' l)).map (·.val) = [.loc (if a.label = l' then ⟨l, a.offset⟩ else a) g] := by
  rw [vals_lr, h]; by_cases e : a.label = l' <;> simp [lrv, e]

theorem IniAt_at {i₁ i₂ : WeakMem.AllocLabel → Nat} {c c₂ : Cell} {a b : WeakMem.Address} {U : Ty}
    (hty : c₂.ty = c.ty) (ho : a.offset = b.offset) (hi : i₁ a.label ≤ i₂ b.label) (h : IniAt i₁ c a U) :
    IniAt i₂ c₂ b U := by
  intro N e hc
  rcases h N e (hty ▸ hc) with ⟨h1, h2⟩ | ⟨us, j, o, h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1.trans hty.symm, h2.trans ho⟩
  · exact Or.inr ⟨us, j, o, h1, Nat.lt_of_lt_of_le h2 hi, h3.trans ho, h4⟩

theorem IniR_lr {ρ : Nat → Nat} {i₁ i₂ : WeakMem.AllocLabel → Nat} (hne : ∀ m, m ≠ l' → i₁ m ≤ i₂ m)
    (hl : i₁ l' ≤ i₂ l) : ∀ (ψ : Pred) (ws : List Word), IniR ρ i₁ ψ ws → IniR ρ i₂ ψ (ws.map (lr l' l))
  | .ini k, ws, h => by
    intro b hb
    rw [vals_lr] at hb
    rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
    · simp at hb
    · cases hv : w.val with
      | loc a g =>
        simp only [List.map, hv] at hb
        have ha := h a (by simp [hv]; by_cases e : a.label = l' <;> simp [lrv, e] at hb <;> exact hb.2)
        by_cases e : a.label = l'
        · simp [lrv, e] at hb; obtain ⟨rfl, -⟩ := hb; simp only; rw [e] at ha; exact Nat.le_trans ha hl
        · simp [lrv, e] at hb; obtain ⟨rfl, -⟩ := hb; exact Nat.le_trans ha (hne _ e)
      | _ => simp [hv, lrv] at hb
    · simp at hb
  | .and p q, ws, h => ⟨IniR_lr hne hl p ws h.1, IniR_lr hne hl q ws h.2⟩
  | .tt, _, _ => trivial
  | .le _ _, _, _ => trivial
  | .eq _ _, _, _ => trivial

theorem ownW_lr (μ : Mode) {ws : List Word} (h : μ = .own → ∀ a g, ws.map (·.val) = [.loc a g] → a.label ≠ l') :
    ownW μ (ws.map (lr l' l)) = ownW μ ws := by
  cases μ with
  | own =>
    have h' := h rfl
    simp only [ownW]
    rw [vals_lr]
    rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
    · rfl
    · cases hv : w.val with
      | loc a g =>
        have := h' a g (by simp [hv])
        simp [lrv, hv, this]
      | _ => simp [lrv, hv]
    · simp
  | _ => rfl

end
end TermSound.Flat
