import WeakCore.LiftUpClosed
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **VarBox** (G-c support): a box variant's payload merges back to the original's.
`MergeOKQ.box` at a variant label `bv x k` (with `f (bv x k) = x`) asks
`η′.box x = {B_var with pay := B_var.pay.map (rl f)}`; with `B_var.pay = rlI (dec k) B.pay` this is `B`
as soon as `f` undoes `σ`, `cpy` and every `bv · k'` on the payload's labels. -/

section
variable {σ cpy f : WeakMem.AllocLabel → WeakMem.AllocLabel} {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

theorem rl_rl_back {g : WeakMem.AllocLabel → WeakMem.AllocLabel} {w : Word}
    (h : ∀ a k, w.val = .loc a k → f (g a.label) = a.label) : rl f (rl g w) = w := by
  cases w with
  | mk v vw rt =>
    cases v with
    | loc a k => have := h a k rfl; simp [rl, rlv, this]
    | _ => simp [rl, rlv]

theorem rlI_back : ∀ (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (ws : List Word),
    (∀ i w a k, ws[i]? = some w → w.val = .loc a k → f (G i a.label) = a.label) → (rlI G ws).map (rl f) = ws
  | _, [], _ => rfl
  | G, w :: ws, h => by
    simp only [rlI_cons, List.map_cons]
    rw [rl_rl_back (fun a k hv => h 0 w a k rfl hv),
      rlI_back (fun i => G (i + 1)) ws (fun i w' a k h1 h2 => h (i + 1) w' a k (by simpa using h1) h2)]

/-- Every decoded position map is three-way (or the default `σ`). -/
theorem dec_three (k j : Nat) :
    PCode.dec σ cpy bv k j = σ ∨ PCode.dec σ cpy bv k j = cpy ∨ ∃ k', PCode.dec σ cpy bv k j = fun y => bv y k' := by
  unfold PCode.dec
  split
  · rename_i e _
    match e with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr (Or.inl rfl)
    | e + 2 => exact Or.inr (Or.inr ⟨_, rfl⟩)
  · exact Or.inl rfl

/-- **variant_pay_back**: the variant payload merges back to the original payload. -/
theorem variant_pay_back (k : Nat) (pay : List Word)
    (hb : ∀ w ∈ pay, ∀ a g, w.val = .loc a g →
      f (σ a.label) = a.label ∧ f (cpy a.label) = a.label ∧ ∀ k', f (bv a.label k') = a.label) :
    (rlI (PCode.dec σ cpy bv k) pay).map (rl f) = pay := by
  refine rlI_back _ pay (fun i w a g hw hv => ?_)
  have hm : w ∈ pay := List.mem_of_getElem? hw
  obtain ⟨h1, h2, h3⟩ := hb w hm a g hv
  rcases dec_three (σ := σ) (cpy := cpy) (bv := bv) k i with e | e | ⟨k', e⟩ <;> rw [e]
  · exact h1
  · exact h2
  · exact h3 k'

end
end TermSound.Flat
