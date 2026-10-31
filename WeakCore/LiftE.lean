import WeakCore.LiftG
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

section
variable {cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

-- dec_corr / ofArm_corr moved to VRbClosure.

theorem ExS_unboxed {η : TEnv} {tr : Tier} {as : List Ty} {ws p q : List Word} {j j' : Nat} {R : Ty}
    {gq : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel}
    (hd : decodeArm tr as ws = some (j, p)) (hp : p ≠ []) (hq : ofArm R j' p = some q)
    (hx : ExS cpy σ Cp bv η q gq) : ExS cpy σ Cp bv η ws (unI tr (shIA R gq)) := by
  intro i; rw [unI_shIA]
  rcases hx (ixA R (ixU tr i)) with h | ⟨h1, h2⟩ | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨h1, fun w a g hw hv => ?_⟩)
    obtain ⟨w', g', hw', hv', hvw'⟩ := dec_corr hd hp i w a g hw hv
    obtain ⟨w'', g'', hw'', hv'', hvw''⟩ := ofArm_corr hq _ w' a g' hw' hv'
    have := h2 w'' a g'' hw'' hv''
    rw [hvw'', hvw'] at this; exact this
  · exact Or.inr (Or.inr h)

theorem ExS_shT {η : TEnv} {T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel}
    (hT : ∀ k rt ws, ExS cpy σ Cp bv η ws (T k rt ws)) : ∀ k rt ws, ExS cpy σ Cp bv η ws (shT σ T k rt ws)
  | 0, _, ws => ExS_cst η ws
  | k + 1, rt, ws => hT k rt ws

theorem gc_ExS (t : Ty) : ∀ (T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel)
    (η : TEnv) (rt : Shp) (ws : List Word), (∀ k rt ws, ExS cpy σ Cp bv η ws (T k rt ws)) →
    ExS cpy σ Cp bv η ws (gc cpy σ Cp bv T TU η t rt ws) := by
  induction t with
  | ptr μ u _ => intro T TU η rt ws hT; cases μ <;> simp only [gc] <;> first | exact pubG_ExS η ws | exact ExS_cst η ws
  | ptrOpt μ u _ => intro T TU η rt ws hT; cases μ <;> simp only [gc] <;> first | exact pubG_ExS η ws | exact ExS_cst η ws
  | loc μ u _ => intro T TU η rt ws hT; cases μ <;> simp only [gc] <;> first | exact pubG_ExS η ws | exact ExS_cst η ws
  | refine t ψ ih => intro T TU η rt ws hT; simp only [gc]; exact ih T TU η rt ws hT
  | iex b ih => intro T TU η rt ws hT; simp only [gc]; split; exact ih T TU η _ ws hT; exact ExS_cst η ws
  | prod a b iha ihb =>
    intro T TU η rt ws hT; simp only [gc]
    split
    · split
      · rename_i n _
        intro i
        by_cases hi : i < n
        · rcases iha T TU η _ (ws.take n) hT i with h | ⟨h1, h2⟩ | ⟨k, h⟩
          · exact Or.inl (by simp only [hi, if_true]; exact h)
          · refine Or.inr (Or.inl ⟨by simp only [hi, if_true]; exact h1, fun w a g hw hv => h2 w a g ?_ hv⟩)
            rw [List.getElem?_take]; simp [hi, hw]
          · exact Or.inr (Or.inr ⟨k, by simp only [hi, if_true]; exact h⟩)
        · rcases ihb T TU η _ (ws.drop n) hT (i - n) with h | ⟨h1, h2⟩ | ⟨k, h⟩
          · exact Or.inl (by simp only [hi, if_false]; exact h)
          · refine Or.inr (Or.inl ⟨by simp only [hi, if_false]; exact h1, fun w a g hw hv => h2 w a g ?_ hv⟩)
            rw [List.getElem?_drop]; rw [show n + (i - n) = i by omega]; exact hw
          · exact Or.inr (Or.inr ⟨k, by simp only [hi, if_false]; exact h⟩)
      · exact ExS_cst η ws
    · exact ExS_cst η ws
  | sum a b iha ihb =>
    intro T TU η rt ws hT; simp only [gc]
    repeat' (first | exact ExS_cst η ws | exact ExS_bv η ws _ | exact iha T TU η _ ws hT | exact ihb T TU η _ ws hT | split)
    all_goals (rename_i hd hp _ _ _ hq; first
      | exact ExS_unboxed hd hp hq (iha T TU η _ _ hT)
      | exact ExS_unboxed hd hp hq (ihb T TU η _ _ hT))
  | tvar k => intro T TU η rt ws hT; simp only [gc]; exact hT k rt ws
  | tex κ b ih => intro T TU η rt ws hT; simp only [gc]; split; exact ih _ _ η _ ws (ExS_shT hT); exact ExS_cst η ws
  | mu b ih => intro T TU η rt ws hT; simp only [gc]; exact ih _ _ η rt ws (ExS_shT hT)
  | iall b ih => intro T TU η rt ws hT; simp only [gc]; exact ih T TU η rt ws hT
  | tid => intro T TU η rt ws hT; simp only [gc]; exact pubG_ExS η ws
  | _ => intro T TU η rt ws hT; simp only [gc]; exact ExS_cst η ws

end
end TermSound.Flat
