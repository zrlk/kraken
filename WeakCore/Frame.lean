import WeakCore.ZRel
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound
open FlatAnchor (RRSound)

section
variable {cp : WeakMem.AllocLabel → Prop} {f σ : WeakMem.AllocLabel → WeakMem.AllocLabel}

theorem lookupE_cons_self (x : String) (ty : Ty) (ws : List Word) (env : Env) :
    lookupE ((x, ty, ws) :: env) x = some (ty, ws) := by simp [lookupE, List.find?]

theorem lookupE_cons_ne {x y : String} (h : y ≠ x) (ty : Ty) (ws : List Word) (env : Env) :
    lookupE ((x, ty, ws) :: env) y = lookupE env y := by
  have : (x == y) = false := by simp; exact fun e => h e.symm
  simp [lookupE, List.find?, this]

theorem Res.sw_mono {A B : Res} (h : A ≤ B) : Res.sw σ A ≤ Res.sw σ B := fun k => h (keySw σ k)

theorem Res.sum_sw : ∀ (l : List Res), Res.sum (l.map (Res.sw σ)) = Res.sw σ (Res.sum l)
  | [] => rfl
  | r :: l => by simp only [List.map_cons, Res.sum_cons, Res.sum_sw l]; rfl

/-- **F1** (VarsOK merge): only the bound variable's words are mapped; the others are `f`-fixed. -/
theorem VarsOK_merge {η₁ η₂ : TEnv} (hm : MergeOKQ cp f σ η₁ η₂) (hR : RelsSound η₁)
    (hr : ∀ k S vs, η₁.rels k S vs → η₂.rels k S (vs.map (rl f)))
    (hur : ∀ k S vs, η₁.urels k S vs → η₂.urels k S (vs.map (rl f)))
    {ρ : Nat → Nat} {σs : List Ty} {vars : List (String × Ty × Bool)} {x : String} {ty : Ty} {ws : List Word}
    {env : Env}
    (hfix : ∀ y e, vars.find? (·.1 == y) = some e → y ≠ x → ∀ rt ws', lookupE env y = some (rt, ws') →
      ws'.map (rl f) = ws')
    (h : VarsOK ρ η₁ σs vars ((x, ty, ws) :: env)) : VarsOKB ρ η₂ σs vars ((x, ty, ws.map (rl f)) :: env) := by
  intro y e hy
  obtain ⟨rt, ws1, hl, hv, hs⟩ := h y e hy
  by_cases hyx : y = x
  · subst hyx
    rw [lookupE_cons_self] at hl; cases hl
    exact ⟨ty, ws.map (rl f), lookupE_cons_self _ _ _ _, VR_merge _ _ _ _ _ _ hm hR hr hur hv, Lay_rl hs⟩
  · rw [lookupE_cons_ne hyx] at hl
    have e1 := hfix y e hy hyx rt ws1 hl
    refine ⟨rt, ws1, by rw [lookupE_cons_ne hyx]; exact hl, ?_, hs⟩
    rw [← e1]; exact VR_merge _ _ _ _ _ _ hm hR hr hur hv

/-- **F2** (HeldOK merge): the holdings are pulled back along `σ` (`Rx' := sw ∘ Rx`), so the bound is `sw Rf`. -/
theorem HeldOK_merge {η₁ η₂ : TEnv} (hm : MergeOKQ cp f σ η₁ η₂) (hRR : RRSound η₁)
    (hr : ∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S (vs.map (rl f)) (Res.sw σ Y))
    (hur : ∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S (vs.map (rl f)) (Res.sw σ Y))
    {ρ : Nat → Nat} {cx : Cx} {x : String} {ty : Ty} {ws : List Word} {env : Env} {Rf : Res}
    (hfix : ∀ y e, cx.vars.find? (·.1 == y) = some e → y ≠ x → ∀ rt ws', lookupE env y = some (rt, ws') →
      ws'.map (rl f) = ws')
    (h : HeldOK ρ η₁ cx ((x, ty, ws) :: env) Rf) :
    HeldOKB ρ η₂ cx ((x, ty, ws.map (rl f)) :: env) (Res.sw σ Rf) := by
  obtain ⟨h1, h2, h3, Rx, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun y => Res.sw σ (Rx y), fun y e hy hh => ?_, ?_⟩
  · obtain ⟨rt, ws1, hl, hv⟩ := h4 y e hy hh
    by_cases hyx : y = x
    · subst hyx
      rw [lookupE_cons_self] at hl; cases hl
      exact ⟨ty, ws.map (rl f), lookupE_cons_self _ _ _ _, VRR_merge _ _ _ _ _ _ _ hm hRR hr hur hv⟩
    · rw [lookupE_cons_ne hyx] at hl
      have e1 := hfix y e hy hyx rt ws1 hl
      refine ⟨rt, ws1, by rw [lookupE_cons_ne hyx]; exact hl, ?_⟩
      rw [← e1]; exact VRR_merge _ _ _ _ _ _ _ hm hRR hr hur hv
  · have := Res.sum_sw (σ := σ) ((cx.vars.filter (Holds cx)).map (fun e => Rx e.1))
    rw [List.map_map] at this
    intro k
    exact Nat.le_trans (Nat.le_of_eq (congrFun this k)) (h5 (keySw σ k))

end
end TermSound.Flat
