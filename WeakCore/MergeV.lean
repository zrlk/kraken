import WeakCore.PubPosM
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

section
variable {cp : WeakMem.AllocLabel → Prop} {f σ : WeakMem.AllocLabel → WeakMem.AllocLabel}

theorem Res.sw_noown {X : Res} (h : ∀ l, X (.own l) = 0) : Res.sw σ X = X := by
  funext k; cases k with
  | own l => simp only [Res.sw, keySw]; rw [h, h]
  | _ => rfl

theorem vals_rl_loc_inv {ws : List Word} {b : WeakMem.Address} {g : Nat}
    (h : (ws.map (rl f)).map (·.val) = [.loc b g]) :
    ∃ a, ws.map (·.val) = [.loc a g] ∧ b = ⟨f a.label, a.offset⟩ := by
  rw [vals_rl] at h
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
  · simp at h
  · cases hv : w.val with
    | loc a g' => simp [hv, rlv] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨a, by simp [hv], rfl⟩
    | _ => simp [hv, rlv] at h
  · simp at h

theorem ownW_own_len {ws : List Word} (h : ws.length ≠ 1) : ownW .own ws = .zero := by
  unfold ownW; split
  · rename_i heq; have := congrArg List.length heq; simp at this; exact absurd this h
  · rfl

theorem ownW_sw (hfs : ∀ m, ¬ cp m → σ (f m) = m) (hsf : ∀ m, ¬ cp (σ m) → f (σ m) = m) (μ : Mode) (ws : List Word)
    (h : μ = .own → ∀ a g, ws.map (·.val) = [.loc a g] → ¬ cp a.label) :
    Res.sw σ (ownW μ ws) = ownW μ (ws.map (rl f)) := by
  cases μ with
  | own =>
    rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
    · rfl
    · cases hv : w.val with
      | loc a g =>
        have hc := h rfl a g (by simp [hv])
        simp only [ownW, List.map, hv, rl, rlv]
        funext k; cases k with
        | own m =>
          simp only [Res.sw, keySw, Res.one_apply]
          by_cases e : σ m = a.label
          · have e2 : m = f a.label := by rw [← e, hsf m (by rw [e]; exact hc)]
            simp [e2, hfs _ hc]
          · have e2 : m ≠ f a.label := fun h' => e (by rw [h', hfs _ hc])
            simp [e, e2]
        | _ => simp [Res.sw, keySw, Res.one_apply]
      | _ => simp only [ownW, List.map, hv, rl, rlv]; rfl
    · rw [ownW_own_len (by simp), ownW_own_len (by simp)]; rfl
  | pub => rfl
  | rgn r => rfl

theorem mem_map_rl_view {ws : List Word} {q : WeakMem.Ts} (hv : ∀ w ∈ ws, q ≤ w.view) :
    ∀ w ∈ ws.map (rl f), q ≤ w.view := by
  intro w hw; obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw; exact hv w0 hw0

theorem IniR_rl1 {ρ : Nat → Nat} {i₁ i₂ : WeakMem.AllocLabel → Nat} {a : WeakMem.Address} {ws : List Word}
    (hw : ws.map (·.val) = [.loc a 0]) (hl : i₁ a.label ≤ i₂ (f a.label)) :
    ∀ (ψ : Pred), IniR ρ i₁ ψ ws → IniR ρ i₂ ψ (ws.map (rl f))
  | .ini k, h => by
    intro b hb
    obtain ⟨a', ha', rfl⟩ := vals_rl_loc_inv hb
    rw [hw] at ha'; simp at ha'; subst ha'
    exact Nat.le_trans (h a hw) hl
  | .and p q, h => ⟨IniR_rl1 hw hl p h.1, IniR_rl1 hw hl q h.2⟩
  | .tt, _ => trivial
  | .le _ _, _ => trivial
  | .eq _ _, _ => trivial

/-- The reference core shared by the `ptr`/`ptrOpt`/`loc` arms. -/
theorem refAt {η₁ η₂ : TEnv} (hm : MergeOKQ cp f σ η₁ η₂) {μ : Mode} {a : WeakMem.Address} {g : Nat}
    {c : Cell} {ws : List Word} (bk : Cell → Prop)
    (hv : ws.map (·.val) = [.loc a g]) (hs : η₁.sto a.label = some c)
    (hmo : ModeOK η₁.tid η₁.pfr η₁.seen μ a.label c ws)
    (flag : ∀ c₂, c₂.ty = c.ty → cp a.label → μ = .pub → η₁.ini a.label ≤ η₂.rc (f a.label) → bk c₂) :
    ∃ c₂, η₂.sto (f a.label) = some c₂ ∧ c₂.ty = c.ty ∧
      ModeOKb η₂.tid η₂.pfr η₂.seen (False ∨ bk c₂) μ (f a.label) c₂ (ws.map (rl f)) ∧
      modeIni μ η₁.ini η₁.rini a.label ≤ modeIni μ η₂.ini η₂.rini (f a.label) ∧
      Res.sw σ (ownW μ ws) = ownW μ (ws.map (rl f)) := by
  by_cases hcp : cp a.label
  · obtain ⟨c₂, hs2, hty, ho, ho2⟩ := hm.cl _ _ hcp hs
    have hle : η₁.ini a.label ≤ η₂.ini (f a.label) := Nat.le_trans (hm.inil _ hcp) (Nat.min_le_left _ _)
    cases μ with
    | own => simp only [ModeOK] at hmo; rw [ho] at hmo; cases hmo
    | pub =>
      obtain ⟨q, hq⟩ := hm.pfrl _ hcp
      exact ⟨c₂, hs2, hty.symm, ⟨q, hq, Or.inr (Or.inr ⟨ho2, Or.inr (flag c₂ hty.symm hcp rfl (hm.inil _ hcp))⟩)⟩,
        hle, rfl⟩
    | rgn r => exact ⟨c₂, hs2, hty.symm, trivial, hle, rfl⟩
  · refine ⟨c, hm.sto _ _ hcp hs, rfl, ?_, ?_, ownW_sw hm.fσ hm.σf μ ws ?_⟩
    · cases μ with
      | own => simp only [ModeOK] at hmo; simp only [ModeOKb]; rw [hmo, hm.tid]
      | pub =>
        obtain ⟨q, hq, h⟩ := hmo
        exact ⟨q, hm.pfr _ _ hcp hq, h.imp (hm.seen _ hcp) (fun hv => Or.inl (mem_map_rl_view hv))⟩
      | rgn r => trivial
    · have h1 := hm.ini _ hcp; have h2 := hm.rini _ hcp
      cases μ <;> simp only [modeIni] <;> omega
    · intro _ a' g' hv'; rw [hv] at hv'; simp at hv'; rw [← hv'.1]
      rintro (h | h)
      · exact hcp h
      · rw [hs] at h; cases h

theorem ownTop_eq {η₁ η₂ : TEnv} (h : η₁.wit = η₂.wit) (t : Ty) : η₁.ownTop t = η₂.ownTop t := by
  cases t <;> simp [TEnv.ownTop, h]

theorem pubTop_eq {η₁ η₂ : TEnv} (h : η₁.wit = η₂.wit) (t : Ty) : η₁.pubTop t = η₂.pubTop t := by
  cases t <;> simp [TEnv.pubTop, h]

theorem selIni_merge {η₁ η₂ : TEnv} (hm : MergeOKQ cp f σ η₁ η₂) (t : Ty) (m : WeakMem.AllocLabel) :
    η₁.selIni t m ≤ η₂.selIni t (f m) := by
  by_cases hcp : cp m
  · have h1 := η₁.selIni_le_ini t m
    have h2 := hm.inil _ hcp
    have h3 : η₂.rc (f m) ≤ η₂.selIni t (f m) := by
      unfold TEnv.selIni TEnv.rc; split
      · exact Nat.le_refl _
      · exact Nat.min_le_left _ _
    omega
  · have h1 := hm.ini _ hcp; have h2 := hm.rini _ hcp
    unfold TEnv.selIni; rw [ownTop_eq hm.wit]; split <;> (try dsimp only) <;> omega

theorem push0_rrs_merge {η₁ η₂ : TEnv} {s : Ty}
    (hr : ∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S (vs.map (rl f)) (Res.sw σ Y)) :
    ∀ k S vs Y, (η₁.push0 s).rrs k S vs Y → (η₂.push0 s).rrs k S (vs.map (rl f)) (Res.sw σ Y) := by
  intro k S vs Y h
  cases k with
  | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | succ k => simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hr k S vs Y (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h)

theorem push0_urrs_merge {η₁ η₂ : TEnv} {s : Ty}
    (hr : ∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S (vs.map (rl f)) (Res.sw σ Y)) :
    ∀ k S vs Y, (η₁.push0 s).urrs k S vs Y → (η₂.push0 s).urrs k S (vs.map (rl f)) (Res.sw σ Y) := by
  intro k S vs Y h
  cases k with
  | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | succ k => simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hr k S vs Y (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h)

theorem accs_array_none (n : Idx) (e : Ty) : accs (.array n e) = none := by simp [accs]

end
end TermSound.Flat
