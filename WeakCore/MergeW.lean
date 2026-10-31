import WeakCore.MergeV
import WeakCore.AnchorFrameTyping
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound
open FlatAnchor (RRSound VRR_PubPosEFresh RRSound.push0 RRSound.unsee)

section
variable {cp : WeakMem.AllocLabel → Prop} {f σ : WeakMem.AllocLabel → WeakMem.AllocLabel}

/-- **VRR_merge** (f-form): W typing at the query env ⇒ ♭ typing at the merged env, of the merged words,
with the resource pulled back along `σ`. -/
theorem VRR_merge (t : Ty) : ∀ (ρ : Nat → Nat) (η₁ η₂ : TEnv) (rt : Shp) (ws : List Word) (X : Res),
    MergeOKQ cp f σ η₁ η₂ → RRSound η₁ →
    (∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S (vs.map (rl f)) (Res.sw σ Y)) →
    (∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S (vs.map (rl f)) (Res.sw σ Y)) →
    VRR ρ η₁ t rt ws X → VRRB ρ η₂ t rt (ws.map (rl f)) (Res.sw σ X) := by
  induction t with
  | unit => intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]; rw [h]; rfl
  | intS i =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    exact ⟨by rw [vals_rl, h.1]; rfl, by rw [h.2]; rfl⟩
  | int =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨n, hn⟩, hX⟩ := h; exact ⟨⟨n, by rw [vals_rl, hn]; rfl⟩, by rw [hX]; rfl⟩
  | opq o =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR, VR] at h; simp only [VRRB, VRF, VRb2]
    obtain ⟨⟨n, hn⟩, hX⟩ := h; exact ⟨⟨n, by rw [vals_rl, hn]; rfl⟩, by rw [hX]; rfl⟩
  | tid =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR, VR] at h; simp only [VRRB, VRF, VRb2]
    obtain ⟨⟨l, c, h1, h2, h3, h4⟩, hX⟩ := h
    refine ⟨?_, by rw [hX]; rfl⟩
    by_cases hcp : cp l
    · -- ♭ tid flag: a copied tid cell is owned at the merged env (`cl`), with a pfr (`pfrl`)
      obtain ⟨c2, hc2, hty, -, how⟩ := hm.cl _ _ hcp h2
      obtain ⟨q, hq⟩ := hm.pfrl _ hcp
      have h3' : c2.ty = .unit := hty ▸ h3
      exact ⟨f l, c2, vals_rl_loc h1, hc2, h3', q, hq,
        Or.inr (Or.inr ⟨how, fun N e he => by rw [h3'] at he; cases he⟩)⟩
    · refine ⟨f l, c, vals_rl_loc h1, hm.sto _ _ hcp h2, h3, ?_⟩
      obtain ⟨q, hq, h⟩ := h4
      exact ⟨q, hm.pfr _ _ hcp hq, h.imp (hm.seen _ hcp) (fun hv => Or.inl (mem_map_rl_view hv))⟩
  | fix sg w =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨hrt, n, hn, hl⟩, hX⟩ := h; exact ⟨⟨hrt, n, by rw [vals_rl, hn]; rfl, hl⟩, by rw [hX]; rfl⟩
  | lanes sg w =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨hrt, n, hn⟩, hX⟩ := h; exact ⟨⟨hrt, n, by rw [vals_rl, hn]; rfl⟩, by rw [hX]; rfl⟩
  | refine t ψ ih =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    refine ⟨ih _ _ _ _ _ _ hm hRR hr hur h.1, IniR_rl (fun m => selIni_merge hm t m) ψ ws h.2, fun hp => ?_⟩
    replace hp := PubPosE_rl hm.wit (fun m B h => ⟨_, hm.box m B h, rfl⟩) hp
    have hF := VRR_PubPosEFresh hRR hp h.1
    by_cases hc : ∃ a, ws.map (·.val) = [.loc a 0] ∧ cp a.label
    · obtain ⟨a, ha, hcp⟩ := hc
      refine Or.inr (IniR_rl1 ha ?_ ψ h.2)
      exact Nat.le_trans (η₁.selIni_le_ini t _) (hm.inil _ hcp)
    · refine Or.inl fun b hb => ?_
      obtain ⟨a, ha, rfl⟩ := vals_rl_loc_inv hb
      have ncp : ¬ cp a.label := fun hcp => hc ⟨a, ha, hcp⟩
      obtain ⟨q, hq, hs⟩ := hF a ha
      exact ⟨q, hm.pfr _ _ ncp hq, hs.imp (hm.seen _ ncp) (fun hv => mem_map_rl_view hv)⟩
  | iex b ih =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ _ hm hRR hr hur hv⟩
  | prod a b iha ihb =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨ra, rb, hrt, Ra, Rb, hRab, hz, hf⟩ := h
    subst hRab
    refine ⟨ra, rb, hrt, Res.sw σ Ra, Res.sw σ Rb, rfl, fun e => by rw [hz e]; rfl, fun n hn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf n hn
    exact ⟨by simpa using h1, by rw [← List.map_take]; exact iha _ _ _ _ _ _ hm hRR hr hur h2,
      by rw [← List.map_drop]; exact ihb _ _ _ _ _ _ hm hRR hr hur h3⟩
  | sum a b iha ihb =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h
    refine ⟨n, Ra, Rb, hrt, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · refine Or.inl ⟨htier, ⟨f x.label, x.offset⟩, s, { B with pay := B.pay.map (rl f) }, vals_rl_loc h1, h2,
        hm.box _ _ h3, h4, ⟨h5.1, by simpa using h5.2⟩, ?_, fun hl => ⟨fun hb => ?_, fun hb => ?_⟩,
        fun hl => ⟨fun hb => ?_, fun hb => ?_⟩⟩
      · rcases h6 with ⟨hs, q, hq, hle⟩ | hv
        · by_cases hcp : cp x.label
          · obtain ⟨q0, hq0, hb⟩ := hm.pfrc _ hcp
            rw [hq0] at hq; cases hq
            exact Or.inr (mem_map_rl_view (fun w _ => Nat.le_trans hle (hb w.view)))
          · exact Or.inl ⟨hm.seen _ hcp hs, q, hm.pfr _ _ hcp hq, hle⟩
        · exact Or.inr (mem_map_rl_view hv)
      · exact iha _ _ _ _ _ _ hm hRR hr hur ((hA hl).1 hb)
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hb
        exact ⟨q.map (rl f), by dsimp only; rw [ofArm_rl, q1]; rfl, ShapeC_rl q2, q3, Valid_rl f _ _ q4,
          iha _ _ _ _ _ _ hm.unsee hRR.unsee hur hur q5⟩
      · exact ihb _ _ _ _ _ _ hm hRR hr hur ((hB hl).1 hb)
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl).2 hb
        exact ⟨q.map (rl f), by dsimp only; rw [ofArm_rl, q1]; rfl, ShapeC_rl q2, q3, Valid_rl f _ _ q4,
          ihb _ _ _ _ _ _ hm.unsee hRR.unsee hur hur q5⟩
    · refine Or.inr ⟨j, p.map (rl f), by rw [decodeArm_rl, hd]; rfl, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj
        exact ⟨q.map (rl f), by rw [ofArm_rl, q1]; rfl, iha _ _ _ _ _ _ hm hRR hr hur q2⟩
      · obtain ⟨q, q1, q2⟩ := hB hj
        exact ⟨q.map (rl f), by rw [ofArm_rl, q1]; rfl, ihb _ _ _ _ _ _ hm hRR hr hur q2⟩
  | tvar k =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨ws', h1, h2⟩ := h; exact ⟨ws'.map (rl f), WLe_rl f h1, Or.inl (hr _ _ _ _ h2)⟩
  | code sg tau e =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨i, d, h1, h2⟩, hX⟩ := h
    refine ⟨⟨i, d, by rw [vals_rl, h1]; rfl, ?_⟩, by rw [hX]; rfl⟩
    rw [← hm.prog, ← hm.wit]; exact h2
  | ptr μ u _ =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨a, c, h1, h2, h3, h4, hmo, h5⟩, hX⟩ := h
    obtain ⟨c₂, hs2, hty, hmo2, -, hR⟩ := refAt hm (fun c₂ => ∀ N e, c₂.ty ≠ .array (.lit N) e) h1 h3 hmo
      (fun c₂ hty _ _ _ N e he => h5 (by rw [← hty, he, accs_array_none]))
    refine ⟨⟨⟨f a.label, a.offset⟩, c₂, vals_rl_loc h1, h2, hs2, by rw [hty, ← hm.wit]; exact h4, hmo2,
      by rw [hty]; exact h5⟩, by rw [hX]; exact hR⟩
  | ptrOpt μ u _ =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨hc, hX⟩ := h
    rcases hc with hn | ⟨a, c, h1, h2, h3, h4, hmo, h5⟩
    · refine ⟨Or.inl (vals_rl_null.2 hn), ?_⟩
      rw [hX]; exact ownW_sw hm.fσ hm.σf μ ws (fun _ a g hv => by rw [hn] at hv; simp at hv)
    · obtain ⟨c₂, hs2, hty, hmo2, -, hR⟩ := refAt hm (fun c₂ => ∀ N e, c₂.ty ≠ .array (.lit N) e) h1 h3 hmo
        (fun c₂ hty _ _ _ N e he => h5 (by rw [← hty, he, accs_array_none]))
      refine ⟨Or.inr ⟨⟨f a.label, a.offset⟩, c₂, vals_rl_loc h1, h2, hs2, by rw [hty, ← hm.wit]; exact h4, hmo2,
        by rw [hty]; exact h5⟩, by rw [hX]; exact hR⟩
  | loc μ u _ =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨hc, hX⟩ := h
    rcases hc with ⟨hn, e, he⟩ | ⟨a, c, U, h1, h3, h4, h5, hmo, hI⟩
    · refine ⟨Or.inl ⟨vals_rl_null.2 hn, e, by rw [← hm.wit]; exact he⟩, ?_⟩
      rw [hX]; exact ownW_sw hm.fσ hm.σf μ ws (fun _ a g hv => by rw [hn] at hv; simp at hv)
    · obtain ⟨c₂, hs2, hty, hmo2, hle, hR⟩ := refAt hm (fun c₂ => IniAt η₂.rc c₂ ⟨f a.label, a.offset⟩ U) h1 h3 hmo
        (fun c₂ hty _ hμ hl => by subst hμ; exact IniAt_at (a := a) hty rfl hl hI)
      refine ⟨Or.inr ⟨⟨f a.label, a.offset⟩, c₂, U, vals_rl_loc h1, hs2, by rw [hty]; exact h4,
        by rw [← hm.wit]; exact h5, hmo2, IniAt_at (a := a) hty rfl hle hI⟩, by rw [hX]; exact hR⟩
  | void => intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h
  | tex κ b ih =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h
    exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ _ (hm.push0 s) (hRR.push0 s) (push0_rrs_merge hr)
      (push0_urrs_merge hur) hv⟩
  | mu b ih =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    rw [← hm.wit]
    exact ih _ _ _ _ _ _ (hm.push0 _) (hRR.push0 _) (push0_rrs_merge hr) (push0_urrs_merge hur) h
  | iall b ih =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    exact fun n => ih _ _ _ _ _ _ hm hRR hr hur (h n)
  | word r P =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨hp, hg⟩, hc⟩ := h
    refine ⟨⟨hp, fun e => ?_⟩, ?_⟩
    · obtain ⟨n, hn, hi⟩ := hg e; exact ⟨n, by rw [vals_rl, hn]; rfl, hi⟩
    · rcases hc with ⟨hw, hX⟩ | ⟨hw, hX⟩
      · refine Or.inl ⟨WordHolds_rl.2 hw, ?_⟩
        rw [hX, Res.sw_noown (by intro l; simp [wdW]; split <;> simp)]
      · refine Or.inr ⟨fun h' => hw (WordHolds_rl.1 h'), ?_⟩
        rw [hX, Res.sw_noown (by intro l; simp [wdW]; split <;> simp)]
  | word2 r P =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨hp, n0, n1, hn, hi⟩, hc⟩ := h
    refine ⟨⟨hp, n0, n1, by rw [vals_rl, hn]; rfl, hi⟩, ?_⟩
    rcases hc with ⟨hw, hX⟩ | ⟨hw, hX⟩
    · exact Or.inl ⟨Word2Holds_rl.2 hw, by rw [hX, Res.sw_noown (by intro l; simp)]⟩
    · exact Or.inr ⟨fun h' => hw (Word2Holds_rl.1 h'), by rw [hX, Res.sw_noown (by intro l; simp)]⟩
  | epair e P =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨hp, n0, n1, hn⟩, hX⟩ := h
    exact ⟨⟨hp, n0, n1, by rw [vals_rl, hn]; rfl⟩, by rw [hX]; rfl⟩
  | tok r st =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h; simp only [VRR] at h; simp only [VRRB]
    rw [h, Res.sw_noown (by intro l; cases st <;> simp)]
  | _ =>
    intro ρ η₁ η₂ rt ws X hm hRR hr hur h
    simp only [VRR] at h; simp only [VRRB]; rw [h]
    first | rfl | exact Res.sw_noown (by intro l; simp)

end
end TermSound.Flat
