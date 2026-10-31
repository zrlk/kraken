import WeakCore.MergeW
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

section
variable {cp : WeakMem.AllocLabel → Prop} {f σ : WeakMem.AllocLabel → WeakMem.AllocLabel}

theorem push0_rels_merge {η₁ η₂ : TEnv} {s : Ty}
    (hr : ∀ k S vs, η₁.rels k S vs → η₂.rels k S (vs.map (rl f))) :
    ∀ k S vs, (η₁.push0 s).rels k S vs → (η₂.push0 s).rels k S (vs.map (rl f)) := by
  intro k S vs h
  cases k with
  | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | succ k => simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hr k S vs (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h)

theorem push0_urels_merge {η₁ η₂ : TEnv} {s : Ty}
    (hr : ∀ k S vs, η₁.urels k S vs → η₂.urels k S (vs.map (rl f))) :
    ∀ k S vs, (η₁.push0 s).urels k S vs → (η₂.push0 s).urels k S (vs.map (rl f)) := by
  intro k S vs h
  cases k with
  | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | succ k => simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hr k S vs (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h)

/-- **VR_merge** (f-form): W `VR` at the query env ⇒ ♭ `VRF False` at the merged env, of the merged words. -/
theorem VR_merge (t : Ty) : ∀ (ρ : Nat → Nat) (η₁ η₂ : TEnv) (rt : Shp) (ws : List Word),
    MergeOKQ cp f σ η₁ η₂ → RelsSound η₁ →
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S (vs.map (rl f))) →
    (∀ k S vs, η₁.urels k S vs → η₂.urels k S (vs.map (rl f))) →
    VR ρ η₁ t rt ws → VRF False ρ η₂ t rt (ws.map (rl f)) := by
  induction t with
  | intS i =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    rw [vals_rl, h]; rfl
  | int =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨n, hn⟩ := h; exact ⟨n, by rw [vals_rl, hn]; rfl⟩
  | opq o =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨n, hn⟩ := h; exact ⟨n, by rw [vals_rl, hn]; rfl⟩
  | tid =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨l, c, h1, h2, h3, h4⟩ := h
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
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨hrt, n, hn, hl⟩ := h; exact ⟨hrt, n, by rw [vals_rl, hn]; rfl, hl⟩
  | lanes sg w =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨hrt, n, hn⟩ := h; exact ⟨hrt, n, by rw [vals_rl, hn]; rfl⟩
  | refine t ψ ih =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    refine ⟨ih _ _ _ _ _ hm hR hr hur h.1, IniR_rl (fun m => selIni_merge hm t m) ψ ws h.2, fun hp => ?_⟩
    replace hp := PubPosE_rl hm.wit (fun m B h => ⟨_, hm.box m B h, rfl⟩) hp
    have hF := VR_PubPosEFresh hR hp h.1
    by_cases hc : ∃ a, ws.map (·.val) = [.loc a 0] ∧ cp a.label
    · obtain ⟨a, ha, hcp⟩ := hc
      exact Or.inr (IniR_rl1 ha (Nat.le_trans (η₁.selIni_le_ini t _) (hm.inil _ hcp)) ψ h.2)
    · refine Or.inl fun b hb => ?_
      obtain ⟨a, ha, rfl⟩ := vals_rl_loc_inv hb
      have ncp : ¬ cp a.label := fun hcp => hc ⟨a, ha, hcp⟩
      obtain ⟨q, hq, hs⟩ := hF a ha
      exact ⟨q, hm.pfr _ _ ncp hq, hs.imp (hm.seen _ ncp) (fun hv => mem_map_rl_view hv)⟩
  | iex b ih =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ hm hR hr hur hv⟩
  | prod a b iha ihb =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨ra, rb, hrt, hf⟩ := h
    refine ⟨ra, rb, hrt, fun n hn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf n hn
    exact ⟨by simpa using h1, by rw [← List.map_take]; exact iha _ _ _ _ _ hm hR hr hur h2,
      by rw [← List.map_drop]; exact ihb _ _ _ _ _ hm hR hr hur h3⟩
  | sum a b iha ihb =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
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
      · exact iha _ _ _ _ _ hm hR hr hur ((hA hl).1 hb)
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hb
        exact ⟨q.map (rl f), by dsimp only; rw [ofArm_rl, q1]; rfl, ShapeC_rl q2, q3, Valid_rl f _ _ q4,
          iha _ _ _ _ _ hm.unsee hR.unsee hur hur q5⟩
      · exact ihb _ _ _ _ _ hm hR hr hur ((hB hl).1 hb)
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl).2 hb
        exact ⟨q.map (rl f), by dsimp only; rw [ofArm_rl, q1]; rfl, ShapeC_rl q2, q3, Valid_rl f _ _ q4,
          ihb _ _ _ _ _ hm.unsee hR.unsee hur hur q5⟩
    · refine Or.inr ⟨j, p.map (rl f), by rw [decodeArm_rl, hd]; rfl, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj
        exact ⟨q.map (rl f), by rw [ofArm_rl, q1]; rfl, iha _ _ _ _ _ hm hR hr hur q2⟩
      · obtain ⟨q, q1, q2⟩ := hB hj
        exact ⟨q.map (rl f), by rw [ofArm_rl, q1]; rfl, ihb _ _ _ _ _ hm hR hr hur q2⟩
  | tvar k =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨ws', h1, h2⟩ := h; exact ⟨ws'.map (rl f), WLe_rl f h1, Or.inl (hr _ _ _ h2)⟩
  | code sg tau e =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨i, d, h1, h2⟩ := h
    refine ⟨i, d, by rw [vals_rl, h1]; rfl, ?_⟩
    rw [← hm.prog, ← hm.wit]; exact h2
  | ptr μ u _ =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨a, c, h1, h2, h3, h4, hmo, h5⟩ := h
    obtain ⟨c₂, hs2, hty, hmo2, -, -⟩ := refAt hm (fun c₂ => ∀ N e, c₂.ty ≠ .array (.lit N) e) h1 h3 hmo
      (fun c₂ hty _ _ _ N e he => h5 (by rw [← hty, he, accs_array_none]))
    exact ⟨⟨f a.label, a.offset⟩, c₂, vals_rl_loc h1, h2, hs2, by rw [hty, ← hm.wit]; exact h4, hmo2,
      by rw [hty]; exact h5⟩
  | ptrOpt μ u _ =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    rcases h with hn | ⟨a, c, h1, h2, h3, h4, hmo, h5⟩
    · exact Or.inl (vals_rl_null.2 hn)
    · obtain ⟨c₂, hs2, hty, hmo2, -, -⟩ := refAt hm (fun c₂ => ∀ N e, c₂.ty ≠ .array (.lit N) e) h1 h3 hmo
        (fun c₂ hty _ _ _ N e he => h5 (by rw [← hty, he, accs_array_none]))
      exact Or.inr ⟨⟨f a.label, a.offset⟩, c₂, vals_rl_loc h1, h2, hs2, by rw [hty, ← hm.wit]; exact h4, hmo2,
        by rw [hty]; exact h5⟩
  | loc μ u _ =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    rcases h with ⟨hn, e, he⟩ | ⟨a, c, U, h1, h3, h4, h5, hmo, hI⟩
    · exact Or.inl ⟨vals_rl_null.2 hn, e, by rw [← hm.wit]; exact he⟩
    · obtain ⟨c₂, hs2, hty, hmo2, hle, -⟩ := refAt hm (fun c₂ => IniAt η₂.rc c₂ ⟨f a.label, a.offset⟩ U) h1 h3 hmo
        (fun c₂ hty _ hμ hl => by subst hμ; exact IniAt_at (a := a) hty rfl hl hI)
      exact Or.inr ⟨⟨f a.label, a.offset⟩, c₂, U, vals_rl_loc h1, hs2, by rw [hty]; exact h4,
        by rw [← hm.wit]; exact h5, hmo2, IniAt_at (a := a) hty rfl hle hI⟩
  | void => intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h
  | tex κ b ih =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h
    exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ (hm.push0 s) (hR.push0 s) (push0_rels_merge hr)
      (push0_urels_merge hur) hv⟩
  | mu b ih =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    rw [← hm.wit]
    exact ih _ _ _ _ _ (hm.push0 _) (hR.push0 _) (push0_rels_merge hr) (push0_urels_merge hur) h
  | iall b ih =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    exact fun n => ih _ _ _ _ _ hm hR hr hur (h n)
  | word r P =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨hp, hg⟩ := h
    exact ⟨hp, fun e => by obtain ⟨n, hn, hi⟩ := hg e; exact ⟨n, by rw [vals_rl, hn]; rfl, hi⟩⟩
  | word2 r P =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨hp, n0, n1, hn, hi⟩ := h
    exact ⟨hp, n0, n1, by rw [vals_rl, hn]; rfl, hi⟩
  | epair e P =>
    intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VR] at h; simp only [VRF, VRb2]
    obtain ⟨hp, n0, n1, hn⟩ := h
    exact ⟨hp, n0, n1, by rw [vals_rl, hn]; rfl⟩
  | _ => intro ρ η₁ η₂ rt ws hm hR hr hur h; simp only [VRF, VRb2]

end
end TermSound.Flat
