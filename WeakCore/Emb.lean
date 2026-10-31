import WeakCore.VRb
/-! P2: the embedding `VR → VRb` at any flag. -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

theorem VR_VRb (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (bk : Prop) (rt : Shp) (ws : List Word),
    VR ρ η t rt ws → VRb ρ η bk t rt ws := by
  induction t with
  | tid =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    obtain ⟨l, c, h1, h2, h3, hm⟩ := h; exact ⟨l, c, h1, h2, h3, ModeOK_b _ hm⟩
  | refine t ψ ih =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    exact ⟨ih _ _ _ _ _ h.1, h.2⟩
  | iex b ih =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ hv⟩
  | prod a b iha ihb =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    obtain ⟨ra, rb, hrt, hf⟩ := h
    exact ⟨ra, rb, hrt, fun n hn => ⟨(hf n hn).1, iha _ _ _ _ _ (hf n hn).2.1, ihb _ _ _ _ _ (hf n hn).2.2⟩⟩
  | sum a b iha ihb =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h
    refine ⟨n, Ra, Rb, hrt, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · refine Or.inl ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, fun hl => ⟨fun hb => iha _ _ _ _ _ ((hA hl).1 hb),
        fun hb => ?_⟩, fun hl => ⟨fun hb => ihb _ _ _ _ _ ((hB hl).1 hb), fun hb => ?_⟩⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hb; exact ⟨q, q1, q2, q3, q4, iha _ _ _ _ _ q5⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl).2 hb; exact ⟨q, q1, q2, q3, q4, ihb _ _ _ _ _ q5⟩
    · refine Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj; exact ⟨q, q1, iha _ _ _ _ _ q2⟩
      · obtain ⟨q, q1, q2⟩ := hB hj; exact ⟨q, q1, ihb _ _ _ _ _ q2⟩
  | ptr μ u _ =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    obtain ⟨a, c, h1, h2, h3, h4, hm, h5⟩ := h; exact ⟨a, c, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩
  | ptrOpt μ u _ =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    rcases h with h | ⟨a, c, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩
  | loc μ u _ =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    rcases h with h | ⟨a, c, U, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, U, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩
  | tex κ b ih =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ hv⟩
  | mu b ih =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    exact ih _ _ _ _ _ h
  | iall b ih =>
    intro ρ η bk rt ws h; simp only [VR] at h; simp only [VRb]
    exact fun n => ih _ _ _ _ _ (h n)
  | _ =>
    intro ρ η bk rt ws h
    (try simp only [VR] at h) <;> (try simp only [VRb]) <;> exact h

/-- The base embedding used by P3: `VR` gives `VRb` at the top flag `False`. -/
theorem VR_VRb0 {ρ η t rt ws} (h : VR ρ η t rt ws) : VRb ρ η False t rt ws := VR_VRb t ρ η False rt ws h

end TermSound.Flat
