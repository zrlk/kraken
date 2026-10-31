import WeakCore.VRbClosure
/-! Route (D), variant Z‴: the inner relation `VRz` against VRb2 and the
original VRb.
* `VRz_VRb2` : VRz ⇒ VRb2 (structural; the `.tvar` arm goes to the left `η.get` disjunct).
* `VRz_VRb`  : VRz ⇒ VRb. So VRb2 Z‴ ⇒ VRb2 Z″ (the inner disjunct only tightens). -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

theorem VRz_VRb2 (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (bk : Prop) (rt : Shp) (ws : List Word),
    VRz ρ η bk t rt ws → VRb2 ρ η bk t rt ws := by
  induction t with
  | tvar k =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    obtain ⟨w0, h0, h1⟩ := h; exact ⟨w0, h0, Or.inl h1⟩
  | refine t ψ ih =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    exact ⟨ih _ _ _ _ _ h.1, h.2⟩
  | iex b ih =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ hv⟩
  | prod a b iha ihb =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    obtain ⟨ra, rb, h1, hf⟩ := h
    exact ⟨ra, rb, h1, fun n hn => let ⟨e1, e2, e3⟩ := hf n hn; ⟨e1, iha _ _ _ _ _ e2, ihb _ _ _ _ _ e3⟩⟩
  | sum a b iha ihb =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := h
    · exact ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm,
        fun hj => ⟨fun e => iha _ _ _ _ _ ((hA hj).1 e), fun e =>
          let ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e; ⟨q, hq, hs1, hw1, hv1, iha _ _ _ _ _ hv⟩⟩,
        fun hj => ⟨fun e => ihb _ _ _ _ _ ((hA' hj).1 e), fun e =>
          let ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e; ⟨q, hq, hs1, hw1, hv1, ihb _ _ _ _ _ hv⟩⟩⟩⟩
    · exact ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => let ⟨q, hq, hv⟩ := h2 hj; ⟨q, hq, iha _ _ _ _ _ hv⟩,
        fun hj => let ⟨q, hq, hv⟩ := h3 hj; ⟨q, hq, ihb _ _ _ _ _ hv⟩⟩⟩
  | tex κ b ih =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ hv⟩
  | mu b ih =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    exact ih _ _ _ _ _ h
  | iall b ih =>
    intro ρ η bk rt ws h; simp only [VRz, VRb2] at h ⊢
    exact fun n => ih _ _ _ _ _ (h n)
  | _ => intro ρ η bk rt ws h; simpa only [VRz, VRb2] using h

end TermSound.Flat
