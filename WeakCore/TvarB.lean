import WeakCore.VRbClosure
/-! Route (D), step S1b: closing the `.tvar` arm.
* `NoTvarRead t`: `t` reaches no type variable through the arms VR recurses into (pointer targets
  and code types are not entered by VR, so variables there are guarded).  On such types VRb2 and the
  inner VRz agree (`VRb2_VRz`), so VRb2's `.tvar` disjunct needs no `rels` at all.
* `VRz_seen`: VRz is monotone in `seen` (memory typing reads at `unsee`, frames at `seen`).
* `CohB η`: every witness is closed and reads no variable. -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

def NoTvarRead : Ty → Prop
  | .tvar _ => False
  | .refine t _ => NoTvarRead t
  | .iex b => NoTvarRead b
  | .tex _ b => NoTvarRead b
  | .mu b => NoTvarRead b
  | .iall b => NoTvarRead b
  | .prod a b => NoTvarRead a ∧ NoTvarRead b
  | .sum a b => NoTvarRead a ∧ NoTvarRead b
  | _ => True

def CohB (η : TEnv) : Prop := ∀ k, Clo (η.wit k) ∧ NoTvarRead (η.wit k)

theorem VRb2_VRz (t : Ty) : NoTvarRead t → ∀ (ρ : Nat → Nat) (η : TEnv) (bk : Prop) (rt : Shp)
    (ws : List Word), VRb2 ρ η bk t rt ws → VRz ρ η bk t rt ws := by
  induction t with
  | tvar k => intro hN; exact hN.elim
  | refine t ψ ih =>
    intro hN ρ η bk rt ws h; simp only [VRb2] at h; simp only [VRz]
    exact ⟨ih hN _ _ _ _ _ h.1, h.2⟩
  | iex b ih =>
    intro hN ρ η bk rt ws h; simp only [VRb2] at h; simp only [VRz]
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih hN _ _ _ _ _ hv⟩
  | prod a b iha ihb =>
    intro hN ρ η bk rt ws h; simp only [VRb2] at h; simp only [VRz]
    obtain ⟨ra, rb, hrt, hf⟩ := h
    exact ⟨ra, rb, hrt, fun n hn => ⟨(hf n hn).1, iha hN.1 _ _ _ _ _ (hf n hn).2.1,
      ihb hN.2 _ _ _ _ _ (hf n hn).2.2⟩⟩
  | sum a b iha ihb =>
    intro hN ρ η bk rt ws h; simp only [VRb2] at h; simp only [VRz]
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h
    refine ⟨n, Ra, Rb, hrt, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · refine Or.inl ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, fun hl => ⟨fun hb =>
        iha hN.1 _ _ _ _ _ ((hA hl).1 hb), fun hb => ?_⟩, fun hl => ⟨fun hb =>
        ihb hN.2 _ _ _ _ _ ((hB hl).1 hb), fun hb => ?_⟩⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hb; exact ⟨q, q1, q2, q3, q4, iha hN.1 _ _ _ _ _ q5⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl).2 hb; exact ⟨q, q1, q2, q3, q4, ihb hN.2 _ _ _ _ _ q5⟩
    · refine Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj; exact ⟨q, q1, iha hN.1 _ _ _ _ _ q2⟩
      · obtain ⟨q, q1, q2⟩ := hB hj; exact ⟨q, q1, ihb hN.2 _ _ _ _ _ q2⟩
  | tex κ b ih =>
    intro hN ρ η bk rt ws h; simp only [VRb2] at h; simp only [VRz]
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; exact ⟨n, rb, s, hrt, hc, hw, ih hN _ _ _ _ _ hv⟩
  | mu b ih =>
    intro hN ρ η bk rt ws h; simp only [VRb2] at h; simp only [VRz]
    exact ih hN _ _ _ _ _ h
  | iall b ih =>
    intro hN ρ η bk rt ws h; simp only [VRb2] at h; simp only [VRz]
    exact fun n => ih hN _ _ _ _ _ (h n)
  | _ =>
    intro _ ρ η bk rt ws h
    (try simp only [VRb2] at h) <;> (try simp only [VRz]) <;> exact h

theorem ModeOKb_seen {i P} {S S' : WeakMem.AllocLabel → Prop} {bk μ l c ws} (hS : ∀ l, S l → S' l)
    (h : ModeOKb i P S bk μ l c ws) : ModeOKb i P S' bk μ l c ws := by
  cases μ with
  | own => exact h
  | pub => obtain ⟨f, hf, h⟩ := h; exact ⟨f, hf, h.imp_left (hS l)⟩
  | rgn _ => trivial

theorem VRz_seen (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (S' : WeakMem.AllocLabel → Prop) (bk : Prop)
    (rt : Shp) (ws : List Word), (∀ l, η.seen l → S' l) →
    VRz ρ η bk t rt ws → VRz ρ { η with seen := S' } bk t rt ws := by
  induction t with
  | tid =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    obtain ⟨l, c, h1, h2, h3, hm⟩ := h; exact ⟨l, c, h1, h2, h3, ModeOKb_seen hS hm⟩
  | refine t ψ ih =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    exact ⟨ih _ _ _ _ _ _ hS h.1, h.2.1, fun hq => (h.2.2 hq).imp_left
      (fun hf a ha => let ⟨f, h1, h2⟩ := hf a ha; ⟨f, h1, h2.imp_left (hS _)⟩)⟩
  | iex b ih =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ _ hS hv⟩
  | prod a b iha ihb =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    obtain ⟨ra, rb, hrt, hf⟩ := h
    exact ⟨ra, rb, hrt, fun n hn => ⟨(hf n hn).1, iha _ _ _ _ _ _ hS (hf n hn).2.1,
      ihb _ _ _ _ _ _ hS (hf n hn).2.2⟩⟩
  | sum a b iha ihb =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h
    refine ⟨n, Ra, Rb, hrt, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · refine Or.inl ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6.imp_left (fun h => ⟨hS _ h.1, h.2⟩),
        fun hl => ⟨fun hb => iha _ _ _ _ _ _ hS ((hA hl).1 hb), fun hb => (hA hl).2 hb⟩,
        fun hl => ⟨fun hb => ihb _ _ _ _ _ _ hS ((hB hl).1 hb), fun hb => (hB hl).2 hb⟩⟩
    · refine Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj; exact ⟨q, q1, iha _ _ _ _ _ _ hS q2⟩
      · obtain ⟨q, q1, q2⟩ := hB hj; exact ⟨q, q1, ihb _ _ _ _ _ _ hS q2⟩
  | ptr μ u _ =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    obtain ⟨a, c, h1, h2, h3, h4, hm, h5⟩ := h; exact ⟨a, c, h1, h2, h3, h4, ModeOKb_seen hS hm, h5⟩
  | ptrOpt μ u _ =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    rcases h with h | ⟨a, c, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, h1, h2, h3, h4, ModeOKb_seen hS hm, h5⟩
  | loc μ u _ =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    rcases h with h | ⟨a, c, U, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, U, h1, h2, h3, h4, ModeOKb_seen hS hm, h5⟩
  | tex κ b ih =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h
    exact ⟨n, rb, s, hrt, hc, hw, ih ρ (η.push0 s) S' bk rb ws hS hv⟩
  | mu b ih =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    exact ih ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) S' bk rt ws hS h
  | iall b ih =>
    intro ρ η S' bk rt ws hS h; simp only [VRz] at h ⊢
    exact fun n => ih _ _ _ _ _ _ hS (h n)
  | _ =>
    intro ρ η S' bk rt ws hS h
    (try simp only [VRz] at h ⊢) <;> exact h

/-- The `.tvar` closure: a word typed in memory (`VRB` at `CE η.unsee`, the shape of `ValOf`) at a
variable's closed, variable-free witness is a value at the variable, in the frame's env `η`. -/
theorem tvar_of_VRB {ρ : Nat → Nat} {η : TEnv} {k : Nat} {T : Ty} {w : Word}
    (hco : CohB η) (hk : η.wit k = T) (hv : VRB (fun _ => 0) (CE η.unsee) T (shp T) [w])
    (hne : ∃ S0 w0, η.rels k S0 w0) :
    VRb2 ρ η False (.tvar k) (shp T) [w] := by
  have hN : NoTvarRead T := by unfold CohB at hco; exact hk ▸ (hco k).2
  have h1 := VRb2_VRz T hN _ _ _ _ _ hv
  have h2 := VRz_seen T (fun _ => 0) (CE η.unsee) η.seen False (shp T) [w] (fun _ h => False.elim h) h1
  simp only [VRb2]
  refine ⟨[w], ⟨⟨rfl, fun _ _ _ => Nat.le_refl _⟩, trivial⟩, Or.inr ?_⟩
  rw [hk]; exact ⟨h2, hne⟩

end TermSound.Flat
