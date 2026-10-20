import WeakCore.TermCkX

/-! # TermCkW (was TermA4W): the A1 checker is sound (A1 checker invariant)

`checkW_sound`: `checkW` accepts ⇒ `Typed`.  A copy of `CoreTyping.check_sound` (D9 core-copy
budget), with `checkW` for `check`; the `let` case goes through `checkW_let`.
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermScope

theorem checkW_sound (p : Prog) : ∀ (e : Expr) (cx : Cx), checkW p cx e = .ok () → Typed p cx e := by
  intro e
  induction e with
  | let_ x op e ih =>
      intro cx h
      obtain ⟨-, c₁, -, hop, -, h2⟩ := checkW_let h
      exact .let_ hop (ih c₁ h2)
  | split a x y e ih =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u v
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
        exact .split h1 h2 h3 (ih c₃ h4)
      · simp at h
  | unpack a i x e ih =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i b
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, h3⟩ := h
        exact .unpack h1 h2 (ih c₂ h3)
      · simp at h
  | unpackT a α x e ih =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i κ b
        split at h
        · simp at h
        · rename_i hg
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, h3⟩ := h
          exact .unpackT h1 (by simpa using hg) h2 (ih c₂ h3)
      · simp at h
  | region a rn pn tn e ih =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u
        split at h
        · simp at h
        · rename_i hs
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
          exact .region h1 (by simpa using hs) h2 h3 (ih c₃ h4)
      · split at h
        · simp at h
        · rename_i hs
          simp only [bind_ok_iff] at h
          obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
          exact .regionBuf h1 (by simpa using hs) h2 h3 (ih c₃ h4)
      · simp at h
  | openPub a rn pn cn e ih =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, c₃, h3, h4⟩ := h
        exact .openPub h1 h2 h3 (ih c₃ h4)
      · simp at h
  | case a x e₁ y e₂ ih₁ ih₂ =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i u v
        simp only [bind_ok_iff] at h
        obtain ⟨c₂, h2, _, h3, c₃, h4, h5⟩ := h
        exact .case h1 h2 (ih₁ c₂ h3) h4 (ih₂ c₃ h5)
      · simp at h
  | ifnull a e₁ y e₂ ih₁ ih₂ =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, h⟩ := h
      try dsimp only at h
      split at h
      · rename_i μ u
        simp only [bind_ok_iff] at h
        obtain ⟨_, h2, c₂, h3, h4⟩ := h
        exact .ifnull h1 (ih₁ c₁ h2) h3 (ih₂ c₂ h4)
      · simp at h
  | parity a k ev od ihe iho =>
    intro cx h
    cases checkW_inv_parity h with
    | parity h1 h2 h3 h4 => exact .parity h1 h2 (ihe _ h3) (iho _ h4)
  | ifeq a b yes no ihy ihn =>
    intro cx h
    cases checkW_inv_ifeq h with
    | ifeqPlain h1 h2 h3 => exact .ifeqPlain h1 (ihy _ h2) (ihn _ h3)
    | ifeq h1 h2 h3 h4 h5 => exact .ifeq h1 h2 (ihy _ h3) h4 (ihn _ h5)
    | ifeqRec h1 h2 h3 h4 h5 h6 => exact .ifeqRec h1 h2 h3 (ihy _ h4) h5 (ihn _ h6)
    | ifeqZero h1 h2 h3 h4 h5 h6 => exact .ifeqZero h1 h2 h3 (ihy _ h4) h5 (ihn _ h6)
  | cas acq rel w e v t ok fail ihok ihf =>
    intro cx h
    cases checkW_inv_cas h with
    | casCell h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 => exact .casCell h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (ihok _ h12) (ihf _ h13)
    | casShare h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 => exact .casShare h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (ihok _ h14) (ihf _ h15)
    | casTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 => exact .casTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 (ihok _ h17) (ihf _ h18)
    | casEpoch h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => exact .casEpoch h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (ihok _ h11) (ihf _ h12)
  | casp acq rel w e0 e1 v0 v1 t ok fail ihok ihf =>
    intro cx h
    cases checkW_inv_casp h with
    | caspE h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => exact .caspE h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (ihok _ h11) (ihf _ h12)
    | caspBump h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 => exact .caspBump h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 (ihok _ h18) (ihf _ h19)
    | caspMove h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 => exact .caspMove h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 (ihok _ h15) (ihf _ h16)
    | caspTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 => exact .caspTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 (ihok _ h16) (ihf _ h17)
  | ret a =>
      intro cx h
      simp only [checkW, bind_ok_iff] at h
      obtain ⟨⟨t, c₁⟩, h1, u, hn, u', _, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        exact .ret h1 (noLeak_sound hn) (sub_sound _ _ _ (by simpa using hs))
  | tail f is a ts =>
      intro cx h
      simp only [checkW] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      simp only [bind_ok_iff] at h
      obtain ⟨d, hd, ⟨at_, rt⟩, hi, ⟨t, c₁⟩, h1, u, hn, u', _, h⟩ := h
      try dsimp only at h
      split at h
      · simp at h
      · rename_i hs
        split at h
        · simp at h
        · rename_i hr
          exact .tail hd hi h1 (noLeak_sound hn) (sub_sound _ _ _ (by simpa using hs))
            (sub_sound _ _ _ (by simpa using hr))


end TermA4

