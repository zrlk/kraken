import WeakCore.LiftTidBox
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

theorem ModeOKb_up {i : Nat} {P : WeakMem.AllocLabel → Option WeakMem.Ts} {S : WeakMem.AllocLabel → Prop}
    {bk : Prop} {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws ws' : List Word}
    (hw : ∀ f, (∀ w ∈ ws, f ≤ w.view) → ∀ w ∈ ws', f ≤ w.view) :
    ModeOKb i P S bk μ l c ws → ModeOKb i P S bk μ l c ws' := by
  cases μ with
  | own => exact id
  | pub => rintro ⟨f, h1, h2 | h2 | h2⟩
           · exact ⟨f, h1, Or.inl h2⟩
           · exact ⟨f, h1, Or.inr (Or.inl (hw f h2))⟩
           · exact ⟨f, h1, Or.inr (Or.inr h2)⟩
  | rgn _ => exact id

/-- `VRRB` is upward closed in the words' views. -/
theorem VRRB_up {ρ : Nat → Nat} {η : TEnv} : ∀ (t : Ty) (rt : Shp) (ws ws' : List Word) (R : Res),
    WLe ws ws' → VRRB ρ η t rt ws R → VRRB ρ η t rt ws' R := by
  intro t
  induction t generalizing ρ η with
  | tex κ b ih =>
      intro rt ws ws' R e hv
      simp only [VRRB] at hv ⊢
      obtain ⟨n, rb, s, hr, hs, haf, hv⟩ := hv
      exact ⟨n, rb, s, hr, hs, haf, ih rb ws ws' R e hv⟩
  | prod a b iha ihb =>
      intro rt ws ws' R e hv
      simp only [VRRB] at hv ⊢
      obtain ⟨ra, rb, hr, Ra, Rb, hR, hz, hf⟩ := hv
      refine ⟨ra, rb, hr, Ra, Rb, hR, hz, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hf n hn
      exact ⟨e.length ▸ h1, iha ra _ _ _ (e.take n) h2, ihb rb _ _ _ (e.drop n) h3⟩
  | iex b ih =>
      intro rt ws ws' R e hv
      simp only [VRRB] at hv ⊢
      obtain ⟨n, rb, w, hr, hv⟩ := hv
      exact ⟨n, rb, w, hr, ih rb ws ws' R e hv⟩
  | refine t ψ ih =>
      intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢
      exact ⟨ih rt ws ws' R e hv.1, IniR_vals e.vals ψ hv.2.1,
        fun hp => (hv.2.2 (PubPosE_vals e.vals hp)).imp (FreshW_wle e) (IniR_vals e.vals ψ)⟩
  | sum a b iha ihb =>
      intro rt ws ws' R e hv
      simp only [VRRB] at hv ⊢
      obtain ⟨n, Ra, Rb, hr, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · exact ⟨n, Ra, Rb, hr, Or.inl ⟨hb, x, s, B, e.vals.symm.trans hx, ho, hB, hn, hsB,
          hm.imp id (WLe_view e hx B.fr), fun hj => ⟨fun e' => iha _ _ _ _ e ((hA hj).1 e'), (hA hj).2⟩,
          fun hj => ⟨fun e' => ihb _ _ _ _ e ((hA' hj).1 e'), (hA' hj).2⟩⟩⟩
      · obtain ⟨p', hd', ep⟩ := decodeArm_wle e hd
        refine ⟨n, Ra, Rb, hr, Or.inr ⟨j, p', hd', fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', iha _ _ _ _ eq hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', ihb _ _ _ _ eq hv⟩
  | mu b ih => intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢; exact ih rt ws ws' R e hv
  | iall b ih => intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢; exact fun n => ih rt ws ws' R e (hv n)
  | tvar k =>
      intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢
      obtain ⟨w0, h0, hr⟩ := hv
      exact ⟨w0, WLe_trans h0 e, hr⟩
  | ptr μ u =>
      intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢
      obtain ⟨⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      exact ⟨⟨a, c, e.vals.symm.trans h1, h2, h3, h4, ModeOKb_up (WLe_view e h1) h5, h6⟩,
        hR.trans (ownW_vals e.vals)⟩
  | ptrOpt μ u =>
      intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢
      obtain ⟨hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl (e.vals.symm.trans hn), hR.trans (ownW_vals e.vals)⟩
      · exact ⟨Or.inr ⟨a, c, e.vals.symm.trans h1, h2, h3, h4, ModeOKb_up (WLe_view e h1) h5, h6⟩,
          hR.trans (ownW_vals e.vals)⟩
  | loc μ u =>
      intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢
      obtain ⟨hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl ⟨e.vals.symm.trans hn.1, hn.2⟩, hR.trans (ownW_vals e.vals)⟩
      · exact ⟨Or.inr ⟨a, c, U, e.vals.symm.trans h1, h3, h4, hF, ModeOKb_up (WLe_view e h1) h5, h6⟩,
          hR.trans (ownW_vals e.vals)⟩
  | tid =>
      intro rt ws ws' R e hv; simp only [VRRB, VRF, VRb2] at hv ⊢
      obtain ⟨⟨l, c, h1, h2, h3, h5⟩, hR⟩ := hv
      exact ⟨⟨l, c, e.vals.symm.trans h1, h2, h3, ModeOKb_up (WLe_view e h1) h5⟩, hR⟩
  | opq _ =>
      intro rt ws ws' R e hv; simp only [VRRB, VRF, VRb2] at hv ⊢
      obtain ⟨⟨n, hn⟩, hR⟩ := hv; exact ⟨⟨n, e.vals.symm.trans hn⟩, hR⟩
  | _ => intro rt ws ws' R e hv; simp only [VRRB] at hv ⊢ <;> first | exact hv | (rw [← e.vals]; exact hv)

section
variable {cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

theorem LiftOKQ.ce {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) : LiftOKQ cpy σ τ Cp bv (CE η₁) (CE η₂) :=
  { wit := rfl, prog := hm.prog, tid := hm.tid, sl := hm.sl, sr := hm.sr, sto := hm.sto, ini := hm.ini, rini := hm.rini,
    pfr := hm.pfr, seen := hm.seen, cown := hm.cown, csto := hm.csto, crini := hm.crini, cpfr := hm.cpfr,
    box := hm.box, cbox := hm.cbox, vbox := hm.vbox, vpfr := hm.vpfr, vseen := hm.vseen, vini := hm.vini,
    vrini := hm.vrini }

theorem LiftCini.ce {η₁ η₂ : TEnv} (h : LiftCini cpy Cp η₁ η₂) : LiftCini cpy Cp (CE η₁) (CE η₂) := h

theorem TvL_ce0 (η₁ η₂ : TEnv) : TvL τ (fun _ _ _ _ => σ) (CE η₁) (CE η₂) := by
  intro k rt ws' ws R hw hor
  rcases hor with h | ⟨-, -, S0, w0, R0, h⟩ <;> exact (h : False).elim

/-- The code view has no variables at `unsee` either (G-b: the payload oracle at `CE` is trivial). -/
theorem TvL_ce0u (η₁ η₂ : TEnv) : TvL τ (fun _ _ _ _ => σ) (CE η₁).unsee (CE η₂).unsee := by
  intro k rt ws' ws R hw hor
  rcases hor with h | ⟨-, -, S0, w0, R0, h⟩ <;> exact (h : False).elim

/-- The top-level variable oracle: a variable's words are relabeled as its witness's at the code view.
Both inner oracles are trivial: `CE` has closed witnesses. -/
noncomputable def Ttop (cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel) (Cp : WeakMem.AllocLabel → Prop)
    (bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel)
    (η : TEnv) : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel :=
  fun k rt ws => gc cpy σ Cp bv (fun _ _ _ _ => σ) (fun _ _ _ _ => σ) η (η.wit k) rt ws

theorem Ttop_ExS (η : TEnv) : ∀ k rt ws, ExS cpy σ Cp bv η ws (Ttop cpy σ Cp bv η k rt ws) :=
  fun k rt ws => gc_ExS _ _ _ _ _ _ (fun _ _ ws => ExS_cst η ws)

/-- The top oracle puts the copy only at deep-pub witnesses. -/
theorem TDp_top (η : TEnv) : NeC cpy σ bv → TDp cpy (Ttop cpy σ Cp bv η) (PTop η) := by
  intro hn k rt ws i h
  exact gc_pp (Cp := Cp) hn.1 hn.2 (η.wit k) _ _ η (fun _ _ _ _ => false) rt ws i (TDp.cst hn.1 _) h

/-- **TvL_top** (G-b): no payload premise. -/
theorem TvL_top (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l) {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂)
    (hB : CohRB η₁) (hW : CohR η₂) : TvL τ (Ttop cpy σ Cp bv η₁) η₁ η₂ := by
  intro k rt ws' ws R hw hor
  have h0 : VRRB (fun _ => 0) (CE η₁) (η₁.wit k) rt ws' R := by
    rcases hor with h | ⟨h, -, -⟩
    · exact ((hB k).1 (fun _ => 0) rt ws' R).1 h
    · exact VRRz_VRRB _ _ _ _ _ _ h
  have h1 := VRRB_up _ _ _ _ _ hw h0
  have h2 := VRR_lift hsc hbc (η₁.wit k) (fun _ _ _ _ => σ) (fun _ _ _ _ => σ) (fun _ => 0) (CE η₁) (CE η₂) η₁ rt ws R
    hm.ce hci.ce ⟨rfl, rfl, rfl⟩ ⟨fun _ _ _ _ h => (h : False).elim, fun _ _ _ _ h => (h : False).elim⟩ (TvL_ce0 η₁ η₂) (TvL_ce0u η₁ η₂) (fun _ _ ws => ExS_cst η₁ ws)
    (fun _ _ ws => ExS_cst η₁.unsee ws) (fun hn => TDp.cst hn.1 _) (fun hn => TDp.cst hn.1 _) h1
  refine ⟨_, WLe_refl _, ?_⟩
  exact ((hW k).1 (fun _ => 0) rt _ _).2 (by rw [hm.wit]; exact h2)

/-- The payload oracle (G-b): `TvL_top` at the `unsee` pair, by `CohRB.unsee` / `CohR.unsee`. -/
theorem TvL_unsee (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l) {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂)
    (hB : CohRB η₁) (hW : CohR η₂) : TvL τ (Ttop cpy σ Cp bv η₁.unsee) η₁.unsee η₂.unsee :=
  TvL_top hsc hbc hm.unsee hci.unsee hB.unsee hW.unsee

/-- **VRR_liftTop**: the lift at a coherent env pair.  No `PayLift`/`LiftPrem` (box variants). -/
theorem VRR_liftTop (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l) {η₁ η₂ : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂)
    (hB : CohRB η₁) (hW : CohR η₂) (hRL : RLink η₁) {ρ : Nat → Nat} {t : Ty} {rt : Shp} {ws : List Word} {X : Res}
    (h : VRRB ρ η₁ t rt ws X) :
    VRR ρ η₂ t rt (rlI (gc cpy σ Cp bv (Ttop cpy σ Cp bv η₁) (Ttop cpy σ Cp bv η₁.unsee) η₁ t rt ws) ws)
      (Res.sw τ X) :=
  VRR_lift hsc hbc t _ _ ρ η₁ η₂ η₁ rt ws X hm hci ⟨rfl, rfl, rfl⟩ hRL (TvL_top hsc hbc hm hci hB hW)
    (TvL_unsee hsc hbc hm hci hB hW) (Ttop_ExS η₁) (Ttop_ExS η₁.unsee) (TDp_top η₁) (TDp_top η₁.unsee) h


/-- `RLink` at a ♭ env with both coherences (as `ExtB` gives): rrs ⇒ VRRB at CE ⇒ VRF at CE ⇒ rels. -/
theorem RLink_of_coh {η : TEnv} (h0 : CohBW η) (h1 : CohRB η) : RLink η := by
  have hce : ∀ η' : TEnv, RLink (CE η') := fun _ => ⟨fun _ _ _ _ h => (h : False).elim, fun _ _ _ _ h => (h : False).elim⟩
  refine ⟨fun k S ws R h => ?_, fun k S ws R h => ?_⟩
  · exact ((h0 k).2.1 (fun _ => 0) S ws).2 (VRR_VRB (bkG := False) _ (hce η) (((h1 k).1 (fun _ => 0) S ws R).1 h))
  · exact ((h0 k).2.2 (fun _ => 0) S ws).2
      (VRR_VRB (bkG := False) _ (hce η.unsee) (((h1 k).2 (fun _ => 0) S ws R).1 h))

end
end TermSound.Flat
