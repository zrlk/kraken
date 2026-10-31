import WeakCore.DPub
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

noncomputable def gR (cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel) (Cp : WeakMem.AllocLabel → Prop)
    (E : TEnv) (ws : List Word) : Mode → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel
  | .pub => pubG cpy σ Cp E ws
  | _ => fun _ => σ

section
variable {cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

theorem gc_ptr {T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {E : TEnv} (μ : Mode)
    (u : Ty) (rt : Shp) (ws : List Word) : gc cpy σ Cp bv T TU E (.ptr μ u) rt ws = gR cpy σ Cp E ws μ := by
  cases μ <;> simp only [gc, gR]
theorem gc_ptrOpt {T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {E : TEnv}
    (μ : Mode) (u : Ty) (rt : Shp) (ws : List Word) :
    gc cpy σ Cp bv T TU E (.ptrOpt μ u) rt ws = gR cpy σ Cp E ws μ := by
  cases μ <;> simp only [gc, gR]
theorem gc_loc {T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {E : TEnv} (μ : Mode)
    (u : Ty) (rt : Shp) (ws : List Word) : gc cpy σ Cp bv T TU E (.loc μ u) rt ws = gR cpy σ Cp E ws μ := by
  cases μ <;> simp only [gc, gR]

theorem ownW_null {G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {μ : Mode}
    {ws : List Word} (hn : ws.map (·.val) = [.null]) : Res.sw τ (ownW μ ws) = ownW μ (rlI G ws) := by
  rw [rlI_single hn]
  exact ownW_sw (cp := fun _ => True) (f := G 0) (fun _ h => absurd trivial h) (fun _ h => absurd trivial h) μ ws
    (fun _ a g hv => by rw [hn] at hv; simp at hv)

theorem ref_lift {ρ : Nat → Nat} {η₁ η₂ E : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hE : SameV E η₁) {μ : Mode}
    {u : Ty} {ws : List Word} {a : WeakMem.Address} {c : Cell} {bk : Prop}
    (h1 : ws.map (·.val) = [.loc a 0]) (h2 : a.offset = 0) (h3 : η₁.sto a.label = some c)
    (h4 : Fd c.ty (cl ρ η₁.wit 0 0 u)) (hmo : ModeOKb η₁.tid η₁.pfr η₁.seen bk μ a.label c ws)
    (h5 : accs c.ty ≠ none) :
    (∃ (a : WeakMem.Address) (c : Cell), (rlI (gR cpy σ Cp E ws μ) ws).map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧
      η₂.sto a.label = some c ∧ Fd c.ty (cl ρ η₂.wit 0 0 u) ∧
      ModeOK η₂.tid η₂.pfr η₂.seen μ a.label c (rlI (gR cpy σ Cp E ws μ) ws) ∧ accs c.ty ≠ none) ∧
    Res.sw τ (ownW μ ws) = ownW μ (rlI (gR cpy σ Cp E ws μ) ws) := by
  rw [rlI_single h1]
  cases μ with
  | own =>
    refine ⟨⟨⟨σ a.label, a.offset⟩, c, vals_rl_loc h1, h2, hm.sto _ _ h3, by rw [hm.wit]; exact h4, ?_, h5⟩,
      ownW_lift hm.sl hm.sr σ .own ws (fun _ => rfl)⟩
    simp only [ModeOK]; simp only [ModeOKb] at hmo; rw [hm.tid]; exact hmo
  | rgn r =>
    exact ⟨⟨⟨σ a.label, a.offset⟩, c, vals_rl_loc h1, h2, hm.sto _ _ h3, by rw [hm.wit]; exact h4, trivial, h5⟩,
      ownW_lift hm.sl hm.sr σ (.rgn r) ws (fun e => by cases e)⟩
  | pub =>
    simp only [gR]
    by_cases hx : exmW Cp E ws
    · rw [pubG_of_exm hx]
      obtain ⟨a', ha', hc, hnF⟩ := hx; rw [h1] at ha'; simp at ha'; subst ha'
      obtain ⟨c₂, hs2, hty⟩ := hm.csto _ _ hc h3
      exact ⟨⟨⟨cpy a.label, a.offset⟩, c₂, vals_rl_loc h1, h2, hs2, by rw [hty, hm.wit]; exact h4,
        modeOK_cpy hm hc _, by rw [hty]; exact h5⟩, ownW_lift hm.sl hm.sr cpy .pub ws (fun e => by cases e)⟩
    · rw [pubG_of_nexm hx]
      have hF := fresh_of_nexm hE hm.cown h1 h3 hmo hx
      have hmo2 := modeOK_lift hm (c := c) hF (fun _ => σ); rw [rlI_cst] at hmo2
      exact ⟨⟨⟨σ a.label, a.offset⟩, c, vals_rl_loc h1, h2, hm.sto _ _ h3, by rw [hm.wit]; exact h4, hmo2, h5⟩,
        ownW_lift hm.sl hm.sr σ .pub ws (fun e => by cases e)⟩

/-- (rc seed) at a copied `pub` reference, the ♭ `ModeOKF` third disjunct gives `IniAt` at `rc`:
`exmW` (not fresh) rules out the first two. -/
theorem iniRc_of_exm {η₁ E : TEnv} (hE : SameV E η₁) {ws : List Word} {a : WeakMem.Address} {c : Cell} {Xp : Prop}
    (h1 : ws.map (·.val) = [.loc a 0]) (hmo : ModeOKb η₁.tid η₁.pfr η₁.seen (False ∨ Xp) .pub a.label c ws)
    (hnF : ¬ FreshW E ws) : Xp := by
  obtain ⟨f, hf, hs | hv | ⟨-, hb⟩⟩ := hmo
  · refine absurd (fun a'' h'' => ?_) hnF
    rw [h1] at h''; simp at h''; subst h''
    exact ⟨f, by rw [hE.2.1]; exact hf, Or.inl (by rw [hE.2.2]; exact hs)⟩
  · refine absurd (fun a'' h'' => ?_) hnF
    rw [h1] at h''; simp at h''; subst h''
    exact ⟨f, by rw [hE.2.1]; exact hf, Or.inr hv⟩
  · exact hb.resolve_left id

theorem loc_lift {ρ : Nat → Nat} {η₁ η₂ E : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂)
    (hE : SameV E η₁) {μ : Mode}
    {u : Ty} {ws : List Word} {a : WeakMem.Address} {c : Cell} {U : Ty}
    (h1 : ws.map (·.val) = [.loc a 0]) (h3 : η₁.sto a.label = some c) (h4 : AtOff c.ty a.offset U)
    (h5 : Fd U (cl ρ η₁.wit 0 0 u))
    (hmo : ModeOKb η₁.tid η₁.pfr η₁.seen (False ∨ IniAt η₁.rc c a U) μ a.label c ws)
    (hI : IniAt (modeIni μ η₁.ini η₁.rini) c a U) :
    (∃ (a : WeakMem.Address) (c : Cell) (U : Ty), (rlI (gR cpy σ Cp E ws μ) ws).map (·.val) = [.loc a 0] ∧
      η₂.sto a.label = some c ∧ AtOff c.ty a.offset U ∧ Fd U (cl ρ η₂.wit 0 0 u) ∧
      ModeOK η₂.tid η₂.pfr η₂.seen μ a.label c (rlI (gR cpy σ Cp E ws μ) ws) ∧
      IniAt (modeIni μ η₂.ini η₂.rini) c a U) ∧
    Res.sw τ (ownW μ ws) = ownW μ (rlI (gR cpy σ Cp E ws μ) ws) := by
  rw [rlI_single h1]
  cases μ with
  | own =>
    refine ⟨⟨⟨σ a.label, a.offset⟩, c, U, vals_rl_loc h1, hm.sto _ _ h3, h4, by rw [hm.wit]; exact h5, ?_,
      IniAt_at (a := a) rfl rfl ?_ hI⟩, ownW_lift hm.sl hm.sr σ .own ws (fun _ => rfl)⟩
    · simp only [ModeOK]; simp only [ModeOKb] at hmo; rw [hm.tid]; exact hmo
    · have := hm.ini a.label; have := hm.rini a.label; simp only [modeIni]; omega
  | rgn r =>
    exact ⟨⟨⟨σ a.label, a.offset⟩, c, U, vals_rl_loc h1, hm.sto _ _ h3, h4, by rw [hm.wit]; exact h5, trivial,
      IniAt_at (a := a) rfl rfl (hm.ini a.label) hI⟩, ownW_lift hm.sl hm.sr σ (.rgn r) ws (fun e => by cases e)⟩
  | pub =>
    simp only [gR]
    by_cases hx : exmW Cp E ws
    · rw [pubG_of_exm hx]
      obtain ⟨a', ha', hc, hnF⟩ := hx; rw [h1] at ha'; simp at ha'; subst ha'
      obtain ⟨c₂, hs2, hty⟩ := hm.csto _ _ hc h3
      exact ⟨⟨⟨cpy a.label, a.offset⟩, c₂, U, vals_rl_loc h1, hs2, by rw [hty]; exact h4,
        by rw [hm.wit]; exact h5, modeOK_cpy hm hc _, IniAt_at (a := a) hty rfl (hci _ hc) (iniRc_of_exm hE h1 hmo hnF)⟩,
        ownW_lift hm.sl hm.sr cpy .pub ws (fun e => by cases e)⟩
    · rw [pubG_of_nexm hx]
      have hF := fresh_of_nexm hE hm.cown h1 h3 hmo hx
      have hmo2 := modeOK_lift hm (c := c) hF (fun _ => σ); rw [rlI_cst] at hmo2
      exact ⟨⟨⟨σ a.label, a.offset⟩, c, U, vals_rl_loc h1, hm.sto _ _ h3, h4, by rw [hm.wit]; exact h5, hmo2,
        IniAt_at (a := a) rfl rfl (hm.ini a.label) hI⟩, ownW_lift hm.sl hm.sr σ .pub ws (fun e => by cases e)⟩

/-- `shIA` only re-indexes. -/
theorem shIA_at (t : Ty) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (j : Nat) :
    ∃ j', shIA t G j = G j' := by
  unfold shIA
  by_cases hs : sumHead t = true
  · simp only [hs, if_true]; cases t.tier <;> simp only [shI] <;> exact ⟨_, rfl⟩
  · simp only [hs, if_false, Bool.false_eq_true]; exact ⟨j, rfl⟩

/-- A `gc`-made map (three-way by `ExS`) has the code shape, after any `shIA`. -/
theorem ok3_of_ExS {η : TEnv} {ws : List Word} {G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel}
    (hx : ExS cpy σ Cp bv η ws G) (t : Ty) (len : Nat) : PCode.Ok3 σ cpy bv (shIA t G) len := by
  intro j _
  obtain ⟨j', e⟩ := shIA_at t G j
  rw [e]
  rcases hx j' with h | ⟨h, -⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The variant's payload read at arm `R` is the canonical relabel of the ♭ arm payload. -/
theorem ofArm_variant {η : TEnv} {R : Ty} {j : Nat} {pay q : List Word}
    {Gq : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} (hx : ExS cpy σ Cp bv η q Gq)
    (hq : ofArm R j pay = some q) :
    ofArm R j (rlI (PCode.dec σ cpy bv (PCode.enc σ cpy bv (shIA R Gq) pay.length)) pay) = some (rlI Gq q) := by
  have e1 : rlI (PCode.dec σ cpy bv (PCode.enc σ cpy bv (shIA R Gq) pay.length)) pay = rlI (shIA R Gq) pay :=
    rlI_congr_lt _ _ pay (fun i hi => PCode.dec_enc σ cpy bv (ok3_of_ExS hx R pay.length) hi)
  rw [e1, ofArm_rlI, hq]
  simp only [Option.map_some]
  exact congrArg some (rlI_congr _ _ q (unA_shIA_loc hq _))

/-- The box behind a lifted boxed-sum pointer: at `σ x`, `cpy x` (exempt) or a variant `bv x k`. -/
theorem boxptr_lift {η₁ η₂ E : TEnv} (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hE : SameV E η₁)
    {x : WeakMem.Address} {B : Box} {w0 : Word} {g : WeakMem.AllocLabel → WeakMem.AllocLabel}
    (h3 : η₁.box x.label = some B)
    (h6 : (η₁.seen x.label ∧ ∃ f, η₁.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ [w0], B.fr ≤ w.view)
    (hg : g = σ ∨ (g = cpy ∧ Cp x.label ∧ ¬ Fr1 E x.label w0.view) ∨ ∃ k, g = fun y => bv y k) :
    ∃ P : List Word, P.length = B.pay.length ∧ η₂.box (g x.label) = some { B with pay := P } ∧
      ((η₂.seen (g x.label) ∧ ∃ f, η₂.pfr (g x.label) = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ [rl g w0], B.fr ≤ w.view) := by
  have hv : (∀ w ∈ [w0], B.fr ≤ w.view) → ∀ w ∈ [rl g w0], B.fr ≤ w.view := fun hv =>
    rlI_views (fun _ => g) (ws := [w0]) hv
  rcases hg with rfl | ⟨rfl, hc, hnF⟩ | ⟨k, rfl⟩
  · obtain ⟨P, hP, hb⟩ := hm.box _ _ h3
    exact ⟨P, hP, hb, h6.imp (fun ⟨hs, f, hf, hle⟩ => ⟨hm.seen _ hs, f, hm.pfr _ _ hf, hle⟩) hv⟩
  · obtain ⟨P, hP, hb⟩ := hm.cbox _ _ hc h3
    refine ⟨P, hP, hb, Or.inr ?_⟩
    rcases h6 with ⟨hs, f, hf, -⟩ | h
    · exact absurd ⟨f, by rw [hE.2.1]; exact hf, Or.inl (by rw [hE.2.2]; exact hs)⟩ hnF
    · exact hv h
  · exact ⟨_, rlI_length _ _, hm.vbox _ _ k h3,
      h6.imp (fun ⟨hs, f, hf, hle⟩ => ⟨hm.vseen _ _ hs, f, hm.vpfr _ _ _ hf, hle⟩) hv⟩

end

section
variable {cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

/-- **VRR_lift** (box variants): ♭ reading at `η₁` ⇒ W reading at `η₂` of the `gc`-relabeled words, resource
`Res.sw τ`.  `T` is the tvar oracle at `η₁`, `TU` the one at `η₁.unsee` (box payloads).  No `PayLift`. -/
theorem VRR_lift (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l)
    (t : Ty) : ∀ (T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel)
    (ρ : Nat → Nat) (η₁ η₂ E : TEnv) (rt : Shp) (ws : List Word) (X : Res),
    LiftOKQ cpy σ τ Cp bv η₁ η₂ → LiftCini cpy Cp η₁ η₂ → SameV E η₁ → RLink η₁ →
    TvL τ T η₁ η₂ → TvL τ TU η₁.unsee η₂.unsee →
    (∀ k rt ws, ExS cpy σ Cp bv E ws (T k rt ws)) → (∀ k rt ws, ExS cpy σ Cp bv E.unsee ws (TU k rt ws)) →
    (NeC cpy σ bv → TDp cpy T (PTop η₁)) → (NeC cpy σ bv → TDp cpy TU (PTop η₁.unsee)) →
    VRRB ρ η₁ t rt ws X →
    VRR ρ η₂ t rt (rlI (gc cpy σ Cp bv T TU E t rt ws) ws) (Res.sw τ X) := by
  induction t with
  | unit => intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR]; rw [h]; rfl
  | intS i =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]; exact ⟨vals_rl_num.2 h.1, by rw [h.2]; rfl⟩
  | int =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]; obtain ⟨⟨n, hn⟩, hX⟩ := h; exact ⟨⟨n, vals_rl_num.2 hn⟩, by rw [hX]; rfl⟩
  | opq o =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB, VRF, VRb2] at h; simp only [VRR, VR, gc]
    rw [rlI_cst]; obtain ⟨⟨n, hn⟩, hX⟩ := h; exact ⟨⟨n, vals_rl_num.2 hn⟩, by rw [hX]; rfl⟩
  | tid =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB, VRF, VRb2] at h; simp only [VRR, VR, gc]
    obtain ⟨⟨l, c, h1, h2, h3, h4⟩, hX⟩ := h
    rw [rlI_single h1]
    by_cases hx : exmW Cp E ws
    · -- (b′)/T1: an exempt tid head goes to its copy (widened to tid heads)
      rw [pubG_of_exm hx]
      obtain ⟨a', ha', hc, -⟩ := hx
      rw [h1] at ha'
      have e := (List.cons.inj ha').1
      injection e with e1
      have hc' : Cp l := by rw [← e1] at hc; exact hc
      obtain ⟨c₂, hs2, hty⟩ := hm.csto _ _ hc' h2
      exact ⟨⟨cpy l, c₂, vals_rl_loc h1, hs2, by rw [hty]; exact h3, modeOK_cpy hm hc' _⟩, by rw [hX]; rfl⟩
    · simp only [pubG_of_nexm hx]
      refine ⟨⟨σ l, c, vals_rl_loc h1, hm.sto _ _ h2, h3, ?_⟩, by rw [hX]; rfl⟩
      obtain ⟨q, hq, hs | hv | ⟨ho, -⟩⟩ := h4
      · exact ⟨q, hm.pfr _ _ hq, Or.inl (hm.seen _ hs)⟩
      · exact ⟨q, hm.pfr _ _ hq, Or.inr (mem_map_rl_view hv)⟩
      · -- the ungated owner disjunct: the owned tid cell is a copy label (`cown`), so non-exemption
        -- makes the word fresh
        have hCp : Cp l := hm.cown l c h2 ho ⟨q, hq⟩
        have hF : FreshW E ws := (Classical.em (FreshW E ws)).elim id
          (fun hn => (hx ⟨⟨l, 0⟩, h1, hCp, hn⟩).elim)
        obtain ⟨q', hq', hs'⟩ := hF ⟨l, 0⟩ h1
        rw [hE.2.1] at hq'; rw [hE.2.2] at hs'
        exact ⟨q', hm.pfr _ _ hq', hs'.imp (hm.seen _) (fun hv => mem_map_rl_view hv)⟩
  | fix sg w =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]; obtain ⟨⟨hrt, n, hn, hl⟩, hX⟩ := h; exact ⟨⟨hrt, n, vals_rl_num.2 hn, hl⟩, by rw [hX]; rfl⟩
  | lanes sg w =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]; obtain ⟨⟨hrt, n, hn⟩, hX⟩ := h; exact ⟨⟨hrt, n, vals_rl_num.2 hn⟩, by rw [hX]; rfl⟩
  | refine t ψ ih =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h
    have h0 := h
    simp only [VRRB] at h; simp only [VRR, gc]
    obtain ⟨h1, h2, -⟩ := h
    refine ⟨ih T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h1, ?_⟩
    rcases Classical.em (∃ a : WeakMem.Address, ws.map (·.val) = [.loc a 0]) with ⟨a, ha⟩ | hn
    · obtain ⟨w, rfl, hw⟩ := single_of_vals ha
      rcases gc0 (TU := TU) hTx t rt hw with hg | ⟨hg, hc, hF⟩ | ⟨k, hg⟩
      · exact IniR_rlI ψ [w] h2 (fun a' _ => by rw [hg]; exact selIni_lift hm t a'.label σ (Or.inl rfl))
      · have hne : NeC cpy σ bv := ⟨fun e => hsc _ hc (congrFun e _), fun k e => hbc _ k hc (congrFun e _)⟩
        have hdp : PubPos η₁ t rt [w] = true := by
          have := gc_pp hne.1 hne.2 t T TU E (PTop η₁) rt [w] 0 (hTd hne) hg
          rwa [hE.1] at this
        rcases D5bTmp_holds.toR hRL h0 hdp with hFr | hr
        · exfalso
          obtain ⟨f, hf, hs⟩ := hFr a (by simp [hw])
          refine hF ⟨f, by rw [hE.2.1]; exact hf, ?_⟩
          rcases hs with hs | hv
          · exact Or.inl (by rw [hE.2.2]; exact hs)
          · exact Or.inr (hv w List.mem_cons_self)
        · refine IniR_rlI ψ [w] hr (fun a' ha' => ?_)
          have e : a' = a := by simp [hw] at ha'; exact ha'.symm
          subst e; rw [hg]; exact selIni_cpy hm hci t hc
      · exact IniR_rlI ψ [w] h2 (fun a' _ => by rw [hg]; exact selIni_lift hm t a'.label _ (Or.inr ⟨k, rfl⟩))
    · exact IniR_rlI ψ ws h2 (fun a' ha' => absurd ⟨a', ha'⟩ hn)
  | iex b ih =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h
    obtain ⟨n, rb, w, hrt, hv⟩ := h; subst hrt; simp only [VRR, gc]
    exact ⟨n, rb, w, rfl, ih T TU (vcons w ρ) η₁ η₂ E rb ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd hv⟩
  | prod a b iha ihb =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h
    obtain ⟨ra, rb, hrt, Ra, Rb, hRab, hz, hf⟩ := h; subst hrt hRab
    simp only [VRR]
    refine ⟨ra, rb, rfl, Res.sw τ Ra, Res.sw τ Rb, Res.sw_add τ Ra Rb, fun e => by rw [hz e]; rfl, fun n hn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf n hn
    have hG : gc cpy σ Cp bv T TU E (.prod a b) (.prod ra rb) ws = fun i => if i < n then
        gc cpy σ Cp bv T TU E a ra (ws.take n) i else gc cpy σ Cp bv T TU E b rb (ws.drop n) (i - n) := by
      simp only [gc, hn]
    rw [hG]
    refine ⟨by rw [rlI_length]; exact h1, ?_, ?_⟩
    · rw [rlI_take, rlI_congr_lt _ (gc cpy σ Cp bv T TU E a ra (ws.take n)) (ws.take n) (fun i hi => by
        simp only [List.length_take] at hi; simp only [show i < n by omega, if_true])]
      exact iha T TU ρ η₁ η₂ E ra (ws.take n) Ra hm hci hE hRL hT hTU hTx hTUx hTd hTUd h2
    · rw [rlI_drop]
      have e : (fun i => (fun i => if i < n then gc cpy σ Cp bv T TU E a ra (ws.take n) i else
          gc cpy σ Cp bv T TU E b rb (ws.drop n) (i - n)) (i + n)) = gc cpy σ Cp bv T TU E b rb (ws.drop n) := by
        funext i; simp only []; rw [if_neg (by omega), Nat.add_sub_cancel]
      rw [e]; exact ihb T TU ρ η₁ η₂ E rb (ws.drop n) Rb hm hci hE hRL hT hTU hTx hTUx hTd hTUd h3
  | sum a b iha ihb =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h; subst hrt; simp only [VRR]
    refine ⟨n, Ra, Rb, rfl, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · subst h4
      obtain ⟨w0, rfl, hw0⟩ := single_of_vals h1
      have h3E : E.box x.label = some B := by rw [hE.1]; exact h3
      -- packaging: once the pointer's label map `g` and the box payload `P` are known
      have pack : ∀ (g : WeakMem.AllocLabel → WeakMem.AllocLabel) (P : List Word), P.length = B.pay.length →
          η₂.box (g x.label) = some { B with pay := P } →
          ((η₂.seen (g x.label) ∧ ∃ f, η₂.pfr (g x.label) = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ [rl g w0], B.fr ≤ w.view) →
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VRR ρ η₂ a (vsh s (shp Ra)) [rl g w0] (Res.sw τ X)) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) P = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VRR ρ η₂.unsee a (shp Ra) q (Res.sw τ X))) →
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VRR ρ η₂ b (vsh (s + (armsOf Ra).length) (shp Rb)) [rl g w0] (Res.sw τ X)) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) P = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VRR ρ η₂.unsee b (shp Rb) q (Res.sw τ X))) →
          ((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x' s' B', [rl g w0].map (·.val) = [.loc x' 0] ∧ x'.offset = 0 ∧
            η₂.box x'.label = some B' ∧ some (s + 1) = some (s' + 1) ∧
            (s' ≤ B'.tag ∧ ((armsOf (.sum Ra Rb))[B'.tag - s']?).bind wc = some B'.pay.length) ∧
            ((η₂.seen x'.label ∧ ∃ f, η₂.pfr x'.label = some f ∧ B'.fr ≤ f) ∨ ∀ w ∈ [rl g w0], B'.fr ≤ w.view) ∧
            (B'.tag - s' < (armsOf Ra).length →
              (isBoxed Ra = true → VRR ρ η₂ a (vsh s' (shp Ra)) [rl g w0] (Res.sw τ X)) ∧
              (isBoxed Ra = false → ∃ q, ofArm Ra (B'.tag - s') B'.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
                Valid Ra q ∧ VRR ρ η₂.unsee a (shp Ra) q (Res.sw τ X))) ∧
            ((armsOf Ra).length ≤ B'.tag - s' →
              (isBoxed Rb = true → VRR ρ η₂ b (vsh (s' + (armsOf Ra).length) (shp Rb)) [rl g w0] (Res.sw τ X)) ∧
              (isBoxed Rb = false → ∃ q, ofArm Rb (B'.tag - s' - (armsOf Ra).length) B'.pay = some q ∧
                ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VRR ρ η₂.unsee b (shp Rb) q (Res.sw τ X)))) := by
        intro g P hP hb hptr hA' hB'
        exact ⟨htier, ⟨g x.label, x.offset⟩, s, { B with pay := P }, vals_rl_loc (ws := [w0]) h1, h2, hb, rfl,
          ⟨h5.1, by rw [hP]; exact h5.2⟩, hptr, hA', hB'⟩
      by_cases hl : B.tag - s < (armsOf Ra).length
      · by_cases hbx : isBoxed Ra = true
        · -- arm boxed: the IH reads the same pointer at the arm
          have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              gc cpy σ Cp bv T TU E a (vsh s (shp Ra)) [w0] := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbx]
          have ih1 := iha T TU ρ η₁ η₂ E _ [w0] X hm hci hE hRL hT hTU hTx hTUx hTd hTUd ((hA hl).1 hbx)
          rw [rlI_one] at ih1; rw [hG, rlI_one]
          obtain ⟨P, hP, hb, hptr⟩ := boxptr_lift hm hE h3 h6 (gc0 (TU := TU) hTx a _ hw0)
          exact Or.inl (pack _ P hP hb hptr (fun _ => ⟨fun _ => ih1, fun e => absurd hbx (by rw [e]; simp)⟩)
            (fun h' => absurd hl (by omega)))
        · -- arm unboxed: the pointer goes to the variant
          have hbf : isBoxed Ra = false := by simpa using hbx
          obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hbf
          have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              fun _ y => bv y (PCode.enc σ cpy bv (shIA Ra (gc cpy σ Cp bv TU TU E.unsee a (shp Ra) q))
                B.pay.length) := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbf, q1, Bool.false_eq_true, if_false]
          rw [hG, rlI_one]
          have hxq := gc_ExS (cpy := cpy) (σ := σ) (Cp := Cp) (bv := bv) a TU TU E.unsee (shp Ra) q hTUx
          refine Or.inl (pack _ _ (rlI_length _ _) (hm.vbox _ _ _ h3)
            (h6.imp (fun ⟨hs, f, hf, hle⟩ => ⟨hm.vseen _ _ hs, f, hm.vpfr _ _ _ hf, hle⟩)
              (fun hv => rlI_views (fun _ => fun y => bv y _) (ws := [w0]) hv))
            (fun _ => ⟨fun e => absurd e (by rw [hbf]; simp), fun _ => ⟨_, ofArm_variant hxq q1, ShapeC_rlI q2, q3,
              Valid_rlI _ _ _ q4,
              iha TU TU ρ η₁.unsee η₂.unsee E.unsee (shp Ra) q X hm.unsee hci.unsee hE.unsee (RLink_unsee hRL) hTU hTU hTUx hTUx hTUd hTUd q5⟩⟩)
            (fun h' => absurd hl (by omega)))
      · have hl' : (armsOf Ra).length ≤ B.tag - s := Nat.le_of_not_lt hl
        by_cases hbx : isBoxed Rb = true
        · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              gc cpy σ Cp bv T TU E b (vsh (s + (armsOf Ra).length) (shp Rb)) [w0] := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbx, if_false]
          have ih1 := ihb T TU ρ η₁ η₂ E _ [w0] X hm hci hE hRL hT hTU hTx hTUx hTd hTUd ((hB hl').1 hbx)
          rw [rlI_one] at ih1; rw [hG, rlI_one]
          obtain ⟨P, hP, hb, hptr⟩ := boxptr_lift hm hE h3 h6 (gc0 (TU := TU) hTx b _ hw0)
          exact Or.inl (pack _ P hP hb hptr (fun h' => absurd h' hl)
            (fun _ => ⟨fun _ => ih1, fun e => absurd hbx (by rw [e]; simp)⟩))
        · have hbf : isBoxed Rb = false := by simpa using hbx
          obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl').2 hbf
          have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              fun _ y => bv y (PCode.enc σ cpy bv (shIA Rb (gc cpy σ Cp bv TU TU E.unsee b (shp Rb) q))
                B.pay.length) := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbf, q1, Bool.false_eq_true, if_false]
          rw [hG, rlI_one]
          have hxq := gc_ExS (cpy := cpy) (σ := σ) (Cp := Cp) (bv := bv) b TU TU E.unsee (shp Rb) q hTUx
          refine Or.inl (pack _ _ (rlI_length _ _) (hm.vbox _ _ _ h3)
            (h6.imp (fun ⟨hs, f, hf, hle⟩ => ⟨hm.vseen _ _ hs, f, hm.vpfr _ _ _ hf, hle⟩)
              (fun hv => rlI_views (fun _ => fun y => bv y _) (ws := [w0]) hv))
            (fun h' => absurd h' hl)
            (fun _ => ⟨fun e => absurd e (by rw [hbf]; simp), fun _ => ⟨_, ofArm_variant hxq q1, ShapeC_rlI q2, q3,
              Valid_rlI _ _ _ q4,
              ihb TU TU ρ η₁.unsee η₂.unsee E.unsee (shp Rb) q X hm.unsee hci.unsee hE.unsee (RLink_unsee hRL) hTU hTU hTUx hTUx hTUd hTUd q5⟩⟩))
    · have ht : ¬ (Ty.sum Ra Rb).tier = .boxed := fun e => by rw [e] at hd; simp [decodeArm] at hd
      refine Or.inr ⟨j, rlI (shI (Ty.sum Ra Rb).tier (gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws)) p,
        by rw [decodeArm_rlI, hd]; rfl, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj
        refine ⟨_, by rw [ofArm_rlI, q1]; rfl, ?_⟩
        have key : rlI (unA Ra (shI (Ty.sum Ra Rb).tier (gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws))) q
            = rlI (gc cpy σ Cp bv T TU E a (shp Ra) q) q := by
          by_cases hp : p = []
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws = fun _ => σ := by
              simp only [gc, ht, if_false, hd, hp, if_true]
            rw [hG, unA_shI_cst]
            subst hp
            rw [rlI_noloc _ q (ofArm_nil_noloc q1), rlI_noloc _ q (ofArm_nil_noloc q1)]
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws =
                unI (Ty.sum Ra Rb).tier (shIA Ra (gc cpy σ Cp bv T TU E a (shp Ra) q)) := by
              simp only [gc, ht, if_false, hd, hp, hj, if_true, q1]
            rw [hG, shI_unI]
            exact rlI_congr _ _ q (unA_shIA_loc q1 _)
        rw [key]; exact iha T TU ρ η₁ η₂ E (shp Ra) q X hm hci hE hRL hT hTU hTx hTUx hTd hTUd q2
      · obtain ⟨q, q1, q2⟩ := hB hj
        refine ⟨_, by rw [ofArm_rlI, q1]; rfl, ?_⟩
        have hj' : ¬ j < (armsOf Ra).length := Nat.not_lt.mpr hj
        have key : rlI (unA Rb (shI (Ty.sum Ra Rb).tier (gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws))) q
            = rlI (gc cpy σ Cp bv T TU E b (shp Rb) q) q := by
          by_cases hp : p = []
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws = fun _ => σ := by
              simp only [gc, ht, if_false, hd, hp, if_true]
            rw [hG, unA_shI_cst]
            subst hp
            rw [rlI_noloc _ q (ofArm_nil_noloc q1), rlI_noloc _ q (ofArm_nil_noloc q1)]
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws =
                unI (Ty.sum Ra Rb).tier (shIA Rb (gc cpy σ Cp bv T TU E b (shp Rb) q)) := by
              simp only [gc, ht, if_false, hd, hp, hj', if_true, q1]
            rw [hG, shI_unI]
            exact rlI_congr _ _ q (unA_shIA_loc q1 _)
        rw [key]; exact ihb T TU ρ η₁ η₂ E (shp Rb) q X hm hci hE hRL hT hTU hTx hTUx hTd hTUd q2
  | tvar k =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    obtain ⟨ws', hw, hor⟩ := h; exact hT k rt ws' ws X hw hor
  | code sg tau e =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]
    obtain ⟨⟨i, d, h1, h2⟩, hX⟩ := h
    refine ⟨⟨i, d, vals_rl_num.2 h1, ?_⟩, by rw [hX]; rfl⟩
    rw [hm.prog, hm.wit]; exact h2
  | void => intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h
  | tex κ b ih =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; subst hrt; simp only [VRR, gc]
    exact ⟨n, rb, s, rfl, hc, hw, ih (shT σ T) (shT σ TU) ρ (η₁.push0 s) (η₂.push0 s) E rb ws X (hm.push0 s)
      (hci.push0 s) hE (RLink_push0 hRL s) (hT.push0 s) (hTU.push0 s) (ExS_shT hTx) (ExS_shT hTUx) (TDp.push0 hTd s) (TDp.push0 hTUd s) hv⟩
  | mu b ih =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [hm.wit]
    exact ih (shT σ T) (shT σ TU) ρ _ _ E rt ws X (hm.push0 _) (hci.push0 _) hE (RLink_push0 hRL _) (hT.push0 _) (hTU.push0 _)
      (ExS_shT hTx) (ExS_shT hTUx) (TDp.push0 hTd _) (TDp.push0 hTUd _) h
  | iall b ih =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    exact fun n => ih T TU (vcons n ρ) η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd (h n)
  | word r P =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]
    obtain ⟨⟨hp, hg⟩, hc⟩ := h
    refine ⟨⟨hp, fun e => ?_⟩, ?_⟩
    · obtain ⟨n, hn, hi⟩ := hg e; exact ⟨n, vals_rl_num.2 hn, hi⟩
    · rcases hc with ⟨hw, hX⟩ | ⟨hw, hX⟩
      · refine Or.inl ⟨WordHolds_rl.2 hw, ?_⟩
        rw [hX, Res.sw_noown (by intro l; simp [wdW]; split <;> simp)]
      · refine Or.inr ⟨fun h' => hw (WordHolds_rl.1 h'), ?_⟩
        rw [hX, Res.sw_noown (by intro l; simp [wdW]; split <;> simp)]
  | word2 r P =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]
    obtain ⟨⟨hp, n0, n1, hn, hi⟩, hc⟩ := h
    refine ⟨⟨hp, n0, n1, vals_rl_pair.2 hn, hi⟩, ?_⟩
    rcases hc with ⟨hw, hX⟩ | ⟨hw, hX⟩
    · exact Or.inl ⟨Word2Holds_rl.2 hw, by rw [hX, Res.sw_noown (by intro l; simp)]⟩
    · exact Or.inr ⟨fun h' => hw (Word2Holds_rl.1 h'), by rw [hX, Res.sw_noown (by intro l; simp)]⟩
  | epair e P =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR, gc]
    rw [rlI_cst]
    obtain ⟨⟨hp, n0, n1, hn⟩, hX⟩ := h
    exact ⟨⟨hp, n0, n1, vals_rl_pair.2 hn⟩, by rw [hX]; rfl⟩
  | tok r st =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR]
    rw [h, Res.sw_noown (by intro l; cases st <;> simp)]
  | ptr μ u _ =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR]
    obtain ⟨⟨a, c, h1, h2, h3, h4, hmo, h5⟩, hX⟩ := h
    rw [hX, gc_ptr]; exact ref_lift hm hE h1 h2 h3 h4 hmo h5
  | ptrOpt μ u _ =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR]
    obtain ⟨hc, hX⟩ := h
    rw [hX, gc_ptrOpt]
    rcases hc with hn | ⟨a, c, h1, h2, h3, h4, hmo, h5⟩
    · exact ⟨Or.inl (vals_rlI_null hn), ownW_null hn⟩
    · obtain ⟨h, hR⟩ := ref_lift hm hE h1 h2 h3 h4 hmo h5; exact ⟨Or.inr h, hR⟩
  | loc μ u _ =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h; simp only [VRRB] at h; simp only [VRR]
    obtain ⟨hc, hX⟩ := h
    rw [hX, gc_loc]
    rcases hc with ⟨hn, e, he⟩ | ⟨a, c, U, h1, h3, h4, h5, hmo, hI⟩
    · exact ⟨Or.inl ⟨vals_rlI_null hn, e, by rw [hm.wit]; exact he⟩, ownW_null hn⟩
    · obtain ⟨h, hR⟩ := loc_lift hm hci hE h1 h3 h4 h5 hmo hI; exact ⟨Or.inr h, hR⟩
  | _ =>
    intro T TU ρ η₁ η₂ E rt ws X hm hci hE hRL hT hTU hTx hTUx hTd hTUd h
    simp only [VRRB] at h; simp only [VRR]; rw [h]
    first | rfl | exact Res.sw_noown (by intro l; simp)

end

/-! T2 ((b′)): at a tid box the ♭ env has `pfr = some 0` (TidBox: `sto l = some ⟨unit, none⟩ ∧ pfr l = some 0`),
so the tid word is fresh, never exempt, and `gc` does not redirect it to the copy. -/
theorem tidBox_fresh {η : TEnv} {ws : List Word} {l : WeakMem.AllocLabel}
    (h1 : ws.map (·.val) = [.loc ⟨l, 0⟩ 0]) (hp : η.pfr l = some 0) : FreshW η ws := by
  intro a ha
  rw [h1] at ha
  have e := (List.cons.inj ha).1
  injection e with e1
  rw [← e1]
  exact ⟨0, hp, Or.inr fun w _ => Nat.zero_le _⟩

theorem tidBox_noexm (Cp : WeakMem.AllocLabel → Prop) {η : TEnv} {ws : List Word} {l : WeakMem.AllocLabel}
    (h1 : ws.map (·.val) = [.loc ⟨l, 0⟩ 0]) (hp : η.pfr l = some 0) : ¬ exmW Cp η ws :=
  fun ⟨_, _, _, hnF⟩ => hnF (tidBox_fresh h1 hp)

theorem tidBox_gc (cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel) (Cp : WeakMem.AllocLabel → Prop)
    (bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel)
    (T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) {η : TEnv} (rt : Shp)
    {ws : List Word} {l : WeakMem.AllocLabel}
    (h1 : ws.map (·.val) = [.loc ⟨l, 0⟩ 0]) (hp : η.pfr l = some 0) :
    gc cpy σ Cp bv T TU η .tid rt ws = fun _ => σ := by
  simp only [gc]; exact pubG_of_nexm (tidBox_noexm Cp h1 hp)

/-- A tid box (`sto l = ⟨.unit, none⟩`) is unowned, so `cown` never fires at a tid *box*; owned unit cells
(the ungated owner disjunct) may reach `cown`, and are handled at the tid arms of `VRR_lift`/`VR_lift`. -/
theorem tidBox_unowned {η : TEnv} {l : WeakMem.AllocLabel} {c : Cell} (hs : η.sto l = some ⟨.unit, none⟩)
    (hc : η.sto l = some c) : c.owner ≠ some η.tid := by
  rw [hs] at hc; cases hc; simp

end TermSound.Flat
