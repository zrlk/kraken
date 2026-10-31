import WeakCore.Head
import WeakCore.VRzLemmas
import WeakCore.PubPosL
/-! Route (D), hand layer (counted as hand lines): flag monotonicity for ModeOKb / VRz / VRb2 (Z'''). -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

theorem VRz_flag (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (bk bk' : Prop) (rt : Shp) (ws : List Word),
    (bk → bk') → VRz ρ η bk t rt ws → VRz ρ η bk' t rt ws := by
  induction t with
  | tid => intro ρ η bk bk' rt ws _ h; exact h
  | refine t ψ ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    exact ⟨ih _ _ _ _ _ _ hb h.1, h.2⟩
  | iex b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ _ hb hv⟩
  | ptr μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    obtain ⟨a, c, h1, h2, h3, h4, hm, h5⟩ := h; exact ⟨a, c, h1, h2, h3, h4, ModeOKb_flag (Or.imp_left hb) hm, h5⟩
  | ptrOpt μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    rcases h with h | ⟨a, c, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, h1, h2, h3, h4, ModeOKb_flag (Or.imp_left hb) hm, h5⟩
  | loc μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    rcases h with h | ⟨a, c, U, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, U, h1, h2, h3, h4, ModeOKb_flag (Or.imp_left hb) hm, h5⟩
  | tex κ b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ _ hb hv⟩
  | mu b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    exact ih _ _ _ _ _ _ hb h
  | iall b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRz] at h ⊢
    exact fun n => ih _ _ _ _ _ _ hb (h n)
  | _ => intro ρ η bk bk' rt ws _ h; exact h


/-! F1: `TEnv.pubTop` lemmas (copies of W's `TEnv.ownTop_*` proofs, `ownHead` ↦ `pubHead`). -/
theorem TEnv.pubTop_congr {η₁ η₂ : TEnv} (hw : η₁.wit = η₂.wit) (t : Ty) : η₁.pubTop t = η₂.pubTop t := by
  cases t <;> simp [TEnv.pubTop, hw]

theorem TEnv.pubTop_agree {η₁ η₂ : TEnv} (t : Ty) (hw : ∀ j, t.tyMentions j = true → η₁.wit j = η₂.wit j) :
    η₁.pubTop t = η₂.pubTop t := by
  cases t with
  | tvar k => simp [TEnv.pubTop, hw k (by simp [Ty.tyMentions])]
  | _ => rfl

theorem TEnv.pubTop_shiftI (η : TEnv) (c : Nat) (t : Ty) : η.pubTop (t.shiftI c) = η.pubTop t := by
  cases t with
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.pubTop_tyEq (η : TEnv) {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) : η.pubTop t = η.pubTop u := by
  cases h with
  | ptr hm _ => cases hm <;> rfl
  | ptrOpt hm _ => cases hm <;> rfl
  | loc hm _ => cases hm <;> rfl
  | _ => rfl

theorem TEnv.pubTop_of_Clo (η : TEnv) {s : Ty} (h : Clo s) : η.pubTop s = s.pubHead := by
  cases s with
  | tvar k => exact absurd h.1 (by simp [tb])
  | _ => rfl

theorem TEnv.pubTop_shiftT_insR (η : TEnv) (c : Nat) {R : Shp → List Word → Prop} {s : Ty}
    {UR : Shp → List Word → Prop} {RR URR : Shp → List Word → Res → Prop} (t : Ty) :
    (η.insR c R s UR RR URR).pubTop (t.shiftT c) = η.pubTop t := by
  cases t with
  | tvar k =>
      by_cases h : k ≥ c
      · have h1 : ¬ k + 1 < c := by omega
        have h2 : k + 1 ≠ c := by omega
        simp [Ty.shiftT, h, TEnv.pubTop, TEnv.insR, h1, h2]
      · have h1 : k < c := by omega
        simp [Ty.shiftT, h, TEnv.pubTop, TEnv.insR, h1]
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.pubTop_cl {η : TEnv} (hw : ∀ k, Clo (η.wit k)) (X : TEnv) (ρ₀ : Nat → Nat) (P : List Ty)
    (d : Nat) (t : Ty) : (TEnv.pre P X).pubTop (cl ρ₀ η.wit P.length d t) = (TEnv.pre P η).pubTop t := by
  cases t with
  | tvar k =>
      by_cases h : k < P.length
      · simp only [cl, h, ↓reduceIte]; exact congrArg Ty.pubHead (pre_wit_lt X η P k h)
      · simp only [cl, h, ↓reduceIte]
        rw [TEnv.pubTop_of_Clo _ (hw _)]
        exact (congrArg Ty.pubHead (pre_wit_ge η P k (by omega))).symm
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem CE_pre (X : TEnv) : ∀ (Q : List Ty), CE (TEnv.pre Q X) = CE X
  | [] => rfl
  | _ :: Q => CE_pre X Q

theorem pre_rc (X : TEnv) (Q : List Ty) : (TEnv.pre Q X).rc = X.rc := by
  funext l; show min _ _ = min _ _; rw [pre_ini, pre_rini]

theorem CE_rc (X : TEnv) : (CE X).rc = X.rc := rfl

theorem VRb2_flag (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (bk bk' : Prop) (rt : Shp) (ws : List Word),
    (bk → bk') → VRb2 ρ η bk t rt ws → VRb2 ρ η bk' t rt ws := by
  induction t with
  | tid => intro ρ η bk bk' rt ws _ h; exact h
  | refine t ψ ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    exact ⟨ih _ _ _ _ _ _ hb h.1, h.2⟩
  | iex b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ _ hb hv⟩
  | ptr μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    obtain ⟨a, c, h1, h2, h3, h4, hm, h5⟩ := h; exact ⟨a, c, h1, h2, h3, h4, ModeOKb_flag (Or.imp_left hb) hm, h5⟩
  | ptrOpt μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    rcases h with h | ⟨a, c, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, h1, h2, h3, h4, ModeOKb_flag (Or.imp_left hb) hm, h5⟩
  | loc μ u _ =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    rcases h with h | ⟨a, c, U, h1, h2, h3, h4, hm, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, c, U, h1, h2, h3, h4, ModeOKb_flag (Or.imp_left hb) hm, h5⟩
  | tex κ b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ _ hb hv⟩
  | mu b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    exact ih _ _ _ _ _ _ hb h
  | iall b ih =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    exact fun n => ih _ _ _ _ _ _ hb (h n)
  | tvar k =>
    intro ρ η bk bk' rt ws hb h; simp only [VRb2] at h ⊢
    obtain ⟨ws', h1, h2⟩ := h; exact ⟨ws', h1, h2.imp id (fun h => ⟨VRz_flag _ _ _ _ _ _ _ hb h.1, h.2⟩)⟩
  | _ => intro ρ η bk bk' rt ws _ h; exact h

/-- `IniRc` reads the words only through their values. -/
theorem IniRc_vals {ρ : Nat → Nat} {rc : WeakMem.AllocLabel → Nat} (ψ : Pred) :
    ∀ {ws ws' : List Word}, ws.map (·.val) = ws'.map (·.val) → IniRc ρ rc ψ ws → IniRc ρ rc ψ ws' := by
  induction ψ with
  | ini k => intro ws ws' e h; obtain ⟨a, h1, h2⟩ := h; exact ⟨a, e.symm.trans h1, h2⟩
  | and p q ihp ihq => intro ws ws' e h; exact h.imp (ihp e) (ihq e)
  | _ => intro ws ws' e h; simp only [IniRc] at h

theorem VRF_flag {bk bk' : Prop} (hb : bk → bk') {ρ η t rt ws} (h : VRF bk ρ η t rt ws) : VRF bk' ρ η t rt ws :=
  VRb2_flag t ρ η bk bk' rt ws hb h
theorem VRF_ofFalse {bk : Prop} {ρ η t rt ws} (h : VRF False ρ η t rt ws) : VRF bk ρ η t rt ws :=
  VRF_flag False.elim h
theorem ModeOKF_ofFalse {bk : Prop} {i P S μ l c ws} (h : ModeOKF False i P S μ l c ws) : ModeOKF bk i P S μ l c ws :=
  ModeOKb_flag False.elim h

/- Z″ note: "ModeOK ⇒ fresh" holds for W's VR (VR_pubFresh) but NOT for VRb2 at `.loc .pub`:
the `.loc` arm's IniAt exemption admits stale words (e.g. the whole-buffer locative). -/

/-- Z″ (c): a stale-or-fresh pub buffer value carries the rc backing its slots need:
fresh, or `ev k ≤ rc` at the buffer's label (so `j < k` gives `j < rc`, i.e. `IniAt rc` at slot j). -/
theorem buf_rc {ρ : Nat → Nat} {η : TEnv} {bk : Prop} {n : Idx} {u : Ty} {k : Idx} {rt : Shp} {ws : List Word}
    (h : VRb2 ρ η bk (.refine (.loc .pub (.array n u)) (.ini k)) rt ws) :
    FreshW η ws ∨ ∀ a : WeakMem.Address, ws.map (·.val) = [.loc a 0] → ev ρ k ≤ η.rc a.label := by
  simp only [VRb2] at h
  rcases h.2.2 ⟨η.box, fun _ _ h => h, rfl⟩ with hf | hr
  · exact Or.inl hf
  · exact Or.inr (by simpa [IniR] using hr)

/-! Z″ conjunct transports. -/
theorem RcC_wle {ρ : Nat → Nat} {η : TEnv} {b : Bool} {ψ : Pred} {ws ws' : List Word} (e : WLe ws ws')
    (h : b = true → FreshW η ws ∨ IniR ρ η.rc ψ ws) :
    b = true → FreshW η ws' ∨ IniR ρ η.rc ψ ws' :=
  fun hp => (h hp).imp (FreshW_wle e) (IniR_vals e.vals ψ)

theorem RcCE_wle {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ψ : Pred} {ws ws' : List Word} (e : WLe ws ws')
    (h : PubPosE η t rt ws → FreshW η ws ∨ IniR ρ η.rc ψ ws) :
    PubPosE η t rt ws' → FreshW η ws' ∨ IniR ρ η.rc ψ ws' :=
  fun hp => (h (PubPosE_vals e.vals hp)).imp (FreshW_wle e) (IniR_vals e.vals ψ)


/-! (P3) `PubPosE` twins of the `TEnv.pubTop` lemmas (via the generic `pp` lemmas
of PubPosL). -/
theorem PubPosE_congrB {η₁ η₂ : TEnv} {t₁ t₂ : Ty} {rt : Shp} {ws : List Word} (hb : η₁.box = η₂.box)
    (h : ∀ bx, pp (PTopB bx η₁) bx t₁ rt ws = pp (PTopB bx η₂) bx t₂ rt ws) :
    PubPosE η₁ t₁ rt ws ↔ PubPosE η₂ t₂ rt ws := by
  constructor
  · rintro ⟨bx, hx, hp⟩
    exact ⟨bx, fun l B h' => hx l B (by rw [hb]; exact h'), by rw [← h bx]; exact hp⟩
  · rintro ⟨bx, hx, hp⟩
    exact ⟨bx, fun l B h' => hx l B (by rw [← hb]; exact h'), by rw [h bx]; exact hp⟩

theorem PubPosE_wit {η₁ η₂ : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (hw : η₁.wit = η₂.wit)
    (hb : η₁.box = η₂.box) : PubPosE η₁ t rt ws ↔ PubPosE η₂ t rt ws :=
  PubPosE_congrB hb (fun bx => by unfold PTopB; rw [hw])

theorem PubPosE_shiftI {η : TEnv} {c : Nat} {t : Ty} {rt : Shp} {ws : List Word} :
    PubPosE η (t.shiftI c) rt ws ↔ PubPosE η t rt ws :=
  PubPosE_congrB rfl (fun bx => pp_shiftI bx t c _ rt ws)

theorem PubPosE_instT {η : TEnv} {us : List Idx} {d : Nat} {t : Ty} {rt : Shp} {ws : List Word} :
    PubPosE η (instT us d t) rt ws ↔ PubPosE η t rt ws :=
  PubPosE_congrB rfl (fun bx => pp_instT bx us t d _ rt ws)

theorem PubPosE_tyEq {η : TEnv} {cx : Cx} {d : Nat} {t u : Ty} {rt : Shp} {ws : List Word} (h : TyEqS cx d t u) :
    PubPosE η t rt ws ↔ PubPosE η u rt ws :=
  PubPosE_congrB rfl (fun bx => pp_tyEq bx h _ rt ws)

theorem PubPosE_agree {η₁ η₂ : TEnv} {t : Ty} {rt : Shp} {ws : List Word} (hb : η₁.box = η₂.box)
    (hw : ∀ j, t.tyMentions j = true → η₁.wit j = η₂.wit j) : PubPosE η₁ t rt ws ↔ PubPosE η₂ t rt ws :=
  PubPosE_congrB hb (fun bx => pp_agree bx t _ _ rt ws (fun k hk => by unfold PTopB; rw [hw k hk]))

theorem PubPosE_shiftT_insR {η : TEnv} {c : Nat} {R : Shp → List Word → Prop} {s : Ty}
    {UR : Shp → List Word → Prop} {RR URR : Shp → List Word → Res → Prop} {t : Ty} {rt : Shp} {ws : List Word} :
    PubPosE (η.insR c R s UR RR URR) (t.shiftT c) rt ws ↔ PubPosE η t rt ws := by
  refine PubPosE_congrB rfl (fun bx => ?_)
  rw [pp_shiftT]
  congr 1
  funext k rt' ws' i
  by_cases h : k < c
  · simp [PTopB, TEnv.insR, h]
  · simp [PTopB, TEnv.insR, h, show ¬ k + 1 < c by omega, show k + 1 ≠ c by omega]

theorem PubPosE_cl {η : TEnv} (hw : ∀ k, Clo (η.wit k)) {X : TEnv} (hX : X.box = η.box) (ρ₀ : Nat → Nat)
    (P : List Ty) (d : Nat) (t : Ty) {rt : Shp} {ws : List Word} :
    PubPosE (TEnv.pre P X) (cl ρ₀ η.wit P.length d t) rt ws ↔ PubPosE (TEnv.pre P η) t rt ws := by
  refine PubPosE_congrB (by rw [pre_box, pre_box, hX]) (fun bx => ?_)
  rw [pp_cl bx ρ₀ η.wit (fun j => (hw j).1)]
  congr 1
  funext k rt' ws' i
  by_cases h : k < P.length
  · simp only [ClO, h, if_true, PTopB]; rw [pre_wit_lt X η P k h]
  · simp only [ClO, h, if_false, PTopB]; rw [pre_wit_ge η P k (by omega)]

/-- `PubPosE` at a closed pub-reference head (the concrete-type `TEnv.pubTop` simp sites). -/
theorem PubPosE_head {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word}
    (h : pp (PTopB η.box η) η.box t rt ws 0 = true) : PubPosE η t rt ws := ⟨η.box, fun _ _ h => h, h⟩


/-- `pp` is invariant under the box-pointer renaming of `VRRz_ren0` (tags shifted in step with
the runtime-sum offsets; boxed runtime heads only). -/
theorem pp_ren {w1 w2 : Word} {x1 x2 : WeakMem.Address} {B1 B2 : Box} (h1 : w1.val = .loc x1 0)
    (h2 : w2.val = .loc x2 0) (bx : WeakMem.AllocLabel → Option Box) (hb1 : bx x1.label = some B1)
    (hb2 : bx x2.label = some B2) (t : Ty) :
    ∀ (PT : Nat → Shp → List Word → Nat → Bool) (R : Shp) (s1 s2 : Nat),
    (∀ k R s1 s2, B1.tag + s2 = B2.tag + s1 → bh R → PT k (vsh s2 R) [w2] = PT k (vsh s1 R) [w1]) →
    B1.tag + s2 = B2.tag + s1 → bh R → pp PT bx t (vsh s2 R) [w2] = pp PT bx t (vsh s1 R) [w1] := by
  induction t with
  | tvar k => intro PT R s1 s2 hPT ht hR; simp only [pp]; exact hPT k R s1 s2 ht hR
  | ptr μ u _ => intro PT R s1 s2 _ _ _; cases μ <;> rfl
  | ptrOpt μ u _ => intro PT R s1 s2 _ _ _; cases μ <;> rfl
  | loc μ u _ => intro PT R s1 s2 _ _ _; cases μ <;> rfl
  | refine t ψ ih => intro PT R s1 s2 hPT ht hR; simp only [pp]; exact ih PT R s1 s2 hPT ht hR
  | iall t ih => intro PT R s1 s2 hPT ht hR; simp only [pp]; exact ih PT R s1 s2 hPT ht hR
  | mu t ih =>
    intro PT R s1 s2 hPT ht hR; simp only [pp]
    refine ih (shPT PT) R s1 s2 (fun k R' s1' s2' ht' hR' => ?_) ht hR
    cases k with
    | zero => rfl
    | succ k => exact hPT k R' s1' s2' ht' hR'
  | iex t ih =>
    intro PT R s1 s2 hPT ht hR
    cases R with
    | iex n R' => simp only [vsh, pp]; exact ih PT R' s1 s2 hPT ht hR
    | _ => simp [vsh, pp]
  | tex κ t ih =>
    intro PT R s1 s2 hPT ht hR
    cases R with
    | tex n R' =>
      simp only [vsh, pp]
      refine ih (shPT PT) R' s1 s2 (fun k R'' s1' s2' ht' hR' => ?_) ht hR
      cases k with
      | zero => rfl
      | succ k => exact hPT k R'' s1' s2' ht' hR'
    | _ => simp [vsh, pp]
  | prod a b _ _ =>
    intro PT R s1 s2 _ _ hR
    cases R with
    | prod a' b' => exact absurd hR (by simp [bh])
    | _ => simp [vsh, pp]
  | sum a b iha ihb =>
    intro PT R s1 s2 hPT ht hR
    cases R with
    | sum n0 R0 =>
      cases R0 with
      | sum Ra Rb =>
        have htb : (Ty.sum Ra Rb).tier = .boxed := hR
        simp only [vsh, pp, htb, if_true, List.map_cons, List.map_nil, h1, h2, hb1, hb2]
        rw [show B2.tag - s2 = B1.tag - s1 by omega]
        by_cases hlt : B1.tag - s1 < (armsOf Ra).length
        · simp only [hlt, if_true]
          by_cases hbr : isBoxed Ra = true
          · simp only [hbr, if_true]; exact iha PT (shp Ra) s1 s2 hPT ht (bh_shp Ra hbr)
          · simp only [hbr]; rfl
        · simp only [hlt, if_false]
          by_cases hbr : isBoxed Rb = true
          · simp only [hbr, if_true]
            exact ihb PT (shp Rb) (s1 + (armsOf Ra).length) (s2 + (armsOf Ra).length) hPT (by omega) (bh_shp Rb hbr)
          · simp only [hbr]; rfl
      | _ => simp [vsh, pp]
    | _ => simp [vsh, pp]
  | _ => intro PT R s1 s2 _ _ _; rfl

theorem PubPosE_ren {η : TEnv} {t : Ty} {w1 w2 : Word} {x1 x2 : WeakMem.Address} {B1 B2 : Box} {R : Shp}
    {s1 s2 : Nat} (h1 : w1.val = .loc x1 0) (h2 : w2.val = .loc x2 0) (hb1 : η.box x1.label = some B1)
    (hb2 : η.box x2.label = some B2) (ht : B1.tag + s2 = B2.tag + s1) (hR : bh R)
    (hp : PubPosE η t (vsh s2 R) [w2]) :
    ∃ bx, (∀ l B, η.box l = some B → bx l = some B) ∧ pp (PTopB bx η) bx t (vsh s1 R) [w1] 0 = true := by
  obtain ⟨bx, hbx, hq⟩ := hp
  refine ⟨bx, hbx, ?_⟩
  rw [← pp_ren h1 h2 bx (hbx _ _ hb1) (hbx _ _ hb2) t (PTopB bx η) R s1 s2 (fun k R' s1' s2' ht' hR' => ?_) ht hR]
  · exact hq
  · funext i
    exact congrFun (pp_ren h1 h2 bx (hbx _ _ hb1) (hbx _ _ hb2) (η.wit k) _ R' s1' s2'
      (fun _ _ _ _ _ _ => rfl) ht' hR') i

theorem pubHead_shiftI (c : Nat) (t : Ty) : (t.shiftI c).pubHead = t.pubHead := by
  cases t <;> simp only [Ty.shiftI, Ty.pubHead] <;> rename_i μ _ <;> cases μ <;> rfl

theorem pubHead_tyEq {cx : CoreTerm.Cx} {d : Nat} {t u : Ty} (h : CoreTyping.TyEqS cx d t u) :
    t.pubHead = u.pubHead := by
  induction h <;> (try cases ‹CoreTyping.MEq _ _ _ _›) <;> simp_all [Ty.pubHead]

theorem pubHead_shiftT (c : Nat) (t : Ty) : (t.shiftT c).pubHead = t.pubHead := by
  cases t <;> simp only [Ty.shiftT] <;> first | rfl | (split <;> rfl) | (rename_i μ _; cases μ <;> rfl)

theorem rc_insR (c : Nat) (R : Shp → List Word → Prop) (s : Ty) (η : TEnv) (UR : Shp → List Word → Prop) :
    (TEnv.insR c R s η UR).rc = η.rc := rfl

theorem FreshW_insR (c : Nat) (R : Shp → List Word → Prop) (s : Ty) (η : TEnv) (UR : Shp → List Word → Prop)
    (ws : List Word) : FreshW (TEnv.insR c R s η UR) ws ↔ FreshW η ws := Iff.rfl

theorem CE_insR (c : Nat) (R : Shp → List Word → Prop) (s : Ty) (η : TEnv) (UR : Shp → List Word → Prop) :
    CE (TEnv.insR c R s η UR) = CE η := rfl

theorem FreshW_CE {η₁ η₂ : TEnv} (h : CE η₁ = CE η₂) (ws : List Word) : FreshW η₁ ws ↔ FreshW η₂ ws := by
  have e1 : η₁.pfr = η₂.pfr := by have h' := congrArg TEnv.pfr h; exact h'
  have e2 : η₁.seen = η₂.seen := by have h' := congrArg TEnv.seen h; exact h'
  simp only [FreshW, e1, e2]

theorem rc_CE {η₁ η₂ : TEnv} (h : CE η₁ = CE η₂) : η₁.rc = η₂.rc := by
  have e1 : η₁.ini = η₂.ini := by have h' := congrArg TEnv.ini h; exact h'
  have e2 : η₁.rini = η₂.rini := by have h' := congrArg TEnv.rini h; exact h'
  funext l; show min (η₁.ini l) (η₁.rini l) = min (η₂.ini l) (η₂.rini l); rw [e1, e2]

theorem ModeOKb_monoP {bk : Prop} {i : Nat} {P P' : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S S' : WeakMem.AllocLabel → Prop} (hP : ∀ l f, P l = some f → P' l = some f) (hS : ∀ l, S l → S' l)
    {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws : List Word} :
    ModeOKb i P S bk μ l c ws → ModeOKb i P' S' bk μ l c ws := by
  cases μ with
  | own => exact id
  | pub =>
    rintro ⟨f, h1, h2 | h2 | h2⟩
    · exact ⟨f, hP l f h1, Or.inl (hS l h2)⟩
    · exact ⟨f, hP l f h1, Or.inr (Or.inl h2)⟩
    · exact ⟨f, hP l f h1, Or.inr (Or.inr h2)⟩
  | rgn _ => exact id

theorem IniRc_monoR {ρ : Nat → Nat} {rc rc' : WeakMem.AllocLabel → Nat} (hr : ∀ l, rc l ≤ rc' l) (ψ : Pred) :
    ∀ ws, IniRc ρ rc ψ ws → IniRc ρ rc' ψ ws := by
  induction ψ with
  | ini k => intro ws h; obtain ⟨a, h1, h2⟩ := h; exact ⟨a, h1, Nat.le_trans h2 (hr _)⟩
  | and p q ihp ihq => intro ws h; exact h.imp (ihp ws) (ihq ws)
  | _ => intro ws h; simp only [IniRc] at h

theorem FreshW_mono {η₁ η₂ : TEnv} (hP : ∀ l f, η₁.pfr l = some f → η₂.pfr l = some f)
    (hS : ∀ l, η₁.seen l → η₂.seen l) {ws : List Word} (h : FreshW η₁ ws) : FreshW η₂ ws := by
  intro a ha; obtain ⟨f, h1, h2⟩ := h a ha; exact ⟨f, hP _ _ h1, h2.imp_left (hS _)⟩

/-- Monotonicity of the original `VRz` (needed by the `.tvar` arm of `VR_mono`); port of W `VR_mono`. -/
theorem VRz_mono : ∀ (t : Ty) (bk : Prop) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) → η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l) → (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    (∀ l, η₁.rini l ≤ η₂.rini l) → VRz ρ η₁ bk t rt ws → VRz ρ η₂ bk t rt ws
  | .tvar k, bk, η₁, η₂, ρ, rt, ws, hr, hur, _, _, _, _, _, hP, hS, hBx, hri, hv => by
      simp only [VRz, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      exact ⟨VRz_mono t _ η₁ η₂ ρ rt ws hr hur hw hp ht hs hi hP hS hBx hri hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2.1,
        fun hq => (hv.2.2 (PubPosE_mono hw hBx hq)).imp (FreshW_mono hP hS) (IniR_mono (TEnv.rc_mono hi hri))⟩
  | .iex b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VRz_mono b _ η₁ η₂ (vcons w ρ) rb ws hr hur hw hp ht hs hi hP hS hBx hri h2⟩
  | .prod a b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VRz_mono a _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hri e2, VRz_mono b _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hri e3⟩
  | .sum a b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, hm.imp (fun ⟨h1, f, h2, h3⟩ => ⟨hS _ h1, f, hP _ _ h2, h3⟩) id,
          fun hj => ⟨fun e => VRz_mono a _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hri ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => VRz_mono b _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hri ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRz_mono a _ η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hri hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRz_mono b _ η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hri hv⟩
      · refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, VRz_mono a _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hri hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj; exact ⟨q, hq, VRz_mono b _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hri hv⟩
  | .code a b _, bk, η₁, η₂, ρ, rt, ws, _, _, hw, hp, _, _, _, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VRz_mono b _ (η₁.push0 s) (η₂.push0 s) ρ rb ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hri h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, bk, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOKb_monoP hP hS h5, h6⟩
  | .ptrOpt μ u, bk, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn
      · exact Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOKb_monoP hP hS h5, h6⟩
  | .loc μ u, bk, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn.1, hw ▸ hn.2⟩
      · exact Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOKb_flag (fun h => h.imp id (IniAt_mono (TEnv.rc_mono hi hri))) (ModeOKb_monoP hP hS h5),
          IniAt_mono (modeIni_le hi hri μ) h6⟩
  | .intS _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simpa only [VRz] using hv
  | .int, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simpa only [VRz] using hv
  | .opq _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRz] at hv ⊢; exact hv
  | .tid, bk, _, _, _, _, _, _, _, _, _, ht, hs, _, hP, hS, _, _, hv => by
        simp only [VRz] at hv ⊢
        obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
        exact ⟨l, c, h1, hs _ _ h2, h3, ht ▸ ModeOKb_monoP hP hS h5⟩
  | .fix _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simpa only [VRz] using hv
  | .lanes _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simpa only [VRz] using hv
  | .unit, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, _ => by simp [VRz]
  | .void, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simp [VRz] at hv
  | .array _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, _ => by simp [VRz]
  | .share _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, _ => by simp [VRz]
  | .cap _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, _ => by simp [VRz]
  | .word _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simpa only [VRz] using hv
  | .tok _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, _ => by simp [VRz]
  | .word2 _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simpa only [VRz] using hv
  | .tok2 _ _ _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, _ => by simp [VRz]
  | .epair _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, hv => by simpa only [VRz] using hv
  | .tokE _ _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hri, _ => by simp [VRz]
  | .mu b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      rw [← hw]
      refine VRz_mono b _ (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hri hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hri, hv => by
      simp only [VRz] at hv ⊢
      exact fun n => VRz_mono b _ η₁ η₂ (vcons n ρ) rt ws hr hur hw hp ht hs hi hP hS hBx hri (hv n)

theorem ModeOKb_unseeP {bkG : Prop} {i : Nat} {P P' : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S S' : WeakMem.AllocLabel → Prop} {V : WeakMem.Ts}
    (hP : ∀ l f, P l = some f → P' l = some f)
    (hS : ∀ l, S l → S' l ∨ ∃ f, P l = some f ∧ f ≤ V)
    {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws : List Word} {a : WeakMem.Address}
    (hw : ws.map (·.val) = [.loc a 0]) (hL : LocAbove V ws) :
    ModeOKb i P S bkG μ l c ws → ModeOKb i P' S' bkG μ l c ws := by
  cases μ with
  | own => exact id
  | pub =>
    rintro ⟨f, h1, h2 | h2⟩
    · rcases hS l h2 with h3 | ⟨f', h3, h4⟩
      · exact ⟨f, hP l f h1, Or.inl h3⟩
      · rw [h1, Option.some.injEq] at h3; subst h3
        refine ⟨f, hP l f h1, Or.inr (Or.inl fun w hw' => Nat.le_trans h4 (hL w hw' a 0 ?_))⟩
        have : w.val ∈ ws.map (·.val) := List.mem_map_of_mem hw'
        rw [hw] at this; simpa using this
    · exact ⟨f, hP l f h1, Or.inr h2⟩
  | rgn _ => exact id

theorem FreshW_unsee {η₁ η₂ : TEnv} {V : WeakMem.Ts} (hP : ∀ l f, η₁.pfr l = some f → η₂.pfr l = some f)
    (hS : ∀ l, η₁.seen l → η₂.seen l ∨ ∃ f, η₁.pfr l = some f ∧ f ≤ V) {ws : List Word} (hL : LocAbove V ws)
    (h : FreshW η₁ ws) : FreshW η₂ ws := by
  intro a ha; obtain ⟨f, h1, h2⟩ := h a ha
  refine ⟨f, hP _ _ h1, ?_⟩
  rcases h2 with h2 | h2
  · rcases hS _ h2 with h3 | ⟨f', h3, h4⟩
    · exact Or.inl h3
    · rw [h1, Option.some.injEq] at h3; subst h3
      refine Or.inr fun w hw => Nat.le_trans h4 (hL w hw a 0 ?_)
      have : w.val ∈ ws.map (·.val) := List.mem_map_of_mem hw
      rw [ha] at this; simpa using this
  · exact Or.inr h2

/-- `VRz` under `unsee` (needed by the `.tvar` arm of `VR_unsee`); port of W `VR_unsee`. -/
theorem VRz_unsee (V : WeakMem.Ts) : ∀ (t : Ty) (bk : Prop) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) → η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l ∨ ∃ f, η₁.pfr l = some f ∧ f ≤ V) →
    (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    LocAbove V ws → (∀ l, η₁.rini l ≤ η₂.rini l) → VRz ρ η₁ bk t rt ws → VRz ρ η₂ bk t rt ws
  | .tvar k, bk, η₁, η₂, ρ, rt, ws, hr, hur, _, _, _, _, _, _, _, hBx, _, hri, hv => by
      simp only [VRz, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      exact ⟨VRz_unsee V t _ η₁ η₂ ρ rt ws hr hur hw hp ht hs hi hP hS hBx hL hri hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2.1,
        fun hq => (hv.2.2 (PubPosE_mono hw hBx hq)).imp (FreshW_unsee hP hS hL) (IniR_mono (TEnv.rc_mono hi hri))⟩
  | .iex b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VRz_unsee V b _ η₁ η₂ (vcons w ρ) rb ws hr hur hw hp ht hs hi hP hS hBx hL hri h2⟩
  | .prod a b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VRz_unsee V a _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.take n) hri e2,
        VRz_unsee V b _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.drop n) hri e3⟩
  | .sum a b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, boxSeen_unsee hP hS hx hL hm,
          fun hj => ⟨fun e => VRz_unsee V a _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hL hri ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => VRz_unsee V b _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hL hri ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRz_mono a _ η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hri hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRz_mono b _ η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hri hv⟩
      · have hLp := LocAbove_decodeArm hd hL
        refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          exact ⟨q, hq, VRz_unsee V a _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hri hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj
          exact ⟨q, hq, VRz_unsee V b _ η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hri hv⟩
  | .code a b _, bk, η₁, η₂, ρ, rt, ws, _, _, hw, hp, _, _, _, _, _, hBx, _, hri, hv => by
      simp only [VRz] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VRz_unsee V b _ (η₁.push0 s) (η₂.push0 s) ρ rb ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hL hri h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, bk, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOKb_unseeP hP hS h1 hL h5, h6⟩
  | .ptrOpt μ u, bk, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn
      · exact Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOKb_unseeP hP hS h1 hL h5, h6⟩
  | .loc μ u, bk, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn.1, hw ▸ hn.2⟩
      · exact Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOKb_flag (fun h => h.imp id (IniAt_mono (TEnv.rc_mono hi hri))) (ModeOKb_unseeP hP hS h1 hL h5),
          IniAt_mono (modeIni_le hi hri μ) h6⟩
  | .intS _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simpa only [VRz] using hv
  | .int, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simpa only [VRz] using hv
  | .opq _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRz] at hv ⊢; exact hv
  | .tid, bk, _, _, _, _, _, _, _, _, _, ht, hs, _, hP, hS, _, hL, _, hv => by
        simp only [VRz] at hv ⊢
        obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
        exact ⟨l, c, h1, hs _ _ h2, h3, ht ▸ ModeOKb_unseeP hP hS h1 hL h5⟩
  | .fix _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simpa only [VRz] using hv
  | .lanes _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simpa only [VRz] using hv
  | .unit, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, _ => by simp [VRz]
  | .void, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simp [VRz] at hv
  | .array _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, _ => by simp [VRz]
  | .share _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, _ => by simp [VRz]
  | .cap _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, _ => by simp [VRz]
  | .word _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simpa only [VRz] using hv
  | .tok _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, _ => by simp [VRz]
  | .word2 _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simpa only [VRz] using hv
  | .tok2 _ _ _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, _ => by simp [VRz]
  | .epair _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, hv => by simpa only [VRz] using hv
  | .tokE _ _ _, bk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hri, _ => by simp [VRz]
  | .mu b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      rw [← hw]
      refine VRz_unsee V b _ (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hL hri hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, bk, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hri, hv => by
      simp only [VRz] at hv ⊢
      exact fun n => VRz_unsee V b _ η₁ η₂ (vcons n ρ) rt ws hr hur hw hp ht hs hi hP hS hBx hL hri (hv n)

theorem ModeOKb_monoV {bkG : Prop} {i : Nat} {P P' : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S S' : WeakMem.AllocLabel → Prop} (hP : ∀ l f, P l = some f → P' l = some f) (hS : ∀ l, S l → S' l)
    {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws ws' : List Word}
    (hw : ∀ f, (∀ w ∈ ws, f ≤ w.view) → ∀ w ∈ ws', f ≤ w.view) :
    ModeOKb i P S bkG μ l c ws → ModeOKb i P' S' bkG μ l c ws' := by
  cases μ with
  | own => exact id
  | pub =>
    rintro ⟨f, h1, h2 | h2 | h2⟩
    · exact ⟨f, hP l f h1, Or.inl (hS l h2)⟩
    · exact ⟨f, hP l f h1, Or.inr (Or.inl (hw f h2))⟩
    · exact ⟨f, hP l f h1, Or.inr (Or.inr h2)⟩
  | rgn _ => exact id

/-- `VRz` is upward closed in word views (port of W `VR_up`). -/
theorem VRz_up {bkG : Prop} {ρ : Nat → Nat} {η : TEnv} : ∀ (t : Ty) (rt : Shp) (ws ws' : List Word),
    WLe ws ws' → VRz ρ η bkG t rt ws → VRz ρ η bkG t rt ws' := by
  intro t
  induction t generalizing ρ η bkG with
  | tex κ b ih =>
      intro rt ws ws' e hv
      simp only [VRz] at hv ⊢
      obtain ⟨n, rb, s, hr, hs, haf, hv⟩ := hv
      exact ⟨n, rb, s, hr, hs, haf, ih rb ws ws' e hv⟩
  | prod a b iha ihb =>
      intro rt ws ws' e hv
      simp only [VRz] at hv ⊢
      obtain ⟨ra, rb, hr, hf⟩ := hv
      refine ⟨ra, rb, hr, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hf n hn
      exact ⟨e.length ▸ h1, iha ra _ _ (e.take n) h2, ihb rb _ _ (e.drop n) h3⟩
  | iex b ih =>
      intro rt ws ws' e hv
      simp only [VRz] at hv ⊢
      obtain ⟨n, rb, w, hr, hv⟩ := hv
      exact ⟨n, rb, w, hr, ih rb ws ws' e hv⟩
  | refine t ψ ih =>
      intro rt ws ws' e hv; simp only [VRz] at hv ⊢; exact ⟨ih rt ws ws' e hv.1, IniR_vals e.vals ψ hv.2.1, RcCE_wle e hv.2.2⟩
  | sum a b iha ihb =>
      intro rt ws ws' e hv
      simp only [VRz] at hv ⊢
      obtain ⟨n, Ra, Rb, hr, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · exact ⟨n, Ra, Rb, hr, Or.inl ⟨hb, x, s, B, e.vals.symm.trans hx, ho, hB, hn, hsB,
          hm.imp id (WLe_view e hx B.fr), fun hj => ⟨fun e' => iha _ _ _ e ((hA hj).1 e'), (hA hj).2⟩,
          fun hj => ⟨fun e' => ihb _ _ _ e ((hA' hj).1 e'), (hA' hj).2⟩⟩⟩
      · obtain ⟨p', hd', ep⟩ := decodeArm_wle e hd
        refine ⟨n, Ra, Rb, hr, Or.inr ⟨j, p', hd', fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', iha _ _ _ eq hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', ihb _ _ _ eq hv⟩
  | mu b ih => intro rt ws ws' e hv; simp only [VRz] at hv ⊢; exact ih rt ws ws' e hv
  | iall b ih => intro rt ws ws' e hv; simp only [VRz] at hv ⊢; exact fun n => ih rt ws ws' e (hv n)
  | tvar k =>
      intro rt ws ws' e hv; simp only [VRz] at hv ⊢
      obtain ⟨w0, h0, hr⟩ := hv
      exact ⟨w0, WLe_trans h0 e, hr⟩
  | ptr μ u =>
      intro rt ws ws' e hv; simp only [VRz] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
        ModeOKb_monoV (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | ptrOpt μ u =>
      intro rt ws ws' e hv; simp only [VRz] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl (e.vals.symm.trans hn)
      · exact Or.inr ⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
          ModeOKb_monoV (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | loc μ u =>
      intro rt ws ws' e hv; simp only [VRz] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨e.vals.symm.trans hn.1, hn.2⟩
      · exact Or.inr ⟨a, c, U, e.vals.symm.trans h1, h3, h4, hF,
          ModeOKb_monoV (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | tid =>
      intro rt ws ws' e hv; simp only [VRz] at hv ⊢
      obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
      exact ⟨l, c, e.vals.symm.trans h1, h2, h3,
        ModeOKb_monoV (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5⟩
  | _ => intro rt ws ws' e hv; simp only [VRz] at hv ⊢ <;> first | exact hv | (rw [← e.vals]; exact hv)

end TermSound.Flat
