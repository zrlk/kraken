import WeakCore.TermNoFul

/-!
# TermPubOnly: discharging `FulSNo` (PubOnly)

**`sNo` transfer**: shallow pub-ness (`TermPtrRts.sNo`, under which every word counts,
`pubWords_of_sNo`) survives everything between a cell's type and the runtime type of a value stored
into it: folding (`Fd`), skeletons and signatures (`sig`, so `WitL`'s two renditions), subsumption
under substitution (`SubS`), and `Lay`'s `etok ∘ skel`.
-/

namespace TermPubOnly
open CoreLang CoreTerm CoreTyping TermRun TermSound TermClose TermPtrRts TermTv
open WeakMem (Msg Memory Address Ts AllocLabel)

/-! ## (B2) `sNo` transfer -/

/-- A noOwn, rgnFree type is shallow-pub. -/
theorem sNo_of_noOwn : ∀ (t : Ty) (ke : KEnv), Ty.noOwnIn ke t = true → rgnFree t = true → sNo t = true := by
  intro t
  induction t with
  | ptr μ u _ => intro ke h1 h2; cases μ <;> simp_all [Ty.noOwnIn, rgnFree, sNo, mPub]
  | ptrOpt μ u _ => intro ke h1 h2; cases μ <;> simp_all [Ty.noOwnIn, rgnFree, sNo, mPub]
  | loc μ u _ => intro ke h1 h2; cases μ <;> simp_all [Ty.noOwnIn, rgnFree, sNo, mPub]
  | prod a b iha ihb =>
      intro ke h1 h2
      simp only [Ty.noOwnIn, rgnFree, sNo, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨iha ke h1.1 h2.1, ihb ke h1.2 h2.2⟩
  | sum a b iha ihb =>
      intro ke h1 h2
      simp only [Ty.noOwnIn, rgnFree, sNo, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨iha ke h1.1 h2.1, ihb ke h1.2 h2.2⟩
  | refine t _ ih => intro ke h1 h2; simp only [Ty.noOwnIn, rgnFree, sNo] at h1 h2 ⊢; exact ih ke h1 h2
  | iall t ih => intro ke h1 h2; simp only [Ty.noOwnIn, rgnFree, sNo] at h1 h2 ⊢; exact ih ke h1 h2
  | iex t ih => intro ke h1 h2; simp only [Ty.noOwnIn, rgnFree, sNo] at h1 h2 ⊢; exact ih ke h1 h2
  | mu t ih => intro ke h1 h2; simp only [Ty.noOwnIn, rgnFree, sNo] at h1 h2 ⊢; exact ih _ h1 h2
  | tex κ t ih =>
      intro ke h1 h2
      simp only [Ty.noOwnIn, rgnFree, sNo, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨h1.1, ih _ h1.2 h2⟩
  | array i t ih => intro ke h1 h2; simp only [Ty.noOwnIn, rgnFree, sNo] at h1 h2 ⊢; exact ih ke h1 h2
  | _ => intro ke _ _; simp [sNo]

theorem mPub_skelM (μ : Mode) : mPub (skelM μ) = mPub μ := by cases μ <;> rfl

theorem sNo_rf (t : Ty) : sNo (rf t) = sNo t := by
  cases t <;> simp [rf, sNo]

/-- `sNo` reads no index, refinement or pointee: skeletons keep it. -/
theorem sNo_skel : ∀ t : Ty, sNo (skel t) = sNo t := by
  intro t
  induction t with
  | ptr μ u _ => simp [skel, sNo, mPub_skelM]
  | ptrOpt μ u _ => simp [skel, sNo, mPub_skelM]
  | loc μ u _ => simp [skel, sNo, mPub_skelM]
  | prod a b iha ihb => simp [skel, sNo, iha, ihb]
  | sum a b iha ihb => simp [skel, sNo, iha, ihb]
  | refine t _ ih => simp only [skel, sNo_rf, sNo]; exact ih
  | iall t ih => simp [skel, sNo, ih]
  | iex t ih => simp [skel, sNo, ih]
  | mu t ih => simp [skel, sNo, ih]
  | tex κ t ih => simp [skel, sNo, ih]
  | array i t ih => simp [skel, sNo, ih]
  | _ => simp [skel, sNo]

theorem sNo_etok : ∀ t : Ty, sNo (etok t) = sNo t := by
  intro t
  induction t with
  | prod a b iha ihb => simp [etok, sNo, iha, ihb]
  | sum a b iha ihb => simp [etok, sNo, iha, ihb]
  | refine t _ ih => simp [etok, sNo, ih]
  | array i t ih => simp [etok, sNo, ih]
  | _ => simp [etok, sNo]

theorem sNo_er : ∀ t : Ty, sNo (er t) = sNo t := by
  intro t
  induction t with
  | prod a b iha ihb => simp [er, sNo, iha, ihb]
  | sum a b iha ihb => simp [er, sNo, iha, ihb]
  | refine t _ ih => simp [er, sNo, ih]
  | iall t ih => simp [er, sNo, ih]
  | iex t ih => simp [er, sNo, ih]
  | mu t ih => simp [er, sNo, ih]
  | tex κ t ih => simp [er, sNo, ih]
  | array i t ih => simp [er, sNo, ih]
  | _ => simp [er, sNo]

/-- `sig` keeps `sNo` (so `WitL`'s two renditions agree on it). -/
theorem sNo_sig (t : Ty) : sNo (sig t) = sNo t := by
  unfold sig; rw [sNo_er, sNo_skel]

theorem sNo_of_sig {t u : Ty} (h : sig t = sig u) : sNo t = sNo u := by
  rw [← sNo_sig t, h, sNo_sig]

theorem mPub_meq {cx : Cx} {d : Nat} {μ ν : Mode} (h : MEq cx d μ ν) : mPub μ = mPub ν := by
  cases h <;> rfl

/-- Equal types (up to indices) have the same `sNo` under any substitution. -/
theorem sNo_substTs_tyEq {cx : Cx} {d0 : Nat} {t u : Ty} (h : TyEqS cx d0 t u) :
    ∀ (σs : List Ty) (c d : Nat), sNo (substTs σs c d t) = sNo (substTs σs c d u) := by
  induction h with
  | refl => intros; rfl
  | prod _ _ iha ihb => intro σs c d; simp only [substTs, sNo, iha σs c d, ihb σs c d]
  | sum _ _ iha ihb => intro σs c d; simp only [substTs, sNo, iha σs c d, ihb σs c d]
  | ptr hm _ _ => intro σs c d; simp only [substTs, sNo, mPub_meq hm]
  | ptrOpt hm _ _ => intro σs c d; simp only [substTs, sNo, mPub_meq hm]
  | loc hm _ _ => intro σs c d; simp only [substTs, sNo, mPub_meq hm]
  | mu _ ih => intro σs c d; simp only [substTs, sNo, ih σs (c + 1) d]
  | tex _ ih => intro σs c d; simp only [substTs, sNo, ih σs (c + 1) d]
  | iall _ ih => intro σs c d; simp only [substTs, sNo, ih σs c (d + 1)]
  | iex _ ih => intro σs c d; simp only [substTs, sNo, ih σs c (d + 1)]
  | refine _ ih => intro σs c d; simp only [substTs, sNo, ih σs c d]
  | refineIni _ _ ih => intro σs c d; simp only [substTs, sNo, ih σs c d]
  | array _ _ ih => intro σs c d; simp only [substTs, sNo, ih σs c d]
  | _ => intros; simp [substTs, sNo]

/-- **Subsumption** under any substitution: the subtype is shallow-pub if the supertype is. -/
theorem sNo_substTs_sub {cx : Cx} {t u : Ty} (h : SubS cx t u) :
    ∀ (σs : List Ty) (c d : Nat), sNo (substTs σs c d u) = true → sNo (substTs σs c d t) = true := by
  induction h with
  | eq he => intro σs c d hu; rw [sNo_substTs_tyEq he]; exact hu
  | intS => intros; simp [substTs, sNo]
  | refine _ ih => intro σs c d hu; simp only [substTs, sNo]; exact ih σs c d hu
  | iniWeak he _ =>
      intro σs c d hu
      simp only [substTs, sNo] at hu ⊢
      rw [sNo_substTs_tyEq he]; exact hu
  | nonNull hm _ => intro σs c d hu; simp only [substTs, sNo] at hu ⊢; rw [mPub_meq hm]; exact hu
  | prod _ _ iha ihb =>
      intro σs c d hu
      simp only [substTs, sNo, Bool.and_eq_true] at hu ⊢
      exact ⟨iha σs c d hu.1, ihb σs c d hu.2⟩
  | sum _ _ iha ihb =>
      intro σs c d hu
      simp only [substTs, sNo, Bool.and_eq_true] at hu ⊢
      exact ⟨iha σs c d hu.1, ihb σs c d hu.2⟩
  | cap _ _ => intros; simp [substTs, sNo]
  | codeR _ _ => intros; simp [substTs, sNo]
  | codeRR _ _ _ _ => intros; simp [substTs, sNo]

theorem mPub_clM (ρ : Nat → Nat) (d : Nat) (μ : Mode) : mPub (clM ρ d μ) = mPub μ := by
  cases μ <;> rfl

/-- Closing with the innermost variable kept, versus substituted: `sNo` of the latter gives the
former (a variable reads `true`). -/
theorem sNo_cl_unshift {ρ : Nat → Nat} {W W1 : Nat → Ty} (hs : ∀ k, W1 (k + 1) = W k) :
    ∀ (t : Ty) (c d : Nat), sNo (cl ρ W1 c d t) = true → sNo (cl ρ W (c + 1) d t) = true := by
  intro t
  induction t with
  | tvar k =>
      intro c d h
      simp only [cl] at h ⊢
      by_cases h1 : k < c + 1
      · simp [h1, sNo]
      · have h2 : ¬ k < c := by omega
        have e : k - c = (k - (c + 1)) + 1 := by omega
        simp only [h1, h2, ↓reduceIte] at h ⊢
        rw [e, hs] at h; exact h
  | ptr μ t _ => intro c d h; simp only [cl, sNo, mPub_clM] at h ⊢; exact h
  | ptrOpt μ t _ => intro c d h; simp only [cl, sNo, mPub_clM] at h ⊢; exact h
  | loc μ t _ => intro c d h; simp only [cl, sNo, mPub_clM] at h ⊢; exact h
  | prod a b iha ihb =>
      intro c d h; simp only [cl, sNo, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb =>
      intro c d h; simp only [cl, sNo, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | mu t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih (c + 1) d h
  | tex κ t ih =>
      intro c d h; simp only [cl, sNo, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih (c + 1) d h.2⟩
  | iall t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c (d + 1) h
  | iex t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c (d + 1) h
  | refine t ψ ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c d h
  | array i t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c d h
  | _ => intro c d _; simp [cl, sNo]

/-- Substituting a shallow-pub type for the innermost kept variable keeps `sNo`. -/
theorem sNo_cl_shift {ρ : Nat → Nat} {W W1 : Nat → Ty} (h0 : sNo (W1 0) = true) (hs : ∀ k, W1 (k + 1) = W k) :
    ∀ (t : Ty) (c d : Nat), sNo (cl ρ W (c + 1) d t) = true → sNo (cl ρ W1 c d t) = true := by
  intro t
  induction t with
  | tvar k =>
      intro c d h
      simp only [cl] at h ⊢
      by_cases h1 : k < c
      · simp [h1, sNo]
      · by_cases h2 : k = c
        · subst h2; simpa using h0
        · have h3 : ¬ k < c + 1 := by omega
          have e : k - c = (k - (c + 1)) + 1 := by omega
          simp only [h1, h3, ↓reduceIte] at h ⊢
          rw [e, hs]; exact h
  | ptr μ t _ => intro c d h; simp only [cl, sNo, mPub_clM] at h ⊢; exact h
  | ptrOpt μ t _ => intro c d h; simp only [cl, sNo, mPub_clM] at h ⊢; exact h
  | loc μ t _ => intro c d h; simp only [cl, sNo, mPub_clM] at h ⊢; exact h
  | prod a b iha ihb =>
      intro c d h; simp only [cl, sNo, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb =>
      intro c d h; simp only [cl, sNo, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | mu t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih (c + 1) d h
  | tex κ t ih =>
      intro c d h; simp only [cl, sNo, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih (c + 1) d h.2⟩
  | iall t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c (d + 1) h
  | iex t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c (d + 1) h
  | refine t ψ ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c d h
  | array i t ih => intro c d h; simp only [cl, sNo] at h ⊢; exact ih c d h
  | _ => intro c d _; simp [cl, sNo]

/-- The closure of an unfolding, as a closure of the body (`TermStep.rgnFree_unfold`'s step). -/
theorem cl_unfold_eq (ρ : Nat → Nat) (W : Nat → Ty) (s : Ty) :
    cl ρ W 0 0 (unfold1 (.mu s)) = cl ρ (TermStep.wcons (cl ρ W 0 0 (.mu s)) W) 0 0 s := by
  have e1 : unfold1 (.mu s) = substTs [.mu s] 0 0 s := TermClose.substT_eq (.mu s) s 0 0
  have e2 := cl_substTs [.mu s] 0 0 (ρ := ρ) (W₀ := W) (W₁ := TermStep.wcons (cl ρ W 0 0 (.mu s)) W)
    (fun k hk => absurd hk (Nat.not_lt_zero _))
    (fun j σ hj => by
      cases j with
      | zero => simp at hj; subst hj; simp [TermStep.wcons]
      | succ j => simp at hj)
    (fun k => by simp [TermStep.wcons]) s 0 0
  simp only [Nat.add_zero] at e2
  rw [e1, e2]

/-- Unfolding a closed `μ` type keeps `sNo`. -/
theorem sNo_unfold {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (h : sNo (cl ρ W 0 0 (.mu s)) = true) :
    sNo (cl ρ W 0 0 (unfold1 (.mu s))) = true := by
  rw [cl_unfold_eq]
  have h1 : sNo (cl ρ W (0 + 1) 0 s) = true := by simp only [cl, sNo] at h; exact h
  exact sNo_cl_shift (W1 := TermStep.wcons (cl ρ W 0 0 (.mu s)) W) (by simpa [TermStep.wcons] using h)
    (fun k => by simp [TermStep.wcons]) s 0 0 h1

/-- Folding a closed `μ` type keeps `sNo`. -/
theorem sNo_fold {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (h : sNo (cl ρ W 0 0 (unfold1 (.mu s))) = true) :
    sNo (cl ρ W 0 0 (.mu s)) = true := by
  have e1 : unfold1 (.mu s) = substTs [.mu s] 0 0 s := TermClose.substT_eq (.mu s) s 0 0
  have e2 := cl_substTs [.mu s] 0 0 (ρ := ρ) (W₀ := W) (W₁ := TermStep.wcons (cl ρ W 0 0 (.mu s)) W)
    (fun k hk => absurd hk (Nat.not_lt_zero _))
    (fun j σ hj => by
      cases j with
      | zero => simp at hj; subst hj; simp [TermStep.wcons]
      | succ j => simp at hj)
    (fun k => by simp [TermStep.wcons]) s 0 0
  simp only [Nat.add_zero] at e2
  rw [e1, e2] at h
  simp only [cl, sNo]
  exact sNo_cl_unshift (W1 := TermStep.wcons (cl ρ W 0 0 (.mu s)) W) (fun k => by simp [TermStep.wcons]) s 0 0 h

/-- A component of a shallow-pub type is shallow-pub. -/
theorem sNo_AtOff {T U : Ty} {o : Nat} (h : AtOff T o U) (hT : sNo T = true) : sNo U = true := by
  induction h with
  | here _ => exact hT
  | fst _ ih => simp only [sNo, Bool.and_eq_true] at hT; exact ih hT.1
  | snd _ _ ih => simp only [sNo, Bool.and_eq_true] at hT; exact ih hT.2
  | elem _ _ _ ih => simp only [sNo] at hT; exact ih hT
  | mu _ _ _ ih => exact ih (sNo_unfold hT)
  | fold _ _ _ _ ih => exact sNo_fold (ih hT)

/-- **Folding**: a folded type of a shallow-pub type is shallow-pub. -/
theorem sNo_Fd {T U : Ty} (h : Fd T U) (hT : sNo T = true) : sNo U = true := by
  induction h with
  | refl => exact hT
  | fold _ _ _ _ ih => exact sNo_fold (ih hT)

/-- `Lay`'s skeleton agreement transfers `sNo` to the runtime type. -/
theorem sNo_lay {σs : List Ty} {t rt : Ty} {ws : List Word} (hl : Lay σs t rt ws)
    (h : sNo (close σs t) = true) : sNo rt = true := by
  have e := congrArg sNo hl.2.1
  rw [sNo_etok, sNo_etok, sNo_skel, sNo_skel] at e
  rw [e]; exact h

/-- **(B2) at a store**: the runtime type `rt` of a value stored, at a subtype `tv` of the
pointee `u`, into a component `U` (at some offset) of a noOwn, rgnFree cell type `T`, the pointee
folding `U` and its two renditions agreeing (`sig_WitL`), is shallow-pub. -/
theorem sNo_store {T U u tv rt : Ty} {o : Nat} {σs : List Ty} {ρ : Nat → Nat} {W : Nat → Ty} {cx : Cx}
    {ws : List Word} (hno : Ty.noOwnIn [] T = true) (hrf : rgnFree T = true) (hat : AtOff T o U)
    (hfd : Fd U (cl ρ W 0 0 u)) (hsig : sig (close σs u) = sig (cl ρ W 0 0 u)) (hsub : SubS cx tv u)
    (hl : Lay σs tv rt ws) : sNo rt = true := by
  have h1 : sNo (cl ρ W 0 0 u) = true := sNo_Fd hfd (sNo_AtOff hat (sNo_of_noOwn T [] hno hrf))
  have h2 : sNo (close σs u) = true := by rw [sNo_of_sig hsig]; exact h1
  exact sNo_lay hl (sNo_substTs_sub hsub σs 0 0 h2)

/-- The pointer form (`VR` at `ptr`: `Fd c.ty (cl … u)`, offset 0 at the whole cell). -/
theorem sNo_store_ptr {T u tv rt : Ty} {σs : List Ty} {ρ : Nat → Nat} {W : Nat → Ty} {cx : Cx}
    {ws : List Word} (hno : Ty.noOwnIn [] T = true) (hrf : rgnFree T = true)
    (hfd : Fd T (cl ρ W 0 0 u)) (hsig : sig (close σs u) = sig (cl ρ W 0 0 u)) (hsub : SubS cx tv u)
    (hl : Lay σs tv rt ws) : sNo rt = true := by
  have h1 : sNo (cl ρ W 0 0 u) = true := sNo_Fd hfd (sNo_of_noOwn T [] hno hrf)
  have h2 : sNo (close σs u) = true := by rw [sNo_of_sig hsig]; exact h1
  exact sNo_lay hl (sNo_substTs_sub hsub σs 0 0 h2)

/-- At such a store, every word of the stored value counts. -/
theorem pubWords_store {T U u tv rt : Ty} {o : Nat} {σs : List Ty} {ρ : Nat → Nat} {W : Nat → Ty} {cx : Cx}
    {ws : List Word} (hno : Ty.noOwnIn [] T = true) (hrf : rgnFree T = true) (hat : AtOff T o U)
    (hfd : Fd U (cl ρ W 0 0 u)) (hsig : sig (close σs u) = sig (cl ρ W 0 0 u)) (hsub : SubS cx tv u)
    (hl : Lay σs tv rt ws) : pubWords rt ws = ws :=
  pubWords_of_sNo (sNo_store hno hrf hat hfd hsig hsub hl) ws

/-! ## (B2) glue: from the typing of a stored operand -/

/-- **(B2) at a typed use**: the runtime type of a variable operand used at `tv`, a subtype of a
pointee `u` whose closure is shallow-pub, is shallow-pub. -/
theorem sNo_of_use {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx c₁ : Cx}
    {env : Env} {x : String} {tv u rt : Ty} {ws : List Word}
    (hi : FInv ρ η σs K cx env) (hu : cx.use (.var x) = .ok (tv, c₁)) (hlk : lookupE env x = some (rt, ws))
    (hsub : SubS c₁ tv u) (ho : cx.opaqueOK u = true) (htb : tb cx.ke.length u = true)
    (hU : sNo (cl ρ η.wit 0 0 u) = true) : sNo rt = true := by
  obtain ⟨-, rt', ws', hev, -, hl⟩ := use_FInv hu hi
  simp only [evalAt, hlk, Option.some.injEq, Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  have hsig : sig (close σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (TermTv.lt_of_guardT htb hi.2.2.2.2.1)
  have h2 : sNo (close σs u) = true := by rw [sNo_of_sig hsig]; exact hU
  exact sNo_lay hl (sNo_substTs_sub hsub σs 0 0 h2)

/-- A cell of a noOwn, rgnFree type folding to the pointee's closure: the closure is shallow-pub. -/
theorem sNo_cl_of_Fd {T U : Ty} (hno : Ty.noOwnIn [] T = true) (hrf : rgnFree T = true) (h : Fd T U) :
    sNo U = true :=
  sNo_Fd h (sNo_of_noOwn T [] hno hrf)

/-- A component of a noOwn, rgnFree cell type: shallow-pub. -/
theorem sNo_cl_of_AtOff {T U : Ty} {o : Nat} (hno : Ty.noOwnIn [] T = true) (hrf : rgnFree T = true)
    (h : AtOff T o U) : sNo U = true :=
  sNo_AtOff h (sNo_of_noOwn T [] hno hrf)

/-! ## Discharging `FulSNo` -/

theorem sNo_cl_adapt : ∀ (u : Ty) (r : Idx) (ρ : Nat → Nat) (W : Nat → Ty) (c d : Nat),
    sNo (cl ρ W c d (adapt r u)) = sNo (cl ρ W c d u) := by
  intro u
  induction u with
  | ptr μ t _ => intro r ρ W c d; cases μ <;> simp only [adapt, cl, sNo, mPub_clM] <;> rfl
  | ptrOpt μ t _ => intro r ρ W c d; cases μ <;> simp only [adapt, cl, sNo, mPub_clM] <;> rfl
  | loc μ t _ => intro r ρ W c d; cases μ <;> simp only [adapt, cl, sNo, mPub_clM] <;> rfl
  | prod a b iha ihb => intro r ρ W c d; simp only [adapt, cl, sNo, iha, ihb]
  | sum a b iha ihb => intro r ρ W c d; simp only [adapt, cl, sNo, iha, ihb]
  | array i t ih => intro r ρ W c d; simp only [adapt, cl, sNo, ih]
  | iex t ih => intro r ρ W c d; simp only [adapt, cl, sNo, ih]
  | iall t ih => intro r ρ W c d; simp only [adapt, cl, sNo, ih]
  | tex κ t ih => intro r ρ W c d; simp only [adapt, cl, sNo, ih]
  | refine t ψ ih => intro r ρ W c d; simp only [adapt, cl, sNo, ih]
  | mu t ih => intro r ρ W c d; simp only [adapt, cl, sNo, ih]
  | _ => intro r ρ W c d; rfl

theorem tb_adapt : ∀ (u : Ty) (r : Idx) (c : Nat), tb c (adapt r u) = tb c u := by
  intro u
  induction u with
  | ptr μ t _ => intro r c; cases μ <;> simp [adapt, tb]
  | ptrOpt μ t _ => intro r c; cases μ <;> simp [adapt, tb]
  | loc μ t _ => intro r c; cases μ <;> simp [adapt, tb]
  | prod a b iha ihb => intro r c; simp only [adapt, tb, iha, ihb]
  | sum a b iha ihb => intro r c; simp only [adapt, tb, iha, ihb]
  | array i t ih => intro r c; simp only [adapt, tb, ih]
  | iex t ih => intro r c; simp only [adapt, tb, ih]
  | iall t ih => intro r c; simp only [adapt, tb, ih]
  | tex κ t ih => intro r c; simp only [adapt, tb, ih]
  | refine t ψ ih => intro r c; simp only [adapt, tb, ih]
  | mu t ih => intro r c; simp only [adapt, tb, ih]
  | _ => intro r c; rfl

theorem sNo_cl_compTy : ∀ (q : List Nat) (u c : Ty) (ρ : Nat → Nat) (W : Nat → Ty) (k d : Nat),
    compTy u q = some c → sNo (cl ρ W k d u) = true → sNo (cl ρ W k d c) = true := by
  intro q
  induction q with
  | nil => intro u c ρ W k d h hu; simp only [compTy, Option.some.injEq] at h; subst h; exact hu
  | cons i q ih =>
    intro u c ρ W k d h hu
    cases u with
    | prod a b =>
      simp only [cl, sNo, Bool.and_eq_true] at hu
      rcases i with _ | _ | i
      · exact ih a c ρ W k d (by simpa [compTy] using h) hu.1
      · exact ih b c ρ W k d (by simpa [compTy] using h) hu.2
      · simp [compTy] at h
    | _ => simp [compTy] at h

theorem tb_compTy : ∀ (q : List Nat) (u c : Ty) (k : Nat), compTy u q = some c → tb k u = true → tb k c = true := by
  intro q
  induction q with
  | nil => intro u c k h hu; simp only [compTy, Option.some.injEq] at h; subst h; exact hu
  | cons i q ih =>
    intro u c k h hu
    cases u with
    | prod a b =>
      simp only [tb, Bool.and_eq_true] at hu
      rcases i with _ | _ | i
      · exact ih a c k (by simpa [compTy] using h) hu.1
      · exact ih b c k (by simpa [compTy] using h) hu.2
      · simp [compTy] at h
    | _ => simp [compTy] at h

theorem sNo_close_intOf : ∀ (t : Ty) (σs : List Ty) (c d : Nat) (o : Option Idx), intOf t = some o →
    sNo (substTs σs c d t) = true := by
  intro t
  induction t with
  | refine t ψ ih => intro σs c d o h; simp only [substTs, sNo]; exact ih σs c d o (by simpa [intOf] using h)
  | intS i => intro σs c d o _; rfl
  | int => intro σs c d o _; rfl
  | _ => intro σs c d o h; simp [intOf] at h

/-- The cell reached through a reference at `t`, a noOwn, rgnFree cell: the pointee's closure is
shallow-pub. -/
theorem sNo_cell {ρ : Nat → Nat} {η : TEnv} {t : Ty} {sh : Shp} {ws : List Word} {μ : Mode} {u : Ty} {pw : Word}
    {b : Address} {sto : Sto} {ca : Cell} (hv : VR ρ η t sh ws) (hc : cellOf t = some (μ, u)) (hws : ws = [pw])
    (hb : addrOf pw = some b) (hsto : ∀ l c, η.sto l = some c → sto l = some c) (hca : sto b.label = some ca)
    (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true) : sNo (cl ρ η.wit 0 0 u) = true := by
  subst hws
  cases t with
  | ptr μ' u' =>
    simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [VR] at hv
    obtain ⟨a, c, hval, -, hs, hfd, -⟩ := hv
    simp only [List.map, List.cons.injEq] at hval
    simp only [addrOf, hval.1, Option.some.injEq] at hb
    subst hb
    rw [hsto _ _ hs, Option.some.injEq] at hca
    subst hca
    exact sNo_cl_of_Fd hno hrf hfd
  | loc μ' u' =>
    simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [VR] at hv
    rcases hv with ⟨hval, -⟩ | ⟨a, c, U, hval, hs, hat, hfd, -⟩
    · simp only [List.map, List.cons.injEq] at hval
      simp [addrOf, hval.1] at hb
    · simp only [List.map, List.cons.injEq] at hval
      simp only [addrOf, hval.1, Option.some.injEq] at hb
      subst hb
      rw [hsto _ _ hs, Option.some.injEq] at hca
      subst hca
      exact sNo_Fd hfd (sNo_cl_of_AtOff hno hrf hat)
  | _ => simp [cellOf] at hc

/-- A store through a reference at a noOwn, rgnFree cell, of a variable at a subtype of the
pointee (or of its region adaptation): the stored entry is shallow-pub. -/
theorem sNo_store_gen {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx c₁ : Cx}
    {env : Env} {a : At} {x : String} {t tv u t0 rt : Ty} {μ : Mode} {ws : List Word} {pw : Word} {b : Address}
    {sto : Sto} {ca : Cell} (hi : FInv ρ η σs K cx env) (htv : TvOK cx) (hpk : cx.peek a = .ok t)
    (hc : cellOf t = some (μ, u)) (hu : cx.use (.var x) = .ok (tv, c₁))
    (hsub : SubS c₁ tv u ∨ ∃ r, SubS c₁ tv (adapt r u)) (hlk : lookupE env x = some (rt, ws))
    (hea : evalAt env a = some (t0, [pw])) (hb : addrOf pw = some b)
    (hsto : ∀ l c, η.sto l = some c → sto l = some c) (hca : sto b.label = some ca)
    (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true) : sNo rt = true := by
  obtain ⟨rta, wsa, hev, hvr, -⟩ := peek_VR hi.2.1 hpk
  rw [hea, Option.some.injEq, Prod.mk.injEq] at hev
  have hU := sNo_cell hvr hc hev.2.symm hb hsto hca hno hrf
  have htb := tb_cellOf (peek_tb htv hpk) hc
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1
  rcases hsub with hsub | ⟨r, hsub⟩
  · exact sNo_of_use hi hu hlk hsub (sub_opaqueOK hsub hotv) htb hU
  · exact sNo_of_use hi hu hlk hsub (sub_opaqueOK hsub hotv) (by rw [tb_adapt]; exact htb)
      (by rw [sNo_cl_adapt]; exact hU)

/-- The element type of a buffer reached through a locative at a noOwn, rgnFree cell. -/
theorem sNo_buf {ρ : Nat → Nat} {η : TEnv} {t : Ty} {sh : Shp} {ws : List Word} {n k : Idx} {u : Ty} {pw : Word}
    {b : Address} {sto : Sto} {ca : Cell} (hv : VR ρ η t sh ws) (hbo : bufOf t = some (.own, n, u, k))
    (hws : ws = [pw]) (hb : addrOf pw = some b) (hsto : ∀ l c, η.sto l = some c → sto l = some c)
    (hca : sto b.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true) (hrf : rgnFree ca.ty = true) :
    sNo (cl ρ η.wit 0 0 u) = true ∧ ∀ c, tb c t = true → tb c u = true := by
  have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
    unfold bufOf at hbo
    split at hbo
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbo
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hbo
      rfl
    · cases hbo
  subst ht
  have hv1 : VR ρ η (.loc .own (.array n u)) sh ws := by simp only [VR] at hv ⊢; exact hv.1
  have h := sNo_cell hv1 (rfl : cellOf (.loc .own (.array n u)) = some (.own, .array n u)) hws hb hsto
    hca hno hrf
  simp only [cl, sNo] at h
  exact ⟨h, fun c hc => by simpa [tb] using hc⟩

/-- An integer-typed variable (a word store's value) is shallow-pub. -/
theorem sNo_wordP {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx} {env : Env}
    {x : String} {j : Idx} {rt : Ty} {ws : List Word} (hi : FInv ρ η σs K cx env) (hii : IntIdx cx (.var x) j)
    (hlk : lookupE env x = some (rt, ws)) : sNo rt = true := by
  obtain ⟨t, hpk, hio⟩ := hii
  obtain ⟨rt', ws', hev, -, hl⟩ := peek_VR hi.2.1 hpk
  simp only [evalAt, hlk, Option.some.injEq, Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  exact sNo_lay hl (sNo_close_intOf t σs 0 0 _ hio)

theorem sNo_word {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx c₁ : Cx}
    {env : Env} {tk : At} {tt : Ty} {x : String} {j : Idx} {rt : Ty} {ws : List Word}
    (hi : FInv ρ η σs K cx env) (hu : cx.use tk = .ok (tt, c₁)) (hii : IntIdx c₁ (.var x) j)
    (hlk : lookupE env x = some (rt, ws)) : sNo rt = true :=
  sNo_wordP (use_FInv hu hi).1 hii hlk

/-- **The discharge of `FulSNo`**: the environment entry a typed thread's data word comes from,
written into a noOwn, rgnFree cell, is shallow-pub. -/
theorem sNo_writeFrom {p : Prog} {E : TEnv} {sto : Sto} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {x : String} {rt : Ty} {ws : List Word} {w : Word} {loc : Address}
    (hsto : ∀ l c, E.sto l = some c → sto l = some c) (hT : ThInvE p E th)
    (hW : TermNoFul.WriteFrom g mem pairs th x rt ws w loc)
    (hca : ∃ ca, sto loc.label = some ca ∧ Ty.noOwnIn [] ca.ty = true ∧ rgnFree ca.ty = true) :
    sNo rt = true := by
  obtain ⟨ρ, η, cx, hE, -, hTy, htv, hi, -⟩ := hT
  subst hE
  have hsto' : ∀ l c, η.sto l = some c → sto l = some c := hsto
  obtain ⟨ca, hca, hno, hrf⟩ := hca
  obtain ⟨hlk, -, ⟨y, op, e, pw, b, rel, us, j, hterm, hdv, hU, -, -, hl⟩ |
    ⟨acq, rel, wa, e, tn, ok, fail, t1, t2, pw, ew, hterm, -, hwa, -, hpw⟩⟩ := hW
  · subst hl
    have hcab : sto b.label = some ca := hca
    rw [hterm] at hTy
    cases hTy with
    | let_ hop _ =>
    cases hop with
    | storeOwn hpk _ hc _ hu hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, -, hb, -⟩ := hU
      exact sNo_store_gen hi htv hpk hc hu (Or.inl hsub) hlk hea hb hsto' hcab hno hrf
    | storePub hpk _ hc _ hu hsub _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, -, hb, -⟩ := hU
      exact sNo_store_gen hi htv hpk hc hu (Or.inl hsub) hlk hea hb hsto' hcab hno hrf
    | storeRgn hpk _ hc _ hu _ hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, -, hb, -⟩ := hU
      exact sNo_store_gen hi htv hpk hc hu (hsub.imp id fun h => ⟨_, h⟩) hlk hea hb hsto' hcab hno hrf
    | storeCap hpk _ hc _ hu _ _ hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, -, hb, -⟩ := hU
      exact sNo_store_gen hi htv hpk hc hu (hsub.imp id fun h => ⟨_, h⟩) hlk hea hb hsto' hcab hno hrf
    | storeWordGive _ _ hu _ hii _ _ _ _ _ _ _ _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact sNo_word hi hu hii hlk
    | storeWordKeep _ _ hu _ hii _ _ _ _ _ _ _ _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact sNo_word hi hu hii hlk
    | storeWordHand _ _ hu _ hii _ _ _ _ _ _ _ _ _ _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      exact sNo_word hi hu hii hlk
    | xchg hpk hxc hu hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, hea, -, -, hb, -⟩ := hU
      cases hxc with
      | own _ hc _ =>
        exact sNo_store_gen hi htv hpk hc hu (Or.inl (hsub.elim id id)) hlk hea hb hsto' hcab hno hrf
      | rgn _ hc _ _ _ =>
        exact sNo_store_gen hi htv hpk hc hu (hsub.imp id fun h => ⟨_, h⟩) hlk hea hb hsto' hcab hno hrf
    | xchgAt hpk hbo _ _ _ _ hu hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, _, _, _, _, hea, -, -, -, -, hb, -, hbb⟩ := hU
      subst hbb
      obtain ⟨rta, wsa, hev, hvr, -⟩ := peek_VR hi.2.1 hpk
      rw [hea, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨hU', htb'⟩ := sNo_buf hvr hbo hev.2.symm hb hsto' hcab hno hrf
      have hotv : cx.opaqueOK _ = true :=
        peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      exact sNo_of_use hi hu hlk hsub (sub_opaqueOK hsub hotv) (htb' _ (peek_tb htv hpk)) hU'
    | xchgAtF hpk hbo hct _ _ _ _ _ hu hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, _, _, _, _, _, _, _, hea, -, -, -, -, hb, -, -, -, hbb⟩ := hU
      subst hbb
      obtain ⟨rta, wsa, hev, hvr, -⟩ := peek_VR hi.2.1 hpk
      rw [hea, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨hU', htb'⟩ := sNo_buf hvr hbo hev.2.symm hb hsto' hcab hno hrf
      have hotv : cx.opaqueOK _ = true :=
        peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      exact sNo_of_use hi hu hlk hsub (sub_opaqueOK hsub hotv)
        (tb_compTy _ _ _ _ hct (htb' _ (peek_tb htv hpk))) (sNo_cl_compTy _ _ _ ρ η.wit 0 0 hct hU')
    | bufInit hub hbo _ _ _ hu hsub _ =>
      simp only [TermNoFul.DataVar] at hdv; subst hdv
      obtain ⟨-, _, _, _, _, _, _, _, _, _, _, _, _, hea, -, -, -, -, hb, -, -, hbb⟩ := hU
      subst hbb
      have hpk := (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hub).1
      obtain ⟨rta, wsa, hev, hvr, -⟩ := peek_VR hi.2.1 hpk
      rw [hea, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨hU', htb'⟩ := sNo_buf hvr hbo hev.2.symm hb hsto' hcab hno hrf
      have hi1 := (use_FInv hub hi).1
      obtain ⟨htv1, -, hke⟩ := use_TvOK hub htv
      have hotv : _ = true :=
        peek_opaqueOK htv1 (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      exact sNo_of_use hi1 hu hlk hsub (sub_opaqueOK hsub hotv)
        (by rw [hke]; exact htb' _ (peek_tb htv hpk)) hU'
    | _ => simp [TermNoFul.DataVar] at hdv
  · rw [hterm] at hTy
    have hcab : sto loc.label = some ca := hca
    cases hTy with
    | casCell hpk _ hc _ _ _ hu _ hsub _ _ _ _ =>
      rcases hc with hc' | ⟨_, hc', _⟩
      · exact sNo_store_gen hi htv hpk hc' hu (Or.inl hsub) hlk hwa hpw hsto' hcab hno hrf
      · exact sNo_store_gen hi htv hpk hc' hu (Or.inl hsub) hlk hwa hpw hsto' hcab hno hrf
    | casShare _ _ _ _ hii _ _ _ _ _ _ _ _ _ _ => exact sNo_wordP hi hii hlk
    | casTake _ _ _ _ hii _ _ _ _ _ _ _ _ _ _ _ _ _ => exact sNo_wordP hi hii hlk
    | casEpoch _ _ _ _ _ hii _ _ _ _ _ _ => exact sNo_wordP hi hii hlk

/-- `FulSNo` holds: the PubOnly staging is discharged. -/
theorem fulSNo (p : Prog) : TermNoFul.FulSNo p :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hsto hT _ hW _ hca => sNo_writeFrom hsto hT hW hca

/-- **K-3(i)**, unconditionally. -/
theorem noFul_step_typed (p : Prog) : NoFulStep p :=
  TermNoFul.noFul_step p (fulSNo p)

end TermPubOnly

#print axioms TermPubOnly.sNo_Fd
#print axioms TermPubOnly.sNo_substTs_sub
#print axioms TermPubOnly.sNo_lay
#print axioms TermPubOnly.sNo_of_noOwn
#print axioms TermPubOnly.sNo_store
#print axioms TermPubOnly.sNo_store_ptr
#print axioms TermPubOnly.pubWords_store
#print axioms TermPubOnly.sNo_of_use
#print axioms TermPubOnly.sNo_writeFrom
#print axioms TermPubOnly.noFul_step_typed
