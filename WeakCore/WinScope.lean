import WeakCore.ShadowWinChain
import WeakCore.TermCertScope
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! The ♭ scope window premise (`ScopeAtB` along a solo run from `RunScope`).
Copies of W TermScope.peek_drfV / scope_termV with VarsOK ↦ VarsOKB
(only the `Lay` component is read), and TermCertScope.scopeAt_of over `ScopeOKB`. -/
namespace TermScope.Flat
open CoreLang CoreTerm CoreTyping TermRun TermSound TermStep TermMain TermScope TermSound.Flat
theorem peek_drfVB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx}
    {env : Env} (hv : VarsOKB ρ η σs cx.vars env) {a : At} {t : Ty} (hp : cx.peek a = .ok t)
    (hf : ∀ x, freeA x a = true → ∀ rt ws, lookupE env x = some (rt, ws) → drf1L rt = true) : drf1L t = true := by
  cases a with
  | var x =>
    obtain ⟨e, he, rfl⟩ := peek_var hp
    obtain ⟨rt, ws, hl, -, hlay⟩ := hv x e he
    exact drf1L_of_Lay hlay (hf x (by simp [freeA]) rt ws hl)
  | lit n => simp only [Cx.peek] at hp; cases hp; rfl
  | unit => simp only [Cx.peek] at hp; cases hp; rfl

theorem scope_termVB {p : Prog} {cx : Cx} {t : Expr} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {env : Env}
    (hT : Typed p cx t) {w : Nat → Ty} (hCk : TermA4.CkW p w cx t) (hv : VarsOKB ρ η σs cx.vars env)
    (hok : allOK t = true) (henv : EnvDRFI env t) (hns : ¬ SpawnT t) :
    StepScope cx t ∨ StepScopeR σs cx t := by
  have hat : ∀ a, (∀ x, freeA x a = true → freeB x t = true) → ∀ ty, cx.peek a = .ok ty → drf1L ty = true :=
    fun a ha ty hp => peek_drfVB hv hp (fun x hx => henv x (ha x hx))
  cases t with
  | let_ x op e =>
    simp only [allOK, Bool.and_eq_true] at hok
    have hat' : ∀ a ∈ opAts op, ∀ ty, cx.peek a = .ok ty → drf1L ty = true :=
      fun a ha => hat a (fun y hy => free_let_op ha hy)
    cases hT with
    | let_ hop _ =>
    cases op
    case load acq a =>
      exact .inl trivial  -- (LDST) OpScope load: any mode
    case store rel a v tok =>
      exact .inl trivial  -- (LDST) OpScope store: any mode
    case xchg a v =>
      exact .inl trivial  -- (G2) OpScope xchg: any mode
    case ldp acq a n0 n1 =>
      refine .inl (fun ty hp => ?_)
      cases hop with
      | ldp hp' hpr _ =>
        rw [hp] at hp'
        cases hp'
        exact pairRef_shapeG hpr
    case stp rel a v0 v1 tk =>
      refine .inl (fun ty hp => ?_)
      cases hop with
      | stpGive hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := word2Of_cases hw
        exact ⟨μ, _, _, hμ⟩
      | stpKeep hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := word2Of_cases hw
        exact ⟨μ, _, _, hμ⟩
    case fetch o acq rel a v =>
      refine .inl (fun ty hp => ?_)
      cases hop with
      | fetchCell hp' hnw hc =>
        rw [hp] at hp'; cases hp'
        rcases hc with hc | ⟨r, hc, -⟩
        · exact ⟨_, _, cell_cases hc⟩
        · exact ⟨_, _, cell_cases hc⟩  -- (G2) region fetch
      | fetchEpoch hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := wordOf_cases hw
        exact ⟨μ, _, hμ⟩
      | fetchShare hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := wordOf_cases hw
        exact ⟨μ, _, hμ⟩
    case publish a =>
      exact .inl (pubScope_of_pubPayDrf (CkW_pubOpDrf hCk))  -- (FLD e)
    case packT a σ τ =>
      simp only [opOK, opTys, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
      refine .inl ⟨?_, noIallV_of_drf1L σ (drf1L_of_drf1 σ hok.1.1.1)⟩
      show PackTOK σ τ
      unfold PackTOK
      split
      · exact hok.1.1.1
      · trivial
    case call f is a ts =>
      simp only [opOK, opTys, Bool.and_eq_true] at hok
      exact .inl (fun σ hσ => ⟨List.all_eq_true.1 hok.1.1 σ hσ, noIallV_of_drf1L σ (drf1L_of_drf1 σ (List.all_eq_true.1 hok.1.1 σ hσ))⟩)
    case new a _ =>
      exact .inl (fun ty c₁ hu => noIallV_of_drf1L ty
        (hat' a (by simp [opAts]) ty (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1))
    case newBuf n τ =>
      simp only [opOK, opTys, TermC1.opShareOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
      exact .inl (noIallV_of_drf1L τ (drf1L_of_drf1 τ hok.1))
    case validate y => simp [opOK] at hok
    case intoRgn r a =>
      refine .inl (show PubScope cx a ∧ RgnCpl cx a from ⟨fun ty hp μ u hu => ?_, fun u c₁ hu => ?_⟩)
      · exact pubScope_of_pubPayDrf (CkW_pubOpDrf hCk) ty hp μ u hu  -- (FLD e)
      · rcases hu with hu | ⟨n, k, u0, rfl, hu⟩
        · exact CkW_intoRgnCpl hCk hu
        · exact (CkW_intoRgnBuf_false hCk hu).elim
    case borrow s a => exact .inr trivial
    case freeze a => exact .inr trivial
    case endBorrow a => exact .inr trivial
    case mkTicket r N P v tk => simp [opOK] at hok
    case claim a tk => simp [opOK] at hok
    case spawn f a T ts => exact (hns trivial).elim
    case spawnI f is a T ts => exact (hns trivial).elim
    case ext n a => exact (hns trivial).elim
    all_goals exact .inl trivial
  | cas acq rel w e v t' ok fail =>
    refine .inl (fun ty hp => ?_)
    cases hT with
    | casCell hp' hnw hc =>
      rw [hp] at hp'; cases hp'
      rcases hc with hc | ⟨r, hc, -⟩
      · exact .inr (.inl ⟨_, cell_cases hc, by assumption⟩)
      · exact .inr (.inr ⟨r, _, cell_cases hc, hnw⟩)  -- (G2) region cas
    | casShare hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := wordOf_cases hw
      exact .inl ⟨μ, _, _, hμ⟩
    | casTake hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := wordOf_cases hw
      exact .inl ⟨μ, _, _, hμ⟩
    | casEpoch hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := wordOf_cases hw
      exact .inl ⟨μ, _, _, hμ⟩
  | casp acq rel w e0 e1 v0 v1 t' ok fail =>
    refine .inl (fun ty hp => ?_)
    cases hT with
    | caspE hp' _ hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := epairOf_cases hw
      exact ⟨μ, _, hμ, .inr ⟨_, _, rfl⟩⟩
    | caspBump hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := word2Of_cases hw
      exact ⟨μ, _, hμ, .inl ⟨_, _, rfl⟩⟩
    | caspMove hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := word2Of_cases hw
      exact ⟨μ, _, hμ, .inl ⟨_, _, rfl⟩⟩
    | caspTake hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := word2Of_cases hw
      exact ⟨μ, _, hμ, .inl ⟨_, _, rfl⟩⟩
  | tail f is a ts =>
    simp only [allOK, Bool.and_eq_true] at hok
    exact .inl (fun σ hσ => ⟨List.all_eq_true.1 hok.1 σ hσ, noIallV_of_drf1L σ (drf1L_of_drf1 σ (List.all_eq_true.1 hok.1 σ hσ))⟩)
  | region a rn pn tn e =>
    cases hT with
    | region hu _ hb1 hb2 _ =>
      refine .inl (show PubScope cx a ∧ RgnCpl cx a from ⟨fun ty hp μ u' hu' => ?_, fun u' c₁' hu' => ?_⟩)
      · -- (FLD e)
        have hp' := (use_cases hu).1
        rw [hp'] at hp; cases hp
        rcases hu' with hu' | ⟨ψ, hu'⟩ <;> cases hu'
        exact TermA4.CkW_regionDrf1 hCk hu
      · rcases hu' with hu' | ⟨n, k, u0, rfl, hu'⟩
        · rw [hu] at hu'; cases hu'; exact (TermA4.CkW_regionC1 hCk hu hb1 hb2).1
        · rw [hu] at hu'; cases hu'
    | regionBuf hu _ hb1 hb2 _ =>
      refine .inl (show PubScope cx a ∧ RgnCpl cx a from ⟨fun ty hp μ u' hu' => ?_, fun u' c₁' hu' => ?_⟩)
      · -- (FLD e)
        have hp' := (use_cases hu).1
        rw [hp'] at hp; cases hp
        rcases hu' with hu' | ⟨ψ, hu'⟩ <;> cases hu'
        exact TermA4.CkW_regionBufDrf1 hCk hu
      · rcases hu' with hu' | ⟨n', k', u0, rfl, hu'⟩
        · rw [hu] at hu'; cases hu'
        · rw [hu] at hu'; cases hu'; exact (TermA4.CkW_regionBufC1 hCk hu hb1 hb2).1
  | _ => exact .inl trivial

end TermScope.Flat

namespace TermCertScope.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermCertScope TermScope TermSound.Flat TermTyped.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **`ScopeAtB` at a `RunScope` configuration** (♭ `scopeAt_of`). -/
theorem scopeAtB_of {p : Prog} {i : Nat} {c : Cfg} (h0 : RunScopeI c) : ScopeAtB p i c := by
  intro th hth hns ρ η cx _ hT _ hi
  have h := h0 i th hth
  exact scopeD_of h.ok (TermScope.Flat.scope_termVB hT.1 hT.2 hi.2.1 h.ok h.env hns)

/-- **The scope premise of the ♭ window chain**, from `RunScope` at the window source. -/
theorem scopeAtB_solo {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg}
    (hp : ProgScopeOK p = true) (h0 : RunScopeI c) :
    ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0 :=
  fun _ hs _ => scopeAtB_of (solo_drf hp hs h0)
end TermCertScope.Flat
