import WeakCore.TermMainDefs
import WeakCore.TermBal

/-!
# TermScope: the scope obligations O0 and T1 (S10)

`O0` (`progT`) is the checker's soundness.  `T1` (`scope`) asks, at every
reachable thread step and for *every* typing context `cx` the invariant offers,
`StepScope cx th.term ∨ StepScopeR th.σs cx th.term`.

The typing context is not canonical, but its modes are pinned: `VarsOK` gives
`Lay σs t rt ws` for each variable, so `etok (skel rt) = etok (skel (close σs t))`,
and `skel` keeps every mode.  So it suffices that the *runtime* types of the
term's free variables mention no region mode (`drf`), which a syntactic program
check (`ProgScopeOK`, region-free interim) makes a run invariant (`ThScope`).
-/

namespace TermScope
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermSound TermStep TermMain

/-! ## Deep region-freedom of types -/

theorem drfM_shift (c : Nat) (μ : Mode) : drfM (μ.shift c) = drfM μ := by
  cases μ <;> rfl

theorem drf_shiftT : ∀ (t : Ty) (c : Nat), drf (t.shiftT c) = drf t := by
  intro t
  induction t with
  | tvar k => intro c; simp only [Ty.shiftT]; split <;> rfl
  | prod a b iha ihb => intro c; simp [Ty.shiftT, drf, iha, ihb]
  | sum a b iha ihb => intro c; simp [Ty.shiftT, drf, iha, ihb]
  | code a b iha ihb => intro c; simp [Ty.shiftT, drf, iha, ihb]
  | array i t ih => intro c; simp [Ty.shiftT, drf, ih]
  | ptr μ t ih => intro c; simp [Ty.shiftT, drf, ih]
  | ptrOpt μ t ih => intro c; simp [Ty.shiftT, drf, ih]
  | loc μ t ih => intro c; simp [Ty.shiftT, drf, ih]
  | mu t ih => intro c; simp [Ty.shiftT, drf, ih]
  | tex κ t ih => intro c; simp [Ty.shiftT, drf, ih]
  | iall t ih => intro c; simp [Ty.shiftT, drf, ih]
  | iex t ih => intro c; simp [Ty.shiftT, drf, ih]
  | refine t ψ ih => intro c; simp [Ty.shiftT, drf, ih]
  | _ => intro c; rfl

theorem drf_shiftI : ∀ (t : Ty) (c : Nat), drf (t.shiftI c) = drf t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c; simp [Ty.shiftI, drf, iha, ihb]
  | sum a b iha ihb => intro c; simp [Ty.shiftI, drf, iha, ihb]
  | code a b iha ihb => intro c; simp [Ty.shiftI, drf, iha, ihb]
  | array i t ih => intro c; simp [Ty.shiftI, drf, ih]
  | ptr μ t ih => intro c; simp [Ty.shiftI, drf, ih, drfM_shift]
  | ptrOpt μ t ih => intro c; simp [Ty.shiftI, drf, ih, drfM_shift]
  | loc μ t ih => intro c; simp [Ty.shiftI, drf, ih, drfM_shift]
  | mu t ih => intro c; simp [Ty.shiftI, drf, ih]
  | tex κ t ih => intro c; simp [Ty.shiftI, drf, ih]
  | iall t ih => intro c; simp [Ty.shiftI, drf, ih]
  | iex t ih => intro c; simp [Ty.shiftI, drf, ih]
  | refine t ψ ih => intro c; simp [Ty.shiftI, drf, ih]
  | _ => intro c; rfl

theorem drf_shiftTN : ∀ (n : Nat) (t : Ty), drf (shiftTN n t) = drf t
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftTN, drf_shiftT, drf_shiftTN n t]

theorem drf_shiftIN : ∀ (n : Nat) (t : Ty), drf (shiftIN n t) = drf t
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftIN, drf_shiftI, drf_shiftIN n t]

/-- Every type of a list is `drf`. -/
def AllDrf (σs : List Ty) : Prop := ∀ σ ∈ σs, drf σ = true

/-- Substitution of `drf` types keeps `drf`. -/
theorem drf_substTs {σs : List Ty} (hσ : AllDrf σs) :
    ∀ (t : Ty) (c d : Nat), drf t = true → drf (substTs σs c d t) = true := by
  intro t
  induction t with
  | tvar k =>
    intro c d _
    simp only [substTs]
    split
    · rfl
    · split
      · rename_i σ h
        rw [drf_shiftIN, drf_shiftTN]
        exact hσ σ (List.mem_of_getElem? h)
      · rfl
  | prod a b iha ihb => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | code a b iha ihb => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | array i t ih => intro c d h; exact ih c d h
  | ptr μ t ih => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih c d h.2⟩
  | ptrOpt μ t ih => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih c d h.2⟩
  | loc μ t ih => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih c d h.2⟩
  | mu t ih => intro c d h; exact ih (c + 1) d h
  | tex κ t ih => intro c d h; exact ih (c + 1) d h
  | iall t _ => intro c d h; simp [drf] at h
  | iex t ih => intro c d h; exact ih c (d + 1) h
  | refine t ψ ih => intro c d h; exact ih c d h
  | _ => intro c d _; rfl

/-- And substitution reflects region modes: a substituted type that is `drf`
came from a `drf` type. -/
theorem drf_of_substTs (σs : List Ty) :
    ∀ (t : Ty) (c d : Nat), drf (substTs σs c d t) = true → drf t = true := by
  intro t
  induction t with
  | prod a b iha ihb => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | code a b iha ihb => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | array i t ih => intro c d h; exact ih c d h
  | ptr μ t ih => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih c d h.2⟩
  | ptrOpt μ t ih => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih c d h.2⟩
  | loc μ t ih => intro c d h; simp only [substTs, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih c d h.2⟩
  | mu t ih => intro c d h; exact ih (c + 1) d h
  | tex κ t ih => intro c d h; exact ih (c + 1) d h
  | iall t _ => intro c d h; simp [substTs, drf] at h
  | iex t ih => intro c d h; exact ih c (d + 1) h
  | refine t ψ ih => intro c d h; exact ih c d h
  | _ => intro c d _; rfl

theorem drf_close {σs : List Ty} (hσ : AllDrf σs) {t : Ty} (h : drf t = true) : drf (close σs t) = true :=
  drf_substTs hσ t 0 0 h

theorem drf_of_close {σs : List Ty} {t : Ty} (h : drf (close σs t) = true) : drf t = true :=
  drf_of_substTs σs t 0 0 h

theorem drf_substT : ∀ (t : Ty) (j : Nat) (s : Ty), drf s = true → drf t = true → drf (Ty.substT j s t) = true := by
  intro t
  induction t with
  | tvar k =>
    intro j s hs _
    simp only [Ty.substT]
    split
    · exact hs
    · split <;> rfl
  | prod a b iha ihb => intro j s hs h; simp only [Ty.substT, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | sum a b iha ihb => intro j s hs h; simp only [Ty.substT, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | code a b iha ihb => intro j s hs h; simp only [Ty.substT, drf, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | array i t ih => intro j s hs h; exact ih j s hs h
  | ptr μ t ih => intro j s hs h; simp only [Ty.substT, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih j s hs h.2⟩
  | ptrOpt μ t ih => intro j s hs h; simp only [Ty.substT, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih j s hs h.2⟩
  | loc μ t ih => intro j s hs h; simp only [Ty.substT, drf, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih j s hs h.2⟩
  | mu t ih => intro j s hs h; exact ih (j + 1) (s.shiftT 0) (by rw [drf_shiftT]; exact hs) h
  | tex κ t ih => intro j s hs h; exact ih (j + 1) (s.shiftT 0) (by rw [drf_shiftT]; exact hs) h
  | iall t _ => intro j s hs h; simp [drf] at h
  | iex t ih => intro j s hs h; exact ih j (s.shiftI 0) (by rw [drf_shiftI]; exact hs) h
  | refine t ψ ih => intro j s hs h; exact ih j s hs h
  | _ => intro j s _ _; rfl

theorem drf_unfold1 {t : Ty} (h : drf t = true) : drf (unfold1 t) = true := by
  cases t <;> simp only [unfold1] <;> try exact h
  exact drf_substT _ 0 _ h h

theorem drf_skel : ∀ t : Ty, drf (skel t) = drf t := by
  intro t
  induction t with
  | prod a b iha ihb => simp [skel, drf, iha, ihb]
  | sum a b iha ihb => simp [skel, drf, iha, ihb]
  | code a b iha ihb => simp [skel, drf, iha, ihb]
  | array i t ih => simp [skel, drf, ih]
  | ptr μ t ih => cases μ <;> simp [skel, skelM, drf, drfM, ih]
  | ptrOpt μ t ih => cases μ <;> simp [skel, skelM, drf, drfM, ih]
  | loc μ t ih => cases μ <;> simp [skel, skelM, drf, drfM, ih]
  | mu t ih => simp [skel, drf, ih]
  | tex κ t ih => simp [skel, drf, ih]
  | iall t ih => simp [skel, drf, ih]
  | iex t ih => simp [skel, drf, ih]
  | refine t ψ ih =>
    simp only [skel, drf]
    rw [← ih]
    cases skel t <;> rfl
  | _ => rfl

theorem drf_etok : ∀ t : Ty, drf (etok t) = drf t := by
  intro t
  induction t with
  | prod a b iha ihb => simp [etok, drf, iha, ihb]
  | sum a b iha ihb => simp [etok, drf, iha, ihb]
  | code a b iha ihb => simp [etok, drf, iha, ihb]
  | array i t ih => simp [etok, drf, ih]
  | ptr μ t ih => simp [etok, drf, ih]
  | ptrOpt μ t ih => simp [etok, drf, ih]
  | loc μ t ih => simp [etok, drf, ih]
  | refine t ψ ih => simp [etok, drf, ih]
  | _ => rfl

theorem rgnFree_of_drf : ∀ t : Ty, drf t = true → rgnFree t = true := by
  intro t
  induction t with
  | prod a b iha ihb => intro h; simp only [drf, rgnFree, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | sum a b iha ihb => intro h; simp only [drf, rgnFree, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | array i t ih => intro h; exact ih h
  | ptr μ t _ => intro h; cases μ <;> simp_all [drf, drfM, rgnFree]
  | ptrOpt μ t _ => intro h; cases μ <;> simp_all [drf, drfM, rgnFree]
  | loc μ t _ => intro h; cases μ <;> simp_all [drf, drfM, rgnFree]
  | mu t ih => intro h; exact ih h
  | tex κ t ih => intro h; exact ih h
  | iall t _ => intro h; simp [drf] at h
  | iex t ih => intro h; exact ih h
  | refine t ψ ih => intro h; exact ih h
  | _ => intro _; rfl

theorem noIallV_of_drf : ∀ t : Ty, drf t = true → TermTv.noIallV t = true := by
  intro t
  induction t with
  | prod a b iha ihb => intro h; simp only [drf, TermTv.noIallV, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | sum a b iha ihb => intro h; simp only [drf, TermTv.noIallV, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | array i t ih => intro h; exact ih h
  | mu t ih => intro h; exact ih h
  | tex κ t ih => intro h; exact ih h
  | iex t ih => intro h; exact ih h
  | refine t ψ ih => intro h; exact ih h
  | iall t _ => intro h; simp [drf] at h
  | _ => intro _; rfl

/-- **The pin**: a layout-agreeing static type of a `drf` runtime type is `drf`. -/
theorem drf_of_Lay {σs : List Ty} {t rt : Ty} {ws : List Word} (h : Lay σs t rt ws) (hd : drf rt = true) :
    drf t = true := by
  have h2 := h.2.1
  have : drf (etok (skel rt)) = drf (etok (skel (close σs t))) := by rw [h2]
  rw [drf_etok, drf_etok, drf_skel, drf_skel, hd] at this
  exact drf_of_close this.symm

/-! ## The syntactic program check (`ProgScopeOK`, region-free interim) -/

/-- Is `x` the atom's variable? -/
def freeA (x : String) : At → Bool
  | .var y => x == y
  | _ => false

/-- The atoms an operation reads (`validate`'s variable included). -/
def opAts : Op → List At
  | .atom a => [a]
  | .pair a b => [a, b]
  | .inl _ a => [a]
  | .inr _ a => [a]
  | .add a b => [a, b]
  | .sub a b => [a, b]
  | .new a => [a]
  | .null _ _ => []
  | .fold a _ => [a]
  | .publish a => [a]
  | .intoRgn _ a => [a]
  | .newBuf n _ => [n]
  | .idx b i => [b, i]
  | .bufInit b i v => [b, i, v]
  | .fld _ a => [a]
  | .load _ a => [a]
  | .store _ a v tok => [a, v] ++ tok.toList
  | .fence _ => []
  | .mkWord _ _ v tok => [v, tok]
  | .pack a _ _ => [a]
  | .packT a _ _ => [a]
  | .validate y => [.var y]
  | .call _ _ a _ => [a]
  | .spawn _ a _ _ => [a]
  | .borrow _ t => [t]
  | .endBorrow t => [t]
  | .xchg a v => [a, v]
  | .fnptr _ => []
  | .callc f a => [f, a]
  | .rem a n => [a, n]
  | .nameI a => [a]
  | .xchgAt b i v => [b, i, v]
  | .loadAt b i => [b, i]
  | .bits _ a b => [a, b]
  | .bit1 _ a => [a]
  | .vmatch lo hi b => [lo, hi, b]
  | .band a m => [a, m]
  | .zero _ => []
  | .loadAtF b i _ => [b, i]
  | .xchgAtF b i _ v => [b, i, v]
  | .freeze t => [t]
  | .cvt _ _ a => [a]
  | .toInt a => [a]
  | .asLanes _ _ a => [a]
  | .fop _ a b => [a, b]
  | .fcmp _ a b => [a, b]
  | .fop1 _ a => [a]
  | .lane a j => [a, j]
  | .setLane a j v => [a, j, v]
  | .ldl b i => [b, i]
  | .stl b i v => [b, i, v]
  | .ldlw b wi j => [b, wi, j]
  | .stlw b wi j v => [b, wi, j, v]
  | .mkWord2 _ _ v0 v1 tok => [v0, v1, tok]
  | .ldp _ a _ _ => [a]
  | .stp _ a v0 v1 tok => [a, v0, v1, tok]
  | .mkEPair _ _ v0 v1 => [v0, v1]
  | .mkTicket _ _ _ v tok => [v, tok]
  | .claim a tok => [a, tok]
  | .fetch _ _ _ a v => [a, v]

/-- (`ProgScopeOK`, per operation) not `validate` or `intoRgn`, and (D5) not a
ticket-lock operation (`mkTicket`, `claim`); every annotation `drf`, including
`null`'s mode. -/
def opOK : Op → Bool
  | .validate _ | .intoRgn _ _ => false
  | .mkTicket _ _ _ _ _ | .claim _ _ => false
  | .null μ τ => drfM μ && drf τ
  | op => (opTys op).all drf

/-- The components a reference type names are `drf` with it. -/
theorem drf_cellOf {t : Ty} {μ : Mode} {u : Ty} (h : cellOf t = some (μ, u)) (ht : drf t = true) :
    drfM μ = true ∧ drf u = true := by
  cases t <;> simp [cellOf] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simpa [drf] using ht

theorem drf_bufElem {t : Ty} {μ : Mode} {u : Ty} (h : bufElem t = some (μ, u)) (ht : drf t = true) :
    drfM μ = true ∧ drf u = true := by
  unfold bufElem at h
  split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp_all [drf]

theorem drf_compOff : ∀ (u : Ty) (p : List Nat) {c : Ty} {o : Nat}, compOff u p = some (c, o) → drf u = true →
    drf c = true := by
  intro u p
  induction p generalizing u with
  | nil => intro c o h hu; simp [compOff] at h; rw [← h.1]; exact hu
  | cons j p ih =>
    intro c o h hu
    cases u <;> try (simp [compOff] at h)
    rename_i a b
    simp only [drf, Bool.and_eq_true] at hu
    match j, h with
    | 0, h => exact ih a h hu.1
    | 1, h =>
      simp only [compOff] at h
      cases hacc : accs a with
      | none => simp [hacc] at h
      | some us =>
        cases hc : compOff b p with
        | none => simp [hacc, hc] at h
        | some co =>
          simp [hacc, hc] at h
          rw [← h.1]
          exact ih b hc hu.2
    | n + 2, h => simp [compOff] at h

theorem drf_fetchRtTy (t : Ty) : drf (fetchRtTy t) = true := by
  unfold fetchRtTy
  split
  · split <;> rfl
  · rfl

/-- Does `x` occur free in the term?  Binders are exactly the variables the
runtime pushes on the environment (`tstep`). -/
def freeB (x : String) : Expr → Bool
  | .let_ y op e => (opAts op).any (freeA x) || (x != y && freeB x e)
  | .split a y z e => freeA x a || (x != y && x != z && freeB x e)
  | .unpack a _ y e => freeA x a || (x != y && freeB x e)
  | .unpackT a _ y e => freeA x a || (x != y && freeB x e)
  | .region a _ p t e => freeA x a || (x != p && x != t && freeB x e)
  | .openPub a _ p c e => freeA x a || (x != p && x != c && freeB x e)
  | .case a y e₁ z e₂ => freeA x a || (x != y && freeB x e₁) || (x != z && freeB x e₂)
  | .ifnull a e₁ y e₂ => freeA x a || freeB x e₁ || (x != y && freeB x e₂)
  | .parity a _ e₁ e₂ => freeA x a || freeB x e₁ || freeB x e₂
  | .ifeq a b e₁ e₂ => freeA x a || freeA x b || freeB x e₁ || freeB x e₂
  | .cas _ _ w e v t ok fail => freeA x w || freeA x e || freeA x v || (x != t && freeB x ok) || freeB x fail
  | .casp _ _ w e0 e1 v0 v1 t ok fail => freeA x w || freeA x e0 || freeA x e1 || freeA x v0 || freeA x v1 ||
      (x != t && freeB x ok) || freeB x fail
  | .ret a => freeA x a
  | .tail _ _ a _ => freeA x a

/-- (`ProgScopeOK`, every subterm) every operation `opOK`; the region
reference `region`/`openPub` bind is dead in the body (the token or capability
may be used); `tail`'s type arguments `drf`. -/
def allOK : Expr → Bool
  | .let_ _ op e => opOK op && allOK e
  | .split _ _ _ e => allOK e
  | .unpack _ _ _ e => allOK e
  | .unpackT _ _ _ e => allOK e
  | .region _ _ p _ e => !freeB p e && allOK e
  | .openPub _ _ p _ e => !freeB p e && allOK e
  | .case _ _ e₁ _ e₂ => allOK e₁ && allOK e₂
  | .ifnull _ e₁ _ e₂ => allOK e₁ && allOK e₂
  | .parity _ _ e₁ e₂ => allOK e₁ && allOK e₂
  | .ifeq _ _ e₁ e₂ => allOK e₁ && allOK e₂
  | .cas _ _ _ _ _ _ ok fail => allOK ok && allOK fail
  | .casp _ _ _ _ _ _ _ _ ok fail => allOK ok && allOK fail
  | .ret _ => true
  | .tail _ _ _ ts => ts.all drf

/-- **The program scope check** (S10 T1, region-free interim): every code
block has `drf` signature types and an `allOK` body. -/
def ProgScopeOK (p : Prog) : Bool := p.all fun d => drf d.argTy && drf d.retTy && allOK d.body

theorem ProgScopeOK.decl {p : Prog} (hp : ProgScopeOK p = true) {d : Decl} (hd : d ∈ p) :
    drf d.argTy = true ∧ drf d.retTy = true ∧ allOK d.body = true := by
  have h := List.all_eq_true.1 hp d hd
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## The run invariant -/

/-- Every free variable of `t` has a `drf` runtime type in `env`. -/
def EnvDRF (env : Env) (t : Expr) : Prop :=
  ∀ x, freeB x t = true → ∀ rt ws, lookupE env x = some (rt, ws) → drf rt = true

/-- A stack frame: its continuation checked, its type arguments and return
type `drf`, and its free variables (other than the returned one) `drf`. -/
structure FrDRF (f : Frame) : Prop where
  ok : allOK f.body = true
  σs : AllDrf f.σs
  ty : drf f.ty = true
  env : ∀ x, freeB x f.body = true → x ≠ f.x → ∀ rt ws, lookupE f.env x = some (rt, ws) → drf rt = true

/-- **The per-thread run invariant.** -/
structure ThScope (th : TTh) : Prop where
  ok : allOK th.term = true
  σs : AllDrf th.σs
  env : EnvDRF th.env th.term
  stk : ∀ f ∈ th.stack, FrDRF f

/-- **The run invariant**: every thread satisfies `ThScope`. -/
def RunScope (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ThScope th

theorem lookupE_cons (x y : String) (t : Ty) (ws : List Word) (env : Env) :
    lookupE ((x, t, ws) :: env) y = if x = y then some (t, ws) else lookupE env y := by
  unfold lookupE
  by_cases h : x = y
  · subst h; simp [List.find?]
  · have : (x == y) = false := by simpa using h
    simp [List.find?, h, this]

theorem evalAt_drf {env : Env} {a : At} {t : Ty} {ws : List Word}
    (hf : ∀ x, freeA x a = true → ∀ rt ws, lookupE env x = some (rt, ws) → drf rt = true)
    (h : evalAt env a = some (t, ws)) : drf t = true := by
  cases a with
  | var x => exact hf x (by simp [freeA]) t ws h
  | lit n => simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | unit => simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl

/-- `ol` of an option. -/
theorem mem_ol {β : Type} {o : Option β} {r : β} (h : r ∈ ol o) : o = some r := by
  cases o <;> simp_all [ol]

theorem drf_cellOf' {t : Ty} {p : Mode × Ty} (h : cellOf t = some p) : drf t = true →
    drfM p.1 = true ∧ drf p.2 = true := drf_cellOf h

theorem drf_bufElem' {t : Ty} {p : Mode × Ty} (h : bufElem t = some p) : drf t = true →
    drfM p.1 = true ∧ drf p.2 = true := drf_bufElem h

theorem drf_compOff' {u : Ty} {ps : List Nat} {q : Ty × Nat} (h : compOff u ps = some q) : drf u = true →
    drf q.1 = true := drf_compOff u ps h

theorem drf_unfold1_prod {u c1 c2 : Ty} (h : unfold1 u = .prod c1 c2) (hu : drf u = true) :
    drf c1 = true ∧ drf c2 = true := by
  have := drf_unfold1 hu
  rw [h] at this
  simpa [drf] using this

macro "fwd" : tactic => `(tactic| (
  all_goals (try (have := @drf_cellOf' _ _ (by assumption)))
  all_goals (try (have := @drf_bufElem' _ _ (by assumption)))
  all_goals (try (have := @drf_compOff' _ _ _ (by assumption)))
  all_goals (try (have := @drf_cellOf _ _ _ (by assumption)))
  all_goals (try (have := @drf_bufElem _ _ _ (by assumption)))
  all_goals (try (have := @drf_compOff _ _ _ _ (by assumption)))
  all_goals (try (have := @drf_unfold1_prod _ _ _ (by assumption)))
  all_goals (try (have := List.mem_of_find?_eq_some (by assumption)))))

macro "olcase" : tactic => `(tactic| (
  intro r hr
  have h := mem_ol hr
  repeat' (first
    | (obtain ⟨_, hh, h⟩ := h)
    | (split at h)
    | (simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        reduceCtorEq] at h))
  all_goals subst_vars
  fwd
  all_goals simp_all [drf, drfM]))

/- **Every outcome of `evalOp` has a `drf` type** when the operation is
checked, its atoms' types, the type arguments, and the program's signatures are
`drf`. -/

set_option maxHeartbeats 8000000 in
theorem evalOp_drf {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    (hok : opOK op = true) (hσ : AllDrf σs)
    (hA0 : ∀ a ∈ opAts op, ∀ t ws, evalAt env a = some (t, ws) → drf t = true)
    (hp : ∀ d ∈ g.p, drf d.argTy = true ∧ drf d.retTy = true) :
    ∀ r ∈ evalOp g env σs s op, drf r.2.1 = true := by
  have hc : ∀ {t}, drf t = true → drf (close σs t) = true := fun h => drf_close hσ h
  have hA : ∀ a ∈ opAts op, ∀ p, evalAt env a = some p → drf p.1 = true := fun a ha p h => hA0 a ha p.1 p.2 h
  clear hA0
  cases op <;> simp only [opAts, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    List.cons_append, List.nil_append] at hA <;> simp only [opOK, opTys, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hok
  case add => olcase
  case sub => olcase
  case publish => olcase
  case fop => olcase
  case fcmp => olcase
  case fop1 => olcase
  case lane => olcase
  case setLane => olcase
  case idx => olcase
  case fld => olcase
  case stl =>
    intro r hr
    simp only [evalOp] at hr
    repeat' split at hr
    all_goals (try simp only [List.not_mem_nil] at hr)
    simp only [List.mem_flatMap] at hr
    obtain ⟨_, -, hr⟩ := hr
    split at hr
    · simp only [List.mem_map] at hr
      obtain ⟨_, -, rfl⟩ := hr
      rfl
    · simp at hr
  case stlw =>
    intro r hr
    simp only [evalOp] at hr
    repeat' split at hr
    all_goals (try simp only [List.not_mem_nil] at hr)
    simp only [List.mem_flatMap] at hr
    obtain ⟨_, -, hr⟩ := hr
    split at hr
    · simp only [List.mem_map] at hr
      obtain ⟨_, -, rfl⟩ := hr
      rfl
    · simp at hr
  all_goals (simp only [evalOp] <;> (repeat' split) <;>
    simp_all [ol, drf, drfM, Option.bind_eq_some_iff] <;> intros <;> subst_vars <;>
    (try simp_all [drf, drfM, drf_fetchRtTy]))
  fwd
  all_goals (try simp_all [drf, drfM])

/-! ## `tstep` keeps the run invariant -/

theorem envDRF_cons {env : Env} {t : Expr} {x : String} {T : Ty} {ws : List Word}
    (hT : freeB x t = true → drf T = true)
    (h : ∀ y, freeB y t = true → y ≠ x → ∀ rt ws, lookupE env y = some (rt, ws) → drf rt = true) :
    EnvDRF ((x, T, ws) :: env) t := by
  intro y hy rt ws' hl
  rw [lookupE_cons] at hl
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hl
    rw [← hl.1]
    exact hT hy
  · simp only [hxy, ↓reduceIte] at hl
    exact h y hy (Ne.symm hxy) rt ws' hl

theorem envDRF_sub {env : Env} {t t' : Expr} (h : EnvDRF env t) (hs : ∀ y, freeB y t' = true → freeB y t = true) :
    EnvDRF env t' := fun y hy => h y (hs y hy)

theorem ThScope_withS {th : TTh} (s : St) (h : ThScope th) : ThScope (withS th s) := ⟨h.ok, h.σs, h.env, h.stk⟩

theorem allDrf_cons {σ : Ty} {σs : List Ty} (h1 : drf σ = true) (h2 : AllDrf σs) : AllDrf (σ :: σs) := by
  intro τ hτ
  rcases List.mem_cons.1 hτ with rfl | hτ
  · exact h1
  · exact h2 τ hτ

theorem allDrf_inst {σs ts : List Ty} (hσ : AllDrf σs) (hts : ts.all drf = true) :
    AllDrf (ts.map (close σs)).reverse := by
  intro τ hτ
  rw [List.mem_reverse, List.mem_map] at hτ
  obtain ⟨σ, hσ', rfl⟩ := hτ
  exact drf_close hσ (List.all_eq_true.1 hts σ hσ')

theorem drf_retOf {tf t : Ty} (h1 : drf tf = true) (h2 : drf t = true) : drf (retOf tf t) = true := by
  unfold retOf
  split
  · simp only [drf, Bool.and_eq_true] at h1; exact h1.2
  · exact h2

/-- Entering a code block of a checked program from a `drf` frame. -/
theorem enter_drf {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At} (hp : ProgScopeOK g.p = true)
    (hσ : AllDrf th.σs) (hts : ts.all drf = true) (h : enter g th f ts a = some th') :
    allOK th'.term = true ∧ AllDrf th'.σs ∧ EnvDRF th'.env th'.term ∧ th'.stack = th.stack := by
  unfold enter at h
  cases hd : g.p.find? (·.name == f) with
  | none => simp [hd] at h
  | some d =>
  cases hev : evalAt th.env a with
  | none => simp [hd, hev] at h
  | some p =>
  simp [hd, hev] at h
  subst h
  obtain ⟨hA, -, hB⟩ := ProgScopeOK.decl hp (List.mem_of_find?_eq_some hd)
  have hσ' := allDrf_inst hσ hts
  refine ⟨hB, hσ', envDRF_cons (fun _ => drf_close hσ' hA) (fun y _ _ rt ws h => by simp [lookupE] at h), rfl⟩

theorem callFrame_drf {g : G} {th : TTh} {f : String} {ts : List Ty} {x : String} {e : Expr} {fr : Frame}
    (hp : ProgScopeOK g.p = true) (hσ : AllDrf th.σs) (hts : ts.all drf = true) (he : allOK e = true)
    (hfv : ∀ y, freeB y e = true → y ≠ x → ∀ rt ws, lookupE th.env y = some (rt, ws) → drf rt = true)
    (h : callFrame g th f ts x e = some fr) : FrDRF fr := by
  unfold callFrame at h
  cases hd : g.p.find? (·.name == f) with
  | none => simp [hd] at h
  | some d =>
  simp [hd] at h
  subst h
  obtain ⟨-, hR, -⟩ := ProgScopeOK.decl hp (List.mem_of_find?_eq_some hd)
  exact ⟨he, hσ, drf_close (allDrf_inst hσ hts) hR, hfv⟩

/-- The let-bound atoms are free in the `let`. -/
theorem free_let_op {y x : String} {op : Op} {e : Expr} {a : At} (ha : a ∈ opAts op) (hy : freeA y a = true) :
    freeB y (.let_ x op e) = true := by
  simp only [freeB, Bool.or_eq_true, List.any_eq_true]
  exact Or.inl ⟨a, ha, hy⟩

theorem free_let_body {y x : String} {op : Op} {e : Expr} (hy : freeB y e = true) (hne : y ≠ x) :
    freeB y (.let_ x op e) = true := by
  simp [freeB, hy, hne]

/-- **`tstep` keeps `ThScope`** for a checked program. -/
theorem tstep_drf {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {r : WeakMem.Memory × List WeakMem.Ts × TTh} (hp : ProgScopeOK g.p = true) (h : ThScope th)
    (hr : r ∈ tstep g mem pairs th) : ThScope r.2.2 := by
  obtain ⟨hok, hσ, henv, hstk⟩ := h
  unfold tstep at hr
  split at hr
  · -- call
    rename_i _ x f is a ts e heq
    rw [heq] at hok henv
    simp only [allOK, opOK, opTys, Bool.and_eq_true] at hok
    cases hcf : callFrame g th f ts x e with
    | none => simp [hcf, ol] at hr
    | some fr =>
      cases hen : enter g { th with stack := fr :: th.stack } f ts a with
      | none => simp [hcf, hen, ol] at hr
      | some th' =>
        simp only [hcf, hen, ol, Option.bind_some, Option.map_some, Option.toList_some,
          List.mem_singleton] at hr
        subst hr
        obtain ⟨h1, h2, h3, h4⟩ := enter_drf (th := { th with stack := fr :: th.stack }) hp hσ hok.1 hen
        refine ⟨h1, h2, h3, ?_⟩
        rw [h4]
        intro f' hf'
        rcases List.mem_cons.1 hf' with rfl | hf'
        · exact callFrame_drf hp hσ hok.1 hok.2 (fun y hy hne => henv y (free_let_body hy hne)) hcf
        · exact hstk f' hf'
  · -- callc
    rename_i _ x f a e heq
    rw [heq] at hok henv
    simp only [allOK, opOK, opTys, List.all_nil, Bool.and_eq_true, Bool.true_and] at hok
    split at hr
    · rename_i tf w hev
      split at hr
      · rename_i i _
        split at hr
        · rename_i d hd
          have hdp : d ∈ g.p := List.mem_of_getElem? hd
          have htf : drf tf = true :=
            evalAt_drf (fun y hy => henv y (free_let_op (by simp [opAts]) hy)) hev
          cases hcf : callFrame g th d.name [] x e with
          | none => simp [hcf, ol] at hr
          | some fr =>
            cases hen : enter g { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack } d.name [] a with
            | none => simp [hcf, hen, ol] at hr
            | some th' =>
              simp only [hcf, hen, ol, Option.bind_some, Option.map_some, Option.toList_some,
                List.mem_singleton] at hr
              subst hr
              obtain ⟨h1, h2, h3, h4⟩ := enter_drf (th := { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack }) hp hσ rfl hen
              refine ⟨h1, h2, h3, ?_⟩
              rw [h4]
              intro f' hf'
              rcases List.mem_cons.1 hf' with rfl | hf'
              · have hF := callFrame_drf hp hσ rfl hok (fun y hy hne => henv y (free_let_body hy hne)) hcf
                exact ⟨hF.ok, hF.σs, drf_retOf htf hF.ty, hF.env⟩
              · exact hstk f' hf'
        · simp at hr
      · simp at hr
    · simp at hr
  · -- every other let
    rename_i _ x op e _ _ heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true] at hok
    simp only [List.mem_map] at hr
    obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
    have ht : drf t = true := evalOp_drf hok.1 hσ
      (fun a ha t ws hev => evalAt_drf (fun y hy => henv y (free_let_op ha hy)) hev)
      (fun d hd => let h := ProgScopeOK.decl hp hd; ⟨h.1, h.2.1⟩) _ hm
    exact ThScope_withS _ ⟨hok.2, hσ, envDRF_cons (fun _ => ht)
      (fun y hy hne => henv y (free_let_body hy hne)), hstk⟩
  · -- split
    rename_i _ a x y e heq
    rw [heq] at hok henv
    split at hr
    · rename_i u w ws hev
      split at hr
      · simp only [List.mem_singleton] at hr
        subst hr
        have hd := evalAt_drf (fun z hz => henv z (by simp [freeB, hz])) hev
        simp only [drf, Bool.and_eq_true] at hd
        refine ⟨hok, hσ, envDRF_cons (fun _ => hd.2) (fun z hz hzy => ?_), hstk⟩
        intro rt ws' hl
        rw [lookupE_cons] at hl
        by_cases hxz : x = z
        · subst hxz
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hl
          rw [← hl.1]; exact hd.1
        · simp only [hxz, ↓reduceIte] at hl
          exact henv z (by simp [freeB, hz, hzy, Ne.symm hxz]) rt ws' hl
      · simp at hr
    · simp at hr
  · -- unpack
    rename_i _ a i x e heq
    rw [heq] at hok henv
    split at hr
    · rename_i b ws hev
      simp only [List.mem_singleton] at hr
      subst hr
      have hd := evalAt_drf (fun z hz => henv z (by simp [freeB, hz])) hev
      exact ⟨hok, hσ, envDRF_cons (fun _ => hd)
        (fun z hz hzx => henv z (by simp [freeB, hz, hzx])), hstk⟩
    · simp at hr
  · -- unpackT
    rename_i _ a α x e heq
    rw [heq] at hok henv
    split at hr
    · rename_i κ b ws hev
      simp only [List.mem_singleton] at hr
      subst hr
      have hd := evalAt_drf (fun z hz => henv z (by simp [freeB, hz])) hev
      exact ⟨hok, allDrf_cons rfl hσ, envDRF_cons (fun _ => drf_substT b 0 .unit rfl hd)
        (fun z hz hzx => henv z (by simp [freeB, hz, hzx])), hstk⟩
    · simp at hr
  · -- region
    rename_i _ a rn pn tn e heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    have key : ∀ (P : Ty) (ws : List Word),
        EnvDRF ((tn, .tok (.lit 0) none, []) :: (pn, P, ws) :: th.env) e := by
      intro P ws
      refine envDRF_cons (fun _ => rfl) (fun z hz hzt rt ws' hl => ?_)
      rw [lookupE_cons] at hl
      by_cases hpz : pn = z
      · subst hpz; rw [hok.1] at hz; cases hz
      · simp only [hpz, ↓reduceIte] at hl
        exact henv z (by simp [freeB, hz, hzt, Ne.symm hpz]) rt ws' hl
    split at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      exact ThScope_withS _ ⟨hok.2, hσ, key _ _, hstk⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      exact ThScope_withS _ ⟨hok.2, hσ, key _ _, hstk⟩
    · simp at hr
  · -- openPub
    rename_i _ a rn pn cn e heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    split at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨hok.2, hσ, envDRF_cons (fun _ => rfl) (fun z hz hzt rt ws' hl => ?_), hstk⟩
      rw [lookupE_cons] at hl
      by_cases hpz : pn = z
      · subst hpz; rw [hok.1] at hz; cases hz
      · simp only [hpz, ↓reduceIte] at hl
        exact henv z (by simp [freeB, hz, hzt, Ne.symm hpz]) rt ws' hl
    · simp at hr
  · -- case
    rename_i _ a x e₁ y e₂ heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true] at hok
    split at hr
    · rename_i t u w ws hev
      have hd := evalAt_drf (fun z hz => henv z (by simp [freeB, hz])) hev
      simp only [drf, Bool.and_eq_true] at hd
      simp only [List.mem_flatMap, List.mem_map] at hr
      obtain ⟨⟨s1, j, q⟩, -, ⟨s2, q'⟩, -, rfl⟩ := hr
      apply ThScope_withS
      by_cases hj : j < (armsOf u).length
      · simp only [hj, ite_true]
        exact ⟨hok.1, hσ, envDRF_cons (fun _ => hd.1)
          (fun z hz hzx => henv z (by simp [freeB, hz, hzx])), hstk⟩
      · simp only [hj, ite_false]
        exact ⟨hok.2, hσ, envDRF_cons (fun _ => hd.2)
          (fun z hz hzx => henv z (by simp [freeB, hz, hzx])), hstk⟩
    · simp at hr
  · -- ifnull
    rename_i _ a e₁ y e₂ heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true] at hok
    split at hr
    · rename_i μ u w hev
      have hd := evalAt_drf (fun z hz => henv z (by simp [freeB, hz])) hev
      simp only [drf, Bool.and_eq_true] at hd
      split at hr
      · simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨hok.1, hσ, envDRF_sub henv (fun z hz => by simp [freeB, hz]), hstk⟩
      · simp only [List.mem_singleton] at hr
        subst hr
        refine ⟨hok.2, hσ, envDRF_cons (fun _ => ?_) (fun z hz hzx => henv z (by simp [freeB, hz, hzx])), hstk⟩
        simp only [drf, Bool.and_eq_true]
        exact hd
      · simp at hr
    · simp at hr
  · -- parity
    rename_i _ a k ev od heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_singleton] at hr
        subst hr
        split
        · exact ⟨hok.1, hσ, envDRF_sub henv (fun z hz => by simp [freeB, hz]), hstk⟩
        · exact ⟨hok.2, hσ, envDRF_sub henv (fun z hz => by simp [freeB, hz]), hstk⟩
      · simp at hr
    · simp at hr
  · -- ifeq
    rename_i _ a b yes no heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_singleton] at hr
        subst hr
        split
        · exact ⟨hok.1, hσ, envDRF_sub henv (fun z hz => by simp [freeB, hz]), hstk⟩
        · exact ⟨hok.2, hσ, envDRF_sub henv (fun z hz => by simp [freeB, hz]), hstk⟩
      · simp at hr
    · simp at hr
  · -- cas
    rename_i _ acq rel w e v t ok fail heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_map] at hr
        obtain ⟨⟨mem', th''⟩, -, rfl⟩ := hr
        apply ThScope_withS
        split
        · exact ⟨hok.1, hσ, envDRF_cons (fun _ => rfl) (fun z hz hzt => henv z (by simp [freeB, hz, hzt])), hstk⟩
        · exact ⟨hok.2, hσ, envDRF_sub henv (fun z hz => by simp [freeB, hz]), hstk⟩
      · simp at hr
    · simp at hr
  · -- casp
    rename_i _ acq rel w e0 e1 v0 v1 t ok fail heq
    rw [heq] at hok henv
    simp only [allOK, Bool.and_eq_true] at hok
    split at hr
    · split at hr
      · simp only [List.mem_map] at hr
        obtain ⟨⟨mem', pairs', th''⟩, -, rfl⟩ := hr
        apply ThScope_withS
        split
        · exact ⟨hok.1, hσ, envDRF_cons (fun _ => rfl) (fun z hz hzt => henv z (by simp [freeB, hz, hzt])), hstk⟩
        · exact ⟨hok.2, hσ, envDRF_sub henv (fun z hz => by simp [freeB, hz]), hstk⟩
      · simp at hr
    · simp at hr
  · -- ret
    rename_i _ a heq
    split at hr
    · rename_i f rest _ ws hst _
      simp only [List.mem_singleton] at hr
      subst hr
      rw [hst] at hstk
      have hf := hstk f (List.mem_cons_self ..)
      exact ⟨hf.ok, hf.σs, envDRF_cons (fun _ => hf.ty) hf.env, fun f' hf' => hstk f' (List.mem_cons_of_mem _ hf')⟩
    · simp at hr
  · -- tail
    rename_i _ f is a ts heq
    rw [heq] at hok
    simp only [allOK] at hok
    cases hen : enter g th f ts a with
    | none => simp [hen, ol] at hr
    | some th' =>
      simp only [hen, ol, Option.map_some, Option.toList_some, List.mem_singleton] at hr
      subst hr
      obtain ⟨h1, h2, h3, h4⟩ := enter_drf hp hσ hok hen
      exact ⟨h1, h2, h3, by rw [h4]; exact hstk⟩

/-! ## The invariant along runs -/

/-- **`RunScope` along every run** of a checked program. -/
theorem runDRF_step {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c1 c2 : Cfg}
    (hp : ProgScopeOK p = true) (h0 : RunScope c1) (hs : Step p k arch c1 c2) : RunScope c2 := by
    cases hs with
    | thread i hc _ =>
      obtain ⟨th, r, hth, hr, -, -, e3, ho⟩ := TermStepper.threadSteps_upd hc
      intro j thj hj
      by_cases hji : j = i
      · subst hji
        rw [e3] at hj
        cases hj
        exact tstep_drf (g := gOf p k arch _ j) hp (h0 j th hth) hr
      · rw [ho j hji] at hj
        exact h0 j thj hj
    | prom i a v w hi _ _ =>
      obtain ⟨th, hth⟩ : ∃ th, c1.ths[i]? = some th := ⟨_, Array.getElem?_eq_getElem hi⟩
      obtain ⟨-, hpj, -⟩ := TermStep.promise_inv (a := a) (v := v) (w := w) hth
      intro j thj hj
      by_cases hji : j = i
      · subst hji
        rw [hpj] at hj
        cases hj
        exact ⟨(h0 j th hth).ok, (h0 j th hth).σs, (h0 j th hth).env, (h0 j th hth).stk⟩
      · rw [TermStepper.promise_other hth hji] at hj
        exact h0 j thj hj

/-- (spawn, run-closed) **`RunScope` at every configuration reachable from `cs`** by machine steps and
`Sp` steps. -/
def RunScopeR (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (Sp : Cfg → Cfg → Prop) (cs : Cfg) : Prop :=
  ∀ {c : Cfg}, TermSpawnStep.StepsG p k arch Sp cs c → RunScope c

/-- **`RunScope` along every run** of a checked program (the generic induction; the `Sp` arm is the
caller's). -/
theorem runDRFR_of {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Sp : Cfg → Cfg → Prop} {cs : Cfg}
    (hp : ProgScopeOK p = true) (hSp : ∀ c c', Sp c c' → RunScope c → RunScope c') (h : RunScope cs) :
    RunScopeR p k arch Sp cs :=
  fun hr => TermSpawnStep.stepsG_pres (fun _ _ hs hv => runDRF_step hp hv hs) hSp hr h

/-- `RunScopeR` at `Sp := ⊥` from `RunScope` at the start (no premise beyond it). -/
theorem runDRFR_bot {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cs : Cfg}
    (hp : ProgScopeOK p = true) (h : RunScope cs) : RunScopeR p k arch (fun _ _ => False) cs :=
  runDRFR_of hp (fun _ _ hf _ => hf.elim) h

#print axioms runDRF_step
#print axioms runDRFR_of
#print axioms runDRFR_bot

/-- **`RunScope` along every run** of a checked program. -/
theorem run_drf {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Sp : Cfg → Cfg → Prop} {c0 c : Cfg}
    (_hp : ProgScopeOK p = true) (h0 : RunScopeR p k arch Sp c0) (hr : TermSpawnStep.StepsG p k arch Sp c0 c) :
    RunScope c := h0 hr

/-! ## From the invariant to the scope -/

theorem peek_var {cx : Cx} {x : String} {t : Ty} (h : cx.peek (.var x) = .ok t) :
    ∃ e, cx.vars.find? (·.1 == x) = some e ∧ e.2.1 = t := by
  unfold Cx.peek Cx.find at h
  cases hf : cx.vars.find? (·.1 == x) with
  | none => simp [hf] at h
  | some e =>
    obtain ⟨y, t', b⟩ := e
    refine ⟨_, rfl, ?_⟩
    simp only [hf] at h
    cases b <;> simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] <;>
      (try cases h) <;> (try rfl)

/-- **The pin, at an atom**: a typing context's type of a free atom is `drf`
(from `VarsOK` alone). -/
theorem peek_drfV {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx}
    {env : Env} (hv : VarsOK ρ η σs cx.vars env) {a : At} {t : Ty} (hp : cx.peek a = .ok t)
    (hf : ∀ x, freeA x a = true → ∀ rt ws, lookupE env x = some (rt, ws) → drf rt = true) : drf t = true := by
  cases a with
  | var x =>
    obtain ⟨e, he, rfl⟩ := peek_var hp
    obtain ⟨rt, ws, hl, -, hlay⟩ := hv x e he
    exact drf_of_Lay hlay (hf x (by simp [freeA]) rt ws hl)
  | lit n => simp only [Cx.peek] at hp; cases hp; rfl
  | unit => simp only [Cx.peek] at hp; cases hp; rfl

theorem drfM_cases {μ : Mode} (h : drfM μ = true) : μ = .own ∨ μ = .pub := by
  cases μ <;> simp_all [drfM]

theorem wordOf_cases {t : Ty} {r : Idx} {P : Proto} (h : wordOf t = some (r, P)) :
    ∃ μ, t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P) := by
  unfold wordOf at h
  split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

theorem word2Of_cases {t : Ty} {r : Idx} {P : Proto2} (h : word2Of t = some (r, P)) :
    ∃ μ, t = .ptr μ (.word2 r P) ∨ t = .loc μ (.word2 r P) := by
  unfold word2Of at h
  split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

theorem epairOf_cases {t : Ty} {r : Idx} {P : ECounter} (h : epairOf t = some (r, P)) :
    ∃ μ, t = .ptr μ (.epair r P) ∨ t = .loc μ (.epair r P) := by
  unfold epairOf at h
  split at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

theorem drfM_of_ref {t : Ty} {μ : Mode} {u : Ty} (h : t = .ptr μ u ∨ t = .loc μ u) (ht : drf t = true) :
    μ = .own ∨ μ = .pub := by
  rcases h with rfl | rfl <;> simp only [drf, Bool.and_eq_true] at ht <;> exact drfM_cases ht.1

/-- A word-pair or epoch-pair reference of a `drf` type: own or pub. -/
theorem pairRef_shape {t : Ty} (h : pairRef t = true) (ht : drf t = true) :
    ∃ μ u, (t = .ptr μ u ∨ t = .loc μ u) ∧ (μ = .own ∨ μ = .pub) ∧
      ((∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P)) := by
  unfold pairRef at h
  simp only [Bool.or_eq_true, Option.isSome_iff_exists] at h
  rcases h with ⟨⟨r, P⟩, h⟩ | ⟨⟨r, P⟩, h⟩
  · obtain ⟨μ, hμ⟩ := word2Of_cases h
    exact ⟨μ, _, hμ, drfM_of_ref hμ ht, .inl ⟨r, P, rfl⟩⟩
  · obtain ⟨μ, hμ⟩ := epairOf_cases h
    exact ⟨μ, _, hμ, drfM_of_ref hμ ht, .inr ⟨r, P, rfl⟩⟩

/-- `peek_drf` at a resourceful frame. -/
theorem peek_drf {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop} {cx : Cx}
    {env : Env} {Rf : Res} (hi : FInvR ρ η σs K cx env Rf) {a : At} {t : Ty} (hp : cx.peek a = .ok t)
    (hf : ∀ x, freeA x a = true → ∀ rt ws, lookupE env x = some (rt, ws) → drf rt = true) : drf t = true :=
  peek_drfV hi.1.2.1 hp hf

/-- **The scope at a term** whose free variables have `drf` runtime types, for
every typing of it (from `VarsOK` alone). -/
theorem scope_termV {p : Prog} {cx : Cx} {t : Expr} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {env : Env}
    (hT : Typed p cx t) (hv : VarsOK ρ η σs cx.vars env) (hok : allOK t = true) (henv : EnvDRF env t)
    (hns : ¬ SpawnT t) :
    StepScope cx t ∨ StepScopeR σs cx t := by
  have hat : ∀ a, (∀ x, freeA x a = true → freeB x t = true) → ∀ ty, cx.peek a = .ok ty → drf ty = true :=
    fun a ha ty hp => peek_drfV hv hp (fun x hx => henv x (ha x hx))
  cases t with
  | let_ x op e =>
    simp only [allOK, Bool.and_eq_true] at hok
    have hat' : ∀ a ∈ opAts op, ∀ ty, cx.peek a = .ok ty → drf ty = true :=
      fun a ha => hat a (fun y hy => free_let_op ha hy)
    cases hT with
    | let_ hop _ =>
    cases op
    case load acq a =>
      refine .inl (fun ty hp r u hc => ?_)
      have := (drf_cellOf hc (hat' a (by simp [opAts]) ty hp)).1
      simp [drfM] at this
    case store rel a v tok =>
      refine .inl (fun ty hp r u hc => ?_)
      have := (drf_cellOf hc (hat' a (by simp [opAts]) ty hp)).1
      simp [drfM] at this
    case xchg a v =>
      refine .inl (fun ty hp r u hc => ?_)
      have := (drf_cellOf hc (hat' a (by simp [opAts]) ty hp)).1
      simp [drfM] at this
    case ldp acq a n0 n1 =>
      refine .inl (fun ty hp => ?_)
      cases hop with
      | ldp hp' hpr _ =>
        rw [hp] at hp'
        cases hp'
        exact pairRef_shape hpr (hat' _ (by simp [opAts]) _ hp)
    case stp rel a v0 v1 tk =>
      refine .inl (fun ty hp => ?_)
      have hd := hat' a (by simp [opAts]) ty hp
      cases hop with
      | stpGive hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := word2Of_cases hw
        exact ⟨μ, _, _, hμ, drfM_of_ref hμ hd⟩
      | stpKeep hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := word2Of_cases hw
        exact ⟨μ, _, _, hμ, drfM_of_ref hμ hd⟩
    case fetch o acq rel a v =>
      refine .inl (fun ty hp => ?_)
      have hd := hat' a (by simp [opAts]) ty hp
      cases hop with
      | fetchCell hp' _ hc =>
        rw [hp] at hp'; cases hp'
        rcases hc with hc | ⟨r, hc, -⟩
        · exact ⟨_, _, cell_cases hc, .inr rfl⟩
        · have := (drf_cellOf hc hd).1; simp [drfM] at this
      | fetchEpoch hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := wordOf_cases hw
        exact ⟨μ, _, hμ, drfM_of_ref hμ hd⟩
      | fetchShare hp' hw =>
        rw [hp] at hp'; cases hp'
        obtain ⟨μ, hμ⟩ := wordOf_cases hw
        exact ⟨μ, _, hμ, drfM_of_ref hμ hd⟩
    case publish a =>
      refine .inl (fun ty hp μ u hu => ?_)
      have hd := hat' a (by simp [opAts]) ty hp
      apply rgnFree_of_drf
      rcases hu with rfl | ⟨ψ, rfl⟩
      · simp only [drf, Bool.and_eq_true] at hd; exact hd.2
      · simp only [drf, Bool.and_eq_true] at hd; exact hd.2
    case packT a σ τ =>
      simp only [opOK, opTys, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
      refine .inl ⟨?_, noIallV_of_drf σ hok.1.1⟩
      show PackTOK σ τ
      unfold PackTOK
      split
      · exact fun _ => rgnFree_of_drf σ hok.1.1
      · trivial
    case call f is a ts =>
      simp only [opOK, opTys] at hok
      exact .inl (fun σ hσ => ⟨rgnFree_of_drf σ (List.all_eq_true.1 hok.1 σ hσ), noIallV_of_drf σ (List.all_eq_true.1 hok.1 σ hσ)⟩)
    case new a =>
      exact .inl (fun ty c₁ hu => noIallV_of_drf ty
        (hat' a (by simp [opAts]) ty (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1))
    case newBuf n τ =>
      simp only [opOK, opTys, List.all_cons, List.all_nil, Bool.and_true] at hok
      exact .inl (noIallV_of_drf τ hok.1)
    case validate y => simp [opOK] at hok
    case intoRgn r a => simp [opOK] at hok
    case borrow s a => exact .inr trivial
    case freeze a => exact .inr trivial
    case endBorrow a => exact .inr trivial
    case mkTicket r N P v tk => simp [opOK] at hok
    case claim a tk => simp [opOK] at hok
    case spawn f a T ts => exact (hns trivial).elim
    all_goals exact .inl trivial
  | cas acq rel w e v t' ok fail =>
    refine .inl (fun ty hp => ?_)
    have hd := hat w (fun y hy => by simp [freeB, hy]) ty hp
    cases hT with
    | casCell hp' _ hc =>
      rw [hp] at hp'; cases hp'
      rcases hc with hc | ⟨r, hc, -⟩
      · exact .inr ⟨_, cell_cases hc, by assumption⟩
      · have := (drf_cellOf hc hd).1; simp [drfM] at this
    | casShare hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := wordOf_cases hw
      exact .inl ⟨μ, _, _, hμ, drfM_of_ref hμ hd⟩
    | casTake hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := wordOf_cases hw
      exact .inl ⟨μ, _, _, hμ, drfM_of_ref hμ hd⟩
    | casEpoch hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := wordOf_cases hw
      exact .inl ⟨μ, _, _, hμ, drfM_of_ref hμ hd⟩
  | casp acq rel w e0 e1 v0 v1 t' ok fail =>
    refine .inl (fun ty hp => ?_)
    have hd := hat w (fun y hy => by simp [freeB, hy]) ty hp
    cases hT with
    | caspE hp' _ hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := epairOf_cases hw
      exact ⟨μ, _, hμ, drfM_of_ref hμ hd, .inr ⟨_, _, rfl⟩⟩
    | caspBump hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := word2Of_cases hw
      exact ⟨μ, _, hμ, drfM_of_ref hμ hd, .inl ⟨_, _, rfl⟩⟩
    | caspMove hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := word2Of_cases hw
      exact ⟨μ, _, hμ, drfM_of_ref hμ hd, .inl ⟨_, _, rfl⟩⟩
    | caspTake hp' hw =>
      rw [hp] at hp'; cases hp'
      obtain ⟨μ, hμ⟩ := word2Of_cases hw
      exact ⟨μ, _, hμ, drfM_of_ref hμ hd, .inl ⟨_, _, rfl⟩⟩
  | tail f is a ts =>
    simp only [allOK] at hok
    exact .inl (fun σ hσ => ⟨rgnFree_of_drf σ (List.all_eq_true.1 hok σ hσ), noIallV_of_drf σ (List.all_eq_true.1 hok σ hσ)⟩)
  | _ => exact .inl trivial

/-- `scope_termV` at a resourceful frame. -/
theorem scope_term {p : Prog} {cx : Cx} {t : Expr} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → Nat → List Word → Res → Prop} {env : Env} {Rf : Res}
    (hT : Typed p cx t) (hi : FInvR ρ η σs K cx env Rf) (hok : allOK t = true) (henv : EnvDRF env t)
    (hns : ¬ SpawnT t) :
    StepScope cx t ∨ StepScopeR σs cx t :=
  scope_termV hT hi.1.2.1 hok henv hns

/-! ## The obligations O0 and T1 -/

/-- **O0** from the checker. -/
theorem progT_of_check {p : Prog} (h : checkProg p = .ok ()) : ProgT p := checkProg_sound p h

/-- **T1 (`Obligations.scope`)** for a program passing `ProgScopeOK`, on runs
from a configuration satisfying `RunScope`. -/
theorem scope_of {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hp : ProgScopeOK p = true) (h0 : TermScope.RunScopeR p k arch Sp c0) :
    ∀ {c c' : Cfg} {Eg : TermCut.GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → WeakMem.Ts → Res} {i : Nat}
    {th : TTh} {r : WeakMem.Memory × List WeakMem.Ts × TTh} {S : WeakMem.AllocLabel → Prop} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    StepScope cx th.term ∨ StepScopeR th.σs cx th.term := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y
  have h := run_drf hp h0 X.run i th X.hth
  exact scope_term Y.2.2.2.1.1 Y.2.2.2.2.2.1 h.ok h.env (not_spawnT_of_mem X.hr)

/-! ## D5: ticket-freedom (`NoTicket`, `ResidualNoTicket`) -/

theorem exprNoTicket_of_allOK : ∀ t : Expr, allOK t = true → TermBal.exprNoTicket t = true := by
  intro t
  induction t with
  | let_ x op e ih =>
    intro h
    simp only [allOK, Bool.and_eq_true] at h
    simp only [TermBal.exprNoTicket, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ih h.2⟩
    cases op <;> simp_all [opOK, TermBal.opTicket]
  | split _ _ _ e ih => intro h; exact ih h
  | unpack _ _ _ e ih => intro h; exact ih h
  | unpackT _ _ _ e ih => intro h; exact ih h
  | region _ _ _ _ e ih => intro h; simp only [allOK, Bool.and_eq_true] at h; exact ih h.2
  | openPub _ _ _ _ e ih => intro h; simp only [allOK, Bool.and_eq_true] at h; exact ih h.2
  | case _ _ e₁ _ e₂ ih₁ ih₂ => intro h; simp only [allOK, Bool.and_eq_true] at h; simp [TermBal.exprNoTicket, ih₁ h.1, ih₂ h.2]
  | ifnull _ e₁ _ e₂ ih₁ ih₂ => intro h; simp only [allOK, Bool.and_eq_true] at h; simp [TermBal.exprNoTicket, ih₁ h.1, ih₂ h.2]
  | parity _ _ e₁ e₂ ih₁ ih₂ => intro h; simp only [allOK, Bool.and_eq_true] at h; simp [TermBal.exprNoTicket, ih₁ h.1, ih₂ h.2]
  | ifeq _ _ e₁ e₂ ih₁ ih₂ => intro h; simp only [allOK, Bool.and_eq_true] at h; simp [TermBal.exprNoTicket, ih₁ h.1, ih₂ h.2]
  | cas _ _ _ _ _ _ e₁ e₂ ih₁ ih₂ => intro h; simp only [allOK, Bool.and_eq_true] at h; simp [TermBal.exprNoTicket, ih₁ h.1, ih₂ h.2]
  | casp _ _ _ _ _ _ _ _ e₁ e₂ ih₁ ih₂ => intro h; simp only [allOK, Bool.and_eq_true] at h; simp [TermBal.exprNoTicket, ih₁ h.1, ih₂ h.2]
  | ret _ => intro _; rfl
  | tail _ _ _ _ => intro _; rfl

/-- **`noTicket`** from `ProgScopeOK`. -/
theorem noTicket_of {p : Prog} (hp : ProgScopeOK p = true) : TermBal.NoTicket p = true := by
  unfold TermBal.NoTicket
  rw [List.all_eq_true]
  intro d hd
  exact exprNoTicket_of_allOK _ (ProgScopeOK.decl hp hd).2.2

/-- **`residualNoTicket`** from `ProgScopeOK` and `RunScope c0`. -/
theorem residualNoTicket_of {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c0 : Cfg}
    (hp : ProgScopeOK p = true) (h0 : TermScope.RunScopeR p k arch Sp c0) : TermBal.ResidualNoTicket p k arch Sp c0 :=
  fun _ c hr i th hth => exprNoTicket_of_allOK _ (run_drf hp h0 hr i th hth).ok

#print axioms noTicket_of
#print axioms residualNoTicket_of
#print axioms drf_of_Lay
#print axioms evalOp_drf
#print axioms tstep_drf
#print axioms run_drf
#print axioms scope_term
#print axioms progT_of_check
#print axioms scope_of

end TermScope

#print axioms TermScope.ThScope_withS
