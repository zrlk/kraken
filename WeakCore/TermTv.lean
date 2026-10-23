import WeakCore.TermClose

/-!
# TermTv — context types stay in scope (T3c-4, option 2)

`TvOK cx` says that every type the context records — each variable's, each
torn read's, and the return type — has all its free type variables below
`cx.ke.length` (`tb`, TermClose).  The checker never checks this directly:
it follows from the well-formedness checks on annotations (`inl`, `null`,
`newBuf`, `pack`, …), on type arguments (`instantiate`'s `admitsIn`), and on
declarations (`DeclT`), because every other type the checker records is built
from types already in the context by operations that keep `tb`
(projections, `adapt`, `unfold1`, index shifts and instantiation, `pushT`'s
type shift).

**Why.**  T3c-4's layout agreement (`TermSound.sig_WitL`) needs every
unguarded type variable of a type the machine lays out to be one the frame
has a runtime type argument for; `FInv` already has `ke.length ≤ σs.length`,
so `TvOK` plus `guardT_of_tb` gives it (option (2)).

* §1 `tb` through the type operations; §1b `mg` (guarded `μ` bodies).
* §2 `TvOK` and the context operations.
* §3 `OpT_TvOK`: every operation rule preserves `TvOK`.
* §4 The structural rules of `Typed`, and `declCx`.
-/

namespace TermTv
open CoreLang CoreTerm CoreTyping TermClose

/-! ## §1 `tb` through the type operations -/

theorem tb_of_wf (t : Ty) : ∀ {nt ni : Nat}, t.wf nt ni = true → tb nt t = true := by
  induction t with
  | tvar k => intro nt ni h; simpa [Ty.wf, tb] using h
  | prod a b iha ihb => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | sum a b iha ihb => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | code a b iha ihb => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | array i t ih => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ih h.2
  | ptr μ t ih => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ih h.2
  | ptrOpt μ t ih => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ih h.2
  | loc μ t ih => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ih h.2
  | mu t ih => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ih h.2
  | tex κ t ih => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ih h.2
  | iall t ih => intro nt ni h; simp only [Ty.wf, tb] at h ⊢; exact ih h
  | iex t ih => intro nt ni h; simp only [Ty.wf, tb] at h ⊢; exact ih h
  | refine t ψ ih => intro nt ni h; simp only [Ty.wf, tb, Bool.and_eq_true] at h ⊢; exact ih h.2
  | _ => intros; simp [tb]

/-- A type variable at or above the bound is guarded (it does not occur). -/
theorem guardT_of_tb (t : Ty) : ∀ {c k : Nat}, tb c t = true → c ≤ k → t.guardT k = true := by
  induction t with
  | tvar j => intro c k h hk; simp only [tb, decide_eq_true_eq] at h; simp only [Ty.guardT, bne_iff_ne, ne_eq]; omega
  | prod a b iha ihb =>
      intro c k h hk; simp only [tb, Ty.guardT, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1 hk, ihb h.2 hk⟩
  | sum a b iha ihb =>
      intro c k h hk; simp only [tb, Ty.guardT, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1 hk, ihb h.2 hk⟩
  | code a b iha ihb =>
      intro c k h hk; simp only [tb, Ty.guardT, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1 hk, ihb h.2 hk⟩
  | array _ t ih => intro c k h hk; simp only [tb, Ty.guardT] at h ⊢; exact ih h hk
  | mu t ih => intro c k h hk; simp only [tb, Ty.guardT] at h ⊢; exact ih h (by omega)
  | tex κ t ih => intro c k h hk; simp only [tb, Ty.guardT] at h ⊢; exact ih h (by omega)
  | iall t ih => intro c k h hk; simp only [tb, Ty.guardT] at h ⊢; exact ih h hk
  | iex t ih => intro c k h hk; simp only [tb, Ty.guardT] at h ⊢; exact ih h hk
  | refine t _ ih => intro c k h hk; simp only [tb, Ty.guardT] at h ⊢; exact ih h hk
  | _ => intros; simp [Ty.guardT]

/-- The form `TermSound.sig_WitL` asks for: every unguarded type variable of a
type bounded by `c` is below any `n ≥ c`. -/
theorem lt_of_guardT {c n : Nat} {t : Ty} (h : tb c t = true) (hc : c ≤ n) :
    ∀ k, t.guardT k = false → k < n :=
  fun k hk => Nat.lt_of_not_le (fun hn => by rw [guardT_of_tb t h (Nat.le_trans hc hn)] at hk; cases hk)

theorem tb_shiftI (t : Ty) : ∀ (k c : Nat), tb c (t.shiftI k) = tb c t := by
  induction t <;> intro k c <;> simp_all [Ty.shiftI, tb]

theorem tb_shiftIN (n : Nat) (t : Ty) (c : Nat) : tb c (shiftIN n t) = tb c t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftIN, tb_shiftI, ih]

theorem tb_instT (us : List Idx) (t : Ty) : ∀ (d c : Nat), tb c (instT us d t) = tb c t := by
  induction t <;> intro d c <;> simp_all [instT, tb]

theorem tb_adapt (t : Ty) : ∀ (r : Idx) (c : Nat), tb c (adapt r t) = tb c t := by
  induction t with
  | prod a b iha ihb => intro r c; simp [adapt, tb, iha, ihb]
  | sum a b iha ihb => intro r c; simp [adapt, tb, iha, ihb]
  | array i t ih => intro r c; simp [adapt, tb, ih]
  | iex t ih => intro r c; simp [adapt, tb, ih]
  | iall t ih => intro r c; simp [adapt, tb, ih]
  | tex κ t ih => intro r c; simp [adapt, tb, ih]
  | refine t ψ ih => intro r c; simp [adapt, tb, ih]
  | mu t ih => intro r c; simp [adapt, tb, ih]
  | ptr μ t ih => intro r c; cases μ <;> simp [adapt, tb]
  | ptrOpt μ t ih => intro r c; cases μ <;> simp [adapt, tb]
  | loc μ t ih => intro r c; cases μ <;> simp [adapt, tb]
  | _ => intro r c; simp [adapt, tb]

/-- Shifting type variables up, under one more bound. -/
theorem tb_shiftT_up (t : Ty) : ∀ (k c : Nat), tb c t = true → tb (c + 1) (t.shiftT k) = true := by
  induction t with
  | tvar j =>
      intro k c h; simp only [tb, decide_eq_true_eq] at h
      simp only [Ty.shiftT]; split <;> simp [tb] <;> omega
  | prod a b iha ihb =>
      intro k c h; simp only [tb, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨iha k c h.1, ihb k c h.2⟩
  | sum a b iha ihb =>
      intro k c h; simp only [tb, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨iha k c h.1, ihb k c h.2⟩
  | code a b iha ihb =>
      intro k c h; simp only [tb, Ty.shiftT, Bool.and_eq_true] at h ⊢; exact ⟨iha k c h.1, ihb k c h.2⟩
  | array _ t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih k c h
  | ptr _ t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih k c h
  | ptrOpt _ t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih k c h
  | loc _ t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih k c h
  | mu t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih (k + 1) (c + 1) h
  | tex κ t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih (k + 1) (c + 1) h
  | iall t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih k c h
  | iex t ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih k c h
  | refine t _ ih => intro k c h; simp only [tb, Ty.shiftT] at h ⊢; exact ih k c h
  | _ => intros; simp [tb, Ty.shiftT]

theorem tb_shiftTN {c : Nat} {t : Ty} (h : tb c t = true) : ∀ n, tb (c + n) (shiftTN n t) = true
  | 0 => h
  | n + 1 => tb_shiftT_up _ 0 _ (tb_shiftTN h n)

/-- Substituting for the variable `j` removes one bound. -/
theorem tb_substT (t : Ty) : ∀ (j c : Nat) (s : Ty), j ≤ c → tb c s = true → tb (c + 1) t = true →
    tb c (Ty.substT j s t) = true := by
  induction t with
  | tvar k =>
      intro j c s hj hs h; simp only [tb, decide_eq_true_eq] at h
      simp only [Ty.substT]
      split
      · exact hs
      · rename_i hne
        simp only [beq_iff_eq] at hne
        split
        · simp only [tb, decide_eq_true_eq]; omega
        · simp only [tb, decide_eq_true_eq]; omega
  | prod a b iha ihb =>
      intro j c s hj hs h; simp only [tb, Ty.substT, Bool.and_eq_true] at h ⊢
      exact ⟨iha j c s hj hs h.1, ihb j c s hj hs h.2⟩
  | sum a b iha ihb =>
      intro j c s hj hs h; simp only [tb, Ty.substT, Bool.and_eq_true] at h ⊢
      exact ⟨iha j c s hj hs h.1, ihb j c s hj hs h.2⟩
  | code a b iha ihb =>
      intro j c s hj hs h; simp only [tb, Ty.substT, Bool.and_eq_true] at h ⊢
      exact ⟨iha j c s hj hs h.1, ihb j c s hj hs h.2⟩
  | array _ t ih => intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢; exact ih j c s hj hs h
  | ptr _ t ih => intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢; exact ih j c s hj hs h
  | ptrOpt _ t ih => intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢; exact ih j c s hj hs h
  | loc _ t ih => intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢; exact ih j c s hj hs h
  | mu t ih =>
      intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢
      exact ih (j + 1) (c + 1) _ (by omega) (tb_shiftT_up s 0 c hs) h
  | tex κ t ih =>
      intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢
      exact ih (j + 1) (c + 1) _ (by omega) (tb_shiftT_up s 0 c hs) h
  | iall t ih =>
      intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢
      exact ih j c _ hj (by rw [tb_shiftI]; exact hs) h
  | iex t ih =>
      intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢
      exact ih j c _ hj (by rw [tb_shiftI]; exact hs) h
  | refine t _ ih => intro j c s hj hs h; simp only [tb, Ty.substT] at h ⊢; exact ih j c s hj hs h
  | _ => intros; simp [tb, Ty.substT]

theorem tb_unfold1 {c : Nat} {u : Ty} (h : tb c u = true) : tb c (unfold1 u) = true := by
  cases u with
  | mu t => exact tb_substT t 0 c (.mu t) (Nat.zero_le _) h (by simpa [tb] using h)
  | _ => simpa [unfold1] using h

/-- Simultaneous substitution of types bounded by `m`. -/
theorem tb_substTs {σs : List Ty} {m : Nat} (hσ : ∀ σ ∈ σs, tb m σ = true) (t : Ty) :
    ∀ c d, tb (c + σs.length) t = true → tb (c + m) (substTs σs c d t) = true := by
  induction t with
  | tvar k =>
      intro c d h; simp only [tb, decide_eq_true_eq] at h
      simp only [substTs]
      split
      · simp [tb]; omega
      · split
        · rename_i σ hs
          rw [tb_shiftIN]
          have := tb_shiftTN (hσ σ (List.mem_of_getElem? hs)) c
          have e : m + c = c + m := Nat.add_comm _ _
          rwa [e] at this
        · rename_i hs
          have := List.getElem?_eq_none_iff.1 hs
          simp only [tb, decide_eq_true_eq]; omega
  | prod a b iha ihb =>
      intro c d h; simp only [tb, substTs, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb =>
      intro c d h; simp only [tb, substTs, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | code a b iha ihb =>
      intro c d h; simp only [tb, substTs, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | array _ t ih => intro c d h; simp only [tb, substTs] at h ⊢; exact ih c d h
  | ptr _ t ih => intro c d h; simp only [tb, substTs] at h ⊢; exact ih c d h
  | ptrOpt _ t ih => intro c d h; simp only [tb, substTs] at h ⊢; exact ih c d h
  | loc _ t ih => intro c d h; simp only [tb, substTs] at h ⊢; exact ih c d h
  | mu t ih =>
      intro c d h; simp only [tb, substTs] at h ⊢
      have e1 : c + 1 + σs.length = c + σs.length + 1 := by omega
      have e2 : c + 1 + m = c + m + 1 := by omega
      have := ih (c + 1) d (by rw [e1]; exact h)
      rwa [e2] at this
  | tex κ t ih =>
      intro c d h; simp only [tb, substTs] at h ⊢
      have e1 : c + 1 + σs.length = c + σs.length + 1 := by omega
      have e2 : c + 1 + m = c + m + 1 := by omega
      have := ih (c + 1) d (by rw [e1]; exact h)
      rwa [e2] at this
  | iall t ih => intro c d h; simp only [tb, substTs] at h ⊢; exact ih c (d + 1) h
  | iex t ih => intro c d h; simp only [tb, substTs] at h ⊢; exact ih c (d + 1) h
  | refine t _ ih => intro c d h; simp only [tb, substTs] at h ⊢; exact ih c d h
  | _ => intros; simp [tb, substTs]

theorem tb_cellOf {c : Nat} {t u : Ty} {μ : Mode} (h : tb c t = true) (e : cellOf t = some (μ, u)) :
    tb c u = true := by
  cases t with
  | ptr μ' t' => simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]; simpa [tb] using h
  | loc μ' t' => simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]; simpa [tb] using h
  | _ => simp [cellOf] at e

theorem tb_codeOf {c : Nat} {t σ τ : Ty} (h : tb c t = true) (e : codeOf t = some (σ, τ)) :
    tb c σ = true ∧ tb c τ = true := by
  cases t with
  | code a b =>
      simp only [codeOf, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      simpa [tb] using h
  | _ => simp [codeOf] at e

theorem tb_bufOf {c : Nat} {t u : Ty} {μ : Mode} {n k : Idx} (h : tb c t = true)
    (e : bufOf t = some (μ, n, u, k)) : tb c u = true := by
  unfold bufOf at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, -, rfl, -⟩ := e
    simpa [tb] using h
  · simp at e

theorem tb_compTy {c : Nat} (q : List Nat) : ∀ {t u : Ty}, tb c t = true → compTy t q = some u → tb c u = true := by
  induction q with
  | nil => intro t u h e; simp only [compTy, Option.some.injEq] at e; subst e; exact h
  | cons i q ih =>
      intro t u h e
      cases t with
      | prod a b =>
          simp only [tb, Bool.and_eq_true] at h
          match i, e with
          | 0, e => exact ih h.1 (by simpa [compTy] using e)
          | 1, e => exact ih h.2 (by simpa [compTy] using e)
          | n + 2, e => simp [compTy] at e
      | _ => simp [compTy] at e

theorem tb_xchg {cx : Cx} {c : Nat} {t u o : Ty} (hx : XchgCell cx t u o) (h : tb c t = true) :
    tb c u = true ∧ tb c o = true := by
  cases hx with
  | own _ hc => exact ⟨tb_cellOf h hc, tb_cellOf h hc⟩
  | rgn _ hc _ _ => rw [tb_adapt]; exact ⟨tb_cellOf h hc, tb_cellOf h hc⟩

/-! ### `guardT` under shifts (T3c-4d) -/

theorem guardT_shiftI (t : Ty) : ∀ (c k : Nat), (t.shiftI c).guardT k = t.guardT k := by
  induction t <;> intro c k <;> simp_all [Ty.shiftI, Ty.guardT]

/-- The variable a shift skips is absent, hence guarded. -/
theorem guardT_shiftT_at (t : Ty) : ∀ c : Nat, (t.shiftT c).guardT c = true := by
  induction t with
  | tvar j => intro c; simp only [Ty.shiftT]; split <;> simp [Ty.guardT] <;> omega
  | mu t ih => intro c; simp only [Ty.shiftT, Ty.guardT]; exact ih (c + 1)
  | tex κ t ih => intro c; simp only [Ty.shiftT, Ty.guardT]; exact ih (c + 1)
  | _ => intro c; simp_all [Ty.shiftT, Ty.guardT]

theorem guardT_shiftT_succ (t : Ty) : ∀ (c k : Nat), c ≤ k → (t.shiftT c).guardT (k + 1) = t.guardT k := by
  induction t with
  | tvar j =>
      intro c k h; simp only [Ty.shiftT]
      split
      · by_cases e : j = k
        · subst e; simp [Ty.guardT]
        · have e' : j + 1 ≠ k + 1 := by omega
          simp [Ty.guardT, e, e']
      · have e : j ≠ k := by omega
        have e' : j ≠ k + 1 := by omega
        simp only [Ty.guardT]; rw [bne_iff_ne.2 e, bne_iff_ne.2 e']
  | mu t ih => intro c k h; simp only [Ty.shiftT, Ty.guardT]; exact ih (c + 1) (k + 1) (by omega)
  | tex κ t ih => intro c k h; simp only [Ty.shiftT, Ty.guardT]; exact ih (c + 1) (k + 1) (by omega)
  | _ => intro c k h; simp_all [Ty.shiftT, Ty.guardT]

/-! ### §1b Guarded `μ` bodies (`mg`, T3c-5a)

`Ty.wf` asks every `μ` body to be guarded (`unguarded 0 = false`), but `tb`
forgets it.  Reading a component of a cell through `μ` (`TermStep` §7) needs
it at the cell's type, so `TvOK` carries it too, as `mg`: `wf`'s guard
condition without its scope condition. -/

theorem mg_of_wf (t : Ty) : ∀ {nt ni : Nat}, t.wf nt ni = true → mg t = true := by
  induction t with
  | prod a b iha ihb => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | sum a b iha ihb => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | code a b iha ihb => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | array i t ih => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ih h.2
  | ptr μ t ih => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ih h.2
  | ptrOpt μ t ih => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ih h.2
  | loc μ t ih => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ih h.2
  | mu t ih => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih h.2⟩
  | tex κ t ih => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ih h.2
  | iall t ih => intro nt ni h; simp only [Ty.wf, mg] at h ⊢; exact ih h
  | iex t ih => intro nt ni h; simp only [Ty.wf, mg] at h ⊢; exact ih h
  | refine t ψ ih => intro nt ni h; simp only [Ty.wf, mg, Bool.and_eq_true] at h ⊢; exact ih h.2
  | _ => intros; simp [mg]

theorem nbeq_false {a b : Nat} (h : a ≠ b) : (a == b) = false := by simpa using h

theorem nbeq_iff {a b c d : Nat} (h₁ : a = b → c = d) (h₂ : c = d → a = b) : (a == b) = (c == d) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact ⟨h₁, h₂⟩

theorem unguarded_shiftI (t : Ty) : ∀ (c d : Nat), (t.shiftI c).unguarded d = t.unguarded d := by
  induction t <;> intro c d <;> simp_all [Ty.shiftI, Ty.unguarded]

theorem unguarded_shiftIN (n : Nat) (t : Ty) (d : Nat) : (shiftIN n t).unguarded d = t.unguarded d := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftIN, unguarded_shiftI, ih]

theorem unguarded_instT (us : List Idx) (t : Ty) : ∀ (k d : Nat), (instT us k t).unguarded d = t.unguarded d := by
  induction t <;> intro k d <;> simp_all [instT, Ty.unguarded]

theorem unguarded_adapt (t : Ty) : ∀ (r : Idx) (d : Nat), (adapt r t).unguarded d = t.unguarded d := by
  induction t with
  | prod a b iha ihb => intro r d; simp [adapt, Ty.unguarded, iha, ihb]
  | sum a b iha ihb => intro r d; simp [adapt, Ty.unguarded, iha, ihb]
  | array i t ih => intro r d; simp [adapt, Ty.unguarded, ih]
  | iex t ih => intro r d; simp [adapt, Ty.unguarded, ih]
  | iall t ih => intro r d; simp [adapt, Ty.unguarded, ih]
  | tex κ t ih => intro r d; simp [adapt, Ty.unguarded, ih]
  | refine t ψ ih => intro r d; simp [adapt, Ty.unguarded, ih]
  | mu t ih => intro r d; simp [adapt, Ty.unguarded, ih]
  | ptr μ t ih => intro r d; cases μ <;> simp [adapt, Ty.unguarded]
  | ptrOpt μ t ih => intro r d; cases μ <;> simp [adapt, Ty.unguarded]
  | loc μ t ih => intro r d; cases μ <;> simp [adapt, Ty.unguarded]
  | _ => intro r d; simp [adapt, Ty.unguarded]

/-- The variable a shift skips does not occur, so it is not unguarded. -/
theorem unguarded_shiftT_at (t : Ty) : ∀ c : Nat, (t.shiftT c).unguarded c = false := by
  induction t with
  | tvar j => intro c; simp only [Ty.shiftT]; split <;> simp only [Ty.unguarded] <;> exact nbeq_false (by omega)
  | prod a b iha ihb => intro c; simp only [Ty.shiftT, Ty.unguarded, iha, ihb, Bool.or_self]
  | sum a b iha ihb => intro c; simp only [Ty.shiftT, Ty.unguarded, iha, ihb, Bool.or_self]
  | array _ t ih => intro c; simp only [Ty.shiftT, Ty.unguarded]; exact ih c
  | mu t ih => intro c; simp only [Ty.shiftT, Ty.unguarded]; exact ih (c + 1)
  | tex κ t ih => intro c; simp only [Ty.shiftT, Ty.unguarded]; exact ih (c + 1)
  | iall t ih => intro c; simp only [Ty.shiftT, Ty.unguarded]; exact ih c
  | iex t ih => intro c; simp only [Ty.shiftT, Ty.unguarded]; exact ih c
  | refine t _ ih => intro c; simp only [Ty.shiftT, Ty.unguarded]; exact ih c
  | _ => intro c; simp [Ty.shiftT, Ty.unguarded]

theorem unguarded_shiftT_succ (t : Ty) : ∀ (c k : Nat), c ≤ k → (t.shiftT c).unguarded (k + 1) = t.unguarded k := by
  induction t with
  | tvar j =>
      intro c k h; simp only [Ty.shiftT]
      split <;> simp only [Ty.unguarded] <;> exact nbeq_iff (fun _ => by omega) (fun _ => by omega)
  | prod a b iha ihb => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; rw [iha c k h, ihb c k h]
  | sum a b iha ihb => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; rw [iha c k h, ihb c k h]
  | array _ t ih => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c k h
  | mu t ih => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; exact ih (c + 1) (k + 1) (by omega)
  | tex κ t ih => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; exact ih (c + 1) (k + 1) (by omega)
  | iall t ih => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c k h
  | iex t ih => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c k h
  | refine t _ ih => intro c k h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c k h
  | _ => intro c k h; simp [Ty.shiftT, Ty.unguarded]

theorem unguarded_shiftT_lt (t : Ty) : ∀ (c d : Nat), d < c → (t.shiftT c).unguarded d = t.unguarded d := by
  induction t with
  | tvar j =>
      intro c d h; simp only [Ty.shiftT]
      split <;> simp only [Ty.unguarded] <;> exact nbeq_iff (fun _ => by omega) (fun _ => by omega)
  | prod a b iha ihb => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; rw [iha c d h, ihb c d h]
  | sum a b iha ihb => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; rw [iha c d h, ihb c d h]
  | array _ t ih => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c d h
  | mu t ih => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; exact ih (c + 1) (d + 1) (by omega)
  | tex κ t ih => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; exact ih (c + 1) (d + 1) (by omega)
  | iall t ih => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c d h
  | iex t ih => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c d h
  | refine t _ ih => intro c d h; simp only [Ty.shiftT, Ty.unguarded]; exact ih c d h
  | _ => intro c d h; simp [Ty.shiftT, Ty.unguarded]

theorem unguarded_shiftTN_lt (t : Ty) : ∀ (n d : Nat), d < n → (shiftTN n t).unguarded d = false
  | 0, d, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => unguarded_shiftT_at (shiftTN n t) 0
  | n + 1, d + 1, h => by
      show (Ty.shiftT 0 (shiftTN n t)).unguarded (d + 1) = false
      rw [unguarded_shiftT_succ _ 0 d (Nat.zero_le _)]; exact unguarded_shiftTN_lt t n d (by omega)

/-- Substituting a type in which `d` is not unguarded for a variable above `d`. -/
theorem unguarded_substT (t : Ty) : ∀ (j d : Nat) (s : Ty), d < j → s.unguarded d = false →
    (Ty.substT j s t).unguarded d = t.unguarded d := by
  induction t with
  | tvar k =>
      intro j d s hd hs; simp only [Ty.substT]
      split
      · rename_i e; simp only [beq_iff_eq] at e; subst e
        rw [hs]; simp only [Ty.unguarded]; exact (nbeq_false (by omega)).symm
      · split <;> simp only [Ty.unguarded] <;> exact nbeq_iff (fun _ => by omega) (fun _ => by omega)
  | prod a b iha ihb => intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]; rw [iha j d s hd hs, ihb j d s hd hs]
  | sum a b iha ihb => intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]; rw [iha j d s hd hs, ihb j d s hd hs]
  | array _ t ih => intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]; exact ih j d s hd hs
  | mu t ih =>
      intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]
      exact ih (j + 1) (d + 1) _ (by omega) (by rw [unguarded_shiftT_succ s 0 d (Nat.zero_le _)]; exact hs)
  | tex κ t ih =>
      intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]
      exact ih (j + 1) (d + 1) _ (by omega) (by rw [unguarded_shiftT_succ s 0 d (Nat.zero_le _)]; exact hs)
  | iall t ih =>
      intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]; exact ih j d _ hd (by rw [unguarded_shiftI]; exact hs)
  | iex t ih =>
      intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]; exact ih j d _ hd (by rw [unguarded_shiftI]; exact hs)
  | refine t _ ih => intro j d s hd hs; simp only [Ty.substT, Ty.unguarded]; exact ih j d s hd hs
  | _ => intros; simp [Ty.substT, Ty.unguarded]

/-- A simultaneous substitution leaves the variables below `c` as they were. -/
theorem unguarded_substTs (σs : List Ty) (t : Ty) : ∀ (c i d : Nat), d < c →
    (substTs σs c i t).unguarded d = t.unguarded d := by
  induction t with
  | tvar k =>
      intro c i d hd; simp only [substTs]
      split
      · rfl
      · rename_i hk
        split
        · rename_i σ hs
          rw [unguarded_shiftIN, unguarded_shiftTN_lt σ c d hd]; simp only [Ty.unguarded]
          exact (nbeq_false (by omega)).symm
        · rename_i hs
          have := List.getElem?_eq_none_iff.1 hs
          simp only [Ty.unguarded]; exact nbeq_iff (fun _ => by omega) (fun _ => by omega)
  | prod a b iha ihb => intro c i d hd; simp only [substTs, Ty.unguarded]; rw [iha c i d hd, ihb c i d hd]
  | sum a b iha ihb => intro c i d hd; simp only [substTs, Ty.unguarded]; rw [iha c i d hd, ihb c i d hd]
  | array _ t ih => intro c i d hd; simp only [substTs, Ty.unguarded]; exact ih c i d hd
  | mu t ih => intro c i d hd; simp only [substTs, Ty.unguarded]; exact ih (c + 1) i (d + 1) (by omega)
  | tex κ t ih => intro c i d hd; simp only [substTs, Ty.unguarded]; exact ih (c + 1) i (d + 1) (by omega)
  | iall t ih => intro c i d hd; simp only [substTs, Ty.unguarded]; exact ih c (i + 1) d hd
  | iex t ih => intro c i d hd; simp only [substTs, Ty.unguarded]; exact ih c (i + 1) d hd
  | refine t _ ih => intro c i d hd; simp only [substTs, Ty.unguarded]; exact ih c i d hd
  | _ => intros; simp [substTs, Ty.unguarded]

theorem mg_shiftI (t : Ty) : ∀ c : Nat, mg (t.shiftI c) = mg t := by
  induction t <;> intro c <;> simp_all [Ty.shiftI, mg, unguarded_shiftI]

theorem mg_shiftIN (n : Nat) (t : Ty) : mg (shiftIN n t) = mg t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftIN, mg_shiftI, ih]

theorem mg_instT (us : List Idx) (t : Ty) : ∀ d : Nat, mg (instT us d t) = mg t := by
  induction t <;> intro d <;> simp_all [instT, mg, unguarded_instT]

theorem mg_adapt (t : Ty) : ∀ r : Idx, mg (adapt r t) = mg t := by
  induction t with
  | prod a b iha ihb => intro r; simp [adapt, mg, iha, ihb]
  | sum a b iha ihb => intro r; simp [adapt, mg, iha, ihb]
  | array i t ih => intro r; simp [adapt, mg, ih]
  | iex t ih => intro r; simp [adapt, mg, ih]
  | iall t ih => intro r; simp [adapt, mg, ih]
  | tex κ t ih => intro r; simp [adapt, mg, ih]
  | refine t ψ ih => intro r; simp [adapt, mg, ih]
  | mu t ih => intro r; simp [adapt, mg, ih, unguarded_adapt]
  | ptr μ t ih => intro r; cases μ <;> simp [adapt, mg]
  | ptrOpt μ t ih => intro r; cases μ <;> simp [adapt, mg]
  | loc μ t ih => intro r; cases μ <;> simp [adapt, mg]
  | _ => intro r; simp [adapt, mg]

theorem mg_shiftT (t : Ty) : ∀ c : Nat, mg (t.shiftT c) = mg t := by
  induction t with
  | tvar j => intro c; simp only [Ty.shiftT]; split <;> simp [mg]
  | mu t ih => intro c; simp only [Ty.shiftT, mg]; rw [unguarded_shiftT_lt t (c + 1) 0 (Nat.succ_pos _), ih]
  | _ => intro c; simp_all [Ty.shiftT, mg]

theorem mg_shiftTN (n : Nat) (t : Ty) : mg (shiftTN n t) = mg t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftTN, mg_shiftT, ih]

theorem mg_substT (t : Ty) : ∀ (j : Nat) (s : Ty), mg s = true → mg t = true → mg (Ty.substT j s t) = true := by
  induction t with
  | tvar k =>
      intro j s hs _; simp only [Ty.substT]
      split
      · exact hs
      · split <;> simp [mg]
  | prod a b iha ihb =>
      intro j s hs h; simp only [mg, Ty.substT, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | sum a b iha ihb =>
      intro j s hs h; simp only [mg, Ty.substT, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | code a b iha ihb =>
      intro j s hs h; simp only [mg, Ty.substT, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | array _ t ih => intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih j s hs h
  | ptr _ t ih => intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih j s hs h
  | ptrOpt _ t ih => intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih j s hs h
  | loc _ t ih => intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih j s hs h
  | mu t ih =>
      intro j s hs h; simp only [mg, Ty.substT, Bool.and_eq_true] at h ⊢
      refine ⟨?_, ih (j + 1) _ (by rw [mg_shiftT]; exact hs) h.2⟩
      rw [unguarded_substT t (j + 1) 0 (s.shiftT 0) (Nat.succ_pos _) (unguarded_shiftT_at s 0)]; exact h.1
  | tex κ t ih =>
      intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih (j + 1) _ (by rw [mg_shiftT]; exact hs) h
  | iall t ih =>
      intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih j _ (by rw [mg_shiftI]; exact hs) h
  | iex t ih =>
      intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih j _ (by rw [mg_shiftI]; exact hs) h
  | refine t _ ih => intro j s hs h; simp only [mg, Ty.substT] at h ⊢; exact ih j s hs h
  | _ => intros; simp [mg, Ty.substT]

theorem mg_unfold1 {u : Ty} (h : mg u = true) : mg (unfold1 u) = true := by
  cases u with
  | mu t =>
      have h' := h
      simp only [mg, Bool.and_eq_true] at h'
      exact mg_substT t 0 (.mu t) h h'.2
  | _ => simpa [unfold1] using h

theorem mg_substTs {σs : List Ty} (hσ : ∀ σ ∈ σs, mg σ = true) (t : Ty) :
    ∀ c d, mg t = true → mg (substTs σs c d t) = true := by
  induction t with
  | tvar k =>
      intro c d _; simp only [substTs]
      split
      · simp [mg]
      · split
        · rename_i σ hs
          rw [mg_shiftIN, mg_shiftTN]; exact hσ σ (List.mem_of_getElem? hs)
        · simp [mg]
  | prod a b iha ihb =>
      intro c d h; simp only [mg, substTs, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb =>
      intro c d h; simp only [mg, substTs, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | code a b iha ihb =>
      intro c d h; simp only [mg, substTs, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | array _ t ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih c d h
  | ptr _ t ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih c d h
  | ptrOpt _ t ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih c d h
  | loc _ t ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih c d h
  | mu t ih =>
      intro c d h; simp only [mg, substTs, Bool.and_eq_true] at h ⊢
      refine ⟨?_, ih (c + 1) d h.2⟩
      rw [unguarded_substTs σs t (c + 1) d 0 (Nat.succ_pos _)]; exact h.1
  | tex κ t ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih (c + 1) d h
  | iall t ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih c (d + 1) h
  | iex t ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih c (d + 1) h
  | refine t _ ih => intro c d h; simp only [mg, substTs] at h ⊢; exact ih c d h
  | _ => intros; simp [mg, substTs]

/-- A type whose free type variables are below `n` has none unguarded at `j ≥ n`. -/
theorem unguarded_tb (t : Ty) : ∀ (n j : Nat), tb n t = true → n ≤ j → t.unguarded j = false := by
  induction t with
  | tvar k => intro n j h hj; simp only [tb, decide_eq_true_eq] at h; simp only [Ty.unguarded]; exact nbeq_false (by omega)
  | prod a b iha ihb => intro n j h hj; simp only [tb, Bool.and_eq_true] at h; simp [Ty.unguarded, iha n j h.1 hj, ihb n j h.2 hj]
  | sum a b iha ihb => intro n j h hj; simp only [tb, Bool.and_eq_true] at h; simp [Ty.unguarded, iha n j h.1 hj, ihb n j h.2 hj]
  | array _ t ih => intro n j h hj; simp only [tb] at h; simp only [Ty.unguarded]; exact ih n j h hj
  | mu t ih => intro n j h hj; simp only [tb] at h; simp only [Ty.unguarded]; exact ih (n + 1) (j + 1) h (by omega)
  | tex κ t ih => intro n j h hj; simp only [tb] at h; simp only [Ty.unguarded]; exact ih (n + 1) (j + 1) h (by omega)
  | iall t ih => intro n j h hj; simp only [tb] at h; simp only [Ty.unguarded]; exact ih n j h hj
  | iex t ih => intro n j h hj; simp only [tb] at h; simp only [Ty.unguarded]; exact ih n j h hj
  | refine t _ ih => intro n j h hj; simp only [tb] at h; simp only [Ty.unguarded]; exact ih n j h hj
  | _ => intros; simp [Ty.unguarded]

/-- Closing with closed witnesses keeps which bound variables are unguarded. -/
theorem unguarded_cl {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, tb 0 (W k) = true) (t : Ty) :
    ∀ (c d j : Nat), j < c → (cl ρ W c d t).unguarded j = t.unguarded j := by
  induction t with
  | tvar k =>
    intro c d j hj
    simp only [cl]
    split
    · rfl
    · rw [unguarded_tb _ 0 j (hW _) (Nat.zero_le _)]; simp only [Ty.unguarded]; exact (nbeq_false (by omega)).symm
  | prod a b iha ihb => intro c d j hj; simp only [cl, Ty.unguarded, iha c d j hj, ihb c d j hj]
  | sum a b iha ihb => intro c d j hj; simp only [cl, Ty.unguarded, iha c d j hj, ihb c d j hj]
  | array _ t ih => intro c d j hj; simp only [cl, Ty.unguarded]; exact ih c d j hj
  | mu t ih => intro c d j hj; simp only [cl, Ty.unguarded]; exact ih (c + 1) d (j + 1) (by omega)
  | tex κ t ih => intro c d j hj; simp only [cl, Ty.unguarded]; exact ih (c + 1) d (j + 1) (by omega)
  | iall t ih => intro c d j hj; simp only [cl, Ty.unguarded]; exact ih c (d + 1) j hj
  | iex t ih => intro c d j hj; simp only [cl, Ty.unguarded]; exact ih c (d + 1) j hj
  | refine t _ ih => intro c d j hj; simp only [cl, Ty.unguarded]; exact ih c d j hj
  | _ => intros; simp [cl, Ty.unguarded]

/-- (GStoMg) **Closing keeps `μ` bodies guarded**, for closed guarded witnesses. -/
theorem mg_cl {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, tb 0 (W k) = true) (hm : ∀ k, mg (W k) = true)
    (t : Ty) : ∀ (c d : Nat), mg t = true → mg (cl ρ W c d t) = true := by
  induction t with
  | tvar k => intro c d _; simp only [cl]; split <;> simp [mg, hm]
  | prod a b iha ihb => intro c d h; simp only [mg, cl, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | sum a b iha ihb => intro c d h; simp only [mg, cl, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | code a b iha ihb => intro c d h; simp only [mg, cl, Bool.and_eq_true] at h ⊢; exact ⟨iha c d h.1, ihb c d h.2⟩
  | array _ t ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih c d h
  | ptr _ t ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih c d h
  | ptrOpt _ t ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih c d h
  | loc _ t ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih c d h
  | mu t ih =>
    intro c d h; simp only [mg, cl, Bool.and_eq_true] at h ⊢
    exact ⟨by rw [unguarded_cl hW t (c + 1) d 0 (Nat.succ_pos _)]; exact h.1, ih (c + 1) d h.2⟩
  | tex κ t ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih (c + 1) d h
  | iall t ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih c (d + 1) h
  | iex t ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih c (d + 1) h
  | refine t _ ih => intro c d h; simp only [mg, cl] at h ⊢; exact ih c d h
  | _ => intros; simp [mg, cl]

theorem mg_cellOf {t u : Ty} {μ : Mode} (h : mg t = true) (e : cellOf t = some (μ, u)) : mg u = true := by
  cases t with
  | ptr μ' t' => simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]; simpa [mg] using h
  | loc μ' t' => simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]; simpa [mg] using h
  | _ => simp [cellOf] at e

theorem mg_codeOf {t σ τ : Ty} (h : mg t = true) (e : codeOf t = some (σ, τ)) : mg σ = true ∧ mg τ = true := by
  cases t with
  | code a b =>
      simp only [codeOf, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      simpa [mg] using h
  | _ => simp [codeOf] at e

theorem mg_bufOf {t u : Ty} {μ : Mode} {n k : Idx} (h : mg t = true) (e : bufOf t = some (μ, n, u, k)) :
    mg u = true := by
  unfold bufOf at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, -, rfl, -⟩ := e
    simpa [mg] using h
  · simp at e

theorem mg_compTy (q : List Nat) : ∀ {t u : Ty}, mg t = true → compTy t q = some u → mg u = true := by
  induction q with
  | nil => intro t u h e; simp only [compTy, Option.some.injEq] at e; subst e; exact h
  | cons i q ih =>
      intro t u h e
      cases t with
      | prod a b =>
          simp only [mg, Bool.and_eq_true] at h
          match i, e with
          | 0, e => exact ih h.1 (by simpa [compTy] using e)
          | 1, e => exact ih h.2 (by simpa [compTy] using e)
          | n + 2, e => simp [compTy] at e
      | _ => simp [compTy] at e

theorem mg_xchg {cx : Cx} {t u o : Ty} (hx : XchgCell cx t u o) (h : mg t = true) : mg u = true ∧ mg o = true := by
  cases hx with
  | own _ hc => exact ⟨mg_cellOf h hc, mg_cellOf h hc⟩
  | rgn _ hc _ _ => rw [mg_adapt]; exact ⟨mg_cellOf h hc, mg_cellOf h hc⟩

/-! ## §2 `TvOK` and the context operations -/

theorem noIallV_shiftI (c : Nat) (t : Ty) : noIallV (t.shiftI c) = noIallV t := by
  induction t generalizing c <;> simp_all [Ty.shiftI, noIallV]

theorem noIallV_shiftT (c : Nat) (t : Ty) : noIallV (t.shiftT c) = noIallV t := by
  induction t generalizing c <;> simp_all [Ty.shiftT, noIallV] <;> split <;> rfl

/-- Every type the context records has its type variables below `ke.length`;
(T3c-4d) every variable's type exposes no opaque variable (`opaqueOK`, which
`Cx.bind` checks), so its layout is the same in both renditions (`sig_WitL`);
(T3c-5a) every type it records has its `μ` bodies guarded (`mg`).
(P1) The return type keeps no `∀` at a value position (`noIallV`):
established from the program's scope check at a block's entry. -/
def TvOK (cx : Cx) : Prop :=
  (∀ e ∈ cx.vars, tb cx.ke.length e.2.1 = true) ∧ (∀ tn ∈ cx.torn, tb cx.ke.length tn.ty = true) ∧
    tb cx.ke.length cx.ret = true ∧ (∀ e ∈ cx.vars, cx.opaqueOK e.2.1 = true) ∧
    (∀ e ∈ cx.vars, mg e.2.1 = true) ∧ (∀ tn ∈ cx.torn, mg tn.ty = true) ∧ mg cx.ret = true ∧
    noIallV cx.ret = true

/-- A context whose types are among another's, at the same number of type
variables. -/
theorem TvOK_of {cx c' : Cx} (hv : TvOK cx) (h2 : c'.ke.length = cx.ke.length) (h3 : c'.ret = cx.ret)
    (h1 : ∀ e ∈ c'.vars, ∃ e0 ∈ cx.vars, e.2.1 = e0.2.1)
    (h4 : ∀ tn ∈ c'.torn, ∃ tn0 ∈ cx.torn, tn.ty = tn0.ty) (h5 : c'.opq = cx.opq) : TvOK c' := by
  refine ⟨fun e he => ?_, fun tn htn => ?_, ?_, fun e he => ?_, fun e he => ?_, fun tn htn => ?_, ?_, ?_⟩
  · obtain ⟨e0, h0, he0⟩ := h1 e he; rw [h2, he0]; exact hv.1 _ h0
  · obtain ⟨tn0, h0, he0⟩ := h4 tn htn; rw [h2, he0]; exact hv.2.1 _ h0
  · rw [h2, h3]; exact hv.2.2.1
  · obtain ⟨e0, h0, he0⟩ := h1 e he; unfold Cx.opaqueOK; rw [h5, he0]; exact hv.2.2.2.1 _ h0
  · obtain ⟨e0, h0, he0⟩ := h1 e he; rw [he0]; exact hv.2.2.2.2.1 _ h0
  · obtain ⟨tn0, h0, he0⟩ := h4 tn htn; rw [he0]; exact hv.2.2.2.2.2.1 _ h0
  · rw [h3]; exact hv.2.2.2.2.2.2.1
  · rw [h3]; exact hv.2.2.2.2.2.2.2

theorem peek_tb {cx : Cx} {a : At} {t : Ty} (hv : TvOK cx) (h : cx.peek a = .ok t) :
    tb cx.ke.length t = true := by
  cases a with
  | lit n => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; simp [tb]
  | unit => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; simp [tb]
  | var x =>
      simp only [Cx.peek, Cx.find, bind_ok_iff] at h
      obtain ⟨⟨t', b⟩, hf, h⟩ := h
      split at hf
      · rename_i y u b' hy
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        split at h
        · simp at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          exact hv.1 _ (List.mem_of_find?_eq_some hy)
      · simp at hf

/-- (T3c-4d) A peeked type exposes no opaque variable. -/
theorem peek_opaqueOK {cx : Cx} {a : At} {t : Ty} (hv : TvOK cx) (h : cx.peek a = .ok t) :
    cx.opaqueOK t = true := by
  cases a with
  | lit n => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; simp [Cx.opaqueOK, Ty.guardT]
  | unit => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; simp [Cx.opaqueOK, Ty.guardT]
  | var x =>
      simp only [Cx.peek, Cx.find, bind_ok_iff] at h
      obtain ⟨⟨t', b⟩, hf, h⟩ := h
      split at hf
      · rename_i y u b' hy
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        split at h
        · simp at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          exact hv.2.2.2.1 _ (List.mem_of_find?_eq_some hy)
      · simp at hf

theorem use_TvOK {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) (hv : TvOK cx) :
    TvOK c₁ ∧ tb cx.ke.length t = true ∧ c₁.ke = cx.ke := by
  unfold Cx.use at h
  simp only [bind_ok_iff] at h
  obtain ⟨t', ht, h⟩ := h
  have htb := peek_tb hv ht
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨TvOK_of hv rfl rfl (fun e he => ?_) (fun tn htn => ⟨tn, htn, rfl⟩) rfl, htb, rfl⟩
      simp only [List.mem_map] at he
      obtain ⟨⟨z, u, b⟩, h0, rfl⟩ := he
      exact ⟨(z, u, b), h0, by dsimp only; split <;> rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hv, htb, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hv, htb, rfl⟩

/-- (T3c-5a) A peeked type has its `μ` bodies guarded. -/
theorem peek_mg {cx : Cx} {a : At} {t : Ty} (hv : TvOK cx) (h : cx.peek a = .ok t) : mg t = true := by
  cases a with
  | lit n => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; simp [mg]
  | unit => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; simp [mg]
  | var x =>
      simp only [Cx.peek, Cx.find, bind_ok_iff] at h
      obtain ⟨⟨t', b⟩, hf, h⟩ := h
      split at hf
      · rename_i y u b' hy
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        split at h
        · simp at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          exact hv.2.2.2.2.1 _ (List.mem_of_find?_eq_some hy)
      · simp at hf

theorem use_mg {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) (hv : TvOK cx) : mg t = true := by
  unfold Cx.use at h
  simp only [bind_ok_iff] at h
  obtain ⟨t', ht, h⟩ := h
  have hm := peek_mg hv ht
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hm
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hm
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hm

theorem bindCx_eq {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    c' = { cx with vars := (x, t, true) :: cx.vars } := by
  unfold Cx.bind at h
  split at h <;> split at h <;> (try split at h) <;>
    simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- `Cx.bind` checked that the bound type exposes no opaque variable. -/
theorem bind_opaqueOK {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') : cx.opaqueOK t = true := by
  unfold Cx.bind at h
  split at h <;> split at h <;> (try split at h) <;>
    simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem bind_TvOK {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') (hv : TvOK cx)
    (ht : tb cx.ke.length t = true) (hm : mg t = true) : TvOK c' ∧ c'.ke = cx.ke := by
  have ho := bind_opaqueOK h
  have hc := bindCx_eq h
  subst hc
  refine ⟨⟨?_, hv.2.1, hv.2.2.1, ?_, ?_, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2⟩, rfl⟩
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ht
    · exact hv.1 _ he
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ho
    · exact hv.2.2.2.1 _ he
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hm
    · exact hv.2.2.2.2.1 _ he

theorem push_TvOK {cx : Cx} (n : String) (hv : TvOK cx) : TvOK (cx.push n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [Cx.push, List.mem_map] at he
    obtain ⟨⟨z, u, b⟩, h0, rfl⟩ := he
    show tb cx.ke.length (u.shiftI 0) = true
    rw [tb_shiftI]; exact hv.1 _ h0
  · intro tn htn
    simp only [Cx.push, List.mem_map] at htn
    obtain ⟨tn0, h0, rfl⟩ := htn
    show tb cx.ke.length (tn0.ty.shiftI 0) = true
    rw [tb_shiftI]; exact hv.2.1 _ h0
  · show tb cx.ke.length (cx.ret.shiftI 0) = true
    rw [tb_shiftI]; exact hv.2.2.1
  · intro e he
    simp only [Cx.push, List.mem_map] at he
    obtain ⟨⟨z, u, b⟩, h0, rfl⟩ := he
    have := hv.2.2.2.1 _ h0
    simp only [Cx.opaqueOK, List.all_eq_true] at this ⊢
    intro k hk
    show (u.shiftI 0).guardT k = true
    rw [guardT_shiftI]; exact this k hk
  · intro e he
    simp only [Cx.push, List.mem_map] at he
    obtain ⟨⟨z, u, b⟩, h0, rfl⟩ := he
    show mg (u.shiftI 0) = true
    rw [mg_shiftI]; exact hv.2.2.2.2.1 _ h0
  · intro tn htn
    simp only [Cx.push, List.mem_map] at htn
    obtain ⟨tn0, h0, rfl⟩ := htn
    show mg (tn0.ty.shiftI 0) = true
    rw [mg_shiftI]; exact hv.2.2.2.2.2.1 _ h0
  · show mg (cx.ret.shiftI 0) = true
    rw [mg_shiftI]; exact hv.2.2.2.2.2.2.1
  · show noIallV (cx.ret.shiftI 0) = true
    rw [noIallV_shiftI]; exact hv.2.2.2.2.2.2.2

theorem pushT_TvOK {cx : Cx} (κ : Kind) (hv : TvOK cx) : TvOK (cx.pushT κ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [Cx.pushT, List.mem_map] at he
    obtain ⟨⟨z, u, b⟩, h0, rfl⟩ := he
    exact tb_shiftT_up u 0 _ (hv.1 _ h0)
  · intro tn htn
    simp only [Cx.pushT, List.mem_map] at htn
    obtain ⟨tn0, h0, rfl⟩ := htn
    exact tb_shiftT_up _ 0 _ (hv.2.1 _ h0)
  · exact tb_shiftT_up _ 0 _ hv.2.2.1
  · intro e he
    simp only [Cx.pushT, List.mem_map] at he
    obtain ⟨⟨z, u, b⟩, h0, rfl⟩ := he
    have := hv.2.2.2.1 _ h0
    simp only [Cx.opaqueOK, List.all_eq_true] at this
    simp only [Cx.opaqueOK, Cx.pushT, List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true,
      Function.comp]
    refine ⟨guardT_shiftT_at u 0, fun k hk => ?_⟩
    rw [guardT_shiftT_succ u 0 k (Nat.zero_le _)]; exact this k hk
  · intro e he
    simp only [Cx.pushT, List.mem_map] at he
    obtain ⟨⟨z, u, b⟩, h0, rfl⟩ := he
    exact (mg_shiftT u 0).trans (hv.2.2.2.2.1 _ h0)
  · intro tn htn
    simp only [Cx.pushT, List.mem_map] at htn
    obtain ⟨tn0, h0, rfl⟩ := htn
    exact (mg_shiftT _ 0).trans (hv.2.2.2.2.2.1 _ h0)
  · exact (mg_shiftT _ 0).trans hv.2.2.2.2.2.2.1
  · exact (noIallV_shiftT 0 _).trans hv.2.2.2.2.2.2.2

theorem observeCx_TvOK {cx : Cx} (x w : String) (acq : Bool) (hv : TvOK cx) : TvOK (observeCx cx x w acq) := by
  have hp := push_TvOK x hv
  refine TvOK_of hp rfl rfl (fun e he => ⟨e, he, rfl⟩) (fun tn htn => ?_) rfl
  simp only [observeCx, List.mem_map] at htn
  obtain ⟨tn0, h0, rfl⟩ := htn
  exact ⟨tn0, h0, by split <;> rfl⟩

theorem fenceCx_TvOK {cx : Cx} (f : Fence) (hv : TvOK cx) : TvOK (fenceCx cx f) := by
  unfold fenceCx
  dsimp only
  split <;> split <;>
    refine TvOK_of hv rfl rfl (fun e he => ⟨e, he, rfl⟩) (fun tn htn => ?_) rfl <;>
    first
    | exact ⟨tn, htn, rfl⟩
    | (simp only [List.mem_map] at htn; obtain ⟨tn0, h0, rfl⟩ := htn; exact ⟨tn0, h0, rfl⟩)

theorem endCx_TvOK {cx : Cx} (y : String) (hv : TvOK cx) : TvOK (cx.endCx y) := by
  refine TvOK_of hv rfl rfl (fun e he => ?_) (fun tn htn => ⟨tn, htn, rfl⟩) rfl
  simp only [Cx.endCx, List.mem_map, List.mem_filter] at he
  obtain ⟨⟨z, u, b⟩, ⟨h0, -⟩, rfl⟩ := he
  exact ⟨(z, u, b), h0, by dsimp only; split <;> rfl⟩

theorem nzCx_TvOK {cx : Cx} (u : Nat) (hv : TvOK cx) : TvOK (nzCx cx u) := push_TvOK "_nz" hv

theorem NoCx_TvOK {cx c' : Cx} {i j : Idx} (h : NoCx cx i j c') (hv : TvOK cx) : TvOK c' := by
  cases h with
  | same => exact hv
  | nzL _ _ => exact nzCx_TvOK _ hv
  | nzR _ _ => exact nzCx_TvOK _ hv

theorem LendCx_TvOK {cx c₂ : Cx} {acq rel : Bool} {r : Idx} {t : String} {P : Proto} {c c' : Nat}
    {k k' : Idx} (h : LendCx cx acq rel r t P c k c' k' c₂) (hv : TvOK cx) : TvOK c₂ := by
  cases h with
  | none _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | up _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | down _ _ _ _ hu hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1

/-! ### `instantiate` (moved here from TermSound) -/

theorem find_mem {p : Prog} {f : String} {d : Decl} (h : p.find f = .ok d) : d ∈ p := by
  unfold Prog.find at h
  split at h
  · rename_i d' hd; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact List.mem_of_find?_eq_some hd
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem instantiate_ok {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d is ts = .ok (at_, rt)) :
    ∃ us : List Idx, ts.length = d.tparams.length ∧
      at_ = substTs ts.reverse 0 0 (instT us 0 d.argTy) ∧ rt = substTs ts.reverse 0 0 (instT us 0 d.retTy) := by
  unfold instantiate at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i hlen
  split at h
  · simp at h
  rename_i hts
  have hl : ts.length = d.tparams.length := by simpa using hts
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i us _
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨us.reverse, hl, h.1.symm, h.2.symm⟩

/-- A `for` loop in `Except` that only ever yields ran its body on every element. -/
theorem forIn_ok {α : Type} {l : List α} {f : α → PUnit → Except String (ForInStep PUnit)} {u : PUnit}
    (hy : ∀ x r, f x PUnit.unit = .ok r → r = .yield PUnit.unit)
    (h : forIn l PUnit.unit f = .ok u) : ∀ x ∈ l, ∃ r, f x PUnit.unit = .ok r := by
  induction l with
  | nil => simp
  | cons y l ih =>
      simp only [List.forIn_cons] at h
      cases hf : f y PUnit.unit with
      | error e => rw [hf] at h; simp [bind, Except.bind] at h
      | ok r =>
          have hr := hy y r hf
          subst hr
          rw [hf] at h
          simp only [bind, Except.bind] at h
          intro x hx
          cases hx with
          | head => exact ⟨_, hf⟩
          | tail _ hx => exact ih h x hx

/-- `instantiate` checked every type argument: well formed, and exposing no
unpacked type. -/
theorem instantiate_ts {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d is ts = .ok (at_, rt)) :
    ∀ σ ∈ ts, cx.opaqueOK σ = true ∧ σ.wf cx.ke.length cx.inames.length = true := by
  unfold instantiate at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i hts
  have hl : ts.length = d.tparams.length := by simpa using hts
  split at h
  · simp at h
  rename_i hf
  have key := forIn_ok (fun x r hr => by
      split at hr <;> (try split at hr) <;> simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]) hf
  intro σ hσ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hσ
  have hm : (d.tparams[i]'(by rw [← hl]; exact hi), ts[i]) ∈ d.tparams.zip ts := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp only [List.length_zip]; omega, by simp⟩
  obtain ⟨r, hr⟩ := key _ hm
  split at hr
  · simp [throw, throwThe, MonadExceptOf.throw] at hr
  rename_i ha
  split at hr
  · simp [throw, throwThe, MonadExceptOf.throw] at hr
  rename_i ho
  simp only [Bool.not_eq_true', Bool.not_eq_false] at ha ho
  refine ⟨by simpa using ho, ?_⟩
  simp only [admitsIn, Bool.and_eq_true] at ha
  first | exact ha.1.1.1.1.1.1.1.1 | exact ha.1.1.1.1.1.1.1.1.1 | exact ha.1.1.1.1.1.1.1.1.1.1

/-- `instantiate` checked each type argument against its parameter's kind
(`admitsIn`), pairing them in order. -/
theorem instantiate_admits {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d is ts = .ok (at_, rt)) :
    ts.length = d.tparams.length ∧ ∀ κ σ, (κ, σ) ∈ d.tparams.zip ts → admitsIn cx κ σ = true := by
  unfold instantiate at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i hts
  have hl : ts.length = d.tparams.length := by simpa using hts
  split at h
  · simp at h
  rename_i hf
  have key := forIn_ok (fun x r hr => by
      split at hr <;> (try split at hr) <;> simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]) hf
  refine ⟨hl, fun κ σ hm => ?_⟩
  obtain ⟨r, hr⟩ := key _ hm
  split at hr
  · simp [throw, throwThe, MonadExceptOf.throw] at hr
  rename_i ha
  simpa using ha

/-- The instantiated signature stays within the caller's type variables. -/
theorem instantiate_tb {p : Prog} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d is ts = .ok (at_, rt)) (hd : DeclT p d) :
    tb cx.ke.length at_ = true ∧ tb cx.ke.length rt = true := by
  obtain ⟨us, hlen, rfl, rfl⟩ := instantiate_ok h
  have hts := instantiate_ts h
  obtain ⟨hwa, hwr, -, -, -⟩ := hd
  have hσ : ∀ σ ∈ ts.reverse, tb cx.ke.length σ = true :=
    fun σ hm => tb_of_wf σ (hts σ (List.mem_reverse.1 hm)).2
  have e : ∀ t : Ty, t.wf d.tparams.length d.idx.length = true →
      tb cx.ke.length (substTs ts.reverse 0 0 (instT us 0 t)) = true := by
    intro t hw
    have := tb_substTs hσ (instT us 0 t) 0 0
      (by rw [Nat.zero_add, List.length_reverse, hlen, tb_instT]; exact tb_of_wf t hw)
    rwa [Nat.zero_add] at this
  exact ⟨e _ hwa, e _ hwr⟩

/-- (T3c-5a) The instantiated signature has its `μ` bodies guarded. -/
theorem instantiate_mg {p : Prog} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d is ts = .ok (at_, rt)) (hd : DeclT p d) : mg at_ = true ∧ mg rt = true := by
  obtain ⟨us, -, rfl, rfl⟩ := instantiate_ok h
  have hts := instantiate_ts h
  obtain ⟨hwa, hwr, -, -, -⟩ := hd
  have hσ : ∀ σ ∈ ts.reverse, mg σ = true := fun σ hm => mg_of_wf σ (hts σ (List.mem_reverse.1 hm)).2
  exact ⟨mg_substTs hσ _ 0 0 (by rw [mg_instT]; exact mg_of_wf _ hwa),
    mg_substTs hσ _ 0 0 (by rw [mg_instT]; exact mg_of_wf _ hwr)⟩

/-! ## §3 Every operation rule preserves `TvOK` -/

/-- (E1) An extern's result type is closed and guarded. -/
theorem extSig_tb (n : ExtName) (k : Nat) : tb k n.sig.2 = true := by cases n <;> simp [ExtName.sig, tb]

theorem extSig_mg (n : ExtName) : mg n.sig.2 = true := by cases n <;> simp [ExtName.sig, mg]

theorem OpT_TvOK {p : Prog} (hP : ProgT p) {cx c' : Cx} {x : String} {op : Op}
    (h : OpT p cx x op c') (hv : TvOK cx) : TvOK c' := by
  cases h with
  | atom hu hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact ht) (use_mg hu hv)).1
  | pair hu1 hu2 hb =>
      obtain ⟨h1, ht, hk1⟩ := use_TvOK hu1 hv
      obtain ⟨h2, hu, hk2⟩ := use_TvOK hu2 h1
      exact (bind_TvOK hb h2 (by simp only [tb, Bool.and_eq_true, hk2, hk1] at hu ⊢; exact ⟨ht, hu⟩)
        (by simp only [mg, Bool.and_eq_true]; exact ⟨use_mg hu1 hv, use_mg hu2 h1⟩)).1
  | inl hw hu hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simp only [tb, Bool.and_eq_true]; exact ⟨ht, tb_of_wf _ hw⟩)
        (by simp only [mg, Bool.and_eq_true]; exact ⟨use_mg hu hv, mg_of_wf _ hw⟩)).1
  | inr hw hu hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simp only [tb, Bool.and_eq_true]; exact ⟨tb_of_wf _ hw, ht⟩)
        (by simp only [mg, Bool.and_eq_true]; exact ⟨mg_of_wf _ hw, use_mg hu hv⟩)).1
  | addS _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | addI _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | subS _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | new hu _ hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simpa [tb] using ht) (by simpa [mg] using use_mg hu hv)).1
  | publish hu _ hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simpa [tb] using ht) (by simpa [mg] using use_mg hu hv)).1
  | publishBuf hu _ hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simpa [tb] using ht) (by simpa [mg] using use_mg hu hv)).1
  | intoRgn _ hu _ hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simpa [tb] using ht) (by simpa [mg] using use_mg hu hv)).1
  | intoRgnBuf _ hu _ hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simpa [tb] using ht) (by simpa [mg] using use_mg hu hv)).1
  | newBuf hw _ _ _ _ hb => exact (bind_TvOK hb hv (by simpa [tb] using tb_of_wf _ hw) (by simpa [mg] using mg_of_wf _ hw)).1
  | idxOwn hp hbuf _ _ _ _ hu hb =>
      have hu' := tb_bufOf (peek_tb hv hp) hbuf
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simpa [tb] using hu')
        (by simpa [mg] using mg_bufOf (peek_mg hv hp) hbuf)).1
  | idxShared hp hbuf _ _ _ _ _ hb =>
      have hu' := tb_bufOf (peek_tb hv hp) hbuf
      exact (bind_TvOK hb hv (by simpa [tb] using hu') (by simpa [mg] using mg_bufOf (peek_mg hv hp) hbuf)).1
  | bufInit hu hbuf _ _ _ hu2 _ hb =>
      obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
      have hu' := tb_bufOf ht hbuf
      obtain ⟨h2, -, hk2⟩ := use_TvOK hu2 h1
      exact (bind_TvOK hb h2 (by rw [hk2, hk]; simpa [tb] using hu')
        (by simpa [mg] using mg_bufOf (use_mg hu hv) hbuf)).1
  | null hw hb => exact (bind_TvOK hb hv (tb_of_wf _ hw) (mg_of_wf _ hw)).1
  | fold hw hu _ hb =>
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact tb_of_wf _ hw) (mg_of_wf _ hw)).1
  | fldOwn hp hc hunf _ hu hb =>
      have hu' := tb_unfold1 (tb_cellOf (peek_tb hv hp) hc)
      rw [hunf] at hu'
      simp only [tb, Bool.and_eq_true] at hu'
      have hm' := mg_unfold1 (mg_cellOf (peek_mg hv hp) hc)
      rw [hunf] at hm'
      simp only [mg, Bool.and_eq_true] at hm'
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; simp only [tb]; split <;> simp [hu'])
        (by simp only [mg]; split <;> simp [hm'])).1
  | fldShared hp hc _ hunf _ hb =>
      have hu' := tb_unfold1 (tb_cellOf (peek_tb hv hp) hc)
      rw [hunf] at hu'
      simp only [tb, Bool.and_eq_true] at hu'
      have hm' := mg_unfold1 (mg_cellOf (peek_mg hv hp) hc)
      rw [hunf] at hm'
      simp only [mg, Bool.and_eq_true] at hm'
      exact (bind_TvOK hb hv (by simp only [tb]; split <;> simp [hu']) (by simp only [mg]; split <;> simp [hm'])).1
  | loadWord _ _ _ hb => exact (bind_TvOK hb (observeCx_TvOK _ _ _ hv) (by simp [tb]) (by simp [mg])).1
  | loadOwn hp _ hc _ hb => exact (bind_TvOK hb hv (tb_cellOf (peek_tb hv hp) hc) (mg_cellOf (peek_mg hv hp) hc)).1
  | loadPub hp _ hc _ _ hb => exact (bind_TvOK hb hv (tb_cellOf (peek_tb hv hp) hc) (mg_cellOf (peek_mg hv hp) hc)).1
  | loadRgn hp _ hc _ _ hb =>
      exact (bind_TvOK hb hv (by rw [tb_adapt]; exact tb_cellOf (peek_tb hv hp) hc)
        (by rw [mg_adapt]; exact mg_cellOf (peek_mg hv hp) hc)).1
  | loadCap hp _ hc _ _ _ hb =>
      exact (bind_TvOK hb hv (by rw [tb_adapt]; exact tb_cellOf (peek_tb hv hp) hc)
        (by rw [mg_adapt]; exact mg_cellOf (peek_mg hv hp) hc)).1
  | loadTorn hp _ hc _ _ _ =>
      refine ⟨hv.1, fun tn htn => ?_, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, fun tn htn => ?_, hv.2.2.2.2.2.2⟩
      · simp only [List.mem_cons] at htn
        rcases htn with rfl | htn
        · show tb cx.ke.length (adapt _ _) = true
          rw [tb_adapt]; exact tb_cellOf (peek_tb hv hp) hc
        · exact hv.2.1 _ htn
      · simp only [List.mem_cons] at htn
        rcases htn with rfl | htn
        · show mg (adapt _ _) = true
          rw [mg_adapt]; exact mg_cellOf (peek_mg hv hp) hc
        · exact hv.2.2.2.2.2.1 _ htn
  | storeWordGive _ _ hu _ _ _ _ _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | storeWordHand _ _ hu _ _ _ _ _ _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | storeWordKeep _ _ hu _ _ _ _ _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | storeOwn _ _ _ _ hu _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | storePub _ _ _ _ hu _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | storeRgn _ _ _ _ hu _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | storeCap _ _ _ _ hu _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | fence hb => exact (bind_TvOK hb (fenceCx_TvOK _ hv) (by simp [tb]) (by simp [mg])).1
  | mkWord _ _ hu _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | mkWordGhost _ _ hu _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | mkWord2 _ _ hu _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | ldp _ _ hb => exact (bind_TvOK hb (push_TvOK _ (push_TvOK _ hv)) (by simp [tb]) (by simp [mg])).1
  | mkEPair _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | mkTicket _ _ _ _ _ hu _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | claim _ _ _ hu _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | fetchCell _ _ _ hu _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | fetchEpoch _ _ _ _ _ _ hb =>
      exact (bind_TvOK hb hv (by simp [tb, fetchEpochTy]) (by simp [mg, fetchEpochTy])).1
  | fetchShare _ _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | stpGive _ _ hu _ _ _ _ _ _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | stpKeep _ _ hu _ _ _ _ _ _ _ _ _ _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | pack _ hw hu _ _ hb =>
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact tb_of_wf _ hw) (mg_of_wf _ hw)).1
  | packT _ hw _ hu _ _ hb =>
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact tb_of_wf _ hw) (mg_of_wf _ hw)).1
  | validate hf _ _ _ hb =>
      exact (bind_TvOK hb hv (hv.2.1 _ (List.mem_of_find?_eq_some hf))
        (hv.2.2.2.2.2.1 _ (List.mem_of_find?_eq_some hf))).1
  | call hfind hinst hu _ _ hb =>
      have hr := (instantiate_tb hinst (hP _ (find_mem hfind))).2
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact hr) (instantiate_mg hinst (hP _ (find_mem hfind))).2).1
  | borrow _ _ _ hu hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | freeze hu _ hb =>
      obtain ⟨h1, -, -⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by simp [tb]) (by simp [mg])).1
  | endBorrow _ _ hb => exact (bind_TvOK hb (endCx_TvOK _ hv) (by simp [tb]) (by simp [mg])).1
  | xchg hp hx hu _ hb =>
      have ho := (tb_xchg hx (peek_tb hv hp)).2
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact ho) (mg_xchg hx (peek_mg hv hp)).2).1
  | fnptr hfind htp _ hb =>
      rename_i d
      obtain ⟨hwa, hwr, -, -, -⟩ := hP _ (find_mem hfind)
      rw [htp] at hwa hwr
      exact (bind_TvOK hb hv (by
        simp only [tb, Bool.and_eq_true]
        exact ⟨tb_mono _ (tb_of_wf _ hwa) (Nat.zero_le _), tb_mono _ (tb_of_wf _ hwr) (Nat.zero_le _)⟩)
        (by simp only [mg, Bool.and_eq_true]; exact ⟨mg_of_wf _ hwa, mg_of_wf _ hwr⟩)).1
  | callc hp hc hu _ _ hb =>
      have hτ := (tb_codeOf (peek_tb hv hp) hc).2
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact hτ) (mg_codeOf (peek_mg hv hp) hc).2).1
  | rem _ _ _ _ hb =>
      exact (bind_TvOK hb (push_TvOK x (push_TvOK (x ++ "_d") hv)) (by simp [tb]) (by simp [mg])).1
  | nameI _ hb => exact (bind_TvOK hb (push_TvOK x hv) (by simp [tb]) (by simp [mg])).1
  | spawn hu _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb => exact (bind_TvOK hb (use_TvOK hu hv).1 (by simp [tb]) (by simp [mg])).1
  | ext hu _ hb => exact (bind_TvOK hb (use_TvOK hu hv).1 (extSig_tb _ _) (extSig_mg _)).1
  | xchgAt hp hbuf _ _ _ _ hu _ hb =>
      have hu' := tb_bufOf (peek_tb hv hp) hbuf
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact hu') (mg_bufOf (peek_mg hv hp) hbuf)).1
  | loadAt hp hbuf _ _ _ _ hb => exact (bind_TvOK hb hv (tb_bufOf (peek_tb hv hp) hbuf) (mg_bufOf (peek_mg hv hp) hbuf)).1
  | bits _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | bit1 _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | vmatch _ _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | band _ _ _ _ hb =>
      exact (bind_TvOK hb (push_TvOK x (push_TvOK (x ++ "_d") hv)) (by simp [tb]) (by simp [mg])).1
  | zero hw _ _ hb => exact (bind_TvOK hb hv (tb_of_wf _ hw) (mg_of_wf _ hw)).1
  | xchgAtF hp hbuf hq _ _ _ _ _ hu _ hb =>
      have hc := tb_compTy _ (tb_bufOf (peek_tb hv hp) hbuf) hq
      obtain ⟨h1, -, hk⟩ := use_TvOK hu hv
      exact (bind_TvOK hb h1 (by rw [hk]; exact hc) (mg_compTy _ (mg_bufOf (peek_mg hv hp) hbuf) hq)).1
  | loadAtF hp hbuf hq _ _ _ _ _ hb =>
      exact (bind_TvOK hb hv (tb_compTy _ (tb_bufOf (peek_tb hv hp) hbuf) hq)
        (mg_compTy _ (mg_bufOf (peek_mg hv hp) hbuf) hq)).1
  | cvt _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | toInt _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | asLanes _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | fop _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | fcmp _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | fop1 _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | lane _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | setLane _ _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | ldlw _ _ _ _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | stlw _ _ _ _ _ _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | ldl _ _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1
  | stl _ _ _ _ _ _ _ _ hb => exact (bind_TvOK hb hv (by simp [tb]) (by simp [mg])).1

/-! ## §4 The structural rules of `Typed`, and `declCx` -/

theorem split_TvOK {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {u v : Ty}
    (hu : cx.use a = .ok (.prod u v, c₁)) (hb1 : c₁.bind x u = .ok c₂) (hb2 : c₂.bind y v = .ok c₃)
    (hv : TvOK cx) : TvOK c₃ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  simp only [tb, Bool.and_eq_true] at ht
  have hm := use_mg hu hv
  simp only [mg, Bool.and_eq_true] at hm
  obtain ⟨h2, hk2⟩ := bind_TvOK hb1 h1 (by rw [hk]; exact ht.1) hm.1
  exact (bind_TvOK hb2 h2 (by rw [hk2, hk]; exact ht.2) hm.2).1

theorem unpack_TvOK {cx c₁ c₂ : Cx} {a : At} {i x : String} {b : Ty}
    (hu : cx.use a = .ok (.iex b, c₁)) (hb : (c₁.push i).bind x b = .ok c₂) (hv : TvOK cx) : TvOK c₂ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  exact (bind_TvOK hb (push_TvOK i h1) (by show tb c₁.ke.length b = true; rw [hk]; simpa [tb] using ht)
    (by simpa [mg] using use_mg hu hv)).1

theorem unpackT_TvOK {cx c₁ c₂ : Cx} {a : At} {x : String} {κ : Kind} {b : Ty}
    (hu : cx.use a = .ok (.tex κ b, c₁)) (hb : (c₁.pushT κ).bind x b = .ok c₂) (hv : TvOK cx) : TvOK c₂ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  exact (bind_TvOK hb (pushT_TvOK κ h1)
    (by show tb (c₁.ke.length + 1) b = true; rw [hk]; simpa [tb] using ht)
    (by simpa [mg] using use_mg hu hv)).1

theorem region_TvOK {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {u T : Ty}
    (hu : cx.use a = .ok (T, c₁)) (hT : tb cx.ke.length T = true → tb cx.ke.length u = true)
    (hM : mg T = true → mg u = true)
    (hb1 : (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂)
    (hb2 : c₂.bind tn (.tok (.var 0) none) = .ok c₃) (hv : TvOK cx) : TvOK c₃ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  obtain ⟨h2, -⟩ := bind_TvOK hb1 (push_TvOK rn h1)
    (by show tb c₁.ke.length (Ty.ptr _ (u.shiftI 0)) = true
        simp only [tb, tb_shiftI]; rw [hk]; exact hT ht)
    (by show mg (Ty.ptr _ (u.shiftI 0)) = true
        simp only [mg, mg_shiftI]; exact hM (use_mg hu hv))
  exact (bind_TvOK hb2 h2 (by simp [tb]) (by simp [mg])).1

theorem regionBuf_TvOK {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {n k : Idx} {u : Ty}
    (hu : cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁))
    (hb1 : (c₁.push rn).bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0)) = .ok c₂)
    (hb2 : c₂.bind tn (.tok (.var 0) none) = .ok c₃) (hv : TvOK cx) : TvOK c₃ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  obtain ⟨h2, -⟩ := bind_TvOK hb1 (push_TvOK rn h1)
    (by show tb c₁.ke.length (Ty.refine (.loc _ ((Ty.array n u).shiftI 0)) _) = true
        simp only [tb, tb_shiftI]; rw [hk]; simpa [tb] using ht)
    (by show mg (Ty.refine (.loc _ ((Ty.array n u).shiftI 0)) _) = true
        simp only [mg, mg_shiftI]; simpa [mg] using use_mg hu hv)
  exact (bind_TvOK hb2 h2 (by simp [tb]) (by simp [mg])).1

theorem openPub_TvOK {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn cn : String} {u : Ty}
    (hu : cx.use a = .ok (.ptr .pub u, c₁))
    (hb1 : (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂)
    (hb2 : c₂.bind cn (.cap .pub (.var 0)) = .ok c₃) (hv : TvOK cx) : TvOK c₃ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  obtain ⟨h2, -⟩ := bind_TvOK hb1 (push_TvOK rn h1)
    (by show tb c₁.ke.length (Ty.ptr _ (u.shiftI 0)) = true
        simp only [tb, tb_shiftI]; rw [hk]; simpa [tb] using ht)
    (by show mg (Ty.ptr _ (u.shiftI 0)) = true
        simp only [mg, mg_shiftI]; simpa [mg] using use_mg hu hv)
  exact (bind_TvOK hb2 h2 (by simp [tb]) (by simp [mg])).1

theorem case_TvOK {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {u v : Ty}
    (hu : cx.use a = .ok (.sum u v, c₁)) (hb1 : c₁.bind x u = .ok c₂) (hb2 : c₁.bind y v = .ok c₃)
    (hv : TvOK cx) : TvOK c₂ ∧ TvOK c₃ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  simp only [tb, Bool.and_eq_true] at ht
  have hm := use_mg hu hv
  simp only [mg, Bool.and_eq_true] at hm
  exact ⟨(bind_TvOK hb1 h1 (by rw [hk]; exact ht.1) hm.1).1, (bind_TvOK hb2 h1 (by rw [hk]; exact ht.2) hm.2).1⟩

theorem ifnull_TvOK {cx c₁ c₂ : Cx} {a : At} {y : String} {μ : Mode} {u : Ty}
    (hu : cx.use a = .ok (.ptrOpt μ u, c₁)) (hb : c₁.bind y (.ptr μ u) = .ok c₂) (hv : TvOK cx) :
    TvOK c₁ ∧ TvOK c₂ := by
  obtain ⟨h1, ht, hk⟩ := use_TvOK hu hv
  exact ⟨h1, (bind_TvOK hb h1 (by rw [hk]; simpa [tb] using ht) (by simpa [mg] using use_mg hu hv)).1⟩

/-- (P1) Every code block's return type is `∀`-free at value positions
(`noIallV`; from `ProgScopeOK`'s `drf d.retTy`).  A class, so that the step
lemmas carry it to `declCx_TvOK` without changing their call sites. -/
class ProgRetIall (p : Prog) : Prop where
  ret : ∀ d ∈ p, noIallV d.retTy = true

/-- A declaration's body context: its signature is well formed. -/
theorem declCx_TvOK {p : Prog} {d : Decl} (h : DeclT p d) (hR : noIallV d.retTy = true) : TvOK (declCx d) := by
  obtain ⟨hwa, hwr, -, -, -⟩ := h
  refine ⟨?_, fun tn htn => by simp [declCx] at htn, ?_, fun e _ => by simp [declCx, Cx.opaqueOK], ?_,
    fun tn htn => by simp [declCx] at htn, mg_of_wf _ hwr, hR⟩
  · intro e he
    simp only [declCx, List.mem_singleton] at he
    subst he
    simp only [declCx, List.length_map, List.length_reverse]
    exact tb_of_wf _ hwa
  · simp only [declCx, List.length_map, List.length_reverse]
    exact tb_of_wf _ hwr
  · intro e he
    simp only [declCx, List.mem_singleton] at he
    subst he
    exact mg_of_wf _ hwa

#print axioms tb_of_wf
#print axioms guardT_of_tb
#print axioms lt_of_guardT
#print axioms tb_substT
#print axioms tb_substTs
#print axioms instantiate_tb
#print axioms OpT_TvOK
#print axioms declCx_TvOK
#print axioms noIallV_shiftI
#print axioms noIallV_shiftT
#print axioms peek_opaqueOK
#print axioms bind_opaqueOK
#print axioms instantiate_admits
#print axioms mg_of_wf
#print axioms mg_unfold1
#print axioms instantiate_mg
#print axioms peek_mg
#print axioms mg_cl

end TermTv
