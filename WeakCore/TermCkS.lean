import WeakCore.TermCk0

/-! # TermCkS (was TermA4S): A1 checker (A) spike prototypes

`wrapTop` (the A1 rule without descending into references or code), its substitution lemma
through `cl` (the nested-`substTs` case of `enter` and of a new cell's type), the witness clause
`WitA` at `call` (r3) and at `unpackT` (r1), and the new cell's `wrapTop` (r4).
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermClose TermScope TermTv




theorem wrapTopE_of_wrapOKE : ∀ (t : Ty) (env : List Bool), wrapOKE env t = true → wrapTopE env t = true := by
  intro t
  induction t with
  | sum a b iha ihb =>
      intro env h; simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [wrapTopE, Bool.and_eq_true]; exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, iha env h.1.2⟩, ihb env h.2⟩
  | prod a b iha ihb =>
      intro env h; simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [wrapTopE, Bool.and_eq_true]; exact ⟨iha env h.1, ihb env h.2⟩
  | iex t ih =>
      intro env h; simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [wrapTopE, Bool.and_eq_true]; exact ⟨h.1, ih env h.2⟩
  | refine t ψ ih =>
      intro env h; simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [wrapTopE, Bool.and_eq_true]; exact ⟨h.1, ih env h.2⟩
  | tex κ t ih =>
      intro env h; simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [wrapTopE, Bool.and_eq_true]; exact ⟨h.1, ih _ h.2⟩
  | mu t ih => intro env h; simp only [wrapOKE] at h; simp only [wrapTopE]; exact ih _ h
  | array i t ih => intro env h; simp only [wrapOKE] at h; simp only [wrapTopE]; exact ih _ h
  | iall t ih => intro env h; simp only [wrapOKE] at h; simp only [wrapTopE]; exact ih _ h
  | _ => intro env _; rfl

theorem wrapTop_of_wrapOK {t : Ty} (h : wrapOK t = true) : wrapTop t = true :=
  wrapTopE_of_wrapOKE t [] h

/-- `wrapTopE` reads only the variables a type mentions. -/
theorem rwT_tb : ∀ (t : Ty) (c : Nat) (e1 e2 : List Bool), tb c t = true →
    (∀ k, k < c → e1.getD k false = e2.getD k false) → wrapTopE e1 t = wrapTopE e2 t := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro c e1 e2 ht h; simp only [tb, Bool.and_eq_true] at ht
      simp only [wrapTopE, iha c e1 e2 ht.1 h, ihb c e1 e2 ht.2 h]
  | sum a b iha ihb =>
      intro c e1 e2 ht h; simp only [tb, Bool.and_eq_true] at ht
      simp only [wrapTopE, iha c e1 e2 ht.1 h, ihb c e1 e2 ht.2 h,
        (rw_tb a c e1 e2 ht.1 h).1, (rw_tb b c e1 e2 ht.2 h).1]
  | array i t ih => intro c e1 e2 ht h; simp only [tb] at ht; simp only [wrapTopE, ih c e1 e2 ht h]
  | iall t ih => intro c e1 e2 ht h; simp only [tb] at ht; simp only [wrapTopE, ih c e1 e2 ht h]
  | iex t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht
      simp only [wrapTopE, ih c e1 e2 ht h, (rw_tb t c e1 e2 ht h).1]
  | refine t ψ ih =>
      intro c e1 e2 ht h; simp only [tb] at ht
      simp only [wrapTopE, ih c e1 e2 ht h, (rw_tb t c e1 e2 ht h).1]
  | tex κ t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht
      simp only [wrapTopE, ih (c + 1) _ _ ht (agree_cons h rfl),
        (rw_tb t (c + 1) _ _ ht (agree_cons (e1 := e1) (e2 := e2) h rfl)).1]
  | mu t ih =>
      intro c e1 e2 ht h; simp only [tb] at ht
      have h0 := (rw_tb t (c + 1) (false :: e1) (false :: e2) ht (agree_cons h rfl)).1
      simp only [wrapTopE]; exact ih (c + 1) _ _ ht (agree_cons h h0)
  | _ => intro c e1 e2 _ _; rfl

theorem wrapTopE_closed {t : Ty} (ht : tb 0 t = true) (e : List Bool) : wrapTopE e t = wrapTop t :=
  rwT_tb t 0 e [] ht (fun _ hk => absurd hk (Nat.not_lt_zero _))

/-! ## The substitution lemma (r3, r4): `cl` at `argTop` witnesses -/

/-- **`cl` keeps `wrapTop`**, at witnesses that are `argTop` off the opaque set `O`, when every
opaque variable is guarded (`guardT`, which `Cx.bind` and `instantiate` check). -/
theorem top_cl {ρ : Nat → Nat} {W : Nat → Ty} {O : List Nat} {n : Nat}
    (hWc : ∀ k, tb 0 (W k) = true) (hW : ∀ k, k < n → k ∉ O → argTop (W k) = true) :
    ∀ (σ : Ty) (c d : Nat) (env : List Bool), env.length = c → tb (c + n) σ = true →
      (∀ j ∈ O, σ.guardT (j + c) = true) →
      rcarE env (cl ρ W c d σ) = rcarE env σ ∧
        (wrapOKE env σ = true → wrapTopE env (cl ρ W c d σ) = true) := by
  intro σ
  induction σ with
  | tvar k =>
      intro c d env hl ht hg
      simp only [tb, decide_eq_true_eq] at ht
      simp only [cl]
      by_cases hk : k < c
      · refine ⟨?_, fun _ => ?_⟩ <;> simp [hk, wrapTopE]
      · simp only [hk, ite_false]
        have hnO : k - c ∉ O := by
          intro hm
          have := hg _ hm
          simp only [Ty.guardT, bne_iff_ne, ne_eq] at this
          exact this (by omega)
        have hA := hW (k - c) (by omega) hnO
        simp only [argTop, Bool.and_eq_true, Bool.not_eq_true'] at hA
        have e1 : env.getD k false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : env.length ≤ k)]
        refine ⟨?_, fun _ => ?_⟩
        · rw [rcarE_closed (hWc _), hA.2]; simp only [rcarE, e1]
        · rw [wrapTopE_closed (hWc _)]; exact hA.1
  | prod a b iha ihb =>
      intro c d env hl ht hg
      simp only [tb, Bool.and_eq_true] at ht
      have ga : ∀ j ∈ O, a.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simp only [Ty.guardT, Bool.and_eq_true] at this; exact this.1
      have gb : ∀ j ∈ O, b.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simp only [Ty.guardT, Bool.and_eq_true] at this; exact this.2
      obtain ⟨a1, a2⟩ := iha c d env hl ht.1 ga
      obtain ⟨b1, b2⟩ := ihb c d env hl ht.2 gb
      refine ⟨by simp only [cl, rcarE, a1, b1], fun h => ?_⟩
      simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [cl, wrapTopE, Bool.and_eq_true]; exact ⟨a2 h.1, b2 h.2⟩
  | sum a b iha ihb =>
      intro c d env hl ht hg
      simp only [tb, Bool.and_eq_true] at ht
      have ga : ∀ j ∈ O, a.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simp only [Ty.guardT, Bool.and_eq_true] at this; exact this.1
      have gb : ∀ j ∈ O, b.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simp only [Ty.guardT, Bool.and_eq_true] at this; exact this.2
      obtain ⟨a1, a2⟩ := iha c d env hl ht.1 ga
      obtain ⟨b1, b2⟩ := ihb c d env hl ht.2 gb
      refine ⟨by simp only [cl, rcarE, a1, b1], fun h => ?_⟩
      simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [cl, wrapTopE, Bool.and_eq_true, a1, b1]
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, a2 h.1.2⟩, b2 h.2⟩
  | array i t ih =>
      intro c d env hl ht hg
      simp only [tb] at ht
      have gt : ∀ j ∈ O, t.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simpa only [Ty.guardT] using this
      refine ⟨rfl, fun h => ?_⟩
      simp only [wrapOKE] at h
      simp only [cl, wrapTopE]; exact (ih c d env hl ht gt).2 h
  | iall t ih =>
      intro c d env hl ht hg
      simp only [tb] at ht
      have gt : ∀ j ∈ O, t.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simpa only [Ty.guardT] using this
      obtain ⟨h1, h2⟩ := ih c (d + 1) env hl ht gt
      refine ⟨by simp only [cl, rcarE, h1], fun h => ?_⟩
      simp only [wrapOKE] at h
      simp only [cl, wrapTopE]; exact h2 h
  | iex t ih =>
      intro c d env hl ht hg
      simp only [tb] at ht
      have gt : ∀ j ∈ O, t.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simpa only [Ty.guardT] using this
      obtain ⟨h1, h2⟩ := ih c (d + 1) env hl ht gt
      refine ⟨by simp only [cl, rcarE, h1], fun h => ?_⟩
      simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [cl, wrapTopE, Bool.and_eq_true, h1]; exact ⟨h.1, h2 h.2⟩
  | refine t ψ ih =>
      intro c d env hl ht hg
      simp only [tb] at ht
      have gt : ∀ j ∈ O, t.guardT (j + c) = true := fun j hj => by
        have := hg j hj; simpa only [Ty.guardT] using this
      obtain ⟨h1, h2⟩ := ih c d env hl ht gt
      refine ⟨by simp only [cl, rcarE, h1], fun h => ?_⟩
      simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [cl, wrapTopE, Bool.and_eq_true, h1]; exact ⟨h.1, h2 h.2⟩
  | tex κ t ih =>
      intro c d env hl ht hg
      simp only [tb] at ht
      have gt : ∀ j ∈ O, t.guardT (j + (c + 1)) = true := fun j hj => by
        have := hg j hj; simp only [Ty.guardT] at this; rwa [← Nat.add_assoc]
      obtain ⟨h1, h2⟩ := ih (c + 1) d (false :: env) (by simp [hl]) (by rwa [Nat.add_right_comm]) gt
      refine ⟨by simp only [cl, rcarE, h1], fun h => ?_⟩
      simp only [wrapOKE, Bool.and_eq_true] at h
      simp only [cl, wrapTopE, Bool.and_eq_true, h1]; exact ⟨h.1, h2 h.2⟩
  | mu t ih =>
      intro c d env hl ht hg
      simp only [tb] at ht
      have ht' : tb (c + 1 + n) t = true := by rwa [Nat.add_right_comm]
      have gt : ∀ j ∈ O, t.guardT (j + (c + 1)) = true := fun j hj => by
        have := hg j hj; simp only [Ty.guardT] at this; rwa [← Nat.add_assoc]
      have h0 := (ih (c + 1) d (false :: env) (by simp [hl]) ht' gt).1
      obtain ⟨h1, h2⟩ := ih (c + 1) d (rcarE (false :: env) t :: env) (by simp [hl]) ht' gt
      refine ⟨by simp only [cl, rcarE, h0, h1], fun h => ?_⟩
      simp only [wrapOKE] at h
      simp only [cl, wrapTopE, h0]; exact h2 h
  | ptr μ t _ => intro c d env _ _ _; exact ⟨rfl, fun _ => rfl⟩
  | ptrOpt μ t _ => intro c d env _ _ _; exact ⟨rfl, fun _ => rfl⟩
  | loc μ t _ => intro c d env _ _ _; exact ⟨rfl, fun _ => rfl⟩
  | code a b _ _ => intro c d env _ _ _; exact ⟨rfl, fun _ => rfl⟩
  | _ => intro c d env _ _ _; exact ⟨rfl, fun _ => rfl⟩

/-- (r4) **A new cell's type is `wrapTop`**: its static content type is `wrapOK` and guards the
opaque variables; its non-opaque witnesses are `argTop`. -/
theorem wrapTop_cl0 {ρ : Nat → Nat} {W : Nat → Ty} {O : List Nat} {n : Nat} {σ : Ty}
    (hWc : ∀ k, tb 0 (W k) = true) (hW : ∀ k, k < n → k ∉ O → argTop (W k) = true)
    (ht : tb n σ = true) (hg : ∀ j ∈ O, σ.guardT j = true) (hw : wrapOK σ = true) :
    wrapTop (cl ρ W 0 0 σ) = true :=
  (top_cl hWc hW σ 0 0 [] rfl (by simpa using ht) (by simpa using hg)).2 hw

/-- (r3) **A checked type argument closes to an `argTop` witness.** -/
theorem argTop_cl0 {ρ : Nat → Nat} {W : Nat → Ty} {O : List Nat} {n : Nat} {σ : Ty}
    (hWc : ∀ k, tb 0 (W k) = true) (hW : ∀ k, k < n → k ∉ O → argTop (W k) = true)
    (ht : tb n σ = true) (hg : ∀ j ∈ O, σ.guardT j = true) (ha : argOK σ = true) :
    argTop (cl ρ W 0 0 σ) = true := by
  simp only [argOK, Bool.and_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨h1, h2⟩ := top_cl (ρ := ρ) hWc hW σ 0 0 [] rfl (by simpa using ht) (by simpa using hg)
  simp only [argTop, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨h2 ha.1, by simpa [rcar] using h1.trans ha.2⟩

/-! ## The witness clause -/


/-- (r3) **`WitA` at `call`/`tail`**: the callee's context has no opaque variable, and each
witness is a checked type argument (`opArgOK`) closed at the caller's witnesses. -/
theorem WitA_call {ρ₀ : Nat → Nat} {ω : Nat → Ty} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hA : WitA cx ω) (hWc : ∀ k, tb 0 (ω k) = true)
    (hinst : instantiate cx d is ts = .ok (at_, rt)) (hts : ts.all argOK = true) :
    WitA (declCx d) (subW ρ₀ ω ts.reverse) := by
  obtain ⟨hl, -⟩ := instantiate_admits hinst
  have hT := instantiate_ts hinst
  intro k hk _
  have hk' : k < ts.reverse.length := by simpa [declCx, hl] using hk
  have e : ts.reverse[k]? = some (ts.reverse[k]'hk') := List.getElem?_eq_getElem hk'
  have hm : ts.reverse[k]'hk' ∈ ts := List.mem_reverse.1 (List.getElem_mem hk')
  show argTop (match ts.reverse[k]? with | some σ => cl ρ₀ ω 0 0 σ | none => ω (k - ts.reverse.length)) = true
  rw [e]
  obtain ⟨ho, hwf⟩ := hT _ hm
  refine argTop_cl0 (O := cx.opq) (n := cx.ke.length) hWc hA (tb_of_wf _ hwf) (fun j hj => ?_)
    (List.all_eq_true.1 hts _ hm)
  simp only [Cx.opaqueOK, List.all_eq_true] at ho
  exact ho j hj

/-- (r1) **`WitA` at `unpackT`**: the fresh variable is opaque; the others move up one on both
sides. -/
theorem WitA_pushT {ω ω' : Nat → Ty} {cx : Cx} {κ : Kind} (hA : WitA cx ω) (hw : ∀ k, ω' (k + 1) = ω k) :
    WitA (cx.pushT κ) ω' := by
  intro k hk ho
  cases k with
  | zero => exact absurd (by simp [Cx.pushT]) ho
  | succ k =>
      rw [hw k]
      refine hA k (by simpa [Cx.pushT] using hk) (fun hm => ho ?_)
      simp only [Cx.pushT, List.mem_cons, List.mem_map]
      exact Or.inr ⟨k, hm, rfl⟩

/-- `Cx.bind` keeps the type parameters and the opaque set. -/
theorem bind_ke_opq {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    c'.ke = cx.ke ∧ c'.opq = cx.opq := by
  unfold Cx.bind at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;>
    simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  all_goals (subst h; exact ⟨rfl, rfl⟩)

/-- `Cx.use` keeps the type parameters and the opaque set. -/
theorem use_ke_opq {cx c' : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c')) :
    c'.ke = cx.ke ∧ c'.opq = cx.opq := by
  unfold Cx.use at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · split at h <;> simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
        (obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem WitA_congr {cx c' : Cx} {ω : Nat → Ty} (hk : c'.ke = cx.ke) (ho : c'.opq = cx.opq) (h : WitA cx ω) :
    WitA c' ω := by
  intro k h1 h2; rw [hk] at h1; rw [ho] at h2; exact h k h1 h2

/-- (r1) **The `unpackT` step's new frame meets `WitA`.** -/
theorem WitA_unpackT {ω ω' : Nat → Ty} {cx c₁ c₂ : Cx} {a : At} {κ : Kind} {b : Ty} {x : String}
    (hA : WitA cx ω) (hu : cx.use a = .ok (.tex κ b, c₁)) (hb : (c₁.pushT κ).bind x b = .ok c₂)
    (hw : ∀ k, ω' (k + 1) = ω k) :
    WitA c₂ ω' := by
  obtain ⟨hk, ho⟩ := bind_ke_opq hb
  have hu' := use_ke_opq hu
  exact WitA_congr hk ho (WitA_pushT (WitA_congr hu'.1 hu'.2 hA) hw)

end TermA4

