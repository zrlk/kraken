import WeakCore.TermCkS

/-! # TermCkS2 (was TermA4S2): A1 checker (A) spike, the checker-pinned clause

`CkW p ω cx e`: the frame's context is the checker's (`checkW` accepts the rest of the block),
its variables have `wrapOK` types (`VarsW`) and its non-opaque witnesses are `argTop` (`WitA`).
Prototyped here: the `let` inversion (r4: the checker's `OpT` is re-selected through
`checkOp_sound`) and the `unpackT` preservation (r1).
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermClose TermScope TermTv

/-- `rcarE`/`wrapOKE` read only `getD`. -/
theorem rw_ext : ∀ (t : Ty) (e1 e2 : List Bool), (∀ k, e1.getD k false = e2.getD k false) →
    rcarE e1 t = rcarE e2 t ∧ wrapOKE e1 t = wrapOKE e2 t := by
  intro t
  induction t with
  | tvar k => intro e1 e2 h; exact ⟨by simp only [rcarE, h k], rfl⟩
  | prod a b iha ihb =>
      intro e1 e2 h; obtain ⟨a1, a2⟩ := iha e1 e2 h; obtain ⟨b1, b2⟩ := ihb e1 e2 h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, a1, a2, b1, b2]
  | sum a b iha ihb =>
      intro e1 e2 h; obtain ⟨a1, a2⟩ := iha e1 e2 h; obtain ⟨b1, b2⟩ := ihb e1 e2 h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, a1, a2, b1, b2]
  | code a b iha ihb =>
      intro e1 e2 h; obtain ⟨-, a2⟩ := iha e1 e2 h; obtain ⟨-, b2⟩ := ihb e1 e2 h
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, a2, b2]
  | array i t ih => intro e1 e2 h; obtain ⟨-, h2⟩ := ih e1 e2 h; refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | ptr μ t ih => intro e1 e2 h; obtain ⟨-, h2⟩ := ih e1 e2 h; refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | ptrOpt μ t ih => intro e1 e2 h; obtain ⟨-, h2⟩ := ih e1 e2 h; refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | loc μ t ih => intro e1 e2 h; obtain ⟨-, h2⟩ := ih e1 e2 h; refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h2]
  | iall t ih => intro e1 e2 h; obtain ⟨h1, h2⟩ := ih e1 e2 h; refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | iex t ih => intro e1 e2 h; obtain ⟨h1, h2⟩ := ih e1 e2 h; refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | refine t ψ ih => intro e1 e2 h; obtain ⟨h1, h2⟩ := ih e1 e2 h; refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | tex κ t ih =>
      intro e1 e2 h
      have hc : ∀ k, (false :: e1).getD k false = (false :: e2).getD k false := by
        intro k; cases k with | zero => rfl | succ k => simpa using h k
      obtain ⟨h1, h2⟩ := ih _ _ hc
      refine ⟨?_, ?_⟩ <;> simp only [rcarE, wrapOKE, h1, h2]
  | mu t ih =>
      intro e1 e2 h
      have hc : ∀ k, (false :: e1).getD k false = (false :: e2).getD k false := by
        intro k; cases k with | zero => rfl | succ k => simpa using h k
      have h0 := (ih _ _ hc).1
      have hc2 : ∀ k, (rcarE (false :: e1) t :: e1).getD k false = (rcarE (false :: e2) t :: e2).getD k false := by
        intro k; cases k with | zero => simpa using h0 | succ k => simpa using h k
      obtain ⟨h1, h2⟩ := ih _ _ hc2
      simp only [rcarE, wrapOKE]; exact ⟨h1, h2⟩
  | _ => intro e1 e2 _; exact ⟨rfl, rfl⟩

/-- An all-`false` environment reads like the empty one. -/
theorem getD_false_nil (k : Nat) : [false].getD k false = ([] : List Bool).getD k false := by
  cases k <;> rfl

/-- `shiftT` past the environment changes nothing `rcarE`/`wrapOKE` see. -/
theorem rw_shiftT : ∀ (t : Ty) (c : Nat) (env : List Bool), env.length = c →
    rcarE env (t.shiftT c) = rcarE env t ∧ wrapOKE env (t.shiftT c) = wrapOKE env t := by
  intro t
  induction t with
  | tvar k =>
      intro c env hl
      simp only [Ty.shiftT]
      by_cases hk : k ≥ c
      · simp only [hk, ite_true]
        have e1 : env.getD (k + 1) false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : env.length ≤ k + 1)]
        have e2 : env.getD k false = false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : env.length ≤ k)]
        constructor
        · simp only [rcarE]; rw [e1, e2]
        · rfl
      · simp only [hk, ite_false]; constructor <;> first | rfl | trivial
  | prod a b iha ihb =>
      intro c env hl; obtain ⟨a1, a2⟩ := iha c env hl; obtain ⟨b1, b2⟩ := ihb c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, a1, a2, b1, b2]
  | sum a b iha ihb =>
      intro c env hl; obtain ⟨a1, a2⟩ := iha c env hl; obtain ⟨b1, b2⟩ := ihb c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, a1, a2, b1, b2]
  | code a b iha ihb =>
      intro c env hl; obtain ⟨-, a2⟩ := iha c env hl; obtain ⟨-, b2⟩ := ihb c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, a2, b2]
  | array i t ih =>
      intro c env hl; obtain ⟨-, h2⟩ := ih c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h2]
  | ptr μ t ih =>
      intro c env hl; obtain ⟨-, h2⟩ := ih c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h2]
  | ptrOpt μ t ih =>
      intro c env hl; obtain ⟨-, h2⟩ := ih c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h2]
  | loc μ t ih =>
      intro c env hl; obtain ⟨-, h2⟩ := ih c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h2]
  | iall t ih =>
      intro c env hl; obtain ⟨h1, h2⟩ := ih c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h1, h2]
  | iex t ih =>
      intro c env hl; obtain ⟨h1, h2⟩ := ih c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h1, h2]
  | refine t ψ ih =>
      intro c env hl; obtain ⟨h1, h2⟩ := ih c env hl
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h1, h2]
  | tex κ t ih =>
      intro c env hl; obtain ⟨h1, h2⟩ := ih (c + 1) (false :: env) (by simp [hl])
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftT, rcarE, wrapOKE, h1, h2]
  | mu t ih =>
      intro c env hl
      have h0 := (ih (c + 1) (false :: env) (by simp [hl])).1
      obtain ⟨h1, h2⟩ := ih (c + 1) (rcarE (false :: env) t :: env) (by simp [hl])
      simp only [Ty.shiftT, rcarE, wrapOKE, h0]; exact ⟨h1, h2⟩
  | _ => intro c env _; exact ⟨rfl, rfl⟩

theorem wrapOK_shiftT0 {t : Ty} (h : wrapOK t = true) : wrapOK (t.shiftT 0) = true := by
  unfold wrapOK; rw [(rw_shiftT t 0 [] rfl).2]; exact h

theorem wrapOK_tex_body {κ : Kind} {b : Ty} (h : wrapOK (.tex κ b) = true) : wrapOK b = true := by
  simp only [wrapOK, wrapOKE, Bool.and_eq_true] at h
  unfold wrapOK; rw [← (rw_ext b [false] [] getD_false_nil).2]; exact h.2

/-! ## `VarsW` -/


theorem VarsW_find {cx : Cx} {x : String} {t : Ty} {b : Bool} (hv : VarsW cx) (h : cx.find x = .ok (t, b)) :
    wrapOK t = true := by
  unfold Cx.find at h
  split at h
  · rename_i y u b' hf
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hv _ (List.mem_of_find?_eq_some hf)
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem VarsW_peek {cx : Cx} {a : At} {t : Ty} (hv : VarsW cx) (h : cx.peek a = .ok t) : wrapOK t = true := by
  cases a with
  | lit n => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | unit => simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | var x =>
      simp only [Cx.peek, bind_ok_iff] at h
      obtain ⟨⟨u, b⟩, hf, h⟩ := h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact VarsW_find hv hf

theorem VarsW_use {cx c' : Cx} {a : At} {t : Ty} (hv : VarsW cx) (h : cx.use a = .ok (t, c')) :
    wrapOK t = true ∧ VarsW c' := by
  unfold Cx.use at h
  simp only [bind_ok_iff] at h
  obtain ⟨u, hp, h⟩ := h
  have hu := VarsW_peek hv hp
  split at h
  · split at h <;> simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · refine ⟨hu, fun v hm => ?_⟩
      simp only [List.mem_map] at hm
      obtain ⟨⟨y, w, b⟩, h0, rfl⟩ := hm
      have := hv _ h0
      dsimp only; split <;> exact this
    · exact ⟨hu, hv⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨hu, hv⟩

theorem bind_vars {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    c'.vars = (x, t, true) :: cx.vars := by
  unfold Cx.bind at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;>
    simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  all_goals (subst h; rfl)

theorem VarsW_bind {cx c' : Cx} {x : String} {t : Ty} (hv : VarsW cx) (ht : wrapOK t = true)
    (h : cx.bind x t = .ok c') : VarsW c' := by
  intro v hm
  rw [bind_vars h, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact ht
  · exact hv v hm

theorem VarsW_pushT {cx : Cx} {κ : Kind} (hv : VarsW cx) : VarsW (cx.pushT κ) := by
  intro v hm
  simp only [Cx.pushT, List.mem_map] at hm
  obtain ⟨⟨y, w, b⟩, h0, rfl⟩ := hm
  exact wrapOK_shiftT0 (hv _ h0)

/-! ## The checker-pinned clause -/


/-- (r4) **`let`: the checker's operation typing**, re-selected: `checkOp`'s context, an `OpT`
by `checkOp_sound`, the bound type `wrapOK`, and `checkW` on the rest. -/
theorem checkW_let {p : Prog} {cx : Cx} {x : String} {op : Op} {e : Expr}
    (h : checkW p cx (.let_ x op e) = .ok ()) :
    opArgOK op = true ∧ ∃ c, checkOp p cx x op = .ok c ∧ OpT p cx x op c ∧
      (∀ y t b, c.vars.find? (·.1 == x) = some (y, t, b) → wrapOK t = true) ∧ checkW p c e = .ok () := by
  simp only [checkW] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  rename_i hA
  simp only [bind_ok_iff] at h
  obtain ⟨c, hc, h⟩ := h
  refine ⟨by simpa using hA, c, hc, checkOp_sound p cx x op c hc, ?_⟩
  split at h
  · rename_i y t b hf
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · rename_i hw
      try (simp only [bind_ok_iff, pure, Except.pure] at h; obtain ⟨_, -, h⟩ := h)
      refine ⟨fun y' t' b' hf' => ?_, h⟩
      rw [hf] at hf'; simp only [Option.some.injEq, Prod.mk.injEq] at hf'
      obtain ⟨-, rfl, -⟩ := hf'; simpa using hw
  · rename_i hf
    try (simp only [bind_ok_iff, pure, Except.pure] at h; obtain ⟨_, -, h⟩ := h)
    refine ⟨fun y' t' b' hf' => ?_, h⟩
    rw [hf] at hf'; cases hf'

/-- (r1) **`unpackT`: the child of an accepted block is accepted**, at the context `Typed`'s
`unpackT` rule computes (`use`/`pushT`/`bind` are functions). -/
theorem checkW_unpackT {p : Prog} {cx c₁ c₂ : Cx} {a : At} {α x : String} {e : Expr} {κ : Kind} {b : Ty}
    (h : checkW p cx (.unpackT a α x e) = .ok ()) (hu : cx.use a = .ok (.tex κ b, c₁))
    (hb : (c₁.pushT κ).bind x b = .ok c₂) : checkW p c₂ e = .ok () := by
  simp only [checkW, bind_ok_iff] at h
  obtain ⟨⟨t, c₁'⟩, hu', h⟩ := h
  rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
  obtain ⟨rfl, rfl⟩ := hu'
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [bind_ok_iff] at h
    obtain ⟨c₂', hb', h⟩ := h
    rw [hb] at hb'; cases hb'; exact h

/-- (r1) **`CkW` across `unpackT`**: fresh opaque `α`, witness `s` (any: `α` is opaque). -/
theorem CkW_unpackT {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ : Cx} {a : At} {α x : String} {e : Expr}
    {κ : Kind} {b : Ty} {ω' : Nat → Ty}
    (h : CkW p ω cx (.unpackT a α x e)) (hu : cx.use a = .ok (.tex κ b, c₁))
    (hb : (c₁.pushT κ).bind x b = .ok c₂) (hw : ∀ k, ω' (k + 1) = ω k) : CkW p ω' c₂ e := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  exact ⟨checkW_unpackT hW hu hb, VarsW_bind (VarsW_pushT hV1) (wrapOK_tex_body ht) hb,
    WitA_unpackT hA hu hb hw⟩

/-- (r3) **`CkW` at `call`/`tail`**: the callee's declaration context, at the instantiated
witnesses.  `hD`: the program's declarations pass `checkW` and have `wrapOK` parameters
(`declWrapOK`). -/
theorem CkW_call {p : Prog} {ρ₀ : Nat → Nat} {ω : Nat → Ty} {cx : Cx} {d : Decl} {is : List String}
    {ts : List Ty} {at_ rt : Ty} (hA : WitA cx ω) (hWc : ∀ k, tb 0 (ω k) = true)
    (hinst : instantiate cx d is ts = .ok (at_, rt)) (hts : ts.all argOK = true)
    (hD : checkW p (declCx d) d.body = .ok () ∧ wrapOK d.argTy = true) :
    CkW p (subW ρ₀ ω ts.reverse) (declCx d) d.body := by
  refine ⟨hD.1, fun v hm => ?_, WitA_call hA hWc hinst hts⟩
  simp only [declCx, List.mem_singleton] at hm
  subst hm; exact hD.2


/-- (r4) **The new cell's type is `wrapTop`**: `new a` at the checker's context. -/
theorem CkW_newCell {p : Prog} {ω : Nat → Ty} {cx : Cx} {e : Expr} {a : At} {tv : Ty} {ρ : Nat → Nat}
    (h : CkW p ω cx e) (hWc : ∀ k, tb 0 (ω k) = true) (hp : cx.peek a = .ok tv)
    (htb : tb cx.ke.length tv = true) (hg : cx.opaqueOK tv = true) :
    wrapTop (cl ρ ω 0 0 tv) = true := by
  refine wrapTop_cl0 (O := cx.opq) hWc h.2.2 htb (fun j hj => ?_) (VarsW_peek h.2.1 hp)
  simp only [Cx.opaqueOK, List.all_eq_true] at hg
  exact hg j hj

end TermA4

