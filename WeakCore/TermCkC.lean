import WeakCore.TermCkX

/-! # TermCkC (was TermA4C): `CkW` across the deterministic formers (A1 checker invariant)

At `split`, `unpack`, `region`, `openPub`, `case` and `ifnull` the child context of `Typed`'s rule
is computed by functions (`use`, `push`, `bind`), so it is the checker's: `checkW` passes to
it, the new variables are components of a `wrapOK` type, and `ke`/`opq` are kept.
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermClose TermScope TermTv

/-- Index shifts are invisible to `rcarE`/`wrapOKE`. -/
theorem rw_shiftI : ∀ (t : Ty) (c : Nat) (env : List Bool),
    rcarE env (t.shiftI c) = rcarE env t ∧ wrapOKE env (t.shiftI c) = wrapOKE env t := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro c env; obtain ⟨a1, a2⟩ := iha c env; obtain ⟨b1, b2⟩ := ihb c env
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, a1, a2, b1, b2]
  | sum a b iha ihb =>
      intro c env; obtain ⟨a1, a2⟩ := iha c env; obtain ⟨b1, b2⟩ := ihb c env
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, a1, a2, b1, b2]
  | code a b iha ihb =>
      intro c env; obtain ⟨-, a2⟩ := iha c env; obtain ⟨-, b2⟩ := ihb c env
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, a2, b2]
  | array i t ih =>
      intro c env; obtain ⟨-, h2⟩ := ih c env; refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h2]
  | ptr μ t ih =>
      intro c env; obtain ⟨-, h2⟩ := ih c env; refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h2]
  | ptrOpt μ t ih =>
      intro c env; obtain ⟨-, h2⟩ := ih c env; refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h2]
  | loc μ t ih =>
      intro c env; obtain ⟨-, h2⟩ := ih c env; refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h2]
  | iall t ih =>
      intro c env; obtain ⟨h1, h2⟩ := ih (c + 1) env
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h1, h2]
  | iex t ih =>
      intro c env; obtain ⟨h1, h2⟩ := ih (c + 1) env
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h1, h2]
  | refine t ψ ih =>
      intro c env; obtain ⟨h1, h2⟩ := ih c env
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h1, h2]
  | tex κ t ih =>
      intro c env; obtain ⟨h1, h2⟩ := ih c (false :: env)
      refine ⟨?_, ?_⟩ <;> simp only [Ty.shiftI, rcarE, wrapOKE, h1, h2]
  | mu t ih =>
      intro c env
      have h0 := (ih c (false :: env)).1
      obtain ⟨h1, h2⟩ := ih c (rcarE (false :: env) t :: env)
      simp only [Ty.shiftI, rcarE, wrapOKE, h0]; exact ⟨h1, h2⟩
  | _ => intro c env; exact ⟨rfl, rfl⟩

theorem wrapOK_shiftI {t : Ty} (c : Nat) (h : wrapOK t = true) : wrapOK (t.shiftI c) = true := by
  unfold wrapOK; rw [(rw_shiftI t c []).2]; exact h

theorem VarsW_push {cx : Cx} (n : String) (hv : VarsW cx) : VarsW (cx.push n) := by
  intro v hm
  simp only [Cx.push, List.mem_map] at hm
  obtain ⟨⟨y, w, b⟩, h0, rfl⟩ := hm
  exact wrapOK_shiftI 0 (hv _ h0)

theorem WitA_of_eq {cx c' : Cx} {ω : Nat → Ty} (hk : c'.ke = cx.ke) (ho : c'.opq = cx.opq) (h : WitA cx ω) :
    WitA c' ω := WitA_congr hk ho h

theorem ko_use {cx c' : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c')) : c'.ke = cx.ke ∧ c'.opq = cx.opq :=
  use_ke_opq h

theorem ko_bind {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') : c'.ke = cx.ke ∧ c'.opq = cx.opq :=
  bind_ke_opq h

theorem ko_push (cx : Cx) (n : String) : (cx.push n).ke = cx.ke ∧ (cx.push n).opq = cx.opq := ⟨rfl, rfl⟩

/-! ## Per former -/

theorem CkW_split {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {e : Expr} {u v : Ty}
    (h : CkW p ω cx (.split a x y e)) (hu : cx.use a = .ok (.prod u v, c₁)) (hb1 : c₁.bind x u = .ok c₂)
    (hb2 : c₂.bind y v = .ok c₃) : CkW p ω c₃ e := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  simp only [wrapOK, wrapOKE, Bool.and_eq_true] at ht
  refine ⟨?_, VarsW_bind (VarsW_bind hV1 ht.1 hb1) ht.2 hb2, ?_⟩
  · simp only [checkW, bind_ok_iff] at hW
    obtain ⟨⟨t, c₁'⟩, hu', hW⟩ := hW
    rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
    obtain ⟨rfl, rfl⟩ := hu'
    simp only [bind_ok_iff] at hW
    obtain ⟨c₂', hb', c₃', hb2', hW⟩ := hW
    rw [hb1] at hb'; cases hb'; rw [hb2] at hb2'; cases hb2'; exact hW
  · obtain ⟨k1, o1⟩ := ko_use hu; obtain ⟨k2, o2⟩ := ko_bind hb1; obtain ⟨k3, o3⟩ := ko_bind hb2
    exact WitA_of_eq (k3.trans (k2.trans k1)) (o3.trans (o2.trans o1)) hA

theorem CkW_unpack {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ : Cx} {a : At} {i x : String} {e : Expr} {b : Ty}
    (h : CkW p ω cx (.unpack a i x e)) (hu : cx.use a = .ok (.iex b, c₁)) (hb : (c₁.push i).bind x b = .ok c₂) :
    CkW p ω c₂ e := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  simp only [wrapOK, wrapOKE, Bool.and_eq_true] at ht
  refine ⟨?_, VarsW_bind (VarsW_push i hV1) ht.2 hb, ?_⟩
  · simp only [checkW, bind_ok_iff] at hW
    obtain ⟨⟨t, c₁'⟩, hu', hW⟩ := hW
    rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
    obtain ⟨rfl, rfl⟩ := hu'
    simp only [bind_ok_iff] at hW
    obtain ⟨c₂', hb', hW⟩ := hW
    rw [hb] at hb'; cases hb'; exact hW
  · obtain ⟨k1, o1⟩ := ko_use hu; obtain ⟨k2, o2⟩ := ko_bind hb
    exact WitA_of_eq (k2.trans k1) (o2.trans o1) hA

theorem CkW_region {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {e : Expr} {u : Ty}
    (h : CkW p ω cx (.region a rn pn tn e)) (hu : cx.use a = .ok (.ptr .own u, c₁))
    (hb1 : (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂)
    (hb2 : c₂.bind tn (.tok (.var 0) none) = .ok c₃) : CkW p ω c₃ e := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  have hp : wrapOK (.ptr (.rgn (.var 0)) (u.shiftI 0)) = true := by
    have := wrapOK_shiftI 0 (show wrapOK u = true by simpa only [wrapOK, wrapOKE] using ht)
    simpa only [wrapOK, wrapOKE] using this
  refine ⟨?_, VarsW_bind (VarsW_bind (VarsW_push rn hV1) hp hb1) rfl hb2, ?_⟩
  · simp only [checkW, bind_ok_iff] at hW
    obtain ⟨⟨t, c₁'⟩, hu', hW⟩ := hW
    rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
    obtain ⟨rfl, rfl⟩ := hu'
    dsimp only at hW
    split at hW
    · simp [throw, throwThe, MonadExceptOf.throw] at hW
    · simp only [bind_ok_iff] at hW
      obtain ⟨c₂', hb', c₃', hb2', hW⟩ := hW
      rw [hb1] at hb'; cases hb'; rw [hb2] at hb2'; cases hb2'; exact hW
  · obtain ⟨k1, o1⟩ := ko_use hu; obtain ⟨k2, o2⟩ := ko_bind hb1; obtain ⟨k3, o3⟩ := ko_bind hb2
    exact WitA_of_eq (k3.trans (k2.trans k1)) (o3.trans (o2.trans o1)) hA

theorem CkW_regionBuf {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn tn : String} {e : Expr}
    {n k : Idx} {u : Ty}
    (h : CkW p ω cx (.region a rn pn tn e)) (hu : cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁))
    (hb1 : (c₁.push rn).bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0)) = .ok c₂)
    (hb2 : c₂.bind tn (.tok (.var 0) none) = .ok c₃) : CkW p ω c₃ e := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  have hp : wrapOK (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0)) = true := by
    have hu' : wrapOK (Ty.array n u) = true := by
      simp only [wrapOK, wrapOKE, Bool.and_eq_true] at ht; simpa only [wrapOK, wrapOKE] using ht.2
    have := wrapOK_shiftI 0 hu'
    simp only [wrapOK] at this
    simp only [wrapOK, wrapOKE, rcarE, Bool.not_false, Bool.true_and]; exact this
  refine ⟨?_, VarsW_bind (VarsW_bind (VarsW_push rn hV1) hp hb1) rfl hb2, ?_⟩
  · simp only [checkW, bind_ok_iff] at hW
    obtain ⟨⟨t, c₁'⟩, hu', hW⟩ := hW
    rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
    obtain ⟨rfl, rfl⟩ := hu'
    dsimp only at hW
    split at hW
    · simp [throw, throwThe, MonadExceptOf.throw] at hW
    · simp only [bind_ok_iff] at hW
      obtain ⟨c₂', hb', c₃', hb2', hW⟩ := hW
      rw [hb1] at hb'; cases hb'; rw [hb2] at hb2'; cases hb2'; exact hW
  · obtain ⟨k1, o1⟩ := ko_use hu; obtain ⟨k2, o2⟩ := ko_bind hb1; obtain ⟨k3, o3⟩ := ko_bind hb2
    exact WitA_of_eq (k3.trans (k2.trans k1)) (o3.trans (o2.trans o1)) hA

theorem CkW_openPub {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ c₃ : Cx} {a : At} {rn pn cn : String} {e : Expr} {u : Ty}
    (h : CkW p ω cx (.openPub a rn pn cn e)) (hu : cx.use a = .ok (.ptr .pub u, c₁))
    (hb1 : (c₁.push rn).bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0)) = .ok c₂)
    (hb2 : c₂.bind cn (.cap .pub (.var 0)) = .ok c₃) : CkW p ω c₃ e := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  have hp : wrapOK (.ptr (.rgn (.var 0)) (u.shiftI 0)) = true := by
    have := wrapOK_shiftI 0 (show wrapOK u = true by simpa only [wrapOK, wrapOKE] using ht)
    simpa only [wrapOK, wrapOKE] using this
  refine ⟨?_, VarsW_bind (VarsW_bind (VarsW_push rn hV1) hp hb1) rfl hb2, ?_⟩
  · simp only [checkW, bind_ok_iff] at hW
    obtain ⟨⟨t, c₁'⟩, hu', hW⟩ := hW
    rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
    obtain ⟨rfl, rfl⟩ := hu'
    simp only [bind_ok_iff] at hW
    obtain ⟨c₂', hb', c₃', hb2', hW⟩ := hW
    rw [hb1] at hb'; cases hb'; rw [hb2] at hb2'; cases hb2'; exact hW
  · obtain ⟨k1, o1⟩ := ko_use hu; obtain ⟨k2, o2⟩ := ko_bind hb1; obtain ⟨k3, o3⟩ := ko_bind hb2
    exact WitA_of_eq (k3.trans (k2.trans k1)) (o3.trans (o2.trans o1)) hA

theorem CkW_case {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ c₃ : Cx} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty}
    (h : CkW p ω cx (.case a x e₁ y e₂)) (hu : cx.use a = .ok (.sum u v, c₁)) (hb1 : c₁.bind x u = .ok c₂)
    (hb2 : c₁.bind y v = .ok c₃) : CkW p ω c₂ e₁ ∧ CkW p ω c₃ e₂ := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  simp only [wrapOK, wrapOKE, Bool.and_eq_true] at ht
  obtain ⟨k1, o1⟩ := ko_use hu; obtain ⟨k2, o2⟩ := ko_bind hb1; obtain ⟨k3, o3⟩ := ko_bind hb2
  simp only [checkW, bind_ok_iff] at hW
  obtain ⟨⟨t, c₁'⟩, hu', hW⟩ := hW
  rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
  obtain ⟨rfl, rfl⟩ := hu'
  simp only [bind_ok_iff] at hW
  obtain ⟨c₂', hb', _, hW1, c₃', hb2', hW2⟩ := hW
  rw [hb1] at hb'; cases hb'; rw [hb2] at hb2'; cases hb2'
  exact ⟨⟨hW1, VarsW_bind hV1 ht.1.2 hb1, WitA_of_eq (k2.trans k1) (o2.trans o1) hA⟩,
    ⟨hW2, VarsW_bind hV1 ht.2 hb2, WitA_of_eq (k3.trans k1) (o3.trans o1) hA⟩⟩

theorem CkW_ifnull {p : Prog} {ω : Nat → Ty} {cx c₁ c₂ : Cx} {a : At} {y : String} {e₁ e₂ : Expr} {μ : Mode} {u : Ty}
    (h : CkW p ω cx (.ifnull a e₁ y e₂)) (hu : cx.use a = .ok (.ptrOpt μ u, c₁))
    (hb : c₁.bind y (.ptr μ u) = .ok c₂) : CkW p ω c₁ e₁ ∧ CkW p ω c₂ e₂ := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨ht, hV1⟩ := VarsW_use hV hu
  have hp : wrapOK (.ptr μ u) = true := by simpa only [wrapOK, wrapOKE] using ht
  obtain ⟨k1, o1⟩ := ko_use hu; obtain ⟨k2, o2⟩ := ko_bind hb
  simp only [checkW, bind_ok_iff] at hW
  obtain ⟨⟨t, c₁'⟩, hu', hW⟩ := hW
  rw [hu] at hu'; simp only [Except.ok.injEq, Prod.mk.injEq] at hu'
  obtain ⟨rfl, rfl⟩ := hu'
  simp only [bind_ok_iff] at hW
  obtain ⟨_, hW1, c₂', hb', hW2⟩ := hW
  rw [hb] at hb'; cases hb'
  exact ⟨⟨hW1, hV1, WitA_of_eq k1 o1 hA⟩, ⟨hW2, VarsW_bind hV1 hp hb, WitA_of_eq (k2.trans k1) (o2.trans o1) hA⟩⟩

end TermA4

