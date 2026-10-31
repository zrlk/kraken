import WeakCore.TermCkL

/-! # TermCkB (was TermA4B): `CkW` at the branch-fact formers (A1 checker invariant)

`TypedR_CkW`: the checker's derivation at `parity`/`ifeq`/`cas`/`casp` (`checkW_inv_*`) has
`CkW` at every child: the children add facts, push an index (`NoCx`'s `nzCx`), or bind a
token, share or unit (all `wrapOK`), keeping `ke`/`opq`.
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermClose TermScope TermTv

/-- A child context: `VarsW` passes to it, and it keeps `ke`/`opq`. -/
def KW (cx c : Cx) : Prop := (VarsW cx → VarsW c) ∧ c.ke = cx.ke ∧ c.opq = cx.opq

theorem KW_refl (cx : Cx) : KW cx cx := ⟨id, rfl, rfl⟩

theorem KW_trans {a b c : Cx} (h1 : KW a b) (h2 : KW b c) : KW a c :=
  ⟨fun h => h2.1 (h1.1 h), h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem KW_bind {cx c : Cx} {x : String} {t : Ty} (ht : wrapOK t = true) (h : cx.bind x t = .ok c) : KW cx c :=
  ⟨fun hv => VarsW_bind hv ht h, (bind_ke_opq h).1, (bind_ke_opq h).2⟩

theorem KW_use {cx c : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c)) : KW cx c :=
  ⟨fun hv => (VarsW_use hv h).2, (use_ke_opq h).1, (use_ke_opq h).2⟩

theorem KW_nz (cx : Cx) (u : Nat) : KW cx (nzCx cx u) :=
  ⟨fun hv v hm => VarsW_push "_nz" hv v hm, rfl, rfl⟩

theorem KW_noCx {cx c : Cx} {i j : Idx} (h : NoCx cx i j c) : KW cx c := by
  cases h with
  | same => exact KW_refl cx
  | nzL _ _ => exact KW_nz cx _
  | nzR _ _ => exact KW_nz cx _

theorem KW_lend {cx c₂ : Cx} {acq rel : Bool} {r : Idx} {t : String} {P : Proto} {c c' : Nat} {k k' : Idx}
    (h : LendCx cx acq rel r t P c k c' k' c₂) : KW cx c₂ := by
  cases h with
  | none _ hb => exact KW_bind rfl hb
  | up _ _ hb => exact KW_bind rfl hb
  | down _ _ _ _ hu hb => exact KW_trans (KW_use hu) (KW_bind rfl hb)

theorem KW_facts (cx : Cx) (fs : Facts) : KW cx { cx with facts := fs } := ⟨id, rfl, rfl⟩

theorem KW_pushF (cx : Cx) (k : String) (fs : Facts) : KW cx { cx.push k with facts := fs } :=
  ⟨fun hv v hm => VarsW_push k hv v hm, rfl, rfl⟩

theorem KW_mono {cx c₂ : Cx} (P : Proto) (r : Idx) (h : KW cx c₂) :
    KW cx (if monotone P then { c₂ with unsealed := r :: c₂.unsealed } else c₂) := by
  split
  · exact ⟨fun hv v hm => h.1 hv v hm, h.2.1, h.2.2⟩
  · exact h

/-- A checked child with a `KW` context meets `CkW`. -/
theorem ckK {p : Prog} {ω : Nat → Ty} {cx c : Cx} {e : Expr} (hV : VarsW cx) (hA : WitA cx ω) (k : KW cx c)
    (h : CkQ p c e) : CkW p ω c e :=
  ⟨h, k.1 hV, WitA_of_eq k.2.1 k.2.2 hA⟩

/-- **The checker's branch derivation carries `CkW` at every child.** -/
theorem TypedR_CkW {p : Prog} {ω : Nat → Ty} {cx : Cx} {e : Expr} (h : TypedR (CkQ p) p cx e) (hV : VarsW cx)
    (hA : WitA cx ω) : TypedR (CkW p ω) p cx e := by
  cases h with
  | parity h1 h2 h3 h4 => exact .parity h1 h2 (ckK hV hA (KW_pushF _ _ _) h3) (ckK hV hA (KW_pushF _ _ _) h4)
  | ifeqPlain h1 h2 h3 => exact .ifeqPlain h1 (ckK hV hA (KW_refl _) h2) (ckK hV hA (KW_refl _) h3)
  | ifeq h1 h2 h3 h4 h5 => exact .ifeq h1 h2 (ckK hV hA (KW_refl _) h3) h4 (ckK hV hA (KW_noCx h4) h5)
  | ifeqRec h1 h2 h3 h4 h5 h6 =>
      exact .ifeqRec h1 h2 h3 (ckK hV hA (KW_facts _ _) h4) h5 (ckK hV hA (KW_noCx h5) h6)
  | ifeqZero h1 h2 h3 h4 h5 h6 =>
      exact .ifeqZero h1 h2 h3 (ckK hV hA (KW_facts _ _) h4) h5 (ckK hV hA (KW_noCx h5) h6)
  | casCell h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
      exact .casCell h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        (ckK hV hA (KW_trans (KW_use h7) (KW_bind rfl h11)) h12) (ckK hV hA (KW_use h7) h13)
  | casShare h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
      exact .casShare h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (ckK hV hA (KW_lend h13) h14)
        (ckK hV hA (KW_refl _) h15)
  | casTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 =>
      exact .casTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        (ckK hV hA (KW_mono _ _ (KW_bind rfl h16)) h17) (ckK hV hA (KW_refl _) h18)
  | casEpoch h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      exact .casEpoch h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (ckK hV hA (KW_bind rfl h10) h11) (ckK hV hA (KW_refl _) h12)
  | caspE h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      exact .caspE h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (ckK hV hA (KW_bind rfl h10) h11) (ckK hV hA (KW_refl _) h12)
  | caspBump h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 =>
      exact .caspBump h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        (ckK hV hA (KW_bind rfl h17) h18) (ckK hV hA (KW_refl _) h19)
  | caspMove h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
      exact .caspMove h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 (ckK hV hA (KW_bind rfl h14) h15)
        (ckK hV hA (KW_refl _) h16)
  | caspTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 =>
      exact .caspTake h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 (ckK hV hA (KW_bind rfl h15) h16)
        (ckK hV hA (KW_refl _) h17)

/-- **Re-selection at a branch former**: from `CkW` at the term, the checker's derivation with
`CkW` at every child. -/
theorem CkW_inv_ifeq {p : Prog} {ω : Nat → Ty} {cx : Cx} {a b : At} {yes no : Expr}
    (h : CkW p ω cx (.ifeq a b yes no)) : TypedR (CkW p ω) p cx (.ifeq a b yes no) :=
  TypedR_CkW (checkW_inv_ifeq h.1) h.2.1 h.2.2

theorem CkW_inv_parity {p : Prog} {ω : Nat → Ty} {cx : Cx} {a : At} {k : String} {ev od : Expr}
    (h : CkW p ω cx (.parity a k ev od)) : TypedR (CkW p ω) p cx (.parity a k ev od) :=
  TypedR_CkW (checkW_inv_parity h.1) h.2.1 h.2.2

theorem CkW_inv_cas {p : Prog} {ω : Nat → Ty} {cx : Cx} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    (h : CkW p ω cx (.cas acq rel w e v t ok fail)) : TypedR (CkW p ω) p cx (.cas acq rel w e v t ok fail) :=
  TypedR_CkW (checkW_inv_cas h.1) h.2.1 h.2.2

theorem CkW_inv_casp {p : Prog} {ω : Nat → Ty} {cx : Cx} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} (h : CkW p ω cx (.casp acq rel w e0 e1 v0 v1 t ok fail)) :
    TypedR (CkW p ω) p cx (.casp acq rel w e0 e1 v0 v1 t ok fail) :=
  TypedR_CkW (checkW_inv_casp h.1) h.2.1 h.2.2

/-- A `CkW` child gives the `Typed` child the step lemma needs (`checkW_sound`). -/
theorem CkW.typed {p : Prog} {ω : Nat → Ty} {c : Cx} {e : Expr} (h : CkW p ω c e) : Typed p c e :=
  checkW_sound p e c h.1

/-- A `CkW` frame, with its `Typed` judgement (the thread invariant's typing slot). -/
theorem CkW.tk {p : Prog} {ω : Nat → Ty} {c : Cx} {e : Expr} (h : CkW p ω c e) : Typed p c e ∧ CkW p ω c e :=
  ⟨h.typed, h⟩

/-- (r3) `tail`'s type arguments are checked `argOK`. -/
theorem checkW_tail_args {p : Prog} {cx : Cx} {f : String} {is : List String} {a : At} {ts : List Ty}
    (h : checkW p cx (.tail f is a ts) = .ok ()) : ts.all argOK = true := by
  simp only [checkW] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i hn; simpa using hn

/-- (r3) `call`'s type arguments are checked `argOK`. -/
theorem opArgOK_call {f : String} {is : List String} {a : At} {ts : List Ty}
    (h : opArgOK (.call f is a ts) = true) : ts.all argOK = true := h

/-- (A1 checker invariant) Every declaration's body passes `checkW` from its entry context, with a `wrapOK`
parameter type (what `declWrapOK` checks, at `declCx`). -/
def ProgCkW (p : Prog) : Prop := ∀ d ∈ p, checkW p (declCx d) d.body = .ok () ∧ wrapOK d.argTy = true

/-- `ProgCkW` as an instance (threaded like `ProgRetIall`), with the checker's verdict on the whole
program (its opened-type-package allocation check is what keeps the per-frame invariant `DyFr`
closed under calls). -/
class ProgCkWC (p : Prog) : Prop where
  ck : ProgCkW p
  checked : checkProg p = .ok ()

/-- An entry frame is the checker's, at any witnesses meeting `WitA`. -/
theorem CkW_decl {p : Prog} {ω : Nat → Ty} {d : Decl}
    (hD : checkW p (declCx d) d.body = .ok () ∧ wrapOK d.argTy = true) (hA : WitA (declCx d) ω) :
    CkW p ω (declCx d) d.body := by
  refine ⟨hD.1, fun v hm => ?_, hA⟩
  simp only [declCx, List.mem_singleton] at hm
  subst hm; exact hD.2

end TermA4
#print axioms TermA4.CkW.tk
#print axioms TermA4.CkW_decl
