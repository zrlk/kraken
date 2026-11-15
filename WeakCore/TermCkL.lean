import WeakCore.TermCkC
import WeakCore.TermCkW

/-! # TermCkL (was TermA4L): `CkW` across `let` (A1 checker invariant)

Every `OpT` rule binds only `x`, after `use`/`push`/`observeCx`/`fenceCx`/`endCx` (or, `loadTorn`,
binds nothing), so `VarsW` passes to the checker's context once `x`'s type is `wrapOK`, which
`checkW` checks.  `CkW_let`: the re-selected (checker's) context meets `CkW`.
-/

namespace TermA4
open CoreLang CoreTerm CoreTyping TermClose TermScope TermTv

theorem VarsW_observeCx {cx : Cx} (x w : String) (acq : Bool) (hv : VarsW cx) : VarsW (observeCx cx x w acq) :=
  VarsW_push x hv

theorem VarsW_fenceCx {cx : Cx} (f : Fence) (hv : VarsW cx) : VarsW (fenceCx cx f) := by
  unfold fenceCx
  dsimp only
  split <;> split <;> exact hv

theorem VarsW_endCx {cx : Cx} (y : String) (hv : VarsW cx) : VarsW (cx.endCx y) := by
  intro v hm
  simp only [Cx.endCx, List.mem_map, List.mem_filter] at hm
  obtain ⟨⟨z, u, b⟩, ⟨h0, -⟩, rfl⟩ := hm
  have := hv _ h0
  dsimp only; split <;> exact this

/-- Binding `x` at a `wrapOK` type (read back by `find?`) keeps `VarsW`. -/
theorem VarsW_bindx {cx c' : Cx} {x : String} {t : Ty} (hv : VarsW cx) (hb : cx.bind x t = .ok c')
    (hx : ∀ y u b, c'.vars.find? (·.1 == x) = some (y, u, b) → wrapOK u = true) : VarsW c' := by
  have e := bind_vars hb
  refine VarsW_bind hv (hx x t true ?_) hb
  rw [e]; simp

theorem VarsW_handOffR {cx : Cx} (T : Ty) (hv : VarsW cx) : VarsW (cx.handOffR T) := by
  intro v; unfold Cx.handOffR Cx.handOff
  split <;> (try split) <;> (try split) <;> intro hm <;> first | exact hv v hm | exact hv v (List.mem_filter.mp hm).1

theorem VarsW_iteH {cx : Cx} (b : Bool) (T : Ty) (hv : VarsW cx) :
    VarsW (if b = true then cx.handOffR T else cx) := by
  cases b
  · exact hv
  · exact VarsW_handOffR T hv

theorem handOffR_ke {cx : Cx} (T : Ty) : (cx.handOffR T).ke = cx.ke := by
  unfold Cx.handOffR Cx.handOff; split <;> (try split) <;> (try split) <;> rfl

theorem handOffR_opq {cx : Cx} (T : Ty) : (cx.handOffR T).opq = cx.opq := by
  unfold Cx.handOffR Cx.handOff; split <;> (try split) <;> (try split) <;> rfl

theorem iteH_ke {cx : Cx} (b : Bool) (T : Ty) : (if b = true then cx.handOffR T else cx).ke = cx.ke := by
  cases b
  · rfl
  · exact handOffR_ke T

theorem iteH_opq {cx : Cx} (b : Bool) (T : Ty) : (if b = true then cx.handOffR T else cx).opq = cx.opq := by
  cases b
  · rfl
  · exact handOffR_opq T

/-- **`OpT` keeps `VarsW`** at a `wrapOK` bound type. -/
theorem OpT_VarsW {p : Prog} {cx c' : Cx} {x : String} {op : Op} (h : OpT p cx x op c') (hv : VarsW cx)
    (hx : ∀ y u b, c'.vars.find? (·.1 == x) = some (y, u, b) → wrapOK u = true) : VarsW c' := by
  cases h
  case loadTorn => exact hv
  case borrow =>
    rename_i hu hb
    refine VarsW_bindx ?_ hb hx
    intro v hm; exact (VarsW_use hv hu).2 v hm
  all_goals
    rename_i hb
    refine VarsW_bindx ?_ hb hx
    first
    | exact hv
    | exact (VarsW_use hv ‹_›).2
    | exact VarsW_iteH _ _ (VarsW_use hv ‹_›).2
    | exact VarsW_handOffR _ (VarsW_use hv ‹_›).2
    | exact (VarsW_use (VarsW_use hv ‹_›).2 ‹_›).2
    | exact VarsW_observeCx _ _ _ hv
    | exact VarsW_fenceCx _ hv
    | exact VarsW_endCx _ hv
    | exact VarsW_push _ hv
    | exact VarsW_push _ (VarsW_push _ hv)
    | exact fun v hm => VarsW_push x (VarsW_push (x ++ "_d") hv) v hm
    | exact fun v hm => VarsW_push x hv v hm

/-- `OpT` keeps the type parameters and the opaque set. -/
theorem OpT_ke_opq {p : Prog} {cx c' : Cx} {x : String} {op : Op} (h : OpT p cx x op c') :
    c'.ke = cx.ke ∧ c'.opq = cx.opq := by
  cases h
  case loadTorn => exact ⟨rfl, rfl⟩
  case borrow =>
    rename_i hu hb
    have k := bind_ke_opq hb; have k1 := use_ke_opq hu
    exact ⟨k.1.trans k1.1, k.2.trans k1.2⟩
  all_goals
    rename_i hb
    have k := bind_ke_opq hb
    first
    | exact k
    | (have k1 := use_ke_opq ‹_›; exact ⟨k.1.trans k1.1, k.2.trans k1.2⟩)
    | (have k1 := use_ke_opq ‹cx.use _ = _›; have k2 := use_ke_opq ‹_›
       exact ⟨k.1.trans (k2.1.trans k1.1), k.2.trans (k2.2.trans k1.2)⟩)
    | exact k
    | (simp only [iteH_ke, iteH_opq, handOffR_ke, handOffR_opq] at k
       have k1 := use_ke_opq ‹_›; exact ⟨k.1.trans k1.1, k.2.trans k1.2⟩)
    | (simp only [observeCx, Cx.push] at k; exact k)
    | (simp only [fenceCx] at k; split at k <;> split at k <;> exact k)
    | (simp only [Cx.endCx] at k; exact k)
    | (simp only [Cx.push] at k; exact k)

/-- (r4) **`CkW` across `let`, re-selected**: the checker's context `c` (an `OpT` by
`checkOp_sound`) meets `CkW`, and is the one the step continues at. -/
theorem CkW_let {p : Prog} {ω : Nat → Ty} {cx : Cx} {x : String} {op : Op} {e : Expr}
    (h : CkW p ω cx (.let_ x op e)) :
    ∃ c, checkOp p cx x op = .ok c ∧ OpT p cx x op c ∧ Typed p c e ∧ CkW p ω c e ∧ opArgOK op = true := by
  obtain ⟨hW, hV, hA⟩ := h
  obtain ⟨hargs, c, hc, hop, hx, hWe⟩ := checkW_let hW
  have k := OpT_ke_opq hop
  exact ⟨c, hc, hop, checkW_sound p e c hWe, ⟨hWe, OpT_VarsW hop hV hx, WitA_of_eq k.1 k.2 hA⟩, hargs⟩

end TermA4


/-! (G2 P2) The region-load checker facts, kept below TermStep (checkW.match_5: equation lemmas are taken here). -/

namespace TermC1
open CoreLang CoreTerm CoreTyping

theorem ruleA_of_checkW {p : Prog} {cx : Cx} {x : String} {op : Op} {e : Expr}
    (h : TermScope.checkW p cx (.let_ x op e) = .ok ()) : ruleA cx op = true := by
  cases hr : ruleA cx op with
  | true => rfl
  | false =>
    exfalso
    rw [TermScope.checkW.eq_1] at h
    split at h <;> (try simp only [hr, Bool.not_false, ite_true] at h) <;>
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem bind_torn1 {cx c : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c) : c.torn = cx.torn := by
  unfold Cx.bind at h
  split at h <;> split at h <;> (try split at h) <;>
    simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  cases h; rfl

theorem checkOp_loadRgn {p : Prog} {cx c : Cx} {x : String} {acq : Bool} {a : At} {t u : Ty} {r : Idx}
    (hpk : cx.peek a = .ok t) (hnw : wordOf t = none) (hcl : cellOf t = some (.rgn r, u))
    (h : checkOp p cx x (.load acq a) = .ok c) :
    ((cx.hasTok r || cx.hasShare r || cx.hasCap r false) = true → c.torn = cx.torn) ∧
    ((cx.hasTok r || cx.hasShare r || cx.hasCap r false) = false →
      ∃ w s, c = { cx with torn := ⟨x, adapt r u, w, s, .opn⟩ :: cx.torn } ∧ cx.vars.any (·.1 == x) = false) := by
  simp only [checkOp, bind_ok_iff] at h
  obtain ⟨t', ht, h⟩ := h
  rw [hpk] at ht; cases ht
  simp only [hnw, hcl] at h
  cases hb : (cx.hasTok r || cx.hasShare r || cx.hasCap r false) with
  | true =>
    refine ⟨fun _ => ?_, fun h' => (nomatch h')⟩
    simp only [Bool.or_eq_true] at hb
    split at h
    · split at h
      · simp at h
      · exact bind_torn1 h
    · rename_i hts
      split at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · exact bind_torn1 h
      · rename_i hcap
        exfalso; simp_all
  | false =>
    refine ⟨fun h' => (nomatch h'), fun _ => ?_⟩
    simp only [Bool.or_eq_false_iff] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    simp only [h1, h2, h3, Bool.or_false, Bool.false_eq_true, ite_false, bind_ok_iff] at h
    obtain ⟨⟨w, s⟩, -, h⟩ := h
    split at h
    · simp at h
    · rename_i hx
      have hx1 : cx.vars.any (·.1 == x) = false := by
        cases hv : cx.vars.any (·.1 == x) with
        | false => rfl
        | true => exact absurd (by rw [hv]; rfl) hx
      refine ⟨w, s, ?_, hx1⟩
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
/-- At a region-cell `xchg`, `checkW` admits only a payload that is not affine or carries no key. -/
theorem xchgGuard_of_checkW {p : Prog} {cx : Cx} {x : String} {a v : At} {e : Expr} {t u : Ty} {r : Idx}
    (h : TermScope.checkW p cx (.let_ x (.xchg a v) e) = .ok ()) (hpk : cx.peek a = .ok t)
    (hcl : cellOf t = some (.rgn r, u)) :
    affine cx.ke (adapt r u) = false ∨ keyFree cx.ke (adapt r u) = true := by
  cases hr : affine cx.ke (adapt r u) with
  | false => exact Or.inl rfl
  | true =>
    cases hk : keyFree cx.ke (adapt r u) with
    | true => exact Or.inr rfl
    | false =>
    exfalso
    rw [TermScope.checkW.eq_1] at h
    split at h <;> (try simp only [Bool.not_eq_true'] at h) <;>
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, hpk, hcl, hr, hk] at h <;>
      (try split at h) <;> (try split at h) <;> simp_all
end TermC1

