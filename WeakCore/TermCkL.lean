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

