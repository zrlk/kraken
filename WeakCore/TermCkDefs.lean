import WeakCore.TermWrapDefs
import WeakCore.TermClose

/-! # TermCkDefs: the A1 checker invariant's frame clauses

`wrapTop` (A1's `wrapOK` stopping at references and code), `VarsW`, the witness clause `WitA` and
the checker-pinned clause `CkW`, over a witness function (so the lemmas sit below `TermSound`).
-/

namespace TermA4
open CoreLang CoreTerm TermScope TermClose

/-- (A1 checker invariant) `wrapOKE` stopping at references, code and arrays' indices: what a value's own
layout shows.  Witnesses under references may carry keys. -/
def wrapTopE (env : List Bool) : Ty → Bool
  | .sum a b => !rcarE env a && !rcarE env b && wrapTopE env a && wrapTopE env b
  | .iex t | .refine t _ => !rcarE env t && wrapTopE env t
  | .tex _ t => !rcarE (false :: env) t && wrapTopE (false :: env) t
  | .mu t => wrapTopE (rcarE (false :: env) t :: env) t
  | .prod a b => wrapTopE env a && wrapTopE env b
  | .array _ t | .iall t => wrapTopE env t
  | _ => true

def wrapTop (t : Ty) : Bool := wrapTopE [] t

/-- A non-opaque witness: `wrapTop` and key-free. -/
def argTop (t : Ty) : Bool := wrapTop t && !rcar t

/-- (A1 checker invariant) Every variable of the frame has a `wrapOK` type. -/
def VarsW (cx : Cx) : Prop := ∀ v ∈ cx.vars, wrapOK v.2.1 = true


/-- (A1 checker invariant, FInv clause) **Non-opaque witnesses are `argTop`** (`w`: the frame's witnesses). -/
def WitA (cx : Cx) (w : Nat → Ty) : Prop := ∀ k, k < cx.ke.length → k ∉ cx.opq → argTop (w k) = true

/-- (A1 checker invariant) **The frame is the checker's**: `checkW` accepts the rest of the block at `cx`,
the variables are `wrapOK`, and the non-opaque witnesses are `argTop`. -/
def CkW (p : Prog) (w : Nat → Ty) (cx : Cx) (e : Expr) : Prop :=
  checkW p cx e = .ok () ∧ VarsW cx ∧ WitA cx w

/-- The callee's witnesses (`subE`'s `wit`). -/
def subW (ρ₀ : Nat → Nat) (w : Nat → Ty) (σs : List Ty) : Nat → Ty := fun k =>
  match σs[k]? with
  | some σ => cl ρ₀ w 0 0 σ
  | none => w (k - σs.length)

end TermA4
