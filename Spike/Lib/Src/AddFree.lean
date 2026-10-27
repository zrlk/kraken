/-
**Bodies with no addition still to lower** (ISA-neutral): a body none of
whose `TailOf` points is a `let x = a + b` reaches no overflow abort.

- `addFreeT`: no `let x = a + b` at a point of the body (the points
  `TailOf` passes: `let`, pair split and unpack bodies, both branches of an
  `if`);
- `tailOf_addFree`: no `TailOf` point of an `addFreeT` body is an addition.
-/
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm

/-- **No `let x = a + b` at a point of the body** (`TailOf`'s points). -/
def addFreeT : Expr → Bool
  | .let_ _ op e => (match op with | .add _ _ => false | _ => true) && addFreeT e
  | .split _ _ _ e => addFreeT e
  | .unpack _ _ _ e => addFreeT e
  | .unpackT _ _ _ e => addFreeT e
  | .ifeq _ _ yes no => addFreeT yes && addFreeT no
  | _ => true

/-- **No point of an `addFreeT` body is an addition.** -/
theorem tailOf_addFree {t e : Expr} (h : TailOf t e) (hf : addFreeT e = true) (x : String) (a b : At)
    (e' : Expr) : t ≠ .let_ x (.add a b) e' := by
  induction h with
  | refl => rintro rfl; simp [addFreeT] at hf
  | let_ y op _ ih => simp only [addFreeT, Bool.and_eq_true] at hf; exact ih hf.2
  | split _ _ _ _ ih => exact ih hf
  | unpack _ _ _ _ ih => exact ih hf
  | unpackT _ _ _ _ ih => exact ih hf
  | yes _ _ _ _ ih => simp only [addFreeT, Bool.and_eq_true] at hf; exact ih hf.1
  | no _ _ _ _ ih => simp only [addFreeT, Bool.and_eq_true] at hf; exact ih hf.2

/-- `addFreeT` on a small body with an addition. -/
example : addFreeT (.let_ "x" (.add (.lit 1) (.lit 2)) (.ret (.var "x"))) = false := rfl

/-- `addFreeT` on a small body without one. -/
example : addFreeT (.let_ "x" (.atom (.lit 1)) (.ret (.var "x"))) = true := rfl

/-- info: 'Spike.Lib.LowerNode.tailOf_addFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms tailOf_addFree

end Spike.Lib.LowerNode
