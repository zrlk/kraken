import Scc.Lower.LowerBodyA64
import Spike.Test.LowerInv

/-!
# The AArch64 items of `ret0.w`'s `main`

`Scc.Lower.LowerBodyA64`'s statements at `ret0.w`'s code block `main`
(closed form `ret0Res`, `ret0_lower0`): its entry label, every instruction
emitting, and the function's items around `bodyItems`, in any context.
The emission is also run on a concrete context, and its items checked to
contain the entry label directly followed by `bodyItems`.
-/

namespace Spike.Test.LowerBodyA64

open Scc Scc.IR Scc.Lower Scc.Lower.Inv Scc.Lower.InvA64 Scc.Emit.A64
open Spike.Test.LowerInv Spike.Lib.Ret0Src

/-- `main`'s function. -/
abbrev mainF : Func := func0 (Names.user "main") ret0Res

theorem hAll : ∀ i ∈ ret0Res.insts, ∃ d p q, i = .addChk d p q :=
  (lower0_insts_addChk _ _ _ _ ret0_lower0).1

-- The entry label, in any context.
example (abortFn : String) (growth : Option IR.Growth) (areas : List (IR.Sym × Nat)) (fi : Nat) :
    (fnCtx abortFn growth areas fi mainF).blockLabel "entry" =
      .ok ((fnCtx abortFn growth areas fi mainF).prefix ++ "0_entry") :=
  blockLabel_func0 _ _ _ _ _ _

-- Every instruction and the result emit.
example (abortFn : String) (growth : Option IR.Growth) (areas : List (IR.Sym × Nat)) (fi : Nat) :
    (∀ i ∈ ret0Res.insts, AddChkOk (fnCtx abortFn growth areas fi mainF) i) ∧
      ∀ v ∈ ret0Res.ret, ∃ l, (fnCtx abortFn growth areas fi mainF).getOp .X0 v = .ok l :=
  addChkOk_func0 _ _ _ _ _ hAll

-- The items around the body.
example (abortFn : String) (growth : Option IR.Growth) (areas : List (IR.Sym × Nat)) (fi : Nat)
    (items : List Item) (sps : List Safepoint)
    (h : emitFunc abortFn growth areas fi mainF = .ok (items, sps)) :
    ∃ pre stubs body, bodyItems (fnCtx abortFn growth areas fi mainF) ret0Res = .ok body ∧
      items = pre ++ [lbl ((fnCtx abortFn growth areas fi mainF).prefix ++ "0_entry")] ++ body ++ stubs :=
  emitFunc_func0_items h hAll

/-- A concrete context: index 5, growable stacks, no argument areas. -/
def ctx : FnCtx := fnCtx "abort" (some ⟨"grow", "release"⟩) [] 5 mainF

/-- `items` contains `lbl` directly followed by `body` (compared as printed). -/
def hasAt (items : List Item) (l : String) (body : List Item) : Bool :=
  let pr (is : List Item) := is.map Item.render
  (List.range items.length).any fun k =>
    pr (items.drop k |>.take (body.length + 1)) == pr (lbl l :: body)

/-- info: ".L5_wc_main.0_entry" -/
#guard_msgs in #eval ctx.prefix ++ "0_entry"
#guard match emitFunc "abort" (some ⟨"grow", "release"⟩) [] 5 mainF, bodyItems ctx ret0Res with
  | .ok (items, _), .ok body => hasAt items (ctx.prefix ++ "0_entry") body
  | _, _ => false

end Spike.Test.LowerBodyA64
