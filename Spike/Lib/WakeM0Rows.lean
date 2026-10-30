/-
**The rows main never takes after the spawn** (`post_step0`; terms in `Spike/Lib/WakeM0.lean`).

main's source after the spawn is at an `MTerm`, and the only `let`s among
them are `wlBody`'s acquire load of `c` and `wlPark`'s `park`. So the rows
whose control is at a store, an exchange or a buffer allocation do not
occur, and a row whose control holds an exchange's word does not occur
either (`Ctl.of` holds none).

- `mterm_let`: a `let` at an `MTerm` is `wlBody`'s or `wlPark`'s.
- `mterm_load`: a `let` of a load at an `MTerm` is `wlBody`.
- `mterm_not_store`, `mterm_not_newBuf`, `mterm_not_xchgSite`: no store, no
  allocation, no exchange site at an `MTerm`.
-/
import Spike.Lib.WakeM0

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.WakeMLive (wlRet)

/-- **A `let` at an `MTerm`** is `wlBody`'s load of `c` or `wlPark`'s
`park`. -/
theorem mterm_let {e : Expr} (hm : MTerm e) {x : String} {op : Op} {e' : Expr} (he : e = .let_ x op e') :
    (x = "d" ∧ op = .load true (.var "c") ∧ e' = wlIf) ∨
      (x = "p" ∧ op = .ext .park .unit ∧ e' = .tail "waitLoop" [] (.var "c") []) := by
  subst he
  rcases hm with h | h | h | h | h <;>
    simp_all [mTail, wlBody, wlIf, wlPark, WakeMLive.wlRet]

/-- **A `let` of a load at an `MTerm`** is `wlBody`. -/
theorem mterm_load {e : Expr} (hm : MTerm e) {x : String} {acq : Bool} {a : At} {e' : Expr}
    (he : e = .let_ x (.load acq a) e') : e = wlBody ∧ x = "d" ∧ acq = true ∧ a = .var "c" ∧ e' = wlIf := by
  rcases mterm_let hm he with ⟨rfl, h, rfl⟩ | ⟨-, h, -⟩
  · injection h with h1 h2
    subst h1 h2
    exact ⟨he, rfl, rfl, rfl, rfl⟩
  · cases h

/-- No store at an `MTerm`. -/
theorem mterm_not_store {e : Expr} (hm : MTerm e) {x : String} {rel : Bool} {a b : At} {o : Option At}
    {e' : Expr} (he : e = .let_ x (.store rel a b o) e') : False := by
  rcases mterm_let hm he with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h

/-- No buffer allocation at an `MTerm`. -/
theorem mterm_not_newBuf {e : Expr} (hm : MTerm e) {x : String} {a : At} {τ : Ty} {e' : Expr}
    (he : e = .let_ x (.newBuf a τ) e') : False := by
  rcases mterm_let hm he with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h

/-- No exchange site at an `MTerm`. -/
theorem mterm_not_xchgSite {c : Ctl} (hm : MTerm c.term) {x : String} {sa : WeakMem.Address} {u : Ty} {v : At}
    {e : Expr} (h : XchgSite c x sa u v e) : False := by
  rcases h.2 with ⟨a, -, -, -, he, -⟩ | ⟨b, i, -, -, -, -, -, -, -, he, -⟩
  · rcases mterm_let hm he with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
  · rcases mterm_let hm he with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h

end Spike.Lib.WakeM0
