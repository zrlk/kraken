/-
**`hello1o`'s `main`, its points decided** (ISA-independent): the facts
`main`'s held-exit call (`mainCallWSF_ofPlaceOKHMV`, both ISAs) asks of the
body at its compiled block.

- `hello1_main_compiled2`: `main` is compiled block `1` (after `rodata`);
- `hello1_main_find`: `main` is the program's `main`;
- `hello1_main_tails`: the points of `main`'s body;
- `hello1_main_hlitP`: its one literal tail is after `print` with one
  immediate;
- `hello1_main_noCallee`: its only call is to the extern `print`, no
  `Callee` at a context with `hello1o`'s externs;
- `hello1_main_noXchg`, `hello1_main_noNewBuf`: no lane store, no buffer
  allocation.
-/
import Spike.Test.Hello1MainSrc
import Spike.Lib.Src.Walk2Facts
import Spike.Lib.LowerCallC1

namespace Spike.Test.Hello1MainSrc

open CoreLang CoreTerm
open Spike.Lib.LowerNode (compiled2 TailAt2 TailOf)

/-- The program. -/
local notation "P1" => hello1o

/-- `hello1o`'s `main`. -/
local notation "MD" => Spike.Test.Hello1MainSrc.mainD

/-- **`hello1o`'s `main` is its compiled block `1`** (after `rodata`). -/
theorem hello1_main_compiled2 : (compiled2 P1)[1]? = some MD := rfl

/-- **`main` is `hello1o`'s `main`.** -/
theorem hello1_main_find : (P1).find? (·.name == "main") = some MD := rfl

/-- **The points of `main`'s body**: the body, after the split, after the
unpack, and the `ret`. -/
theorem hello1_main_tails {t : Expr} (ht : TailOf t (MD).body) :
    t = (MD).body ∨ t = .unpack (.var "sl0") "q" "sl" (.let_ "u" (.call "print" ["q"] (.var "sl") []) (.ret (.lit 0))) ∨
      t = .let_ "u" (.call "print" ["q"] (.var "sl") []) (.ret (.lit 0)) ∨ t = .ret (.lit 0) := by
  change TailOf t (.split (.var "a") "sl0" "me" (.unpack (.var "sl0") "q" "sl"
    (.let_ "u" (.call "print" ["q"] (.var "sl") []) (.ret (.lit 0))))) at ht
  cases ht with
  | refl => exact .inl rfl
  | split _ _ _ ht =>
    cases ht with
    | refl => exact .inr (.inl rfl)
    | unpack _ _ _ ht =>
      cases ht with
      | refl => exact .inr (.inr (.inl rfl))
      | let_ _ _ ht =>
        cases ht with
        | refl => exact .inr (.inr (.inr rfl))

/-- **`main`'s literal tail is after `print` with one immediate.** -/
theorem hello1_main_hlitP : ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) (MD).body →
    g = "print" ∧ is.length = 1 := by
  intro x g is a ts k ht
  rcases hello1_main_tails ht with h | h | h | h
  · cases h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- **`main`'s only call is to the extern `print`**: no plain call at a
context with `hello1o`'s externs. -/
theorem hello1_main_noCallee {cx : Scc.Lower.Ctx} (hcx : cx.externs = Scc.Frontend.externs P1) :
    ∀ x g is a ts e, TailAt2 P1 1 (.let_ x (.call g is a ts) e) → Spike.Lib.LowerCall.Callee cx g → False := by
  intro x g is a ts e ht hC
  have hx : ((Scc.Frontend.externs P1).find? (·.1 == "print")).isSome = true := by decide
  rcases hello1_main_tails (ht _ hello1_main_compiled2) with h | h | h | h
  · cases h
  · cases h
  · cases h
    rw [← hcx, hC.1] at hx
    cases hx
  · cases h

/-- **`main` has no lane store.** -/
theorem hello1_main_noXchg : ∀ x b i v e, ¬ TailAt2 P1 1 (.let_ x (.xchgAt b i v) e) := by
  intro x b i v e ht
  rcases hello1_main_tails (ht _ hello1_main_compiled2) with h | h | h | h <;> cases h

/-- **`main` has no buffer allocation.** -/
theorem hello1_main_noNewBuf : ∀ x cn τ e, ¬ TailAt2 P1 1 (.let_ x (.newBuf cn τ) e) := by
  intro x cn τ e ht
  rcases hello1_main_tails (ht _ hello1_main_compiled2) with h | h | h | h <;> cases h

end Spike.Test.Hello1MainSrc

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.Hello1MainSrc.hello1_main_hlitP' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Test.Hello1MainSrc.hello1_main_hlitP

/-- info: 'Spike.Test.Hello1MainSrc.hello1_main_noCallee' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Test.Hello1MainSrc.hello1_main_noCallee
