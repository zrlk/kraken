/-
**The walk after `rodata`'s allocation** (x86-64; the twin of the `Tr`
part of `Spike/Test/A64Hello1ResL.lean`): plan b1's walk-restricted
resumption takes a landing's context at the points `Tr` after a buffer's
allocation (`TrNb`, the strict tails of an allocation's `let` among the
walk's points), closed under the walk (`TrNb.tail`) and inside it
(`TrNb.tailAt2`). At `hello1o`'s setup block `rodata` the constructs a
resumption must cover are vacuous on `Tr`: `rodata` allocates once
(`nbOnceL`, decided) and has no call (`hello1_rodata_noCallT`).

- `tailOf_trans`: `TailOf` is transitive;
- `TrNb`, `TrNb.intro`, `TrNb.tail`, `TrNb.of_closed`, `tailAt2_tail`, `TrNb.tailAt2`:
  the points after an allocation, closed under the walk and inside a
  closed walk predicate (`TailAt2`);
- `isNewBufLet`, `nbOnceL`, `noNb_of_nbOnceL`: the listed check of a single
  allocation and no allocation after an allocation from it;
- `hello1_rodata_nbOnce`, `hello1_rodata_trNoNb`, `hello1_rodata_trNoCall`:
  `rodata`'s check (decided), no allocation and no call in its `Tr`;
- `hello1_rodata_trNoNbT`: no allocation at `TailAt2 ∧ Tr`.
-/
import Spike.Test.X64Hello1NoCall

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Spike.Lib.LowerNode (compiled2 TailAt2)

section Tr

open Spike.Lib.LowerNode (TailOf)

/-- **`TailOf` is transitive**: a point of a point of `e` is a point of `e`. -/
theorem tailOf_trans {t u e : Expr} (h1 : TailOf t u) (h2 : TailOf u e) : TailOf t e := by
  induction h2 with
  | refl => exact h1
  | let_ x op _ ih => exact .let_ x op ih
  | split a x y _ ih => exact .split a x y ih
  | unpack a i x _ ih => exact .unpack a i x ih
  | unpackT a α x _ ih => exact .unpackT a α x ih
  | yes a b no _ ih => exact .yes a b no ih
  | no a b yes _ ih => exact .no a b yes ih

/-- **The walk's points after a buffer's allocation** (plan b1's `Tr`):
the points of the continuation `e` of some `let x = newBuf cn τ; e` at a
walk point (`T`), i.e. the strict tails of an allocation's `let`. -/
def TrNb (T : Expr → Prop) (t : Expr) : Prop :=
  ∃ x cn τ e, T (.let_ x (.newBuf cn τ) e) ∧ TailOf t e

/-- **An allocation's continuation's points are in `TrNb`** (`landStk_segT`'s
closure premise `hTr` at `Tr j := TrNb (T j)`). -/
theorem TrNb.intro {T : Expr → Prop} {x : String} {cn : At} {τ : Ty} {e t : Expr}
    (hT : T (.let_ x (.newBuf cn τ) e)) (ht : TailOf t e) : TrNb T t :=
  ⟨x, cn, τ, e, hT, ht⟩

/-- **`TrNb` is closed under the walk** (`TailOf`). -/
theorem TrNb.tail {T : Expr → Prop} {t t' : Expr} (h : TrNb T t) (ht : TailOf t' t) : TrNb T t' := by
  obtain ⟨x, cn, τ, e, hT, he⟩ := h
  exact ⟨x, cn, τ, e, hT, tailOf_trans ht he⟩

/-- **`TrNb` stays inside a walk predicate closed under `TailOf`.** -/
theorem TrNb.of_closed {T : Expr → Prop} (hT : ∀ t u, T u → TailOf t u → T t) {t : Expr} (h : TrNb T t) :
    T t := by
  obtain ⟨x, cn, τ, e, hL, he⟩ := h
  exact hT t _ hL (tailOf_trans he (.let_ x _ (.refl e)))

/-- **`TailAt2` is closed under `TailOf`.** -/
theorem tailAt2_tail {p : Prog} {j : Nat} {t u : Expr} (hu : TailAt2 p j u) (ht : TailOf t u) :
    TailAt2 p j t := fun d hd => tailOf_trans ht (hu d hd)

/-- **`TrNb` at the `j`th compiled block's walk is in the walk.** -/
theorem TrNb.tailAt2 {p : Prog} {j : Nat} {t : Expr} (h : TrNb (TailAt2 p j) t) : TailAt2 p j t :=
  h.of_closed fun _ _ hu ht => tailAt2_tail hu ht

/-- A buffer allocation's `let`. -/
def isNewBufLet : Expr → Bool
  | .let_ _ (.newBuf _ _) _ => true
  | _ => false

/-- **The listed check of a single allocation**: at every allocation's
`let` among the points of `e`, no point of its continuation is an
allocation's `let`. -/
def nbOnceL (e : Expr) : Bool :=
  (tailsL e).all fun t => match t with
    | .let_ _ (.newBuf _ _) b => (tailsL b).all fun u => !isNewBufLet u
    | _ => true

/-- **No allocation after an allocation** from `nbOnceL`. -/
theorem noNb_of_nbOnceL {e : Expr} (h : nbOnceL e = true) :
    ∀ x cn τ b, ¬ TrNb (fun t => TailOf t e) (.let_ x (.newBuf cn τ) b) := by
  rintro x cn τ b ⟨y, cn', τ', e', hL, ht⟩
  have h1 := List.all_eq_true.mp h _ (tailOf_mem_tailsL hL)
  have h2 := List.all_eq_true.mp h1 _ (tailOf_mem_tailsL ht)
  simp [isNewBufLet] at h2

end Tr

section Hello1

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- **`rodata`'s body allocates once** in `hello1o` (decided). -/
theorem hello1_rodata_nbOnce : ∀ (j : Nat) (d : Decl), (compiled2 P1)[j]? = some d → d.name = "rodata" →
    nbOnceL d.body = true := by
  have hc : ∀ d ∈ compiled2 P1, d.name = "rodata" → nbOnceL d.body = true := by decide
  exact fun j d hd hn => hc d (List.mem_of_getElem? hd) hn

/-- **No allocation in `rodata`'s `Tr`** (plan b1): no point after its
buffer's allocation is an allocation's `let`. -/
theorem hello1_rodata_trNoNb {j : Nat} {d : Decl} (hd : (compiled2 P1)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x cn τ b, ¬ TrNb (TailAt2 P1 j) (.let_ x (.newBuf cn τ) b) := by
  rintro x cn τ b ⟨y, cn', τ', e', hL, ht⟩
  exact noNb_of_nbOnceL (hello1_rodata_nbOnce j d hd hn) x cn τ b ⟨y, cn', τ', e', hL d hd, ht⟩

/-- **No call in `rodata`'s `Tr`** (plan b1; `rodata` is call-free). -/
theorem hello1_rodata_trNoCall {j : Nat} {d : Decl} (hd : (compiled2 P1)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x g is a ts e, ¬ TrNb (TailAt2 P1 j) (.let_ x (.call g is a ts) e) := fun x g is a ts e h =>
  hello1_rodata_noCallT hd hn x g is a ts e h.tailAt2

/-- **No allocation at the walk restricted to `rodata`'s `Tr`** (the shape
`T ∧ Tr` the restricted resumption's allocation premises are taken at). -/
theorem hello1_rodata_trNoNbT {j : Nat} {d : Decl} (hd : (compiled2 P1)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x cn τ e, ¬ (TailAt2 P1 j (.let_ x (.newBuf cn τ) e) ∧ TrNb (TailAt2 P1 j) (.let_ x (.newBuf cn τ) e)) :=
  fun x cn τ e h => hello1_rodata_trNoNb hd hn x cn τ e h.2

end Hello1

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.tailOf_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.tailOf_trans

/-- info: 'Spike.Lib.LowerX64.TrNb.tail' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.TrNb.tail

/-- info: 'Spike.Lib.LowerX64.TrNb.of_closed' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.TrNb.of_closed

/-- info: 'Spike.Lib.LowerX64.tailAt2_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.tailAt2_tail

/-- info: 'Spike.Lib.LowerX64.TrNb.tailAt2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.TrNb.tailAt2

/-- info: 'Spike.Lib.LowerX64.noNb_of_nbOnceL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.noNb_of_nbOnceL

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_nbOnce' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_nbOnce

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_trNoNb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_trNoNb

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_trNoCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_trNoCall

/-- info: 'Spike.Lib.LowerX64.TrNb.intro' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.TrNb.intro

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_trNoNbT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_trNoNbT
