/-
**A function's segment from its lane stores and buffers alone** (AArch64):
`FnSpecC2` (`Spike/Lib/LowerA64/ProgC2.lean`) of a compiled block whose body
has no call at any point of the lowering walk (`TailOf`), from the
context's lane-store and buffer premises (`LaneC`, `NewBufC`): the plain
calls (`callC2_of_noCallee`) and prints (`PrintCallC`) hold vacuously. A
body's points are decided by listing them (`tailsL`).

- `tailsL`, `tailOf_mem_tailsL`: the points of the lowering walk in a body,
  listed; every `TailOf` point is one;
- `isCallLet`, `noCall_of_tailsL`: a call's `let`; none among the listed
  points, none at any point;
- `printCallC_of_noCall`: `PrintCallC` with no call under the walk
  predicate;
- `fnSpecC2_ofLaneBuf`: `FnSpecC2` of a block without calls from its
  contexts' `LaneC` and `NewBufC`.
-/
import Spike.Lib.LowerA64.ProgC2
import Spike.Lib.LowerA64.VacC2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64
open Spike.Lib.LowerNode (TailOf)

/-- **The points of the lowering walk in `e`, listed**: `e`, then those of
the body of its `let`, pair split or unpack, or of both branches of its
`if` (`TailOf`'s constructors). -/
def tailsL : Expr → List Expr
  | .let_ x op b => .let_ x op b :: tailsL b
  | .split a x y b => .split a x y b :: tailsL b
  | .unpack a i x b => .unpack a i x b :: tailsL b
  | .unpackT a α x b => .unpackT a α x b :: tailsL b
  | .ifeq a b y n => .ifeq a b y n :: (tailsL y ++ tailsL n)
  | e => [e]

/-- `e` is the first of its listed points. -/
theorem self_mem_tailsL (e : Expr) : e ∈ tailsL e := by
  cases e <;> simp [tailsL]

/-- **Every point of the lowering walk is listed** (`tailsL`). -/
theorem tailOf_mem_tailsL {t e : Expr} (h : TailOf t e) : t ∈ tailsL e := by
  induction h with
  | refl => exact self_mem_tailsL _
  | let_ x op _ ih => exact List.mem_cons_of_mem _ ih
  | split a x y _ ih => exact List.mem_cons_of_mem _ ih
  | unpack a i x _ ih => exact List.mem_cons_of_mem _ ih
  | unpackT a α x _ ih => exact List.mem_cons_of_mem _ ih
  | yes a b no _ ih => exact List.mem_cons_of_mem _ (List.mem_append_left _ ih)
  | no a b yes _ ih => exact List.mem_cons_of_mem _ (List.mem_append_right _ ih)

/-- A call's `let`. -/
def isCallLet : Expr → Bool
  | .let_ _ (.call _ _ _ _) _ => true
  | _ => false

/-- **No call at any point of `e`** from none among its listed points. -/
theorem noCall_of_tailsL {e : Expr} (h : (tailsL e).all (fun t => !isCallLet t) = true) :
    ∀ x g is a ts e', ¬ TailOf (.let_ x (.call g is a ts) e') e := fun x g is a ts e' ht => by
  have := List.all_eq_true.mp h _ (tailOf_mem_tailsL ht)
  simp [isCallLet] at this

section Vac

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {lcx : Scc.Lower.Ctx} {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : FragS isaLSE2}
  {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
  {fs : List TermRun.Frame} {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
  {Ab : FragS isaLSE2}

/-- **`PrintCallC` with no call under `T`.** -/
theorem printCallC_of_noCall (hno : ∀ x g is a ts e, ¬ T (.let_ x (.call g is a ts) e)) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk env n x g is a ts e xe dg t b o m cw lits cs bufs _ hT
  exact (hno x g is a ts e hT).elim

end Vac

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
  {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A function's segment from its lane stores and buffers** (`fnSpecC2_of_body`,
`bodySpecC2_of`): a compiled block whose walk predicate `T` holds only at
points of its body (`hT`), none of them a call (`hnc`, e.g. by `decide`), at
every context `CxOk` (every return address with `RaOk`) the lane stores'
and buffers' premises (`hcon`); the plain calls by `callC2_of_noCallee`, the
prints by `printCallC_of_noCall`. -/
theorem fnSpecC2_ofLaneBuf {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (c : FnCode2 exe prog endPc RaOk Cd i T d) (hT : ∀ t, T t → TailOf t d.body)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hcon : ∀ R F fs fp ra tp G0 Ab, CxOk R F fs fp ra tp G0 Ab → RaOk ra →
      LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab ∧
      NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy)) :
    FnSpecC2 W K p lbl lsize ms CxOk c := by
  have hno : ∀ x g is a ts e, ¬ T (.let_ x (.call g is a ts) e) := fun x g is a ts e hT' =>
    noCall_of_tailsL hnc x g is a ts e (hT _ hT')
  refine fnSpecC2_of_body c (bodySpecC2_of c fun R F fs fp ra tp G0 Ab hcx hra => ?_)
  obtain ⟨hl, hb⟩ := hcon R F fs fp ra tp G0 Ab hcx hra
  exact ⟨callC2_of_noCallee fun x g is a ts e hT' _ => hno x g is a ts e hT', hl, hb,
    printCallC_of_noCall hno⟩

end Fn

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.tailOf_mem_tailsL' depends on axioms: [propext] -/
#guard_msgs in #print axioms tailOf_mem_tailsL

/-- info: 'Spike.Lib.LowerA64.noCall_of_tailsL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms noCall_of_tailsL

/-- info: 'Spike.Lib.LowerA64.printCallC_of_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printCallC_of_noCall

/-- info: 'Spike.Lib.LowerA64.fnSpecC2_ofLaneBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnSpecC2_ofLaneBuf

end Spike.Lib.LowerA64
