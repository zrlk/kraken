/-
**A compiled block's code facts at the theorem's immediates** (x86-64; the twin of `Spike/Lib/LowerA64/FnCode2Me.lean`):
`FnCode2`'s immediates `i` are read only at the lowering walk's points
(`hWk`'s `ImmIn`), each in the walk predicate `T`; so code facts at `i`
are code facts at any `i'` agreeing with `i` at `T`'s terms, every other
field the same. The placement check's choice `fnCode2OfP`
(`Spike/Lib/LowerX64/HproOf.lean`) is at `imms2Of p`; the `W2` instances
of the assembled theorem are at `imms2Me Λ p`, which agrees with it at
every point of a compiled block (`imms2Me_tailAt2`).

- `FnCode2.withI`: the code facts at agreeing immediates; its fields
  `c`'s (`withI_lcx`, `withI_Bl`, `withI_fr`, `withI_fn`, `withI_na`);
- `proOK_withI`: the prologue's facts `ProOK` carry over;
- `fnCode2OfPMe`, `fnCode2OfPMe_spec`, `fnCode2OfPMe_spec2`: `fnCode2OfP`
  at `imms2Me Λm p`, with `fnCode2OfP_spec`'s and `fnCode2OfP_spec2`'s
  facts.
-/
import Spike.Lib.LowerX64.HproOf
import Spike.Lib.Src.ImmsMeTail

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.LowerNode (compiled2 TailAt2 lcx2 imms2Me imms2Me_tailAt2 immIn_congr)

namespace FnCode2

variable {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64} {RaOk : BitVec 64 → Prop}
  {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
  {d : Decl}

/-- **The code facts at agreeing immediates**: `c`'s, at immediates `i'`
equal to `i` at every term of the walk predicate `T` (`hi`); only the walk's
`ImmIn` changes (`immIn_congr`). -/
def withI (c : FnCode2 exe cells endPc RaOk Cd i T d) (i' : Expr → String → Nat → Option Nat)
    (hi : ∀ t, T t → ∀ x k, i t x k = i' t x k) : FnCode2 exe cells endPc RaOk Cd i' T d :=
  { c with
    hWk := fun q hq => ⟨immIn_congr (c.hWk q hq).1 (hi _ (c.hWk q hq).2.1), (c.hWk q hq).2⟩ }

variable (c : FnCode2 exe cells endPc RaOk Cd i T d) (i' : Expr → String → Nat → Option Nat)
  (hi : ∀ t, T t → ∀ x k, i t x k = i' t x k)

@[simp] theorem withI_lcx : (c.withI i' hi).lcx = c.lcx := rfl
@[simp] theorem withI_Bl : (c.withI i' hi).Bl = c.Bl := rfl
@[simp] theorem withI_fr : (c.withI i' hi).fr = c.fr := rfl
@[simp] theorem withI_fn : (c.withI i' hi).fn = c.fn := rfl
@[simp] theorem withI_na : (c.withI i' hi).na = c.na := rfl

end FnCode2

/-- **The prologue's facts at agreeing immediates** (`ProOK` reads the
frame, the prologue's cells and the entry label only). -/
theorem proOK_withI (Ly : RuntimeLayout) {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (i' : Expr → String → Nat → Option Nat)
    (hi : ∀ t, T t → ∀ x k, i t x k = i' t x k) : ProOK Ly d (c.withI i' hi) ↔ ProOK Ly d c :=
  Iff.rfl

section Place

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

/-- **The placement check's code facts at the theorem's immediates**:
`fnCode2OfP` at `imms2Me Λm p`, which is `imms2Of p` at every point of the
`j`th compiled block (`imms2Me_tailAt2`). -/
noncomputable def fnCode2OfPMe (Λm : Scc.Sem.Layout) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      (imms2Me Λm p) (TailAt2 p j) d :=
  (fnCode2OfP hp h j d hd).withI _ fun _ ht x k => (imms2Me_tailAt2 hp hd ht x k).symm

/-- **`fnCode2OfPMe`'s lowering context, call predicate and prologue
facts** (`fnCode2OfP_spec`'s). -/
theorem fnCode2OfPMe_spec (Λm : Scc.Sem.Layout) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    (fnCode2OfPMe hp h Λm j d hd).lcx = lcx2 p cfg.layout.obj d ∧
    (fnCode2OfPMe hp h Λm j d hd).Bl = (fun ra => BlC2L OP (Spike.Lib.X64.PhRec.okPc LY)
      (Spike.Lib.X64.PhRec.ph LY) (LY).lab (fnCode2OfPMe hp h Λm j d hd).fr (Int64.ofBitVec ra)) ∧
    ProOK LY d (fnCode2OfPMe hp h Λm j d hd) :=
  fnCode2OfP_spec hp h j d hd

/-- **`fnCode2OfPMe`'s lowering data, parameter count and frame**
(`fnCode2OfP_spec2`'s). -/
theorem fnCode2OfPMe_spec2 (Λm : Scc.Sem.Layout) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d) :
    ∃ w : Spike.Lib.LowerNode.Low2, Spike.Lib.LowerNode.LowC2 p cfg.layout.obj d w ∧
      (fnCode2OfPMe hp h Λm j d hd).na = w.na ∧
      Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
        w.hp w.r ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs ∧
      (fnCode2OfPMe hp h Λm j d hd).fr = frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
        (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc
          w.hp w.r) :=
  fnCode2OfP_spec2 hp h j d hd

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.fnCode2OfPMe_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCode2OfPMe_spec

/-- info: 'Spike.Lib.LowerX64.fnCode2OfPMe_spec2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnCode2OfPMe_spec2

end Spike.Lib.LowerX64
