/-
**The call order of an `Accepted2` program's compiled blocks** (x86-64):
`fnSpecC2_allI`'s premise `hord` at `P := compiled2 p`, from `callOrder2T`
(`Spike/Lib/Src/CallOrder2.lean`), for code facts whose lowering contexts
have the frontend's externs (`hext`).

- `hord_ofAccepted2`: a plain call (`CallIn2`) at a term still to lower
  in the `j`th compiled block's body names the `j'`th compiled block,
  `j' < j`.
-/
import Spike.Lib.LowerX64.ProgC2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Spike.Lib.LowerNode

/-- **`fnSpecC2_allI`'s call order at the compiled blocks** of an
`Accepted2` program: the code facts' lowering contexts with the frontend's
externs (`hext`), a plain call of `g` at a term still to lower in the
`j`th block's body (`CallIn2`) names a block `dg` that is the `j'`th
compiled block, `j' < j`. -/
theorem hord_ofAccepted2 {p : Prog} (hacc : Scc.Lower.Accepted2 p = true) {exe : _root_.Executable}
    {cells : List (Directive × Nat)} {endPc : Int64} {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop} {i : Expr → String → Nat → Option Nat}
    {T : Nat → Expr → Prop}
    (hcode : ∀ (j : Nat) d, (compiled2 p)[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (hext : ∀ (j : Nat) d (hd : (compiled2 p)[j]? = some d), (hcode j d hd).lcx.externs = Scc.Frontend.externs p) :
    ∀ (j : Nat) d (hd : (compiled2 p)[j]? = some d) g dg,
      CallIn2 (hcode j d hd).lcx d.body g → p.find? (·.name == g) = some dg →
      ∃ j' : Nat, j' < j ∧ (compiled2 p)[j']? = some dg := by
  intro j d hd g dg ⟨x, is, a, ts, e', ht, hx⟩ hf
  exact callOrder2T hacc hd ht (hext j d hd ▸ hx) hf

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hord_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hord_ofAccepted2
