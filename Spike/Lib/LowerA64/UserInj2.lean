/-
**Distinct `Accepted2` code blocks have distinct symbols** (AArch64): the
twin of `Spike/Lib/LowerA64/UserInj.lean` for the compiled blocks of an
`Accepted2` program (`compiled2 p`, lowered to `funcs2`): on an output
passing `PlaceOK`, two compiled blocks with one `Names.user` symbol are one
block, so a call names its callee exactly.

- `stackCheck_of_fnPh2`: each compiled block's function's label is right
  before its stack check (`prologueIn`, A12's `fnOk1`);
- `user_inj2_of_placeOK`: a compiled block's symbol determines its index.
-/
import Spike.Lib.LowerA64.UserInj
import Spike.Lib.LowerProgC2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.AArch64.Parser
open Scc.Emit.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Rt.A64 (labelGap)
open Scc.Cert.Code1A64 (ctxOf fnOk1_of_fnCode1Ok fnOk1_facts)
open Spike.Lib.LowerShape (func2 paramsR)
open Spike.Lib.LowerNode (Pairwise2 Low2 compiled2 funcs2 mem_progOf_funcs2)

/-- **Each compiled block's function's label is right before its stack
check** from `PlaceOK` (`prologueIn`, A12's `fnOk1`), as `fnPh2_ofPlaceOK`
numbers them. -/
theorem stackCheck_of_fnPh2 {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Low2 → Prop} {ws : List Low2} {rt : List Scc.IR.Func} (hws : Pairwise2 P (compiled2 p) ws)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws))
    (j : Nat) (hj : j < (compiled2 p).length) :
    let w := ws[j]'(hws.1 ▸ hj)
    labelGap (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (Scc.Lower.Names.user (compiled2 p)[j].name)
      ((ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
        (func2 (Scc.Lower.Names.user (compiled2 p)[j].name) (paramsR (compiled2 p)[j] w.na) w.sc w.hp
          w.r)).local "stack_check")
      0 = true := by
  intro w
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  have hmem : (func2 (Scc.Lower.Names.user (compiled2 p)[j].name) (paramsR (compiled2 p)[j] w.na) w.sc w.hp w.r,
      rt.length + j) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    rw [hir]
    exact mem_progOf_funcs2 cfg.layout rt hws j hj
  have hc1 := fnOk1_of_fnCode1Ok hc hmem rfl
  obtain ⟨ps, hps⟩ := spills_of_fnOk1 hc1
  obtain ⟨⟨entry, -, hpro⟩, -⟩ := fnOk1_facts hc1 rfl hps
  simp only [Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at hpro
  exact hpro.1.1.1.1.1

/-- **A compiled block's symbol determines it** on an `Accepted2` program
whose output passes `PlaceOK`: two compiled blocks with one `Names.user`
symbol are at one index (the first label of the symbol is followed by one
stack check label only, whose index prefix is the function's). -/
theorem user_inj2_of_placeOK {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Low2 → Prop} {ws : List Low2} {rt : List Scc.IR.Func} (hws : Pairwise2 P (compiled2 p) ws)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws))
    {j j' : Nat} (hj : j < (compiled2 p).length) (hj' : j' < (compiled2 p).length)
    (he : Scc.Lower.Names.user (compiled2 p)[j].name = Scc.Lower.Names.user (compiled2 p)[j'].name) : j = j' := by
  have h1 := stackCheck_of_fnPh2 h hws hir j hj
  have h2 := stackCheck_of_fnPh2 h hws hir j' hj'
  simp only at h1 h2
  rw [he] at h1
  have := local_inj (eq_of_labelGap0 h1 h2)
  have e : rt.length + j = rt.length + j' := this
  omega

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.user_inj2_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms user_inj2_of_placeOK

end Spike.Lib.LowerA64
