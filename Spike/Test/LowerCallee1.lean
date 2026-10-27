import Spike.Lib.LowerA64.UserInj

/-!
# The callees of an `Accepted1` code block's lowering

`Spike/Lib/LowerCallee1.lean`, `Spike/Lib/LowerA64/CalleeRow.lean` and
`Spike/Lib/LowerA64/UserInj.lean` at work: the calls of a two-block
program's closed forms, the names before a code block, the non-injective
`Names.user`, the function index of a local label, and the call site's rows
composed with `fnPh1_ofPlaceOK`'s witnesses, with the callee's name.
-/

namespace Spike.Test.LowerCallee1

open Scc.Lower Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts)

/-- `main` calls `g` on `1`. -/
def callProg : CoreTerm.Prog :=
  [{ name := "g", idx := [], arg := "n", argTy := .int, retTy := .int, body := .ret (.var "n") },
   { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
     body := .let_ "r" (.call "g" [] (.lit 1)) (.ret (.var "r")) }]

/-- The callees of the closed form of `d` in `callProg` with depth limit `fr`. -/
def calls (fr : Option Nat) (d : CoreTerm.Decl) : List Scc.IR.Sym :=
  match lowerC { prog := callProg, externs := [], fn := d.name, frames := fr } (env1 d) 0 "entry" 0 d.body with
  | some r => (allInsts r).filterMap fun | .call _ f _ => some f | _ => none
  | none => []

-- `g` calls nothing; `main` calls `g` (`wc_g`), and with the depth counter
-- also the stack abort (`lowerC_callOk`).
#guard callProg.map (calls none) == [[], ["wc_g"]]
#guard callProg.map (calls (some 64)) == [[], [Names.abort, "wc_g"]]

-- `main`'s `earlier` is `g` (`decl1_take`).
example : decl1 ["g"] callProg[1] = true :=
  Spike.Lib.LowerCallee.decl1_take callProg [] (by decide) 1 (by decide)

-- `Names.user` is not injective: the callee is named up to its symbol.
#guard Names.user "_u2d_" == Names.user "-"
#guard Names.user "g" != Names.abort

/-- The call site's rows at `fnPh1_ofPlaceOK`'s witnesses. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    ∃ rs : List Res1, ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws, p[j]? = some d → rs[j]? = some r →
      Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r → ∃ j' dg, j' < j ∧ p[j']? = some dg := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := Spike.Lib.LowerA64.fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, fun j d r ds g ws hd hr hg => ?_⟩
  obtain ⟨j', dg, -, hlt, hdg, -⟩ := Spike.Lib.LowerA64.calleeRow_of_fnPh1 hp h hrs hir hd hr hg
  exact ⟨j', dg, hlt, hdg⟩

-- A local label's function index is its digits after `.L` (`labNumL_local`):
-- the two `wc_f_u27_` functions of `f'` and `f_u27_` have distinct stack
-- checks, so at most one is right after the first `wc_f_u27_` label.
#guard Spike.Lib.LowerA64.labNumL ".L19_wc_f_u27_.stack_check" == ['1', '9']
#guard Spike.Lib.LowerA64.labNumL ".L1_wc_f.stack_check" != Spike.Lib.LowerA64.labNumL ".L11_wc_f.stack_check"
#guard Names.user "f'" == Names.user "f_u27_"

/-- The callee's name at `fnPh1_ofPlaceOK`'s witnesses. -/
example {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) :
    ∃ rs : List Res1, ∀ (j : Nat) (d : CoreTerm.Decl) (r : Res1) ds (g : String) ws, p[j]? = some d →
      rs[j]? = some r → Scc.IR.Inst.call ds (Names.user g) ws ∈ allInsts r → g ∈ p.map (·.name) →
      ∃ j' dg, j' < j ∧ p[j']? = some dg ∧ dg.name = g := by
  obtain ⟨rs, rt, hrs, hir, -⟩ := Spike.Lib.LowerA64.fnPh1_ofPlaceOK hp hlow h (fun _ _ _ => none)
  refine ⟨rs, fun j d r ds g ws hd hr hg hgp => ?_⟩
  obtain ⟨j', dg, -, hlt, hdg, -, hn, -⟩ := Spike.Lib.LowerA64.calleeRow_name_of_fnPh1 hp h hrs hir hd hr hg hgp
  exact ⟨j', dg, hlt, hdg, hn⟩

end Spike.Test.LowerCallee1
