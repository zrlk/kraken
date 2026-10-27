/-
**The output extern's operand at the call site** (ISA-neutral): the facts
`printCallC_of` needs at a call `let x = print(a)`, from the node
invariant at `ofEnv2 env` (`NodeJE`), the walk's literal and slice facts
(`EnvLit`, `EnvSl` at `SlP`), the lowering's grouping (`GrpL`) and the
call's layout (`callsOk2`: `a`'s layout erased is `ownSliceTy`'s).

- `groupL_ownSlice`: `ownSliceTy`'s layout groups four operands as a
  locative and two words;
- `printSite_of`: the operands' grouping, the source's three words, the
  length and the count numbers, `8 · length < 2^63` (`SlP`'s count bound).
-/
import Spike.Lib.Src.PrintCallSrc
import Spike.Lib.Src.NJLBEnv2

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib.Form (opdVal NodeJE sevalAt WordPl WordsRep group)
open Scc.Lower (Env LitV litAt shapeOf)
open Scc.Lower.Inv (atomV)

/-- **`ownSliceTy`'s layout groups a slice's four operands** as its
locative (base, offset), its length and its count. -/
theorem groupL_ownSlice (b o m cw : Scc.IR.Operand) :
    groupL (shapeOf Scc.Frontend.ownSliceTy) [b, o, m, cw] = some [.loc b o, .one m, .one cw] := rfl

/-- **The output extern's operand at the call site**: at a node `NodeJE`
at `ofEnv2 env` with the walk's literal and slice facts, an atom `a` whose
lowering words are `[b, o, m, cw]` (`GrpL env`), bound in the walk
(`InLits`) at a layout erasing to `ownSliceTy`'s, groups as a locative and
two words, and its source words are three, the second and the third
numbers, the second's `8 ·` below `2^63`. -/
theorem printSite_of {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int} {t : Expr}
    {env : Env} {sl : Int → BitVec 64} {c : Ctl} {lits : List (String × LitV)} {L : WeakMem.AllocLabel → Prop}
    {sm : WeakMem.Memory} {a : At} {ta : Ty} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hj : NodeJE lbl rs t (ofEnv2 env) sl c) (hl : EnvLit lits c.env) (hsl : EnvSl (SlP L sm) lits c.env)
    (hg : GrpL env) (hav : atomV env a = some (ta, [b, .reg o, m, cw])) (hsc : InLits lits a)
    (hsh : (litAt lits a).erase = shapeOf Scc.Frontend.ownSliceTy) :
    group ta [b, .reg o, m, cw] = some [.loc b (.reg o), .one m, .one cw] ∧
      ∃ (t' : Ty) (pw wm wn : TermRun.Word) (mv nv : Nat), TermRun.evalAt c.env a = some (t', [pw, wm, wn]) ∧
        wm.val = .num mv ∧ wn.val = .num nv ∧ 8 * mv < 2 ^ 63 := by
  obtain ⟨pls, hgr, hs⟩ := sevalAt_ofEnv2L hg hav
  obtain ⟨t', ws, he, hE, hwr⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hs
  obtain ⟨hc, hn⟩ := hl.evalAt hsc hs he
  have hca : Compat ta (litAt lits a) = true := by rw [← compat_of_eraseLen hE]; exact hc
  have hgo : group ta [b, .reg o, m, cw] = some [.loc b (.reg o), .one m, .one cw] := by
    rw [group_grpL hca, ← groupL_erase, hsh, groupL_ownSlice]
  rw [hgo] at hgr
  cases hgr
  refine ⟨hgo, ?_⟩
  obtain ⟨pw, wm, wn, rfl⟩ : ∃ pw wm wn, ws = [pw, wm, wn] := by
    match ws, hwr with
    | [pw, wm, wn], _ => exact ⟨pw, wm, wn, rfl⟩
  obtain ⟨l, mv, -, hwm, hP⟩ := print_arg_slAt hsl he hsh
  obtain ⟨nv, hwn, -⟩ : IsNum wn := (hn.of_erase hsh) 2 wn rfl (by rfl)
  exact ⟨t', pw, wm, wn, mv, nv, he, hwm, hwn, by have := hP.2.2; omega⟩

/-- info: 'Spike.Lib.LowerNode.printSite_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.printSite_of

end Spike.Lib.LowerNode
