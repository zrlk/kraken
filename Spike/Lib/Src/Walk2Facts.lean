/-
**A compiled block's walk facts for its code facts** (ISA-neutral): the
source side of `FnCode2` (`Spike/Lib/LowerA64/ProgC2.lean`,
`Spike/Lib/LowerX64/ProgC2.lean`) for a compiled block of an `Accepted2`
program, at the lowering's context `lcx2` and its parameter's environment
`env2 d na`.

- `paramK_ne_regName`, `fresh_env2`: the parameter registers `x.i` are no
  `fresh` name, so the parameter's environment is fresh from `0`;
- `compiled2_facts`: a compiled block is a block of the program, neither the
  output extern nor its loop;
- `lcx2`, `lits2`: the lowering's context of a block and its literal walk's
  start;
- `TailAt2`, `tailAt2_of`: the walk predicate at the `j`th compiled block;
- `Walk2Facts`: the walk facts `Accepted2` does not give here yet (the
  bindings' types `EnvTy2`, grouping `GrpL`, locative bases
  `LocBaseRegAt`; the literal walk's `LitPt` and its `ret`s' layouts);
- `walk2_src`: with them, `FnCode2`'s `hWk` (the immediates `imms2Of p`,
  the walk predicate `TailOf · d.body`), `hcnt` and `hxchg` from
  `Accepted2`;
- `walk2Facts_ofAccepted2`, `walk2_srcA`: `Walk2Facts` from `Accepted2`
  (`walk2_ofAccepted2`, `litPts_ofAccepted2`, `ret_layout`), so the code
  facts from `Accepted2` alone;
- `callLk_ofAccepted2`: the literal walk's calls at their callees'
  parameter layouts (`CallLk`), from `callsOk2`.
-/
import Spike.Lib.Src.Walk2Of
import Spike.Lib.Src.ImmIn2
import Spike.Lib.Src.AbortImm2
import Spike.Lib.Src.ExternUnit
import Spike.Lib.Src.CallOrder2
import Spike.Lib.Src.LitPt2
import Spike.Lib.Src.SliceL
import Spike.Lib.LowerProgC2Core

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (Env LitV litAt shapeOf params2 litWalk2)
open Scc.Lower.Inv (regName)

/-! ## The parameter's environment is fresh -/

private theorem dropDigits {c : Char} (hc : c.isDigit = false) :
    ∀ (l rest : List Char), (∀ x ∈ l, x.isDigit = true) → (l ++ c :: rest).dropWhile Char.isDigit = c :: rest
  | [], rest, _ => by simp [hc]
  | x :: l, rest, h => by
    simp only [List.cons_append, List.dropWhile_cons, h x (by simp), ite_true]
    exact dropDigits hc l rest (fun y hy => h y (by simp [hy]))

private theorem sepHead {c : Char} (hc : c.isDigit = false) (a : List Char) (k : Nat) :
    ((a ++ [c] ++ Nat.toDigits 10 k).reverse.dropWhile Char.isDigit).head? = some c := by
  have : (a ++ [c] ++ Nat.toDigits 10 k).reverse = (Nat.toDigits 10 k).reverse ++ c :: a.reverse := by simp
  rw [this, dropDigits hc]
  · rfl
  · intro x hx
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) (List.mem_reverse.mp hx)

/-- **A parameter register is no `fresh` name**: the last non-digit of
`x.i` is `.`, that of `regName z k` is `%` (`param_ne_regName` at any
index). -/
theorem paramK_ne_regName (a z : String) (i k : Nat) : s!"{a}.{i}" ≠ regName z k := by
  intro he
  have hl := congrArg (fun s => (s.toList.reverse.dropWhile Char.isDigit).head?) he
  simp only [regName, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr] at hl
  have h1 : (toString ".").toList = ['.'] := rfl
  have h2 : (toString "%").toList = ['%'] := rfl
  rw [h1, h2, sepHead (by decide), sepHead (by decide)] at hl
  simp at hl

/-- **The parameter's environment is fresh from `0`.** -/
theorem fresh_env2 (d : Decl) (na : Nat) : Fresh (Spike.Lib.LowerShape.env2 d na) 0 := by
  intro v hv o ho r hr y k _
  simp only [Spike.Lib.LowerShape.env2, List.mem_singleton] at hv
  subst hv
  simp only [Spike.Lib.LowerShape.paramsR, List.map_map, List.mem_map, List.mem_range, Function.comp] at ho
  obtain ⟨i, -, rfl⟩ := ho
  cases hr
  exact paramK_ne_regName d.arg y i k

/-! ## A compiled block -/

/-- **A compiled block** (`compiled2 p`) of an `Accepted2` program is a
block of it, neither the output extern nor (with the extern) its loop. -/
theorem compiled2_facts {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl} (hd : d ∈ compiled2 p) :
    d ∈ p ∧ Scc.Lower.isPrintExt d = false ∧ ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL") := by
  simp only [compiled2, List.mem_filter, Bool.not_eq_true'] at hd
  obtain ⟨hd, hc⟩ := hd
  have hne := isPrintExt_false_of_compiled hd hc
  refine ⟨hd, hne, ?_⟩
  have hp' := hp
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hds⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hp'
  rintro ⟨hpr, hnm⟩
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  unfold Scc.Lower.decl2 at hE
  simp only [hne, hpr, hnm, Bool.false_eq_true, ↓reduceIte, Bool.true_and, beq_self_eq_true] at hE
  have hx : Scc.Frontend.externOf d = some .print := by
    unfold Scc.Frontend.externOf
    simp [hnm, hE]
  have : ((Scc.Frontend.externs p).any (·.1 == d.name)) = true :=
    List.any_eq_true.2 ⟨(d.name, .print), List.mem_filterMap.2 ⟨d, hd, by rw [hx]; rfl⟩, by simp⟩
  rw [hc] at this; cases this

/-- **The lowering's context of a compiled block** (`LowC2`'s). -/
abbrev lcx2 (p : Prog) (obj : Scc.ObjLayout) (d : Decl) : Scc.Lower.Ctx :=
  { prog := p, externs := Scc.Frontend.externs p, fn := d.name, obj }

/-- **The literal walk's start** of a block: its parameter at its type's
layout. -/
abbrev lits2 (d : Decl) : List (String × LitV) := (params2 d).map (·, shapeOf d.argTy)

/-- **A term still to lower in the `j`th compiled block's body**: the walk
predicate at index `j` (`fnSpecC2_allI`'s `T j`). -/
def TailAt2 (p : Prog) (j : Nat) (e : Expr) : Prop :=
  ∀ d, (compiled2 p)[j]? = some d → TailOf e d.body

/-- `TailAt2` at the `j`th compiled block. -/
theorem tailAt2_of {p : Prog} {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {e : Expr}
    (h : TailOf e d.body) : TailAt2 p j e := by
  intro d' hd'
  rw [hd] at hd'
  cases hd'
  exact h

/-- **The walk facts of a compiled block not yet from `Accepted2`** (at the
parameter's word count `na`): at every point of the lowering's walk the
bindings' types (`EnvTy2`), grouping (`GrpL`) and the locatives' register
bases (`LocBaseRegAt`); at every point of the literal walk `LitPt`, and
every `ret`'s layout the return type's. -/
def Walk2Facts (p : Prog) (obj : Scc.ObjLayout) (d : Decl) (na : Nat) : Prop :=
  (∀ q ∈ lowerEnvs2 (lcx2 p obj d) (Spike.Lib.LowerShape.env2 d na) 0 d.body,
    EnvTy2 q ∧ GrpL q.2.1 ∧ LocBaseRegAt (ofEnv2 q.2.1) q.1) ∧
  (∀ q ∈ litWalk2 p (lits2 d) d.body, LitPt q) ∧
  ∀ a lits', (.ret a, lits') ∈ litWalk2 p (lits2 d) d.body → (litAt lits' a).erase = shapeOf d.retTy

/-- **A compiled block's source code facts** (`FnCode2`'s `hWk`, `hcnt`,
`hxchg`) from `Accepted2` and `Walk2Facts`: the immediates `imms2Of p`
(`immIn_imms2Of`), the walk predicate `TailOf · d.body`
(`lowerEnvs2_tail`), the pairs' counts (`countsOk2_decl`) and the lane
stores' range (`xchgsB_of_body2`). -/
theorem walk2_src {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {obj : Scc.ObjLayout} {d : Decl}
    (hd : d ∈ compiled2 p) {w : Low2} (hL : LowC2 p obj d w) (hW : Walk2Facts p obj d w.na) :
    (∀ q ∈ lowerEnvs2 (lcx2 p obj d) (Spike.Lib.LowerShape.env2 d w.na) 0 d.body,
      ImmIn (Scc.Lower.imms2Of p) (ofEnv2 q.2.1) q.1 ∧ TailOf q.1 d.body ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) ∧
    Scc.Lower.countsB p [] [] (lits2 d) d.body = true ∧ xchgsB [] [] d.body = true := by
  obtain ⟨hdp, hne, hnl⟩ := compiled2_facts hp hd
  have hext := externs_unit (nodup_of_accepted2 hp)
  have hps : ∀ o ∈ (Spike.Lib.LowerShape.paramsR d w.na).map Operand.reg, IsReg o := by
    intro o ho
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 ho
    exact ⟨r, rfl⟩
  have hpl : Scc.Obj.valWords d.argTy = some ((Spike.Lib.LowerShape.paramsR d w.na).map Operand.reg).length := by
    rw [hL.1]; simp [Spike.Lib.LowerShape.paramsR]
  have himm := immIn_imms2Of hp (cx := lcx2 p obj d) rfl hext hdp hne hnl hps hpl 0
  obtain ⟨-, -, -, -, cx2, hb, -⟩ := decl2_setup hp (cx := lcx2 p obj d) rfl hext hdp hne hnl
  have hp' := hp
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp'
  obtain ⟨⟨-, hcnt⟩, -⟩ := hp'
  refine ⟨fun q hq => ⟨immIn_ofEnv2 (himm q hq), lowerEnvs2_tail _ _ _ q hq, hW.1 q hq⟩,
    countsOk2_decl hcnt hdp hne hnl, xchgsB_of_body2 _ [] [] _ (fun _ _ h => by cases h) hb⟩

/-- **`Walk2Facts` of a compiled block of an `Accepted2` program**: the
bindings' facts (`walk2_ofAccepted2`), the literal walk's `LitPt`
(`litPts_ofAccepted2`) and its `ret`s' layouts (`ret_layout`, `callsOk2`). -/
theorem walk2Facts_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {obj : Scc.ObjLayout}
    {d : Decl} (hd : d ∈ compiled2 p) {na : Nat} (hna : Scc.Obj.valWords d.argTy = some na) :
    Walk2Facts p obj d na := by
  obtain ⟨hdp, hne, hnl⟩ := compiled2_facts hp hd
  have hext := externs_unit (nodup_of_accepted2 hp)
  have hps : ∀ o ∈ (Spike.Lib.LowerShape.paramsR d na).map Operand.reg, IsReg o := by
    intro o ho
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 ho
    exact ⟨r, rfl⟩
  have hpl : Scc.Obj.valWords d.argTy = some ((Spike.Lib.LowerShape.paramsR d na).map Operand.reg).length := by
    rw [hna]; simp [Spike.Lib.LowerShape.paramsR]
  have hc : Scc.Lower.callsOk2 p = true := by
    have hp' := hp
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp'
    exact hp'.1.1.2
  refine ⟨fun q hq => ?_, litPts_ofAccepted2 hp hdp hne hnl, fun a lits' hq => ret_layout hc hdp hq⟩
  obtain ⟨-, -, hT, hG, hB⟩ := walk2_ofAccepted2 hp (cx := lcx2 p obj d) rfl hext hdp hne hnl hps hpl 0 q hq
  exact ⟨hT, hG, hB⟩

/-- **The literal walk's calls of a compiled block of an `Accepted2`
program** at their callees' parameter layouts (`CallLk`, `callsOk2`). -/
theorem callLk_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl} (hd : d ∈ compiled2 p) :
    ∀ q ∈ litWalk2 p (lits2 d) d.body, CallLk p q := by
  obtain ⟨hdp, -, -⟩ := compiled2_facts hp hd
  have hp' := hp
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp'
  exact callLk_of hp'.1.1.2 hdp

/-- **A compiled block's source code facts from `Accepted2` alone**:
`walk2_src` at `walk2Facts_ofAccepted2`. -/
theorem walk2_srcA {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {obj : Scc.ObjLayout} {d : Decl}
    (hd : d ∈ compiled2 p) {w : Low2} (hL : LowC2 p obj d w) :
    (∀ q ∈ lowerEnvs2 (lcx2 p obj d) (Spike.Lib.LowerShape.env2 d w.na) 0 d.body,
      ImmIn (Scc.Lower.imms2Of p) (ofEnv2 q.2.1) q.1 ∧ TailOf q.1 d.body ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) ∧
    Scc.Lower.countsB p [] [] (lits2 d) d.body = true ∧ xchgsB [] [] d.body = true :=
  walk2_src hp hd hL (walk2Facts_ofAccepted2 hp hd hL.1)

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.walk2_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.walk2_src

/-- info: 'Spike.Lib.LowerNode.walk2_srcA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.walk2_srcA

/-- info: 'Spike.Lib.LowerNode.callLk_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callLk_ofAccepted2
