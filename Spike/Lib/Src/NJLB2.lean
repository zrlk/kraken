import Spike.Lib.Src.NJLB
import Spike.Lib.Src.AbortImm2

/-!
**The node invariant with buffers and slices: the edges' source facts**
(ISA-neutral), for the per-construct edges at `bodyN2`.

- `plMask`, `litMask_of_grp`, `litMask_of_group_one`: a value grouped by its
  type (`Form.grp`) has its layout's scalar mask, so a one-placement value
  of a compatible layout is a leaf;
- `NJB.litMask_one`: at a lowering environment's symbolic environment
  (`ofEnv2`), an operand placed as one word is at a leaf of the walk
  (`litMask = [true]`, the premise of `NJB.add_ok`, `.sub_ok`, `.ifeq`).
  Not so at an arbitrary symbolic environment: a locative placed as one
  word represents (`ValRep` of a `.loc`) while its layout is `.loc`;
- `NJB.add_ovf_term`: `NJL.add_ovf` with the source's term at the `+` and
  its environment small (`EnvSmall`), the abort's symbolic environment at
  the source's types (`SEnv.retype`);
- `NJB.asLanesV`: `let x = asLanes sg w a` at any one-word operand at a
  leaf (`NJB.asLanes` is the literal's).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep grp group)
open Scc.Sem (ValRep)
open Scc.Lower (LitV litAt csAfter bufsAfter)

/-! ## Layouts of grouped values -/

/-- **Which placements are one word**: `.one`'s `true`, `.loc`'s `false`. -/
def plMask : List WordPl → List Bool :=
  List.map fun | .one _ => true | .loc _ _ => false

/-- **A value grouped by its type has its layout's scalar mask.** -/
theorem litMask_of_grp : ∀ (t : Ty) (L : LitV) (os : List Scc.IR.Operand) (pls : List WordPl)
    (os' : List Scc.IR.Operand), grp t os = some (pls, os') → Compat t L = true → litMask L = plMask pls := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L os pls os' h hc
    cases L <;> simp only [Compat, Bool.and_eq_true, Bool.false_eq_true] at hc
    simp only [grp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨⟨p1, o1⟩, h1, ⟨p2, o2⟩, h2, he⟩ := h
    cases he
    simp [litMask, plMask, iha _ _ _ _ h1 hc.1, ihb _ _ _ _ h2 hc.2]
  | refine t _ ih => intro L os pls os' h hc; exact ih L os pls os' h hc
  | iall t ih => intro L os pls os' h hc; exact ih L os pls os' h hc
  | mu t ih => intro L os pls os' h hc; exact ih L os pls os' h hc
  | iex b ih =>
    intro L os pls os' h hc
    simp only [Compat, Bool.and_eq_true] at hc
    simp only [grp] at h
    split at h
    · cases h
    · exact ih L os pls os' h hc.2
  | tex k b ih =>
    intro L os pls os' h hc
    simp only [Compat, Bool.and_eq_true] at hc
    simp only [grp] at h
    split at h
    · cases h
    · exact ih L os pls os' h hc.2
  | _ =>
    intro L os pls os' h hc
    cases L <;> cases os <;> simp_all [grp, Compat] <;>
      first
      | (obtain ⟨rfl, -⟩ := h; rfl)
      | (rename_i os; cases os <;> simp_all [grp]; obtain ⟨rfl, -⟩ := h; rfl)

/-- **A one-placement value of a compatible layout is at a leaf.** -/
theorem litMask_of_group_one {t : Ty} {L : LitV} {os : List Scc.IR.Operand} {o : Scc.IR.Operand}
    (h : group t os = some [.one o]) (hc : Compat t L = true) : litMask L = [true] := by
  unfold group at h
  split at h
  · rename_i pls hg
    cases h
    exact litMask_of_grp t L os _ [] hg hc
  · cases h

/-! ## At the node invariant -/

section NJB

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
  {lits : List (String × LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
  {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {B : Nat}

/-- **An operand placed as one word at a lowering environment is at a
leaf of the walk.** -/
theorem NJB.litMask_one {env : Scc.Lower.Env} {t : Expr} {sl : Int → BitVec 64} {c : Ctl} {a : At} {ta : Ty}
    {pa : Scc.IR.Operand} (h : NJB p lbl rs lits cs bufs L sm lsize B t (ofEnv2 env) sl c)
    (ha : sevalAt (ofEnv2 env) a = some (ta, [.one pa])) (hsc : InLits lits a) :
    litMask (litAt lits a) = [true] := by
  obtain ⟨c1, -, hj, hn, -, -, -⟩ := h
  obtain ⟨t1, ws, he, hE, -⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hc := (hn.evalAt hsc ha he).1
  rw [compat_of_eraseLen hE] at hc
  cases a with
  | var x =>
    simp only [sevalAt, lookupS_ofEnv2, Option.map_eq_some_iff] at ha
    obtain ⟨b, -, hb⟩ := ha
    simp only [Prod.mk.injEq] at hb
    obtain ⟨hbt, hbg⟩ := hb
    subst hbt
    have hg : group b.2.1 b.2.2 = some [.one pa] := by
      cases hgr : group b.2.1 b.2.2 with
      | none => rw [hgr] at hbg; cases hbg
      | some q => rw [hgr] at hbg; simp only [Option.getD_some] at hbg; rw [hbg]
    exact litMask_of_group_one hg hc
  | lit n => rfl
  | unit => simp [sevalAt] at ha

/-- `NJL.add_ovf`, with the source's term at the `+` and its environment
small; the abort's symbolic environment `s` at the source's types
(`SEnv.retype`, `SRepE.toSRep`: the node invariant is up to a buffer's
literal lengths), its placements `s`'s. -/
theorem NJB.add_ovf_term {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl}
    {ta tb : Ty} {pa pb : Scc.IR.Operand} {va vb : Nat}
    (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hge : 2 ^ 64 ≤ va + vb)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome) :
    ∃ c1, LocalRun p c c1 ∧ AbSrcL lbl rs lits (s.retype c1.env) sl c1 ∧ EnvSmall c1.env ∧
      c1.term = .let_ x (.add a b) e := by
  obtain ⟨c1, wa, wb, ta', tb', hr, hj, hn, -, -, hS, hea, heb, -, -, hna, hnb, -, -⟩ :=
    h.ops ha hb hsa hsb hma hmb hva hvb
  refine ⟨c1, hr, ⟨⟨x, a, b, e, ta', tb', wa, wb, va, vb, hj.1, hea, heb, hna, hnb, hge⟩, hn, hj.2.2.toSRep,
    fun y hy => ?_⟩, hS, hj.1⟩
  rw [Spike.Lib.Form.lookupS_retype_isSome]
  rw [hj.1] at hy; exact htot y hy

/-- **`let x = asLanes sg w a`** at a one-word operand at a leaf of the walk
(`NJB.asLanes` at any atom): `x` placed where `a` is. -/
theorem NJB.asLanesV {x : String} {sg : Bool} {w : Wd} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64}
    {c : Ctl} {ta : Ty} {pa : Scc.IR.Operand}
    (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x (.asLanes sg w a) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hsc : InLits lits a) (hma : litMask (litAt lits a) = [true]) :
    NJB p lbl rs ((x, .leaf (litAt lits a).one) :: lits) (csAfter x cs (.asLanes sg w a))
      (bufsAfter x cs bufs (.asLanes sg w a)) L sm lsize B e ((x, .lanes sg w, [.one pa]) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn, hb, hm, hS⟩ := h
  obtain ⟨t1, ws, he, -, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hnl := (hn.evalAt hsc ha he).2
  match ws, hw, he, hnl with
  | [wa], ⟨⟨v, hv, hrep⟩, _⟩, he, hnl =>
    obtain ⟨n, hn1, hn2⟩ := hnl.one hma
    rw [hn1] at hrep
    obtain ⟨-, hvn⟩ := hrep
    subst hvn
    have hmod : v % TermRun.W64 = v := Nat.mod_eq_of_lt hn2
    have hst := Spike.Lib.Form.localStep_asLanes (p := p) (n := v) hj.1 he (by simp [TermRun.numOf, hn1])
    have hw' : WordsRep lbl (opdVal rs sl) [TermRun.cst (.num (v % TermRun.W64))] [.one pa] :=
      ⟨⟨v, hv, by simp [TermRun.cst, Promises.TVal.mk0, ValRep, hmod, hn2]⟩, trivial⟩
    obtain ⟨hr2, hj2⟩ := hj.step hst rfl hw' (fun _ _ _ _ _ _ => rfl)
    refine ⟨_, hr.trans hr2, hj2, hn.cons rfl (NumL.of_all fun w' hw'' => ?_),
      hb.cons (SliceL.leaf _ _) (by rintro _ (h | h) <;> cases h) (by intro _ _ h; cases h), hm,
      EnvSmall.cons hS (WordsSmall.num (by rw [hmod]; exact hn2))⟩
    simp only [List.mem_singleton] at hw''
    subst hw''
    exact ⟨v, by simp [TermRun.cst, Promises.TVal.mk0, hmod], hn2⟩

end NJB

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.NJB.litMask_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.litMask_one

/-- info: 'Spike.Lib.LowerNode.NJB.add_ovf_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.add_ovf_term

/-- info: 'Spike.Lib.LowerNode.NJB.asLanesV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.asLanesV

end Spike.Lib.LowerNode
