import Spike.Lib.Src.NJLB2
import Spike.Lib.Src.LitPt2
import Spike.Lib.Src.GroupShape
import Spike.Lib.Src.GroupPl
import Spike.Lib.LowerShapeC2
import Spike.Lib.LowerEnv

/-!
**The node invariant's code-free moves at the lowering's environment**
(ISA-neutral): `NJB`'s per-construct lemmas (`NJB.atom`, `.nameI`, `.pair`,
`.pack`, `.asLanesV`, `.split`, `.unpack`) restated at the grouped symbolic
environment `ofEnv2 env` of the lowering's environment `env`, from the
lowering walk's facts (`atomV`, `pureOp`, `GrpL`, `EnvTy2`) and the literal
walk's (`LitPt`), so that their conclusions are at
`ofEnv2` of the environment the lowering extends.

- `group_opds`: a grouping's placements hold exactly its operands
  (`GroupPl`'s `grp_opds`);
- `GrpOk.toL`; `sevalAt_ofEnv2L`, `sevalAt_ofEnv2_one`: an atom's symbolic
  placements at `ofEnv2` under `GrpL` (`GroupPl`'s `sevalAt_ofEnv2G`,
  `sevalAt_ofEnv2G_one`, under these names too);
- `envFr_sFr`: the lowering's freshness (`Fresh`) as the edges' freshness of
  the symbolic environment's operands, at any `regName y k`, `k ≥ n`
  (`GroupPl`'s `fresh_ofEnv2` is its `regName x n`);
- `NJB.compat`: an atom's type is compatible with its walk layout;
- `NJB.pure_move2` (`pureOp`: atom, `nameI`, `pack`, pair, `asLanes`),
  `NJB.split_move2`, `NJB.unpack_move2`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl grp group)
open Scc.Lower (Env LitV litAt opLit pairOk csAfter bufsAfter unbuf)
open Scc.Lower.Inv (atomV)
open Spike.Lib.LowerShape (pureOp)

/-! ## Groupings hold their operands -/

/-- **A grouping's placements hold exactly its operands** (`grp_opds`). -/
theorem group_opds {t : Ty} {os : List Operand} {pls : List WordPl} (h : group t os = some pls) :
    pls.flatMap WordPl.opds = os := by
  have hg : grp t os = some (pls, []) := by
    simp only [group] at h
    split at h
    · rename_i pls' hg; simp only [Option.some.injEq] at h; subst h; exact hg
    · simp at h
  simpa using grp_opds t os pls [] hg

/-! ## Atoms at `ofEnv2` -/

theorem GrpOk.toL {env : Env} (h : GrpOk env) : GrpL env :=
  fun _ b hb => h b (List.mem_of_find?_eq_some hb)

/-- **An atom's symbolic placements group its operands** (`sevalAt_ofEnv2`
under `GrpL`). -/
theorem sevalAt_ofEnv2L {env : Env} (hg : GrpL env) {a : At} {t : Ty} {ws : List Operand}
    (h : atomV env a = some (t, ws)) : ∃ pls, group t ws = some pls ∧ sevalAt (ofEnv2 env) a = some (t, pls) :=
  sevalAt_ofEnv2G hg h

/-- **A one-operand atom is one word at `ofEnv2`.** -/
theorem sevalAt_ofEnv2_one {env : Env} (hg : GrpL env) {a : At} {t : Ty} {o : Operand}
    (h : atomV env a = some (t, [o])) : sevalAt (ofEnv2 env) a = some (t, [.one o]) :=
  sevalAt_ofEnv2G_one hg h

/-- **The lowering's freshness at `ofEnv2`**: no placed operand of the
symbolic environment is a register `regName y k`, `k ≥ n` (the edges'
`hfr` at `d := regName x n`). -/
theorem envFr_sFr {env : Env} {n : Nat} (h : Fresh env n) :
    ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → ∀ y k, n ≤ k →
      r ≠ Scc.Lower.Inv.regName y k := by
  intro q hq pl hpl o ho r hr
  simp only [ofEnv2, List.mem_map] at hq
  obtain ⟨b, hb, rfl⟩ := hq
  refine h b hb o ?_ r hr
  cases hgr : group b.2.1 b.2.2 with
  | none => simp [hgr] at hpl
  | some pls =>
    simp only [hgr, Option.getD_some] at hpl
    rw [← group_opds hgr]
    exact List.mem_flatMap.2 ⟨pl, hpl, ho⟩

/-! ## The moves -/

section Moves

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
  {lits : List (String × LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
  {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {B : Nat}

/-- **An atom of the walk's scope has a type compatible with its layout.** -/
theorem NJB.compat {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl}
    (h : NJB p lbl rs lits cs bufs L sm lsize B t s sl c) {a : At} {ta : Ty} {pls : List WordPl}
    (ha : sevalAt s a = some (ta, pls)) (hsc : InLits lits a) : Compat ta (litAt lits a) = true := by
  obtain ⟨c1, -, hj, hn, -⟩ := h
  obtain ⟨t1, ws, he, hE, -⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  rw [← compat_of_eraseLen hE]
  exact (hn.evalAt hsc ha he).1

/-- **A `let` without code** (`pureOp`) at `ofEnv2`: the node at its
continuation at `ofEnv2` of the environment the lowering extends. -/
theorem NJB.pure_move2 {pp : Prog} {x : String} {op : Op} {e : Expr} {env : Env} {sl : Int → BitVec 64}
    {c : Ctl} {t : Ty} {ws : List Operand}
    (h : NJB p lbl rs lits cs bufs L sm lsize B (.let_ x op e) (ofEnv2 env) sl c)
    (hp : pureOp env op = some (t, ws)) (hg : GrpL env) (hL : LitPt (.let_ x op e, lits))
    (hpo : pairOk cs bufs lits op = true)
    (hbn : ∀ y n, (∃ b, op = .pair (.var y) b) → bufs.lookup y = some n → n < 2 ^ 28) :
    NJB p lbl rs ((x, opLit pp lits op) :: lits) (csAfter x cs op) (bufsAfter x cs bufs op) L sm lsize B e
      (ofEnv2 ((x, t, ws) :: env)) sl c := by
  have hin : ∀ a ∈ headAtoms (.let_ x op e), InLits lits a := hL.1
  cases op with
  | atom a =>
    obtain ⟨pls, hgr, hs⟩ := sevalAt_ofEnv2L hg hp
    rw [ofEnv2_cons hgr]
    exact NJB.atom h hs (hin a (by simp [headAtoms]))
  | nameI a =>
    obtain ⟨pls, hgr, hs⟩ := sevalAt_ofEnv2L hg hp
    rw [ofEnv2_cons hgr]
    exact NJB.nameI h hs (hin a (by simp [headAtoms]))
  | pack a w τ =>
    simp only [pureOp, Option.map_eq_some_iff] at hp
    obtain ⟨⟨ta, wa⟩, ha, hv⟩ := hp
    simp only [Prod.mk.injEq] at hv
    obtain ⟨ht, hw⟩ := hv
    subst ht
    subst hw
    obtain ⟨pls, hgr, hs⟩ := sevalAt_ofEnv2L hg ha
    have hsc := hin a (by simp [headAtoms])
    have hτ := hL.2.1 x a w τ e rfl
    have hgt : group τ wa = some pls := by
      rw [group_grpL hτ, ← group_grpL (NJB.compat h hs hsc), hgr]
    rw [ofEnv2_cons hgt]
    exact NJB.pack h hs hsc hτ
  | pair a b =>
    simp only [pureOp] at hp
    cases ha : atomV env a with
    | none => simp [ha] at hp
    | some va =>
      obtain ⟨ta, wa⟩ := va
      cases hb : atomV env b with
      | none => simp [ha, hb] at hp
      | some vb =>
        obtain ⟨tb, wb⟩ := vb
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨pa, hga, hsa⟩ := sevalAt_ofEnv2L hg ha
        obtain ⟨pb, hgb, hsb⟩ := sevalAt_ofEnv2L hg hb
        rw [ofEnv2_cons (group_pair hga hgb)]
        exact NJB.pair h hsa hsb (group_grp hga).2.1 (hin a (by simp [headAtoms])) (hin b (by simp [headAtoms]))
          hpo (fun y n hy hl => hbn y n ⟨b, by rw [hy]⟩ hl)
  | asLanes sg w a =>
    simp only [pureOp] at hp
    cases ha : atomV env a with
    | none => simp [ha] at hp
    | some va =>
      obtain ⟨ta, wa⟩ := va
      simp only [ha, Option.bind_eq_bind, Option.bind_some] at hp
      match wa, hp, ha with
      | [o], hp, ha =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have hs := sevalAt_ofEnv2_one hg ha
        obtain ⟨lo, hlo⟩ := hL.2.2.1 x sg w a e rfl
        have hp' : group (.lanes sg w) [o] = some [.one o] := rfl
        rw [ofEnv2_cons hp']
        exact NJB.asLanesV h hs (hin a (by simp [headAtoms])) (by rw [hlo]; rfl)
      | [], hp, _ => simp at hp
      | _ :: _ :: _, hp, _ => simp at hp
  | _ => simp [pureOp] at hp

/-- **A `split`** at `ofEnv2`: the walk's layout at `a` is a pair's
(`Compat` of the product), its parts bound to `a`'s first `nu` words and the
rest. -/
theorem NJB.split_move2 {a : At} {x y : String} {e : Expr} {env : Env} {n : Nat} {sl : Int → BitVec 64}
    {c : Ctl} {t u w : Ty} {ws : List Operand} {nu : Nat}
    (h : NJB p lbl rs lits cs bufs L sm lsize B (.split a x y e) (ofEnv2 env) sl c)
    (ha : atomV env a = some (t, ws)) (hpr : Scc.Lower.prodOf t = some (u, w))
    (hn : Scc.Obj.valWords u = some nu) (hg : GrpL env) (hT : EnvTy2 (.split a x y e, env, n))
    (hL : LitPt (.split a x y e, lits)) :
    NJB p lbl rs
      (match litAt lits a with
        | .node l r => (y, r) :: (x, l) :: lits
        | _ => (y, .leaf none) :: (x, .leaf none) :: lits)
      (unbuf y (unbuf x cs)) (unbuf y (unbuf x bufs)) L sm lsize B e
      (ofEnv2 ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env)) sl c := by
  have hty : Scc.Lower.simpleTy t = true ∧ Scc.Lower.noRefProd t = true := by
    cases a with
    | var z =>
      simp only [atomV, Option.map_eq_some_iff] at ha
      obtain ⟨⟨z', t', ws'⟩, hb, hbe⟩ := ha
      simp only [Prod.mk.injEq] at hbe
      obtain ⟨rfl, rfl⟩ := hbe
      have := hT _ (List.mem_of_find?_eq_some hb)
      exact ⟨this.1, this.2.2⟩
    | lit k =>
      simp only [atomV] at ha
      split at ha
      · cases ha
      · simp only [Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        simp [Scc.Lower.prodOf] at hpr
    | unit =>
      simp only [atomV, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      simp [Scc.Lower.prodOf] at hpr
  have ht := prodOf_noRefProd hty.2 hpr
  subst ht
  have hsu : Scc.Lower.simpleTy u = true := by
    have := hty.1
    simp only [Scc.Lower.simpleTy, Bool.and_eq_true] at this
    exact this.1
  obtain ⟨pls, hgr, hs⟩ := sevalAt_ofEnv2L hg ha
  obtain ⟨pu, pw, hpu, hgu, hgw, rfl⟩ := group_split hgr hn
  have hacc := accsPl_of_valWords hsu hn
  obtain ⟨us, hus⟩ : ∃ us, TermRun.accs u = some us := by
    simp only [accsPl] at hacc
    cases h' : TermRun.accs u with
    | none => rw [h', hpu] at hacc; simp at hacc
    | some us => exact ⟨us, rfl⟩
  have hk := accs_plLen hacc hus
  have hlen : TermRun.nWords us = pu.length := by
    rw [hpu] at hk; exact (Option.some.inj hk).symm
  have hsc := hL.1 a (by simp [headAtoms])
  have hc := NJB.compat h hs hsc
  obtain ⟨l, r, hl⟩ : ∃ l r, litAt lits a = .node l r := by
    revert hc
    cases litAt lits a <;> simp [Compat]
  have hj := NJB.split h hs hus hk hsc hl
  rw [hlen, List.take_left', List.drop_left'] at hj
  · simp only [hl]
    rw [ofEnv2_cons hgw, ofEnv2_cons hgu]
    exact hj
  all_goals rfl

/-- **An index unpack** at `ofEnv2`: `x` bound to the package's words. -/
theorem NJB.unpack_move2 {a : At} {i x : String} {e : Expr} {env : Env} {sl : Int → BitVec 64} {c : Ctl}
    {b : Ty} {ws : List Operand}
    (h : NJB p lbl rs lits cs bufs L sm lsize B (.unpack a i x e) (ofEnv2 env) sl c)
    (ha : atomV env a = some (.iex b, ws)) (hg : GrpL env) (hL : LitPt (.unpack a i x e, lits)) :
    NJB p lbl rs ((x, litAt lits a) :: lits) (unbuf x (unbuf i cs)) (unbuf x (unbuf i bufs)) L sm lsize B e
      (ofEnv2 ((x, b, ws) :: env)) sl c := by
  obtain ⟨pls, hgr, hs⟩ := sevalAt_ofEnv2L hg ha
  rw [ofEnv2_cons (group_iex hgr)]
  exact NJB.unpack h hs (hL.1 a (by simp [headAtoms]))

end Moves

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.envFr_sFr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms envFr_sFr

/-- info: 'Spike.Lib.LowerNode.sevalAt_ofEnv2_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sevalAt_ofEnv2_one

/-- info: 'Spike.Lib.LowerNode.NJB.pure_move2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.pure_move2

/-- info: 'Spike.Lib.LowerNode.NJB.split_move2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.split_move2

/-- info: 'Spike.Lib.LowerNode.NJB.unpack_move2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.unpack_move2

end Spike.Lib.LowerNode
