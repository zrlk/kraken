import Spike.Lib.Src.NJLW
import Spike.Lib.Src.HeapBuf
import Spike.Lib.Src.LowerMarksImm2
import Spike.Lib.Src.ExternUnit
import Scc.Lower.Program

/-!
**An exchange the lowering accepts stores a one-word leaf** (ISA-neutral):
at every point of the source walk (`litWalk2`) of a block whose lowering
succeeds, an `xchgAt`'s stored atom is at a `.leaf` of the walk
(`litMask … = [true]`). `Accepted2` alone does not give it (`xchgAt b[0] b`
stores a locative); the lowering refuses a value of more than one word
(`post_xchgAt_leaf`).

- `xchgLeafQ`: the fact at one point;
- `lowerExpr_xchgLeaf`: along a successful `lowerExpr`, against the walk's
  invariants (`Rel`, `body2`, `BufInv`, `TyOK`, as `walk_rel`);
- `lowerDeclMarks_xchgLeaf`: every point of a block of an `Accepted2`
  program whose `lowerDeclMarks` succeeds (the extern and its loop have no
  exchange: `xchgLeaf_printExt`, `xchgLeaf_printLoop`);
- `xchgLeaf_of_lowerWithMarks`: every point of `litWalks2 p` when the whole
  program's lowering succeeds (the frontend compiles every block but the
  extern and its loop: `compiled_of_accepted2`).

Each of the three is an instance of a generic statement for any fact `Q`
the lowering gives at every `let` (`LetQ`) and that holds at every other
point (`OtherQ`): `lowerExpr_walkQ`, `lowerDeclMarks_walkQ`,
`walkQ_of_lowerWithMarks`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (B BState Env LitV litAt lowerOp lowerExpr Cx2 body2 litWalk2 litWalks2 setHere params2 shapeOf)

/-- **An exchange's stored atom is at a leaf** of the walk's literal words. -/
def xchgLeafQ (q : Expr × List (String × LitV)) : Bool :=
  match q.1 with
  | .let_ _ (.xchgAt _ _ v) _ => litMask (litAt q.2 v) == [true]
  | _ => true

/-- **A fact at every `let` the lowering gives**: from the walk's invariants
at a `let`, every successful lowering of its operation yields `Q` there. -/
def LetQ (cx : Scc.Lower.Ctx) (Q : Expr × List (String × LitV) → Bool) : Prop :=
  ∀ (cx2 : Cx2) (cs bufs : List (String × Nat)) (scope : List String) (env : Env) (lits : List (String × LitV))
    (x : String) (op : Op) (e : Expr), body2 cx2 cs bufs scope (.let_ x op e) = true → Rel env lits scope →
    BufInv env bufs → Post (lowerOp cx env x op) fun _ => Q (.let_ x op e, lits) = true

/-- **A fact that holds at every point but a `let`.** -/
def OtherQ (Q : Expr × List (String × LitV) → Bool) : Prop :=
  ∀ q : Expr × List (String × LitV), (∀ x op e, q.1 ≠ .let_ x op e) → Q q = true

/-- **Along a successful lowering of a body**, from the walk's invariants at
its start, every point of the source walk has `Q`, a fact the lowering gives
at every `let` (`LetQ`) and that holds elsewhere (`OtherQ`). -/
theorem lowerExpr_walkQ {Q : Expr × List (String × LitV) → Bool} {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p)
    (hret : ∀ d ∈ p, Scc.Lower.noRefProd d.retTy = true) (hlet : LetQ cx Q) (hoth : OtherQ Q) (cx2 : Cx2)
    (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String) (env : Env) (lits : List (String × LitV))
      (s s' : BState),
      body2 cx2 cs bufs scope e = true → Rel env lits scope → BufInv env bufs → TyOK env →
      (∀ q ∈ litWalk2 p lits e, layQ q = true ∧ refQ q = true) →
      lowerExpr cx env e s = .ok ((), s') → ∀ q ∈ litWalk2 p lits e, Q q = true := by
  induction e with
  | let_ x op e ih =>
    intro cs bufs scope env lits s s' hb hR hB hT hL hr
    have h0 : setHere (env, Expr.let_ x op e) s = .ok ((), { s with here := some (env, .let_ x op e) }) := rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    obtain ⟨⟨t, ws⟩, s2, h1, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    have hL0 := hL _ (by rw [litWalk2]; exact List.mem_cons_self ..)
    have hhead := hlet cx2 cs bufs scope env lits x op e hb hR hB _ _ _ h1
    obtain ⟨cs', bufs', hb', hop⟩ := let_step hcx hb hR hB hL0.1
    have hQ := hop _ _ _ h1
    have hty := post_lowerOp_ty hcx hret hb hT hB hL0.2 _ _ _ h1
    have cont : ∀ s3 : BState,
        (Scc.Lower.markWords t ws >>= fun _ => lowerExpr cx ((x, t, ws) :: env) e) s3 = .ok ((), s') →
        ∀ q ∈ litWalk2 p lits (.let_ x op e), Q q = true := by
      intro s3 hr3
      obtain ⟨_, s4, -, hr4⟩ := bind_ok_inv hr3
      intro q hq
      rw [litWalk2, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hhead
      · exact ih cs' bufs' (x :: scope) _ _ s4 s' hb' (hR.cons hQ.1) hQ.2 (hT.cons hty)
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) hr4 q hq
    cases op
    all_goals first
      | exact cont s2 hr
      | skip
    dsimp only at hr
    split at hr
    · obtain ⟨d, s3, hg, hr⟩ := bind_ok_inv hr
      cases hg
      revert hr
      generalize Array.back? _ = o
      rcases o with _ | ⟨_ | _, _⟩ <;> intro hr
      · exact cont s2 hr
      · exact cont s2 hr
      · obtain ⟨_, s3, -, hr⟩ := bind_ok_inv hr
        exact cont s3 hr
    · exact cont s2 hr
  | split a x y e ih =>
    intro cs bufs scope env lits s s' hb hR hB hT hL hr
    have h0 : setHere (env, Expr.split a x y e) s = .ok ((), { s with here := some (env, .split a x y e) }) := rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    obtain ⟨⟨t, ws⟩, s2, h2, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    obtain ⟨⟨u, w⟩, s3, h3, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    obtain ⟨k, s4, h4, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    have hl : splitStep env a { s with here := some (env, .split a x y e) } = .ok ((u, w, ws, k), s4) := by
      unfold splitStep
      exact (Scc.Lower.Inv.bind_ok h2).trans ((Scc.Lower.Inv.bind_ok h3).trans
        ((Scc.Lower.Inv.bind_ok h4).trans rfl))
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨l, rr, hla, h1, h2'⟩ := post_splitStep hR (atom1_var hb.1) _ _ _ hl
    obtain ⟨-, hu, hw⟩ := post_splitStep_ty hT a _ _ _ hl
    have hlw : litWalk2 p lits (.split a x y e) =
        (.split a x y e, lits) :: litWalk2 p ((y, rr) :: (x, l) :: lits) e := by
      rw [litWalk2, hla]
    intro q hq
    rw [hlw, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hoth _ fun _ _ _ h => by cases h
    · exact ih _ _ (y :: x :: scope) _ _ s4 s' hb.2 ((hR.cons h1).cons h2') ((hB.cons x _ _).cons y _ _)
        ((hT.cons hu).cons hw) (fun q hq => hL q (by rw [hlw]; exact List.mem_cons_of_mem _ hq)) hr q hq
  | unpack a i x e ih =>
    intro cs bufs scope env lits s s' hb hR hB hT hL hr
    have h0 : setHere (env, Expr.unpack a i x e) s = .ok ((), { s with here := some (env, .unpack a i x e) }) :=
      rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    obtain ⟨⟨t, ws⟩, s2, h2, hr⟩ := bind_ok_inv hr
    try dsimp only at hr
    simp only [body2, Bool.and_eq_true] at hb
    have hI := post_evalAt hR (atom1_var hb.1) _ _ _ h2
    have hty := post_evalAt_ty hT a _ _ _ h2
    split at hr
    · subst_vars
      have hI' : Inv _ _ (litAt lits a) := ⟨by
        have := hI.1; simp only [Compat, Bool.and_eq_true] at this; exact this.2, hI.2⟩
      intro q hq
      rw [litWalk2, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hoth _ fun _ _ _ h => by cases h
      · exact ih _ _ (x :: scope) _ _ s2 s' hb.2 (hR.cons hI') ((hB.sub i).cons x _ _) (hT.cons (noRefProd_iex hty))
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) hr q hq
    · cases hr
  | ifeq a b yes no ihy ihn =>
    intro cs bufs scope env lits s s' hb hR hB hT hL hr
    have h0 : setHere (env, Expr.ifeq a b yes no) s =
        .ok ((), { s with here := some (env, .ifeq a b yes no) }) := rfl
    rw [lowerExpr, Scc.Lower.Inv.bind_ok h0] at hr
    obtain ⟨_, s2, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s3, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s4, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s5, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s6, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s7, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s8, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s9, h9, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s10, -, hr⟩ := bind_ok_inv hr
    obtain ⟨_, s11, -, hr⟩ := bind_ok_inv hr
    simp only [body2, Bool.and_eq_true] at hb
    intro q hq
    rw [litWalk2, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact hoth _ fun _ _ _ h => by cases h
    · exact ihy _ _ _ _ _ s8 s9 hb.1.2 hR hB hT
        (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq))) h9 q hq
    · exact ihn _ _ _ _ _ s11 s' hb.2 hR hB hT
        (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq))) hr q hq
  | _ =>
    intro cs bufs scope env lits s s' hb _ _ _ _ _ q hq
    first
      | (simp [body2] at hb; done)
      | (simp only [litWalk2, List.mem_singleton] at hq; subst hq; exact hoth _ fun _ _ _ h => by cases h)

/-- **The lowering stores a one-word leaf at every exchange** (`post_xchgAt_leaf`). -/
theorem letQ_xchgLeaf (cx : Scc.Lower.Ctx) : LetQ cx xchgLeafQ := by
  intro cx2 cs bufs scope env lits x op e hb hR hB
  cases op with
  | xchgAt b i v =>
    rcases b with b | b | _ <;> rcases i with i | i | _ <;> try (simp [body2] at hb; done)
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨_, hk⟩, hv⟩, _⟩ := hb
    split at hk
    · rename_i k hbk
      obtain ⟨e0, τ, he0, ht0, hτ⟩ := hB b k hbk
      exact Post.mono (post_xchgAt_leaf cx hR x b i hv he0 ht0 hτ) fun _ h => by simp [xchgLeafQ, h]
    · cases hk
  | _ => exact fun _ _ _ _ => rfl

theorem otherQ_xchgLeaf : OtherQ xchgLeafQ := by
  intro ⟨e, lits⟩ h
  unfold xchgLeafQ
  split
  · rename_i heq; exact absurd heq (h _ _ _)
  · rfl

/-- **Along a successful lowering of a body**, from the walk's invariants at
its start, every point of the source walk has `xchgLeafQ`. -/
theorem lowerExpr_xchgLeaf {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p)
    (hret : ∀ d ∈ p, Scc.Lower.noRefProd d.retTy = true) (cx2 : Cx2) (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String) (env : Env) (lits : List (String × LitV))
      (s s' : BState),
      body2 cx2 cs bufs scope e = true → Rel env lits scope → BufInv env bufs → TyOK env →
      (∀ q ∈ litWalk2 p lits e, layQ q = true ∧ refQ q = true) →
      lowerExpr cx env e s = .ok ((), s') → ∀ q ∈ litWalk2 p lits e, xchgLeafQ q = true :=
  lowerExpr_walkQ hcx hret (letQ_xchgLeaf cx) otherQ_xchgLeaf cx2 e

theorem xchgLeaf_printExt {p : Prog} :
    ∀ q ∈ litWalk2 p ((params2 Scc.Frontend.printExtD).map (·, shapeOf Scc.Frontend.printExtD.argTy))
      Scc.Frontend.printExtD.body, xchgLeafQ q = true := by
  exact List.all_eq_true.1 rfl

theorem xchgLeaf_printLoop {p : Prog} :
    ∀ q ∈ litWalk2 p ((params2 Scc.Frontend.printLoopD).map (·, shapeOf Scc.Frontend.printLoopD.argTy))
      Scc.Frontend.printLoopD.body, xchgLeafQ q = true := by
  exact List.all_eq_true.1 rfl

/-- **Along a successful `lowerDeclMarks` of a compiled block** of an
`Accepted2` program (not the extern and its loop), every point of the
block's source walk has `Q` (`lowerExpr_walkQ`). -/
theorem lowerDeclMarks_walkQ {Q : Expr × List (String × LitV) → Bool} (hlet : ∀ cx, LetQ cx Q)
    (hoth : OtherQ Q) {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {externs : List (String × Scc.Frontend.Extern)}
    (hext : ∀ d ∈ p, (externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {obj : Scc.ObjLayout} {frames : Option Nat} {f : Func} {marks : Array (Scc.Lower.Node × Scc.Lower.Point)}
    (h : Scc.Lower.lowerDeclMarks p externs d obj frames = .ok (f, marks)) :
    ∀ q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body, Q q = true := by
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hds⟩, hsp⟩, -⟩, hlay⟩, href⟩, -⟩, -⟩, -⟩ := hp
  obtain ⟨hsig, hpk⟩ := refOk2_parts href
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  obtain ⟨cx2, hb, harg⟩ := body_decl2 hE hne hnl (setup_simple hds hsp)
  have hcx : CxOK { prog := p, externs, fn := d.name, obj, frames } p := ⟨rfl, fun d' hd' => by
    obtain ⟨E, hE⟩ := decl2_of_decls2 hds d' hd'
    exact retTy_decl2 hE, hext⟩
  unfold Scc.Lower.lowerDeclMarks at h
  rcases hv : Scc.Obj.valWords d.argTy with _ | n <;> simp only [hv] at h
  · cases h
  have key : ∀ name cs, Scc.Lower.buildFuncMarks name ((List.range n).map fun k => s!"{d.arg}.{k}") cs (do
      Scc.Lower.markWords d.argTy (((List.range n).map fun k => s!"{d.arg}.{k}").map .reg)
      Scc.Lower.markAt (.block "entry")
        ([(d.arg, d.argTy, ((List.range n).map fun k => s!"{d.arg}.{k}").map .reg)], d.body)
      lowerExpr { prog := p, externs, fn := d.name, obj, frames }
        [(d.arg, d.argTy, ((List.range n).map fun k => s!"{d.arg}.{k}").map .reg)] d.body) = .ok (f, marks) →
      ∀ q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body, Q q = true := by
    intro name cs hbf
    obtain ⟨s', hs', -⟩ := buildFuncMarks_ok hbf
    obtain ⟨_, s1, -, hs'⟩ := bind_ok_inv hs'
    obtain ⟨_, s2, -, hs'⟩ := bind_ok_inv hs'
    have hps : ∀ o ∈ ((List.range n).map fun k => s!"{d.arg}.{k}").map Operand.reg, IsReg o := fun o ho => by
      simp only [List.mem_map] at ho; obtain ⟨r, -, rfl⟩ := ho; exact ⟨r, rfl⟩
    exact lowerExpr_walkQ hcx (fun d hd => (hsig d hd).2) (hlet _) hoth cx2 d.body [] [] _ _ _ s2 s' hb
      (rel_entry harg hps (by simp [hv])) (fun b k h => by cases h)
      (TyOK.cons (fun _ h => by cases h) (hsig d hd).1)
      (fun q hq => ⟨List.all_eq_true.mp hlay q (List.mem_flatMap.2 ⟨d, hd, hq⟩),
        hpk q (List.mem_flatMap.2 ⟨d, hd, hq⟩)⟩) hs'
  simp only [pure, Except.pure, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · exact key _ _ h
    · cases h

/-- **Along a successful `lowerDeclMarks` of a compiled block** of an
`Accepted2` program (not the extern and its loop), every point of the
block's source walk has `xchgLeafQ`. -/
theorem lowerDeclMarks_xchgLeaf {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {externs : List (String × Scc.Frontend.Extern)}
    (hext : ∀ d ∈ p, (externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {obj : Scc.ObjLayout} {frames : Option Nat} {f : Func} {marks : Array (Scc.Lower.Node × Scc.Lower.Point)}
    (h : Scc.Lower.lowerDeclMarks p externs d obj frames = .ok (f, marks)) :
    ∀ q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body, xchgLeafQ q = true :=
  lowerDeclMarks_walkQ letQ_xchgLeaf otherQ_xchgLeaf hp hext hd hne hnl h

/-- **A compiled block of `decl2` is no extern** (`externOf`): `main` and the
setup block by name, the plain blocks by their `Int` result. -/
theorem externOf_none_of_decl2 {E : List String} {s : Option Ty} {x : Bool} {d : Decl}
    (h : Scc.Lower.decl2 E s x d = true) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(x = true ∧ d.name = "printL")) : Scc.Frontend.externOf d = none := by
  have hx : (x && d.name == "printL") = false := by cases x <;> simp_all
  unfold Scc.Lower.decl2 at h
  simp only [hne, hx, Bool.false_eq_true, ↓reduceIte] at h
  have hpl : ∀ {E excl : List String}, Scc.Lower.plain2 E excl x d = true → Scc.Frontend.externOf d = none := by
    intro E excl h
    simp only [Scc.Lower.plain2, Bool.and_eq_true, beq_iff_eq] at h
    have hdl : Scc.Frontend.declIs d Scc.Frontend.printLoopD = false := by
      cases hdi : Scc.Frontend.declIs d Scc.Frontend.printLoopD
      · rfl
      · have hr := congrArg Decl.retTy (Scc.Frontend.declIs_eq hdi)
        rw [h.1.1.2] at hr; simp [Scc.Frontend.printLoopD] at hr
    have hdp : Scc.Frontend.declIs d Scc.Frontend.printLoopPubD = false := by
      cases hdi : Scc.Frontend.declIs d Scc.Frontend.printLoopPubD
      · rfl
      · have hr := congrArg Decl.retTy (Scc.Frontend.declIs_eq hdi)
        rw [h.1.1.2] at hr; simp [Scc.Frontend.printLoopPubD] at hr
    unfold Scc.Frontend.externOf
    simp [h.1.1.2, hdl, hdp]
  split at h
  · rename_i hm
    simp only [beq_iff_eq] at hm
    unfold Scc.Frontend.externOf
    simp [hm]
  · split at h
    · split at h
      · rename_i hr
        simp only [beq_iff_eq] at hr
        unfold Scc.Frontend.externOf
        simp [hr]
      · exact hpl h
    · exact hpl h

/-- **The frontend compiles every block of an `Accepted2` program but the
extern and its loop** (none is among `Frontend.externs`). -/
theorem compiled_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hne : Scc.Lower.isPrintExt d = false) (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) :
    ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by
  have hn := nodup_of_accepted2 hp
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp
  obtain ⟨E, hE⟩ := decl2_of_decls2 hp.1.1.1.1.1.1.1.2 d hd
  have h0 := externOf_none_of_decl2 hE hne hnl
  rcases hc : (Scc.Frontend.externs p).any (·.1 == d.name) with _ | _
  · rfl
  · exfalso
    obtain ⟨y, hy, hyn⟩ := List.any_eq_true.1 hc
    unfold Scc.Frontend.externs at hy
    obtain ⟨d', hd', he⟩ := List.mem_filterMap.1 hy
    obtain ⟨e, he', rfl⟩ := Option.map_eq_some_iff.1 he
    have : d' = d := eq_of_name_nodup hn hd' hd (by simpa using hyn)
    subst this
    rw [h0] at he'
    cases he'

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ x ∈ l, ∃ y, f x = .ok y
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, r, h, x, hx => by
    rcases ha : f a with e | y
    · simp [List.mapM_cons, ha, bind, Except.bind] at h
    · rcases hl : l.mapM f with e | ys
      · simp [List.mapM_cons, ha, hl, bind, Except.bind] at h
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨y, ha⟩
        · exact mapM_ok_mem hl x hx

/-- **Every point of an `Accepted2` program's walk has `Q`** when its
lowering succeeds (`lowerWithMarks`, the frontend's externs), `Q` a fact
the lowering gives (`LetQ`, `OtherQ`) that holds along the extern and its
loop. -/
theorem walkQ_of_lowerWithMarks {Q : Expr × List (String × LitV) → Bool} {p : Prog} (hlet : ∀ cx, LetQ cx Q)
    (hoth : OtherQ Q)
    (hpe : ∀ q ∈ litWalk2 p ((params2 Scc.Frontend.printExtD).map (·, shapeOf Scc.Frontend.printExtD.argTy))
      Scc.Frontend.printExtD.body, Q q = true)
    (hpl : ∀ q ∈ litWalk2 p ((params2 Scc.Frontend.printLoopD).map (·, shapeOf Scc.Frontend.printLoopD.argTy))
      Scc.Frontend.printLoopD.body, Q q = true) (hp : Scc.Lower.Accepted2 p = true) {cfg : Scc.Config}
    {c : Scc.Frontend.Checked} (hcp : c.prog = p) (hce : c.externs = Scc.Frontend.externs p)
    {x : Program × List (Sym × Array (Scc.Lower.Node × Scc.Lower.Point))}
    (h : Scc.Lower.lowerWithMarks cfg c = .ok x) : ∀ q ∈ litWalks2 p, Q q = true := by
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  unfold Scc.Lower.lowerWithMarks at h
  rw [hcp, hce] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i um hum
  intro q hq
  obtain ⟨d, hd, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  have hE' := hE
  unfold Scc.Lower.decl2 at hE'
  cases hne : Scc.Lower.isPrintExt d
  · by_cases hnl : Scc.Lower.hasPrint p = true ∧ d.name = "printL"
    · simp only [hne, hnl.1, hnl.2, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Bool.and_self] at hE'
      have := Scc.Frontend.declIs_eq hE'
      subst this
      exact hpl q hq
    · have hc := compiled_of_accepted2 hp hd hne hnl
      obtain ⟨⟨f, ms⟩, hl⟩ := mapM_ok_mem hum d (List.mem_filter.2 ⟨hd, by simp only [hc]; rfl⟩)
      exact lowerDeclMarks_walkQ hlet hoth hp (externs_unit (nodup_of_accepted2 hp)) hd hne hnl hl q hq
  · simp only [hne, ↓reduceIte, Bool.and_eq_true] at hE'
    have := Scc.Frontend.declIs_eq hE'.1
    subst this
    exact hpe q hq

/-- **Every point of an `Accepted2` program's walk has `xchgLeafQ`** when
its lowering succeeds (`lowerWithMarks`, the frontend's externs). -/
theorem xchgLeaf_of_lowerWithMarks {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cfg : Scc.Config}
    {c : Scc.Frontend.Checked} (hcp : c.prog = p) (hce : c.externs = Scc.Frontend.externs p)
    {x : Program × List (Sym × Array (Scc.Lower.Node × Scc.Lower.Point))}
    (h : Scc.Lower.lowerWithMarks cfg c = .ok x) : ∀ q ∈ litWalks2 p, xchgLeafQ q = true :=
  walkQ_of_lowerWithMarks letQ_xchgLeaf otherQ_xchgLeaf xchgLeaf_printExt xchgLeaf_printLoop hp hcp hce h

end Spike.Lib.LowerNode
