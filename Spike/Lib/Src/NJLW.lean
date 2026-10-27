import Spike.Lib.Src.NJL
import Spike.Lib.Src.SstepLet

/-!
**`NJL`'s premises from the walk** (ISA-neutral). At every point of the
lowering's walk (`lowerEnvs2`) of an `Accepted2` body there is the source
walk's point (`litWalk2`) with literal words `lits` that

- the lowering's environment agrees with, every variable of the point's
  scope bound (`Rel`), so that every atom the body reads is `InLits`;
- the body is still `body2` (its atoms in scope) with buffers (`BufInv`);
- every binding's type has no refined product (`TyOK`), from `refOk2`: so
  the lowering's split (`prodOf`) is on a literal product.

`walk_rel` gives these. From them, per construct: `inLits_of_atom1`; the
`if`/`+`/`-` operands at a leaf (`post_evalOne_leaf`); a `pack`'s type at its
operand's layout (`compat_pack_of_layQ`); the split's type a literal product
(`split_prod`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (B Env LitV litAt lowerOp evalAt evalOne Cx2 body2 litWalk2 litWalks2 layoutOk2 refOk2
  noRefProd prodOf words needSome atom1 retShape)
open Scc.Lower.Inv (atomV)
open Spike.Lib.Form (sevalAt)

/-! ## Types without refined products -/

/-- **Every binding's type has no refined product.** -/
def TyOK (env : Env) : Prop := ∀ b ∈ env, noRefProd b.2.1 = true

theorem TyOK.cons {env : Env} (h : TyOK env) {x : String} {t : Ty} {ws : List Operand}
    (ht : noRefProd t = true) : TyOK ((x, t, ws) :: env) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ht
  · exact h b hb

theorem post_evalAt_ty {env : Env} (h : TyOK env) (a : At) :
    Post (evalAt env a) fun r => noRefProd r.1 = true :=
  Post.mono (post_evalAtV env a) fun r hr => by
    cases a with
    | var x =>
      simp only [atomV, Option.map_eq_some_iff] at hr
      obtain ⟨⟨y, u, vs⟩, hb, rfl⟩ := hr
      exact h _ (List.mem_of_find?_eq_some hb)
    | lit n =>
      simp only [atomV] at hr
      split at hr
      · cases hr
      · cases hr; rfl
    | unit => cases hr; rfl

/-- **A pack point's type** has no refined product (`refOk2`). -/
def refQ (q : Expr × List (String × LitV)) : Bool :=
  match q.1 with
  | .let_ _ (.pack _ _ τ) _ => noRefProd τ
  | _ => true

/-- **The lowering of a `let` keeps `TyOK`**: its type is an atom's, a pair
of atoms', a package's (`refQ`), a callee's result (`hret`), a buffer's, an
element's, or a number's. -/
theorem post_lowerOp_ty {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p)
    (hret : ∀ d ∈ p, noRefProd d.retTy = true) {cx2 : Cx2} {cs bufs : List (String × Nat)}
    {scope : List String} {x : String} {op : Op} {e : Expr} {env : Env} {lits : List (String × LitV)}
    (hb : body2 cx2 cs bufs scope (.let_ x op e) = true) (hT : TyOK env) (hB : BufInv env bufs)
    (hq : refQ (.let_ x op e, lits) = true) :
    Post (lowerOp cx env x op) fun r => noRefProd r.1 = true := by
  cases op <;> try (simp [body2] at hb; done)
  case atom a => exact post_evalAt_ty hT a
  case nameI a => exact post_evalAt_ty hT a
  case add a b => exact Post.mono (post_add cx env x a b) fun r ⟨d, hd⟩ => by subst hd; rfl
  case sub a b => exact Post.mono (post_sub cx env x a b) fun r ⟨d, hd⟩ => by subst hd; rfl
  case pair a b =>
    simp only [lowerOp]
    refine Post.bind (post_evalAt_ty hT a) fun r1 h1 => Post.bind (post_evalAt_ty hT b) fun r2 h2 => ?_
    exact Post.pure (by simp [noRefProd, h1, h2])
  case pack a i τ =>
    simp only [refQ] at hq
    simp only [lowerOp]
    exact Post.bind' fun _ => Post.pure hq
  case asLanes sg w a =>
    simp only [lowerOp]
    exact Post.bind' fun _ => Post.pure rfl
  case call g is a ts =>
    simp only [lowerOp]
    refine Post.bind (post_needSome _ _) fun d hd => Post.bind' fun r => ?_
    refine Post.bind' fun k => Post.bind' fun rs => Post.pure ?_
    rw [hcx.prog] at hd
    exact hret d (List.mem_of_find?_eq_some hd)
  case newBuf n τ =>
    exact Post.mono (post_newBuf cx env x n τ) fun r ⟨q, hq⟩ => by
      subst hq; simp [bufTy, noRefProd, prodOf]
  case xchgAt b i v =>
    rcases b with b | b | _ <;> rcases i with i | i | _ <;> try (simp [body2] at hb; done)
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨_, hk⟩, _⟩, _⟩ := hb
    split at hk
    · rename_i k hbk
      obtain ⟨e0, τ, he0, ht0, hτ⟩ := hB b k hbk
      exact Post.mono (post_xchgAt cx x b i v he0 ht0 hτ) fun r ⟨h1, _, _⟩ => by
        rw [h1]; cases τ <;> simp [Scc.Lower.elem2] at hτ <;> rfl
    · cases hk

/-- **The lowering's split under `TyOK`**: the operand's type is the literal
product of the components it binds, each without a refined product. -/
theorem post_splitStep_ty {env : Env} (hT : TyOK env) (a : At) :
    Post (splitStep env a) fun r =>
      (∃ ws, atomV env a = some (.prod r.1 r.2.1, ws)) ∧ noRefProd r.1 = true ∧ noRefProd r.2.1 = true := by
  unfold splitStep
  refine Post.bind (Post.and (post_evalAtV env a) (post_evalAt_ty hT a)) fun r hr => ?_
  obtain ⟨t, ws⟩ := r
  dsimp only at hr ⊢
  refine Post.bind (post_needSome _ _) fun uw huw => ?_
  obtain ⟨u, w⟩ := uw
  dsimp only
  refine Post.bind' fun k => Post.pure ?_
  have he := eq_prod_of_noRefProd hr.2 huw
  subst he
  exact ⟨⟨ws, hr.1⟩, (noRefProd_prod hr.2).1, (noRefProd_prod hr.2).2⟩

/-! ## The walk -/

/-- **The lowering's walk against the source's, with scope, body, buffers
and types**: `walk_inv` keeping `Rel` (not only `RelE`), the body still
`body2` at the point, and `TyOK`. -/
theorem walk_rel {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p) (hret : ∀ d ∈ p, noRefProd d.retTy = true)
    (cx2 : Cx2) (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String) (env : Env) (lits : List (String × LitV)) (n : Nat),
      body2 cx2 cs bufs scope e = true → Rel env lits scope → BufInv env bufs → TyOK env →
      (∀ q ∈ litWalk2 p lits e, layQ q = true ∧ refQ q = true) →
      ∀ q ∈ lowerEnvs2 cx env n e, ∃ lits' cs' bufs' scope', (q.1, lits') ∈ litWalk2 p lits e ∧
        Rel q.2.1 lits' scope' ∧ body2 cx2 cs' bufs' scope' q.1 = true ∧ BufInv q.2.1 bufs' ∧ TyOK q.2.1 := by
  induction e
  case let_ x op e ih =>
    intro cs bufs scope env lits n hb hR hB hT hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT⟩
    · have hL0 := hL _ (by rw [litWalk2]; exact List.mem_cons_self ..)
      obtain ⟨cs', bufs', hb', hop⟩ := let_step hcx hb hR hB hL0.1
      have hty := post_lowerOp_ty hcx hret hb hT hB hL0.2
      split at hq
      · rename_i hr
        have hQ := post_runB (post_letStep (e := e) (Post.and hop hty)) hr
        obtain ⟨lits', c', b', s', h1, h2⟩ := ih cs' bufs' (x :: scope) _ _ _ hb' (hR.cons hQ.1.1) hQ.1.2
          (hT.cons hQ.2) (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ h1, h2⟩
      · simp at hq
  case split a x y e ih =>
    intro cs bufs scope env lits n hb hR hB hT hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT⟩
    · have hb0 := hb
      simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rename_i hr
        obtain ⟨l, rr, hla, h1, h2⟩ := post_runB (post_splitStep hR (atom1_var hb.1)) hr
        obtain ⟨-, hu, hw⟩ := post_runB (post_splitStep_ty hT a) hr
        have hlw : litWalk2 p lits (.split a x y e) =
            (.split a x y e, lits) :: litWalk2 p ((y, rr) :: (x, l) :: lits) e := by
          rw [litWalk2, hla]
        obtain ⟨lits', c', b', s', h1', h2'⟩ := ih _ _ (y :: x :: scope) _ _ _ hb.2 ((hR.cons h1).cons h2)
          ((hB.cons x _ _).cons y _ _) ((hT.cons hu).cons hw)
          (fun q hq => hL q (by rw [hlw]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', c', b', s', by rw [hlw]; exact List.mem_cons_of_mem _ h1', h2'⟩
      · simp at hq
  case unpack a i x e ih =>
    intro cs bufs scope env lits n hb hR hB hT hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT⟩
    · have hb0 := hb
      simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rename_i hr
        have hI := post_runB (post_evalAt hR (atom1_var hb.1)) hr
        have hty := post_runB (post_evalAt_ty hT a) hr
        have hI' : Inv _ _ (litAt lits a) := ⟨by
          have := hI.1; simp only [Compat, Bool.and_eq_true] at this; exact this.2, hI.2⟩
        obtain ⟨lits', c', b', s', h1, h2⟩ := ih _ _ (x :: scope) _ _ _ hb.2 (hR.cons hI') ((hB.sub i).cons x _ _)
          (hT.cons (noRefProd_iex hty)) (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ h1, h2⟩
      · simp at hq
  case ifeq a b yes no ihy ihn =>
    intro cs bufs scope env lits n hb hR hB hT hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT⟩
    · have hb0 := hb
      simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rw [List.mem_append] at hq
        rcases hq with hq | hq
        · obtain ⟨lits', c', b', s', h1, h2⟩ := ihy _ _ _ _ _ _ hb.1.2 hR hB hT
            (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq))) q hq
          exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h1), h2⟩
        · split at hq
          · obtain ⟨lits', c', b', s', h1, h2⟩ := ihn _ _ _ _ _ _ hb.2 hR hB hT
              (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq))) q hq
            exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ h1),
              h2⟩
          · simp at hq
      · simp at hq
  all_goals
    intro cs bufs scope env lits n hb hR hB hT hL q hq
    first
      | (simp [body2] at hb; done)
      | (simp only [lowerEnvs2, List.mem_singleton] at hq
         subst hq
         exact ⟨lits, cs, bufs, scope, by simp [litWalk2], hR, hb, hB, hT⟩)

/-! ## Per construct -/

/-- **An atom the body reads is in the walk's scope.** -/
theorem inLits_of_atom1 {env : Env} {lits : List (String × LitV)} {scope : List String} (hR : Rel env lits scope)
    {a : At} (ha : atom1 scope a = true) : InLits lits a :=
  fun x hx => hR.2 x (atom1_var ha x hx)

/-- **An operand the lowering reads as one word is at a leaf** (`if`, `+`, `-`). -/
theorem post_evalOne_leaf {env : Env} {lits : List (String × LitV)} {scope : List String} (hR : Rel env lits scope)
    {a : At} (ha : atom1 scope a = true) (what : String) :
    Post (evalOne env a what) fun _ => litMask (litAt lits a) = [true] :=
  Post.mono (post_evalOne hR (atom1_var ha) what) fun _ hw => litMask_of_agreeW hw

/-- **The split's operand is a literal product** in the symbolic environment
of the lowering's (`ofEnv2`): `NJL.split`'s `ha`. -/
theorem split_prod {env : Env} (hT : TyOK env) (hg : GrpOk env) {a : At} {r : Ty × Ty × List Operand × Nat}
    {n n' : Nat} (hr : runB (splitStep env a) n = some (r, n')) :
    ∃ pls, sevalAt (ofEnv2 env) a = some (.prod r.1 r.2.1, pls) := by
  obtain ⟨⟨ws, hw⟩, -, -⟩ := post_runB (post_splitStep_ty hT a) hr
  obtain ⟨pls, -, hs⟩ := sevalAt_ofEnv2 hg hw
  exact ⟨pls, hs⟩

/-! ## From `Accepted2` -/

/-- **`refOk2`'s parts**: every block's types, and the walk's pack points. -/
theorem refOk2_parts {p : Prog} (h : refOk2 p = true) :
    (∀ d ∈ p, noRefProd d.argTy = true ∧ noRefProd d.retTy = true) ∧ ∀ q ∈ litWalks2 p, refQ q = true := by
  simp only [refOk2, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1, fun q hq => by have := h.2 q hq; unfold refQ; split <;> simp_all⟩

/-- **A block's entry against the walk**: its parameter (bound to registers
`ps`) at its declared layout, `Unit` with no word. -/
theorem rel_entry {d : Decl} (harg : d.argTy = .unit ∨ Scc.Lower.simpleTy d.argTy = true) {ps : List Operand}
    (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) :
    Rel [(d.arg, d.argTy, ps)] ((Scc.Lower.params2 d).map (·, Scc.Lower.shapeOf d.argTy)) (Scc.Lower.params2 d) := by
  by_cases hu : d.argTy = .unit
  · have hp : Scc.Lower.params2 d = [] := by simp [Scc.Lower.params2, hu]
    have h0 : ps = [] := by
      rw [hu] at hpl
      simp only [Scc.Obj.valWords, Scc.Obj.slots, Option.map_some, List.length_nil, Option.some.injEq] at hpl
      exact List.length_eq_zero_iff.1 hpl.symm
    rw [hp]
    refine ⟨fun x b hb => ⟨fun L hL => (by simp at hL), fun _ => ?_⟩, fun x hx => (by simp at hx)⟩
    rw [find?_cons_name] at hb
    split at hb
    · cases hb; exact ⟨hu, h0⟩
    · cases hb
  · have hs : Scc.Lower.simpleTy d.argTy = true := harg.resolve_left hu
    have hp : Scc.Lower.params2 d = [d.arg] := by simp [Scc.Lower.params2, hu]
    rw [hp]
    have hcp := compat_shapeOf d.argTy 0 0 hs (slots_of_valWords hpl)
    have hi : Inv d.argTy ps (Scc.Lower.shapeOf d.argTy) := ⟨hcp, agreeW_regs hps (by
      have := valWords_compat hcp; rw [hpl] at this; exact Option.some.inj this)⟩
    refine ⟨relE_nil.cons hi, fun x hx => ?_⟩
    simp only [List.mem_singleton] at hx
    subst hx
    simp

/-- **`walk_rel` on a block of an `Accepted2` program** (`layoutOk2`,
`refOk2`): at every point of the lowering's walk of its body, the source
walk's point with `Rel`, `body2`, `BufInv` and `TyOK`. -/
theorem walk_rel_decl {p : Prog} (hlay : layoutOk2 p = true) (href : refOk2 p = true)
    {cx : Scc.Lower.Ctx} (hcx : CxOK cx p) {d : Decl} (hd : d ∈ p) {cx2 : Cx2}
    (hb : body2 cx2 [] [] (Scc.Lower.params2 d) d.body = true)
    (harg : d.argTy = .unit ∨ Scc.Lower.simpleTy d.argTy = true)
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∃ lits' cs' bufs' scope', (q.1, lits') ∈ litWalks2 p ∧
      Rel q.2.1 lits' scope' ∧ body2 cx2 cs' bufs' scope' q.1 = true ∧ BufInv q.2.1 bufs' ∧ TyOK q.2.1 := by
  intro q hq
  obtain ⟨hsig, hpk⟩ := refOk2_parts href
  have hT : TyOK [(d.arg, d.argTy, ps)] := TyOK.cons (fun _ h => by cases h) (hsig d hd).1
  obtain ⟨lits', c', b', s', h1, h2⟩ := walk_rel hcx (fun d hd => (hsig d hd).2) cx2 d.body [] [] _ _ _ n hb
    (rel_entry harg hps hpl) (fun b k h => by cases h) hT
    (fun q hq => ⟨List.all_eq_true.mp hlay q (List.mem_flatMap.2 ⟨d, hd, hq⟩),
      hpk q (List.mem_flatMap.2 ⟨d, hd, hq⟩)⟩) q hq
  exact ⟨lits', c', b', s', List.mem_flatMap.2 ⟨d, hd, h1⟩, h2⟩

end Spike.Lib.LowerNode
