import Spike.Lib.Src.NJLC
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.XchgB
import Spike.Lib.SlotRepAt

/-!
**The walk facts of an `Accepted2` block from `Accepted2`** (ISA-neutral).
At every point of the lowering's walk (`lowerEnvs2`) of a compiled block of
an `Accepted2` program (not the output extern or its loop), from its
parameter bound to registers:

- `callTs_ofAccepted2`: a call has no type arguments, and no index arguments
  except the output extern's one;
- `callArg_ofAccepted2`: a call's operand has a type at its callee's
  parameter layout (`argShape`) with its word count;
- `retOne_ofAccepted2`: a `ret` of a block of result `Int` is of one word,
  placed as one;
- `walk2_ofAccepted2`: the immediates (`ImmIn`), the point in the walk, the
  bindings' types (`EnvTy2`), grouping (`GrpL`) and register bases
  (`LocBaseRegAt`); `locBaseReg_ofAccepted2` the register bases at every
  variable;
- `litPts_ofAccepted2`: `LitPt` at every point of the block's literal walk;
  `countsB_ofAccepted2`, `xchgsB_ofAccepted2`: the block's counts and lane
  stores.

`decl2_setup` gives the facts all of them start from: the lowering's context
against the program (`CxOK`), the block's `body2` body and the walk's
`Rel`/`body2`/`BufInv`/`TyOK` at every point (`walk_rel`), the source walk's
point a point of the block's own literal walk (for `callsOk2`).
`walk_relB_decl` adds every binding `BOk` (a `simpleTy` type with a word
count, its words grouped, register bases for its locatives: `EnvBOk`) and
every variable with literal words bound (`LitsIn`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (Env LitV litAt shapeOf params2 litWalk2 callsOk2 argShape body2 Cx2 layoutOk2 refOk2)
open Scc.Lower.Inv (atomV)
open Spike.Lib.Form (group grp WordPl lookupS)

/-! ## The block's walk from `Accepted2` -/

/-- **`walk_rel` at a compiled block of an `Accepted2` program**, the source
walk's point in the block's own literal walk. -/
theorem walk_rel_decl' {p : Prog} (hlay : layoutOk2 p = true) (href : refOk2 p = true)
    {cx : Scc.Lower.Ctx} (hcx : CxOK cx p) {d : Decl} (hd : d ∈ p) {cx2 : Cx2}
    (hb : body2 cx2 [] [] (params2 d) d.body = true)
    (harg : d.argTy = .unit ∨ Scc.Lower.simpleTy d.argTy = true)
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∃ lits' cs' bufs' scope',
      (q.1, lits') ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body ∧
      Rel q.2.1 lits' scope' ∧ body2 cx2 cs' bufs' scope' q.1 = true ∧ BufInv q.2.1 bufs' ∧ TyOK q.2.1 := by
  intro q hq
  obtain ⟨hsig, hpk⟩ := refOk2_parts href
  have hT : TyOK [(d.arg, d.argTy, ps)] := TyOK.cons (fun _ h => by cases h) (hsig d hd).1
  exact walk_rel hcx (fun d hd => (hsig d hd).2) cx2 d.body [] [] _ _ _ n hb
    (rel_entry harg hps hpl) (fun b k h => by cases h) hT
    (fun q hq => ⟨List.all_eq_true.mp hlay q (List.mem_flatMap.2 ⟨d, hd, hq⟩),
      hpk q (List.mem_flatMap.2 ⟨d, hd, hq⟩)⟩) q hq

/-- **What a compiled block of an `Accepted2` program starts from**: the
lowering's context against the program, the program's `layoutOk2`,
`refOk2`, `callsOk2`, and the block's `body2` body from its parameters. -/
theorem decl2_setup {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx} (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) :
    CxOK cx p ∧ layoutOk2 p = true ∧ refOk2 p = true ∧ callsOk2 p = true ∧
      ∃ cx2, body2 cx2 [] [] (params2 d) d.body = true ∧ (d.argTy = .unit ∨ Scc.Lower.simpleTy d.argTy = true) := by
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hds⟩, hsp⟩, -⟩, hlay⟩, href⟩, hcalls⟩, -⟩, -⟩ := hp
  have hcx : CxOK cx p := ⟨hprog, fun d' hd' => by
    obtain ⟨E, hE⟩ := decl2_of_decls2 hds d' hd'
    exact retTy_decl2 hE, hext⟩
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  exact ⟨hcx, hlay, href, hcalls, body_decl2 hE hne hnl (setup_simple hds hsp)⟩

/-! ## Bindings with simple types and register bases -/

/-- **A binding's locatives have register bases**: every locative placement
of its words (`Form.group`) has a register base. -/
def LocRegs (t : Ty) (ws : List Operand) : Prop :=
  ∀ pls, group t ws = some pls → ∀ b o, WordPl.loc b o ∈ pls → ∃ r, b = .reg r

/-- **A binding of the walk**: a `simpleTy` type with a word count, its
words grouped, with register bases. -/
def BOk (t : Ty) (ws : List Operand) : Prop :=
  Scc.Lower.simpleTy t = true ∧ (Scc.Obj.valWords t).isSome = true ∧ (group t ws).isSome = true ∧ LocRegs t ws

/-- **Every binding of the environment** (shadowed ones too) is `BOk`. -/
def EnvBOk (env : Env) : Prop := ∀ b ∈ env, BOk b.2.1 b.2.2

/-- **Every variable with literal words is bound** in the environment. -/
def LitsIn (env : Env) (lits : List (String × LitV)) : Prop :=
  ∀ x, (lits.lookup x).isSome = true → (env.find? (·.1 == x)).isSome = true

theorem EnvBOk.cons {env : Env} (h : EnvBOk env) {x : String} {t : Ty} {ws : List Operand} (hb : BOk t ws) :
    EnvBOk ((x, t, ws) :: env) := by
  intro b hb'
  rcases List.mem_cons.mp hb' with rfl | hb'
  · exact hb
  · exact h b hb'

theorem LitsIn.cons {env : Env} {lits : List (String × LitV)} (h : LitsIn env lits) (x : String) (t : Ty)
    (ws : List Operand) (L : LitV) : LitsIn ((x, t, ws) :: env) ((x, L) :: lits) := by
  intro y hy
  rw [find?_cons_name]
  rw [lookup_cons_name] at hy
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, ↓reduceIte, Ne.symm hxy] at hy ⊢
    exact h y hy

/-- Words all registers have register bases. -/
theorem locRegs_regs {t : Ty} {ws : List Operand} (h : ∀ w ∈ ws, IsReg w) : LocRegs t ws := by
  intro pls hg b o hm
  have ho : pls.flatMap WordPl.opds = ws := by
    have hg' : grp t ws = some (pls, []) := by
      simp only [group] at hg
      split at hg
      · rename_i pls' hg'; simp only [Option.some.injEq] at hg; subst hg; exact hg'
      · simp at hg
    simpa using grp_opds t ws pls [] hg'
  exact h b (by rw [← ho]; exact List.mem_flatMap.2 ⟨_, hm, by simp [WordPl.opds]⟩)

/-- Words against a layout group (`grp_compat`). -/
theorem group_of_inv {t : Ty} {ws : List Operand} {L : LitV} (h : Inv t ws L) : (group t ws).isSome = true := by
  obtain ⟨pls, h1, -⟩ := grp_compat t L ws [] h.1 h.2
  simp only [List.append_nil] at h1
  simp [group, h1]

theorem bOk_of {t : Ty} {ws : List Operand} {L : LitV} (hs : Scc.Lower.simpleTy t = true) (hl : LocRegs t ws)
    (hi : Inv t ws L) : BOk t ws :=
  ⟨hs, by rw [valWords_compat hi.1]; rfl, group_of_inv hi, hl⟩

/-- **An atom's value is `BOk`**: a binding's, a literal's or `()`'s. -/
theorem atomV_bOk {env : Env} (hE : EnvBOk env) {a : At} {t : Ty} {ws : List Operand}
    (h : atomV env a = some (t, ws)) : BOk t ws := by
  cases a with
  | var x =>
    simp only [atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨y, u, vs⟩, hb, he⟩ := h
    cases he
    exact hE _ (List.mem_of_find?_eq_some hb)
  | lit n =>
    simp only [atomV] at h
    split at h
    · cases h
    · cases h
      refine ⟨rfl, rfl, rfl, fun pls hp b o hm => ?_⟩
      simp only [group, grp, Option.some.injEq] at hp
      subst hp
      simp at hm
  | unit =>
    cases h
    exact ⟨rfl, rfl, rfl, fun pls hp b o hm => by simp only [group, grp, Option.some.injEq] at hp; subst hp; simp at hm⟩

/-- **An atom of the body has its value against its literal words.** -/
theorem atomV_inv {env : Env} {lits : List (String × LitV)} {scope : List String} (hR : Rel env lits scope)
    (hLi : LitsIn env lits) {a : At} (ha : Scc.Lower.atom1 scope a = true) :
    ∃ t ws, atomV env a = some (t, ws) ∧ Inv t ws (litAt lits a) := by
  cases a with
  | var y =>
    have hy := hR.2 y (atom1_var ha y rfl)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hLi y hy)
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 hy
    refine ⟨b.2.1, b.2.2, by simp [atomV, hb], ?_⟩
    simp only [litAt, hL, Option.getD_some]
    exact (hR.1 y b hb).1 L hL
  | lit n =>
    have hn : n < 2 ^ 63 := by simpa [Scc.Lower.atom1, Scc.Lower.atom0] using ha
    refine ⟨.intS (.lit n), [Scc.Lower.imm n], by simp only [atomV]; split <;> first | (exfalso; omega) | rfl,
      rfl, ?_⟩
    simp [AgreeW, flatL, litAt, Scc.Lower.imm]
    omega
  | unit => simp [Scc.Lower.atom1, Scc.Lower.atom0] at ha

/-- **The lowering of a `let` gives a `simpleTy` type with register bases.** -/
theorem post_lowerOp_ok {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p) {cx2 : Cx2}
    {cs bufs : List (String × Nat)} {scope : List String} {x : String} {op : Op} {e : Expr} {env : Env}
    {lits : List (String × LitV)} (hb : body2 cx2 cs bufs scope (.let_ x op e) = true) (hR : Rel env lits scope)
    (hB : BufInv env bufs) (hE : EnvBOk env) (hL : layQ (.let_ x op e, lits) = true) :
    Post (Scc.Lower.lowerOp cx env x op) fun r => Scc.Lower.simpleTy r.1 = true ∧ LocRegs r.1 r.2 := by
  cases op <;> try (simp [body2] at hb; done)
  case atom a => exact Post.mono (post_evalAtV env a) fun r hr => ⟨(atomV_bOk hE hr).1, (atomV_bOk hE hr).2.2.2⟩
  case nameI a => exact Post.mono (post_evalAtV env a) fun r hr => ⟨(atomV_bOk hE hr).1, (atomV_bOk hE hr).2.2.2⟩
  case add a b =>
    exact Post.mono (post_add cx env x a b) fun r ⟨d, hd⟩ => by
      subst hd; exact ⟨rfl, locRegs_regs (by simp [IsReg])⟩
  case sub a b =>
    exact Post.mono (post_sub cx env x a b) fun r ⟨d, hd⟩ => by
      subst hd; exact ⟨rfl, locRegs_regs (by simp [IsReg])⟩
  case pair a b =>
    simp only [Scc.Lower.lowerOp]
    refine Post.bind (post_evalAtV env a) fun r1 h1 => Post.bind (post_evalAtV env b) fun r2 h2 => Post.pure ?_
    obtain ⟨s1, -, g1, l1⟩ := atomV_bOk hE h1
    obtain ⟨s2, -, g2, l2⟩ := atomV_bOk hE h2
    refine ⟨by simp [Scc.Lower.simpleTy, s1, s2], fun pls hg b o hm => ?_⟩
    obtain ⟨p1, hp1⟩ := Option.isSome_iff_exists.1 g1
    obtain ⟨p2, hp2⟩ := Option.isSome_iff_exists.1 g2
    rw [group_pair hp1 hp2] at hg
    cases hg
    rcases List.mem_append.1 hm with hm | hm
    · exact l1 _ hp1 b o hm
    · exact l2 _ hp2 b o hm
  case pack a i τ =>
    simp only [body2, Bool.and_eq_true] at hb
    have hs : Scc.Lower.simpleTy τ = true := by
      simp only [layQ, Bool.and_eq_true] at hL; exact hL.1.2
    have hg := group_pack_of_layQ hL hR.1 (fun y hy => hR.2 y (atom1_var hb.1 y hy))
    simp only [Scc.Lower.lowerOp]
    refine Post.bind (post_evalAtV env a) fun r h => Post.pure ⟨hs, fun pls hp => ?_⟩
    rw [hg _ _ h] at hp
    exact (atomV_bOk hE h).2.2.2 pls hp
  case asLanes sg w a =>
    simp only [Scc.Lower.lowerOp]
    exact Post.bind' fun _ => Post.pure ⟨rfl, fun pls hp b o hm => by
      simp only [group, grp, Option.some.injEq] at hp; subst hp; simp at hm⟩
  case call g is a ts =>
    simp only [Scc.Lower.lowerOp]
    refine Post.bind (post_needSome _ _) fun d hd => Post.bind' fun r => ?_
    refine Post.bind' fun k => Post.bind (post_callBlock cx g _ k) fun rs hrs => Post.pure ⟨?_, ?_⟩
    · rw [hcx.prog] at hd; exact hcx.ret d (List.mem_of_find?_eq_some hd)
    · rcases hrs with ⟨rfl, -⟩ | ⟨-, hr⟩
      · exact locRegs_regs (by simp)
      · exact locRegs_regs hr
  case newBuf n τ =>
    exact Post.mono (post_newBuf cx env x n τ) fun r ⟨q, hq⟩ => by
      subst hq
      refine ⟨rfl, fun pls hp b o hm => ?_⟩
      simp only [group, grp, bufTy, Option.some.injEq] at hp
      subst hp
      simp only [List.mem_singleton, WordPl.loc.injEq] at hm
      exact ⟨q, hm.1⟩
  case xchgAt b i v =>
    rcases b with b | b | _ <;> rcases i with i | i | _ <;> try (simp [body2] at hb; done)
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨_, hk⟩, _⟩, _⟩ := hb
    split at hk
    · rename_i k hbk
      obtain ⟨e0, τ, he0, ht0, hτ⟩ := hB b k hbk
      exact Post.mono (post_xchgAt cx x b i v he0 ht0 hτ) fun r ⟨h1, _, h3⟩ =>
        ⟨by rw [h1]; cases τ <;> simp [Scc.Lower.elem2] at hτ <;> rfl, locRegs_regs h3⟩
    · cases hk

/-- **The lowering's split reads the operand as the literal product** of
its components, the words whole (under `TyOK`). -/
theorem post_splitStep_v {env : Env} (hT : TyOK env) (a : At) :
    Post (splitStep env a) fun r => atomV env a = some (.prod r.1 r.2.1, r.2.2.1) := by
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
  exact hr.1

/-- **A pair's components are `BOk`**, split where their layouts are. -/
theorem bOk_split {u w : Ty} {ws : List Operand} (hv : BOk (.prod u w) ws) {k : Nat} {l rr : LitV}
    (h1 : Inv u (ws.take k) l) (h2 : Inv w (ws.drop k) rr) : BOk u (ws.take k) ∧ BOk w (ws.drop k) := by
  obtain ⟨hs, -, -, hl⟩ := hv
  simp only [Scc.Lower.simpleTy, Bool.and_eq_true] at hs
  obtain ⟨pu, hpu⟩ := Option.isSome_iff_exists.1 (group_of_inv h1)
  obtain ⟨pw, hpw⟩ := Option.isSome_iff_exists.1 (group_of_inv h2)
  have hg := group_pair hpu hpw
  rw [List.take_append_drop] at hg
  refine ⟨bOk_of hs.1 (fun pls hp b o hm => ?_) h1, bOk_of hs.2 (fun pls hp b o hm => ?_) h2⟩
  · rw [hpu] at hp; cases hp; exact hl _ hg b o (List.mem_append_left _ hm)
  · rw [hpw] at hp; cases hp; exact hl _ hg b o (List.mem_append_right _ hm)

/-- **An index package's body is `BOk`.** -/
theorem bOk_iex {b : Ty} {ws : List Operand} (h : BOk (.iex b) ws) {L : LitV} (hi : Inv b ws L) : BOk b ws := by
  refine bOk_of (by simpa [Scc.Lower.simpleTy] using h.1) (fun pls hp => ?_) hi
  obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.1 h.2.2.1
  have h' := group_iex hp0
  rw [hp] at h'
  cases h'
  exact h.2.2.2 _ hp0

/-- **`walk_rel` keeping `EnvBOk` and `LitsIn`.** -/
theorem walk_relB {cx : Scc.Lower.Ctx} {p : Prog} (hcx : CxOK cx p) (hret : ∀ d ∈ p, Scc.Lower.noRefProd d.retTy = true)
    (cx2 : Cx2) (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String) (env : Env) (lits : List (String × LitV)) (n : Nat),
      body2 cx2 cs bufs scope e = true → Rel env lits scope → BufInv env bufs → TyOK env → EnvBOk env →
      LitsIn env lits → (∀ q ∈ litWalk2 p lits e, layQ q = true ∧ refQ q = true) →
      ∀ q ∈ lowerEnvs2 cx env n e, ∃ lits' cs' bufs' scope', (q.1, lits') ∈ litWalk2 p lits e ∧
        Rel q.2.1 lits' scope' ∧ body2 cx2 cs' bufs' scope' q.1 = true ∧ BufInv q.2.1 bufs' ∧ TyOK q.2.1 ∧
        EnvBOk q.2.1 ∧ LitsIn q.2.1 lits' := by
  induction e
  case let_ x op e ih =>
    intro cs bufs scope env lits n hb hR hB hT hE hLi hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT, hE, hLi⟩
    · have hL0 := hL _ (by rw [litWalk2]; exact List.mem_cons_self ..)
      obtain ⟨cs', bufs', hb', hop⟩ := let_step hcx hb hR hB hL0.1
      have hty := post_lowerOp_ty hcx hret hb hT hB hL0.2
      have hok := post_lowerOp_ok hcx hb hR hB hE hL0.1
      split at hq
      · rename_i hr
        have hQ := post_runB (post_letStep (e := e) (Post.and (Post.and hop hty) hok)) hr
        obtain ⟨lits', c', b', s', h1, h2⟩ := ih cs' bufs' (x :: scope) _ _ _ hb' (hR.cons hQ.1.1.1) hQ.1.1.2
          (hT.cons hQ.1.2) (hE.cons (bOk_of hQ.2.1 hQ.2.2 hQ.1.1.1)) (hLi.cons _ _ _ _)
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ h1, h2⟩
      · simp at hq
  case split a x y e ih =>
    intro cs bufs scope env lits n hb hR hB hT hE hLi hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT, hE, hLi⟩
    · have hb0 := hb
      simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rename_i hr
        obtain ⟨l, rr, hla, h1, h2⟩ := post_runB (post_splitStep hR (atom1_var hb.1)) hr
        obtain ⟨-, hu, hw⟩ := post_runB (post_splitStep_ty hT a) hr
        have hv := post_runB (post_splitStep_v hT a) hr
        have hbo := bOk_split (atomV_bOk hE hv) h1 h2
        have hlw : litWalk2 p lits (.split a x y e) =
            (.split a x y e, lits) :: litWalk2 p ((y, rr) :: (x, l) :: lits) e := by
          rw [litWalk2, hla]
        obtain ⟨lits', c', b', s', h1', h2'⟩ := ih _ _ (y :: x :: scope) _ _ _ hb.2 ((hR.cons h1).cons h2)
          ((hB.cons x _ _).cons y _ _) ((hT.cons hu).cons hw) ((hE.cons hbo.1).cons hbo.2)
          ((hLi.cons _ _ _ _).cons _ _ _ _)
          (fun q hq => hL q (by rw [hlw]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', c', b', s', by rw [hlw]; exact List.mem_cons_of_mem _ h1', h2'⟩
      · simp at hq
  case unpack a i x e ih =>
    intro cs bufs scope env lits n hb hR hB hT hE hLi hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT, hE, hLi⟩
    · have hb0 := hb
      simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rename_i hr
        have hI := post_runB (post_evalAt hR (atom1_var hb.1)) hr
        have hty := post_runB (post_evalAt_ty hT a) hr
        have hv := post_runB (post_evalAtV env a) hr
        have hI' : Inv _ _ (litAt lits a) := ⟨by
          have := hI.1; simp only [Compat, Bool.and_eq_true] at this; exact this.2, hI.2⟩
        obtain ⟨lits', c', b', s', h1, h2⟩ := ih _ _ (x :: scope) _ _ _ hb.2 (hR.cons hI') ((hB.sub i).cons x _ _)
          (hT.cons (noRefProd_iex hty)) (hE.cons (bOk_iex (atomV_bOk hE hv) hI')) (hLi.cons _ _ _ _)
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
        exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ h1, h2⟩
      · simp at hq
  case ifeq a b yes no ihy ihn =>
    intro cs bufs scope env lits n hb hR hB hT hE hLi hL q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨lits, cs, bufs, scope, by rw [litWalk2]; exact List.mem_cons_self .., hR, hb, hB, hT, hE, hLi⟩
    · have hb0 := hb
      simp only [body2, Bool.and_eq_true] at hb
      split at hq
      · rw [List.mem_append] at hq
        rcases hq with hq | hq
        · obtain ⟨lits', c', b', s', h1, h2⟩ := ihy _ _ _ _ _ _ hb.1.2 hR hB hT hE hLi
            (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq))) q hq
          exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h1), h2⟩
        · split at hq
          · obtain ⟨lits', c', b', s', h1, h2⟩ := ihn _ _ _ _ _ _ hb.2 hR hB hT hE hLi
              (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq))) q hq
            exact ⟨lits', c', b', s', by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ h1),
              h2⟩
          · simp at hq
      · simp at hq
  all_goals
    intro cs bufs scope env lits n hb hR hB hT hE hLi hL q hq
    first
      | (simp [body2] at hb; done)
      | (simp only [lowerEnvs2, List.mem_singleton] at hq
         subst hq
         exact ⟨lits, cs, bufs, scope, by simp [litWalk2], hR, hb, hB, hT, hE, hLi⟩)

/-- **A block's entry is `EnvBOk`**: its parameter's type `simpleTy`, its
words registers. -/
theorem envBOk_entry {d : Decl} (harg : d.argTy = .unit ∨ Scc.Lower.simpleTy d.argTy = true) {ps : List Operand}
    (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) : EnvBOk [(d.arg, d.argTy, ps)] := by
  have hs : Scc.Lower.simpleTy d.argTy = true := harg.elim (fun h => by rw [h]; rfl) id
  have hcp := compat_shapeOf d.argTy 0 0 hs (slots_of_valWords hpl)
  have hi : Inv d.argTy ps (shapeOf d.argTy) := ⟨hcp, agreeW_regs hps (by
    have := valWords_compat hcp; rw [hpl] at this; exact Option.some.inj this)⟩
  exact EnvBOk.cons (fun _ h => by cases h) (bOk_of hs (locRegs_regs hps) hi)

theorem litsIn_entry (d : Decl) (ps : List Operand) :
    LitsIn [(d.arg, d.argTy, ps)] ((params2 d).map (·, shapeOf d.argTy)) := by
  intro x hx
  rw [find?_cons_name]
  by_cases h : d.arg = x
  · simp [h]
  · exfalso
    simp only [params2] at hx
    split at hx
    · simp at hx
    · simp [lookup_cons_name, Ne.symm h] at hx

/-- **`walk_relB` at a compiled block of an `Accepted2` program.** -/
theorem walk_relB_decl {p : Prog} (hlay : layoutOk2 p = true) (href : refOk2 p = true)
    {cx : Scc.Lower.Ctx} (hcx : CxOK cx p) {d : Decl} (hd : d ∈ p) {cx2 : Cx2}
    (hb : body2 cx2 [] [] (params2 d) d.body = true)
    (harg : d.argTy = .unit ∨ Scc.Lower.simpleTy d.argTy = true)
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∃ lits' cs' bufs' scope',
      (q.1, lits') ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body ∧
      Rel q.2.1 lits' scope' ∧ body2 cx2 cs' bufs' scope' q.1 = true ∧ BufInv q.2.1 bufs' ∧ TyOK q.2.1 ∧
      EnvBOk q.2.1 ∧ LitsIn q.2.1 lits' := by
  intro q hq
  obtain ⟨hsig, hpk⟩ := refOk2_parts href
  have hT : TyOK [(d.arg, d.argTy, ps)] := TyOK.cons (fun _ h => by cases h) (hsig d hd).1
  exact walk_relB hcx (fun d hd => (hsig d hd).2) cx2 d.body [] [] _ _ _ n hb
    (rel_entry harg hps hpl) (fun b k h => by cases h) hT (envBOk_entry harg hps hpl) (litsIn_entry d ps)
    (fun q hq => ⟨List.all_eq_true.mp hlay q (List.mem_flatMap.2 ⟨d, hd, hq⟩),
      hpk q (List.mem_flatMap.2 ⟨d, hd, hq⟩)⟩) q hq

/-- **`EnvBOk`'s locatives at `ofEnv2`** have register bases. -/
theorem locBase_of_envBOk {env : Env} (hE : EnvBOk env) :
    ∀ y ty pls, lookupS (ofEnv2 env) y = some (ty, pls) → ∀ b o, WordPl.loc b o ∈ pls → ∃ r, b = .reg r := by
  intro y ty pls h b o hm
  rw [lookupS_ofEnv2, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  have hok := hE c (List.mem_of_find?_eq_some hc)
  obtain ⟨p0, hp0⟩ := Option.isSome_iff_exists.1 hok.2.2.1
  rw [hp0, Option.getD_some] at hm
  exact hok.2.2.2 p0 hp0 b o hm

/-! ## The literal walk's facts -/

/-- **The buffers of `body2` against the literal walk**: each with a count
below `2 ^ 28` and literal words. -/
def BufLits (bufs : List (String × Nat)) (lits : List (String × LitV)) : Prop :=
  ∀ b n, bufs.lookup b = some n → n < 2 ^ 28 ∧ (lits.lookup b).isSome = true

theorem lookup_cons_isSome {lits : List (String × LitV)} {y : String} (h : (lits.lookup y).isSome = true)
    (x : String) (L : LitV) : (((x, L) :: lits).lookup y).isSome = true := by
  rw [lookup_cons_name]; split <;> simp [h]

theorem BufLits.sub {bufs : List (String × Nat)} {lits : List (String × LitV)} (h : BufLits bufs lits)
    (i : String) : BufLits (Scc.Lower.unbuf i bufs) lits := by
  intro b n hb
  rw [lookup_unbuf] at hb
  split at hb
  · cases hb
  · exact h b n hb

theorem BufLits.unbuf {bufs : List (String × Nat)} {lits : List (String × LitV)} (h : BufLits bufs lits)
    (x : String) (L : LitV) : BufLits (Scc.Lower.unbuf x bufs) ((x, L) :: lits) := by
  intro b n hb
  obtain ⟨h1, h2⟩ := h.sub x b n hb
  exact ⟨h1, lookup_cons_isSome h2 x L⟩

theorem BufLits.new {bufs : List (String × Nat)} {lits : List (String × LitV)} (h : BufLits bufs lits)
    (x : String) (L : LitV) {k : Nat} (hk : k < 2 ^ 28) :
    BufLits ((x, k) :: Scc.Lower.unbuf x bufs) ((x, L) :: lits) := by
  intro b n hb
  rw [lookup_cons_name] at hb
  split at hb
  · rename_i hbx; subst hbx; cases hb; exact ⟨hk, by simp⟩
  · exact h.unbuf x L b n hb

theorem litsScope_cons {lits : List (String × LitV)} {scope : List String}
    (h : ∀ y ∈ scope, (lits.lookup y).isSome = true) (x : String) (L : LitV) :
    ∀ y ∈ x :: scope, (((x, L) :: lits).lookup y).isSome = true := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · simp
  · exact lookup_cons_isSome (h y hy) x L

/-- **A `body2` `let`'s body is `body2`** with the buffers against the
literal walk. -/
theorem body2_let_lits {cx2 : Cx2} {cs bufs : List (String × Nat)} {scope : List String} {x : String} {op : Op}
    {e : Expr} {lits : List (String × LitV)} (hb : body2 cx2 cs bufs scope (.let_ x op e) = true)
    (hB : BufLits bufs lits) (L : LitV) :
    ∃ cs' bufs', body2 cx2 cs' bufs' (x :: scope) e = true ∧ BufLits bufs' ((x, L) :: lits) := by
  cases op with
  | newBuf n τ =>
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨-, hm⟩ := hb
    split at hm
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      exact ⟨_, _, hm.2, hB.new x L hm.1.2⟩
    · cases hm
  | xchgAt b i v =>
    cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb <;>
      exact ⟨_, _, hb.2, hB.unbuf x L⟩
  | _ => simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb <;> exact ⟨_, _, hb.2, hB.unbuf x L⟩

/-- **`LitPt` at the head of a `body2` body**: its atoms in scope, a
buffer's lane index below its count, the layout checks (`layQ`). -/
theorem litPt_head {cx2 : Cx2} {cs bufs : List (String × Nat)} {scope : List String} {e : Expr}
    {lits : List (String × LitV)} (hb : body2 cx2 cs bufs scope e = true)
    (hS : ∀ y ∈ scope, (lits.lookup y).isSome = true) (hB : BufLits bufs lits) (hL : layQ (e, lits) = true) :
    LitPt (e, lits) := by
  have hA : ∀ a, Scc.Lower.atom1 scope a = true → InLits lits a ∧ ∀ n, a = .lit n → n < 2 ^ 64 := by
    intro a ha
    cases a with
    | var y => exact ⟨fun z hz => (by cases hz; exact hS y (atom1_var ha y rfl)), fun n h => (by cases h)⟩
    | lit n =>
      refine ⟨fun z hz => (by cases hz), fun m hm => ?_⟩
      cases hm
      have : n < 2 ^ 63 := by simpa [Scc.Lower.atom1, Scc.Lower.atom0] using ha
      omega
    | unit => simp [Scc.Lower.atom1, Scc.Lower.atom0] at ha
  have hH : ∀ a ∈ headAtoms e, InLits lits a ∧ ∀ n, a = .lit n → n < 2 ^ 64 := by
    intro a ha
    cases e with
    | let_ x op e' =>
      cases op <;> try (simp [body2] at hb; done)
      case xchgAt b i v =>
        rcases b with b | b | _ <;> rcases i with i | i | _ <;> try (simp [body2] at hb; done)
        simp only [body2, Bool.and_eq_true] at hb
        obtain ⟨⟨⟨_, hk⟩, hv⟩, _⟩ := hb
        split at hk
        · rename_i n hbn
          simp only [decide_eq_true_eq] at hk
          obtain ⟨hn, hl⟩ := hB b n hbn
          simp only [headAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · exact ⟨fun z hz => (by cases hz; exact hl), fun m h => (by cases h)⟩
          · exact ⟨fun z hz => (by cases hz), fun m h => (by cases h; omega)⟩
          · exact hA _ hv
        · cases hk
      all_goals
        simp only [body2, Bool.and_eq_true] at hb
        simp only [headAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
        first
          | (subst ha
             first | exact hA _ hb.1 | exact hA _ hb.1.2 | exact hA _ hb.1.1.2)
          | (rcases ha with rfl | rfl
             · exact hA _ hb.1.1
             · exact hA _ hb.1.2)
    | split a x y e' =>
      simp only [body2, Bool.and_eq_true] at hb
      simp only [headAtoms, List.mem_singleton] at ha
      subst ha; exact hA _ hb.1
    | unpack a i x e' =>
      simp only [body2, Bool.and_eq_true] at hb
      simp only [headAtoms, List.mem_singleton] at ha
      subst ha; exact hA _ hb.1
    | ret a =>
      simp only [body2] at hb
      simp only [headAtoms, List.mem_singleton] at ha
      subst ha; exact hA _ hb
    | ifeq a b y n =>
      simp only [body2, Bool.and_eq_true] at hb
      simp only [headAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hA _ hb.1.1.1
      · exact hA _ hb.1.1.2
    | _ => simp [body2] at hb
  refine ⟨fun a h => (hH a h).1, ?_, ?_, fun n h => (hH _ h).2 n rfl⟩
  · intro x a w τ e' he
    simp only at he
    subst he
    simp only [layQ, Bool.and_eq_true, beq_iff_eq] at hL
    show Compat τ (litAt lits a) = true
    rw [← compat_erase, hL.1.1]
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hL.2
    exact compat_shapeOf τ 0 0 hL.1.2 (slots_of_valWords hk)
  · intro x sg w a e' he
    simp only at he
    subst he
    simp only [layQ] at hL
    split at hL
    · exact ⟨_, ‹_›⟩
    · cases hL

/-- **`LitPt` along the literal walk of a `body2` body.** -/
theorem litPts_walk {p : Prog} (cx2 : Cx2) (e : Expr) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String) (lits : List (String × LitV)),
      body2 cx2 cs bufs scope e = true → (∀ y ∈ scope, (lits.lookup y).isSome = true) → BufLits bufs lits →
      (∀ q ∈ litWalk2 p lits e, layQ q = true) → ∀ q ∈ litWalk2 p lits e, LitPt q := by
  induction e
  case let_ x op e ih =>
    intro cs bufs scope lits hb hS hB hL q hq
    rw [litWalk2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact litPt_head hb hS hB (hL _ (by rw [litWalk2]; exact List.mem_cons_self ..))
    · obtain ⟨cs', bufs', hb', hB'⟩ := body2_let_lits hb hB (Scc.Lower.opLit p lits op)
      exact ih _ _ _ _ hb' (litsScope_cons hS x _) hB'
        (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
  case split a x y e ih =>
    intro cs bufs scope lits hb hS hB hL q hq
    have hb0 := hb
    obtain ⟨l, r, hlw⟩ : ∃ l r, litWalk2 p lits (.split a x y e) =
        (.split a x y e, lits) :: litWalk2 p ((y, r) :: (x, l) :: lits) e := by
      rw [litWalk2]; split <;> exact ⟨_, _, rfl⟩
    rw [hlw, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact litPt_head hb hS hB (hL _ (by rw [hlw]; exact List.mem_cons_self ..))
    · simp only [body2, Bool.and_eq_true] at hb
      exact ih _ _ _ _ hb.2 (litsScope_cons (litsScope_cons hS x l) y r) ((hB.unbuf x l).unbuf y r)
        (fun q hq => hL q (by rw [hlw]; exact List.mem_cons_of_mem _ hq)) q hq
  case unpack a i x e ih =>
    intro cs bufs scope lits hb hS hB hL q hq
    rw [litWalk2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact litPt_head hb hS hB (hL _ (by rw [litWalk2]; exact List.mem_cons_self ..))
    · simp only [body2, Bool.and_eq_true] at hb
      exact ih _ _ _ _ hb.2 (litsScope_cons hS x _) ((hB.sub i).unbuf x _)
        (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ hq)) q hq
  case ifeq a b yes no ihy ihn =>
    intro cs bufs scope lits hb hS hB hL q hq
    rw [litWalk2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact litPt_head hb hS hB (hL _ (by rw [litWalk2]; exact List.mem_cons_self ..))
    · simp only [body2, Bool.and_eq_true] at hb
      rcases List.mem_append.1 hq with hq | hq
      · exact ihy _ _ _ _ hb.1.2 hS hB
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq))) q hq
      · exact ihn _ _ _ _ hb.2 hS hB
          (fun q hq => hL q (by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq))) q hq
  all_goals
    intro cs bufs scope lits hb hS hB hL q hq
    first
      | (simp [body2] at hb; done)
      | (simp only [litWalk2, List.mem_singleton] at hq
         subst hq
         exact litPt_head hb hS hB (hL _ (by simp [litWalk2])))

/-! ## Calls -/

/-- **A call of an `Accepted2` body** has no type arguments, and no index
arguments except the output extern's one (`body2`). -/
theorem callTs_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx}
    (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∀ x g is a ts e, q.1 = .let_ x (.call g is a ts) e →
      ts = [] ∧ (is = [] ∨ (g = "print" ∧ is.length = 1)) := by
  intro q hq x g is a ts e he
  obtain ⟨hcx, hlay, href, -, cx2, hb, harg⟩ := decl2_setup hp hprog hext hd hne hnl
  obtain ⟨_, _, _, _, _, _, hb', _⟩ := walk_rel_decl' hlay href hcx hd hb harg hps hpl n q hq
  rw [he] at hb'
  simp only [body2, Bool.and_eq_true] at hb'
  have h := hb'.1.1
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc h
    exact ⟨h.2, Or.inr ⟨hc.2, h.1.2⟩⟩
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨h.2, Or.inl h.1.2⟩

/-- **A call's operand of an `Accepted2` body** has a type at its callee's
parameter layout with its word count (`callsOk2`). -/
theorem callArg_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx}
    (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∀ x g is a ts e, q.1 = .let_ x (.call g is a ts) e →
      ∃ t ws, atomV q.2.1 a = some (t, ws) ∧ Compat t (argShape p g) = true ∧
        Scc.Obj.valWords t = some ws.length := by
  intro q hq x g is a ts e he
  obtain ⟨hcx, hlay, href, hcalls, cx2, hb, harg⟩ := decl2_setup hp hprog hext hd hne hnl
  obtain ⟨lits, _, _, scope, hm, hR, hb', _, _, _, hLi⟩ := walk_relB_decl hlay href hcx hd hb harg hps hpl n q hq
  have hs := (callsOk2_parts hcalls hd hm).1 x g is a ts e he
  rw [he] at hb'
  simp only [body2, Bool.and_eq_true] at hb'
  obtain ⟨t, ws, hv, hi⟩ := atomV_inv hR hLi hb'.1.2
  exact ⟨t, ws, hv, by rw [← hs, compat_erase]; exact hi.1, by rw [valWords_compat hi.1, hi.2.length]⟩

/-! ## Returns -/

/-- **A `ret` of an `Accepted2` block of result `Int`** is of one word,
placed as one (`callsOk2`). -/
theorem retOne_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx}
    (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) (hint : d.retTy = .int)
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∀ a, q.1 = .ret a →
      ∃ t w, atomV q.2.1 a = some (t, [w]) ∧ group t [w] = some [.one w] := by
  intro q hq a he
  obtain ⟨hcx, hlay, href, hcalls, cx2, hb, harg⟩ := decl2_setup hp hprog hext hd hne hnl
  obtain ⟨lits, _, _, scope, hm, hR, hb', _, _, _, hLi⟩ := walk_relB_decl hlay href hcx hd hb harg hps hpl n q hq
  have hs := (callsOk2_parts hcalls hd hm).2 a he
  rw [hint] at hs
  rw [he] at hb'
  simp only [body2] at hb'
  obtain ⟨t, ws, hv, hi⟩ := atomV_inv hR hLi hb'
  obtain ⟨o, ho⟩ : ∃ o, litAt lits a = .leaf o := by
    revert hs; cases litAt lits a <;> simp [Scc.Lower.LitV.erase, shapeOf]
  rw [ho] at hi
  obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := List.length_eq_one_iff.1 (by simpa [flatL] using hi.2.length)
  obtain ⟨pls, hpl'⟩ := Option.isSome_iff_exists.1 (group_of_inv hi)
  exact ⟨t, w, hv, by rw [hpl', group_one hpl']⟩

/-! ## The walk's facts -/

/-- **The walk facts of an `Accepted2` block**: the immediates, the point
in the walk, the bindings' types (`EnvTy2`), grouping (`GrpL`) and register
bases (`LocBaseRegAt`). -/
theorem walk2_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx}
    (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body,
      ImmIn (Scc.Lower.imms2Of p) (ofEnv2 q.2.1) q.1 ∧ InWalk2 cx [(d.arg, d.argTy, ps)] n d.body q.1 ∧
        EnvTy2 q ∧ GrpL q.2.1 ∧ LocBaseRegAt (ofEnv2 q.2.1) q.1 := by
  intro q hq
  obtain ⟨hI, hW⟩ := walk_imms2Of hp hprog hext hd hne hnl hps hpl n q hq
  obtain ⟨hcx, hlay, href, -, cx2, hb, harg⟩ := decl2_setup hp hprog hext hd hne hnl
  obtain ⟨_, _, _, _, _, _, _, _, hT, hE, _⟩ := walk_relB_decl hlay href hcx hd hb harg hps hpl n q hq
  exact ⟨hI, hW, fun b hb => ⟨(hE b hb).1, (hE b hb).2.1, hT b hb⟩,
    fun x b hb => (hE b (List.mem_of_find?_eq_some hb)).2.2.1,
    fun y _ ty pls h => locBase_of_envBOk hE y ty pls h⟩

/-- **The locatives of an `Accepted2` block's bindings** have register
bases at every point of its walk (at `ofEnv2`). -/
theorem locBaseReg_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx}
    (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∀ y ty pls, lookupS (ofEnv2 q.2.1) y = some (ty, pls) →
      ∀ b o, WordPl.loc b o ∈ pls → ∃ r, b = .reg r := by
  intro q hq
  obtain ⟨hcx, hlay, href, -, cx2, hb, harg⟩ := decl2_setup hp hprog hext hd hne hnl
  obtain ⟨_, _, _, _, _, _, _, _, _, hE, _⟩ := walk_relB_decl hlay href hcx hd hb harg hps hpl n q hq
  exact locBase_of_envBOk hE

/-! ## The literal walk, counts and lane stores from `Accepted2` -/

/-- **What a compiled block of an `Accepted2` program has in its source
alone**: the program's `layoutOk2` and `countsOk2`, and the block's `body2`
body from its parameters. -/
theorem decl2_src {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hne : Scc.Lower.isPrintExt d = false) (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) :
    layoutOk2 p = true ∧ Scc.Lower.countsOk2 p = true ∧ ∃ cx2, body2 cx2 [] [] (params2 d) d.body = true := by
  simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hds⟩, hsp⟩, _⟩, hlay⟩, _⟩, _⟩, hcnt⟩, _⟩ := hp
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  obtain ⟨cx2, hb, -⟩ := body_decl2 hE hne hnl (setup_simple hds hsp)
  exact ⟨hlay, hcnt, cx2, hb⟩

/-- **`LitPt` at every point of an `Accepted2` block's literal walk.** -/
theorem litPts_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hne : Scc.Lower.isPrintExt d = false) (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) :
    ∀ q ∈ litWalk2 p ((params2 d).map (·, shapeOf d.argTy)) d.body, LitPt q := by
  obtain ⟨hlay, -, cx2, hb⟩ := decl2_src hp hd hne hnl
  refine litPts_walk cx2 d.body [] [] _ _ hb (fun y hy => ?_) (fun b n h => by cases h)
    (fun q hq => List.all_eq_true.mp hlay q (List.mem_flatMap.2 ⟨d, hd, hq⟩))
  by_cases hu : d.argTy = .unit
  · simp [params2, hu] at hy
  · have hp2 : params2 d = [d.arg] := by simp [params2, hu]
    rw [hp2] at hy ⊢
    simp only [List.mem_singleton] at hy
    subst hy
    simp

/-- **An `Accepted2` block is `countsB`** from its parameter (`countsOk2`). -/
theorem countsB_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hne : Scc.Lower.isPrintExt d = false) (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) :
    Scc.Lower.countsB p [] [] ((params2 d).map (·, shapeOf d.argTy)) d.body = true :=
  countsOk2_decl (decl2_src hp hd hne hnl).2.1 hd hne hnl

/-- **An `Accepted2` block's lane stores are in range** (`xchgsB`). -/
theorem xchgsB_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hne : Scc.Lower.isPrintExt d = false) (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) :
    xchgsB [] [] d.body = true := by
  obtain ⟨-, -, cx2, hb⟩ := decl2_src hp hd hne hnl
  exact xchgsB_of_body2 d.body [] [] (params2 d) (fun _ _ h => by cases h) hb

end Spike.Lib.LowerNode
