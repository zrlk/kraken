/-
**The split leaves every compiled block of an `Accepted2` program as it
is** (ISA-neutral): the premises of `splitFuncMarks_func2`
(`Spike/Lib/LowerSplitC2.lean`) from `Accepted2`.

- `flatL_erase_length`: dropping the literals keeps a layout's words.
- `retsLe_of_walk`: the closed form's `ret`s are of at most `rw` words when
  every `ret` on the lowering's walk (`lowerEnvs2`) is.
- `retLen_ofAccepted2`: on the walk of a compiled block, a `ret`'s words are
  its block's result words (`callsOk2`, as `retOne_ofAccepted2`).
- `extCallsOk_of_body2`: a `body2` body whose ordinary callees are not
  externs calls an extern only as `print` with the extern.
- `blocksOk2_of_accepted2`, `blocksOk2_decl`: `blocksOk2`'s bound at a
  compiled block.
- `splitFuncMarks_accepted2`: so the split leaves a compiled block's
  lowering and its trace as they are.
-/
import Spike.Lib.LowerSplitC2
import Spike.Lib.LowerShapeC2Some
import Spike.Lib.LowerShapeC2Walk
import Spike.Lib.Src.Walk2Of

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerNode (lowerEnvs2 flatL IsReg)

theorem flatL_erase_length : ∀ L : LitV, (flatL L.erase).length = (flatL L).length
  | .nil => rfl
  | .leaf _ => rfl
  | .loc => rfl
  | .node l r => by simp [LitV.erase, flatL, flatL_erase_length l, flatL_erase_length r]

/-- **`RetsLe` from the walk**: without the depth counter, the closed form's
`ret`s are of at most `rw` words when every `ret` on the walk is. -/
theorem retsLe_of_walk (cx : Scc.Lower.Ctx) (hf : cx.frames = none) (rw : Nat) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res2), lowerC2 cx env n l k e = some r →
      (∀ q ∈ lowerEnvs2 cx env n e, ∀ a, q.1 = .ret a → ∀ t ws, atomV q.2.1 a = some (t, ws) → ws.length ≤ rw) →
        RetsLe rw r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr hW
    by_cases hp : isPure op = true
    · obtain ⟨t, ws, sc, hq, r', hpo, hm, hr', rfl⟩ := lowerC2_pure_inv hp hr
      exact ih _ _ _ _ r' hr' (walk2_tail_pure hp hpo hm hW)
    cases op with
    | add a b =>
      obtain ⟨_, _, _, _, r', ha, hb, hr', rfl⟩ := lowerC2_add_inv hr
      exact ih _ _ _ _ r' hr' (walk2_tail_add ha hb hW)
    | sub a b =>
      obtain ⟨_, _, _, _, r', ha, hb, hr', rfl⟩ := lowerC2_sub_inv hr
      exact ih _ _ _ _ r' hr' (walk2_tail_sub ha hb hW)
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hdg, hrt, ha, hr', rfl⟩
          | ⟨xe, dg, t, b, o, m, c, r', hx, hdg, hrt, ha, hr', rfl⟩
      · exact ih _ _ _ _ r' hr' (walk2_tail_call hf hx hdg hrt ha hW)
      · exact ih _ _ _ _ r' hr' (walk2_tail_print hx hdg hrt ha hW)
    | newBuf c τ =>
      obtain ⟨tk, kv, en, em, h, sc, hq, r', ha, hc, hh, hw, hm, hr', rfl⟩ := lowerC2_newBuf_inv hr
      exact ih _ _ _ _ r' hr' (walk2_tail_newBuf ha hc hh hw hm hW)
    | xchgAt b j v =>
      obtain ⟨t, bw, rb, o, tj, iv, μ, u, nu, mu, tv, w, s1, sc, hq, r', hb, hrf, hj, he, hg, hv, hs, hm, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      exact ih _ _ _ _ r' hr' (walk2_tail_xchg hb hrf hj he hg hv hs hm hW)
    | _ => first | exact absurd rfl hp | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r hr hW
    obtain ⟨t, ws, u, w, nu, ha, hpr, hv, hr'⟩ := lowerC2_split_inv hr
    exact ih _ _ _ _ r hr' (walk2_tail_split ha hpr hv hW)
  | unpack a i x e ih =>
    intro env n l k r hr hW
    obtain ⟨b, ws, ha, hr'⟩ := lowerC2_unpack_inv hr
    exact ih _ _ _ _ r hr' (walk2_tail_unpack ha hW)
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr hW
    obtain ⟨ta, pa, tb, pb, ry, rn, ha, hb, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    have hRy := ihy _ _ _ _ ry hy (walk2_tail_yes ha hb hW)
    have hRn := ihn _ _ _ _ rn hn (walk2_tail_no hf ha hb hy hW)
    unfold RetsLe
    refine ⟨fun ws h => by simp at h, ?_⟩
    intro bl hbl ws h
    simp only [List.mem_cons, List.mem_append] at hbl
    rcases hbl with (rfl | hbl) | rfl | hbl
    · exact hRy.1 ws h
    · exact hRy.2 bl hbl ws h
    · exact hRn.1 ws h
    · exact hRn.2 bl hbl ws h
  | ret a =>
    intro env n l k r hr hW
    obtain ⟨t, ws, ha, rfl⟩ := lowerC2_ret_inv hr
    unfold RetsLe
    refine ⟨fun ws' h => ?_, fun b hb => by simp at hb⟩
    simp only [Term.ret.injEq] at h
    subst h
    exact hW _ (Spike.Lib.LowerNode.mem_lowerEnvs2_head cx env n _) a rfl t ws ha
  | _ => intro env n l k r hr; simp [lowerC2] at hr

/-- **A `ret` on the walk of a compiled block of an `Accepted2` program is
of its result's words** (`callsOk2`: the `ret`'s layout is the result's). -/
theorem retLen_ofAccepted2 {p : Prog} (hp : Accepted2 p = true) {cx : Scc.Lower.Ctx} (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : isPrintExt d = false) (hnl : ¬(hasPrint p = true ∧ d.name = "printL"))
    {nr : Nat} (hnr : Scc.Obj.valWords d.retTy = some nr)
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, ∀ a, q.1 = .ret a → ∀ t ws,
      atomV q.2.1 a = some (t, ws) → ws.length ≤ nr := by
  intro q hq a he t ws hv
  obtain ⟨hcx, hlay, href, hcalls, cx2, hb, harg⟩ := Spike.Lib.LowerNode.decl2_setup hp hprog hext hd hne hnl
  obtain ⟨lits, _, _, scope, hm, hR, hb', _, _, _, hLi⟩ :=
    Spike.Lib.LowerNode.walk_relB_decl hlay href hcx hd hb harg hps hpl n q hq
  have hs := (Spike.Lib.LowerNode.callsOk2_parts hcalls hd hm).2 a he
  rw [he] at hb'
  simp only [body2] at hb'
  obtain ⟨t', ws', hv', hi⟩ := Spike.Lib.LowerNode.atomV_inv hR hLi hb'
  rw [hv] at hv'
  cases hv'
  have hl := hi.2.length
  have hw := Spike.Lib.LowerNode.valWords_compat
    (Spike.Lib.LowerNode.compat_shapeOf d.retTy 0 0 (hcx.ret d hd) (Spike.Lib.LowerNode.slots_of_valWords hnr))
  rw [hnr, ← hs, flatL_erase_length] at hw
  have := Option.some.inj hw
  simp only at this
  omega

/-- **The extern calls of a `body2` body** whose ordinary callees
(`callee2`) are not externs: only `print`, with the extern. -/
theorem extCallsOk_of_body2 (cx2 : Cx2) (isExt : String → Bool)
    (hU : ∀ g, callee2 cx2 g = true → isExt g = false) :
    ∀ (e : Expr) (cs bufs : List (String × Nat)) (scope : List String), body2 cx2 cs bufs scope e = true →
      extCallsOk isExt cx2.ext e = true := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro cs bufs scope hb
    cases op with
    | call g is a ts =>
      by_cases h : (cx2.ext && g == "print") = true
      · simp only [body2, h, ite_true, Bool.and_eq_true] at hb
        simp only [extCallsOk, h, Bool.or_true, Bool.true_and]
        exact ih _ _ _ hb.2
      · rw [Bool.not_eq_true] at h
        simp only [body2, h, Bool.false_eq_true, ite_false, Bool.and_eq_true] at hb
        simp only [extCallsOk, h, hU g hb.1.1.1.1, Bool.not_false, Bool.true_or, Bool.true_and]
        exact ih _ _ _ hb.2
    | newBuf c τ =>
      simp only [body2, Bool.and_eq_true] at hb
      obtain ⟨-, hm⟩ := hb
      split at hm
      · simp only [Bool.and_eq_true] at hm
        exact ih _ _ _ hm.2
      · cases hm
    | xchgAt b i v =>
      cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb
      exact ih _ _ _ hb.2
    | _ =>
      first
      | (simp [body2] at hb; done)
      | (simp only [body2, Bool.and_eq_true] at hb; exact ih _ _ _ hb.2)
  | split a x y e ih =>
    intro cs bufs scope hb
    simp only [body2, Bool.and_eq_true] at hb
    exact ih _ _ _ hb.2
  | unpack a i x e ih =>
    intro cs bufs scope hb
    simp only [body2, Bool.and_eq_true] at hb
    exact ih _ _ _ hb.2
  | ifeq a b yes no ihy ihn =>
    intro cs bufs scope hb
    simp only [body2, Bool.and_eq_true] at hb
    simp only [extCallsOk, Bool.and_eq_true]
    exact ⟨ihy _ _ _ hb.1.2, ihn _ _ _ hb.2⟩
  | _ => intro cs bufs scope hb; first | rfl | simp [body2] at hb

/-- `blocksOk2`, the first conjunct of `Accepted2`. -/
theorem blocksOk2_of_accepted2 {p : Prog} (hp : Accepted2 p = true) : blocksOk2 p = true := by
  simp only [Accepted2, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, _hnodup⟩, _hmain⟩, _hdecls⟩, _hsetup⟩, _himms⟩, _hlay⟩, _href⟩, _hcalls⟩, _hcounts⟩,
    _harg⟩ := hp
  exact hb

/-- **`blocksOk2`'s bound at a code block** of an `Accepted2` program (not
the extern or its loop). -/
theorem blocksOk2_decl {p : Prog} (hp : Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hne : isPrintExt d = false) (hnl : ¬(hasPrint p = true ∧ d.name = "printL")) :
    (decide ((Scc.Obj.valWords d.argTy).getD 0 + openW2 (hasPrint p) ((Scc.Obj.valWords d.retTy).getD 0) d.body ≤
        maxBlockLen) && decide (armsW2 (hasPrint p) ((Scc.Obj.valWords d.retTy).getD 0) d.body ≤ maxBlockLen))
      = true := by
  have h := List.all_eq_true.1 (blocksOk2_of_accepted2 hp) d hd
  have hnl' : (hasPrint p && d.name == "printL") = false := by
    cases hpr : hasPrint p <;> simp_all
  rw [hne, hnl', Bool.false_or, Bool.false_or] at h
  exact h

/-- **The split leaves a compiled block of an `Accepted2` program as it
is**: its lowering and trace (`splitFuncMarks_func2`, its premises from
`Accepted2`). -/
theorem splitFuncMarks_accepted2 {p : Prog} (hp : Accepted2 p = true) {d : Decl} (hd : d ∈ p)
    (hc : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false) {obj : Scc.ObjLayout}
    {fm : Func × Array (Node × Point)} (hl : lowerDeclMarks p (Scc.Frontend.externs p) d obj = .ok fm) :
    splitFuncMarks fm = fm := by
  obtain ⟨na, nr, sc, hq, r, hna, ha, hnr, hr, hm, hlc⟩ := accepted2_lowerC2 hp hd hc hl
  have h2 := lowerDeclMarks_lowerC2 p (Scc.Frontend.externs p) obj hna ha hnr hr hm hlc
  rw [hl] at h2
  cases h2
  have hn := Spike.Lib.LowerNode.nodup_of_accepted2 hp
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp
    exact hp.1.1.1.1.1.1.1.2
  have hsp : setupPresent p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp
    exact hp.1.1.1.1.1.1.2
  have hne := Spike.Lib.LowerNode.isPrintExt_false_of_compiled hd hc
  have hnl : ¬(hasPrint p = true ∧ d.name = "printL") := by
    rintro ⟨hpr, hnm⟩
    obtain ⟨E, hE⟩ := Spike.Lib.LowerNode.decl2_of_decls2 hds d hd
    unfold decl2 at hE
    simp only [hne, hpr, hnm, Bool.false_eq_true, ↓reduceIte, Bool.true_and, beq_self_eq_true] at hE
    have hx : Scc.Frontend.externOf d = some .print := by
      unfold Scc.Frontend.externOf
      simp [hnm, hE]
    have : ((Scc.Frontend.externs p).any (·.1 == d.name)) = true :=
      List.any_eq_true.2 ⟨(d.name, .print), List.mem_filterMap.2 ⟨d, hd, by rw [hx]; rfl⟩, by simp⟩
    rw [hc] at this; cases this
  obtain ⟨E, hE, hEn, hEm⟩ := decl2_nodup hds hn List.nodup_nil (by simp) d hd
  obtain ⟨cx2, hb, -, hex, hext, hearl, -⟩ :=
    body_cx2 hE hEn hne hnl (Spike.Lib.LowerNode.setup_simple hds hsp)
  have hearl' : ∀ g ∈ cx2.earlier, g ∈ p.map (·.name) := fun g hg => by
    rcases hEm g (hearl g hg) with h | h
    · cases h
    · exact h
  have hx : extCallsOk (fun g => ((Scc.Frontend.externs p).find? (·.1 == g)).isSome) (hasPrint p) d.body = true := by
    rw [← hext]
    exact extCallsOk_of_body2 cx2 _ (fun g hg => by simp [(callee_plain hp hex hearl' hg).1]) d.body [] [] _ hb
  have hps : ∀ o ∈ (paramsR d na).map Operand.reg, IsReg o := fun o ho => by
    simp only [List.mem_map] at ho; obtain ⟨r, -, rfl⟩ := ho; exact ⟨r, rfl⟩
  have hpl : Scc.Obj.valWords d.argTy = some ((paramsR d na).map Operand.reg).length := by
    simp [hna, paramsR]
  have hR : RetsLe nr r :=
    retsLe_of_walk { prog := p, externs := Scc.Frontend.externs p, fn := d.name, obj } rfl nr d.body _ 0 "entry" 0
      r hlc (retLen_ofAccepted2 hp rfl (Spike.Lib.LowerNode.externs_unit hn) hd hne hnl hnr hps hpl 0)
  exact splitFuncMarks_func2 { prog := p, externs := Scc.Frontend.externs p, fn := d.name, obj } (hasPrint p)
    _ sc hq hna hnr (blocksOk2_decl hp hd hne hnl) hx hlc hR

end Spike.Lib.LowerShape
