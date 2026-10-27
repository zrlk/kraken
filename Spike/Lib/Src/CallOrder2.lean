/-
**The call order of an `Accepted2` program** (ISA-neutral): a plain call
on a compiled block's lowering walk names a compiled block earlier in
`compiled2 p`.

- `TailOf`, `lowerEnvs2_tail`: the terms still to lower at the points of a
  body (its `let`, pair split and unpack bodies, both branches of an `if`),
  every point of the lowering walk `lowerEnvs2` one;
- `body2_tail`, `body2_callT`, `body2_call`: at a call at such a term (on
  the walk) of an `Accepted2` body, `body2`'s call check: the output
  extern's name (with the extern) or an ordinary callee (`callee2`);
- `decl2_of_split`: the `k`th block of a `decls2` program is `decl2` with
  the names of the blocks before it;
- `callOrder2T`, `callOrder2`: at a call (a `TailOf` of a compiled
  block's body, or a point of its walk from any environment and counter)
  of a block not among the frontend's externs, the block it names is
  compiled and earlier in `compiled2 p`.
-/
import Spike.Lib.LowerProgC2Core
import Spike.Lib.Src.LowerEnvImm2Of
import Spike.Lib.Src.ExternUnit

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (Cx2 body2 callee2 decl2 decls2 main2 setup2 plain2 reserved hasPrint isPrintExt Accepted2 setupOf)

/-- **`t` is a term still to lower at a point of `e`**: `e` itself, or one
at the body of its `let`, pair split or unpack, or at a branch of its
`if` (the points `lowerEnvs2` passes, `lowerEnvs2_tail`). -/
inductive TailOf : Expr → Expr → Prop
  | refl (e : Expr) : TailOf e e
  | let_ {t : Expr} (x : String) (op : Op) {e : Expr} : TailOf t e → TailOf t (.let_ x op e)
  | split {t : Expr} (a : At) (x y : String) {e : Expr} : TailOf t e → TailOf t (.split a x y e)
  | unpack {t : Expr} (a : At) (i x : String) {e : Expr} : TailOf t e → TailOf t (.unpack a i x e)
  | unpackT {t : Expr} (a : At) (α x : String) {e : Expr} : TailOf t e → TailOf t (.unpackT a α x e)
  | yes {t : Expr} (a b : At) {yes : Expr} (no : Expr) : TailOf t yes → TailOf t (.ifeq a b yes no)
  | no {t : Expr} (a b : At) (yes : Expr) {no : Expr} : TailOf t no → TailOf t (.ifeq a b yes no)

/-- **Every point of the lowering walk is a `TailOf` the body.** -/
theorem lowerEnvs2_tail {cx : Scc.Lower.Ctx} :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat), ∀ q ∈ lowerEnvs2 cx env n e, TailOf q.1 e := by
  intro e
  induction e with
  | let_ y op e ih =>
    intro env n q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .refl _
    · revert hq; split
      · intro hq; exact .let_ _ _ (ih _ _ q hq)
      · simp
  | split a y z e ih =>
    intro env n q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .refl _
    · revert hq; split
      · intro hq; exact .split _ _ _ (ih _ _ q hq)
      · simp
  | unpack a i y e ih =>
    intro env n q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .refl _
    · revert hq; split
      · intro hq; exact .unpack _ _ _ (ih _ _ q hq)
      · simp
  | unpackT a α y e ih =>
    intro env n q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .refl _
    · revert hq; split
      · intro hq; exact .unpackT _ _ _ (ih _ _ q hq)
      · simp
  | ifeq a b yes no ihy ihn =>
    intro env n q hq
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .refl _
    · revert hq; split
      · intro hq
        rcases List.mem_append.1 hq with hq | hq
        · exact .yes _ _ _ (ihy _ _ q hq)
        · revert hq; split
          · intro hq; exact .no _ _ _ (ihn _ _ q hq)
          · simp
      · simp
  | _ =>
    intro env n q hq
    simp only [lowerEnvs2, List.mem_singleton] at hq
    subst hq
    exact .refl _

/-- **A `let`'s body is an `Accepted2` body** (at some known values,
buffers and scope) when the `let` is. -/
theorem body2_let_tail {c2 : Cx2} {cs bufs : List (String × Nat)} {scope : List String} {x : String} {op : Op}
    {e : Expr} (h : body2 c2 cs bufs scope (.let_ x op e) = true) :
    ∃ cs' bufs' scope', body2 c2 cs' bufs' scope' e = true := by
  cases op
  all_goals first
    | (simp [body2] at h; done)
    | skip
  all_goals first
    | (simp only [body2, Bool.and_eq_true] at h; exact ⟨_, _, _, h.2⟩)
    | skip
  · rename_i n τ
    simp only [body2, Bool.and_eq_true] at h
    revert h; split
    · intro h; simp only [Bool.and_eq_true] at h; exact ⟨_, _, _, h.2.2⟩
    · simp
  · rename_i b i v
    revert h
    cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true, false_implies]
    all_goals (intro h; exact ⟨_, _, _, h.2⟩)

/-- **A `TailOf` an `Accepted2` body is one** (at some known values,
buffers and scope). -/
theorem body2_tail {c2 : Cx2} {t e : Expr} (ht : TailOf t e) :
    ∀ {cs bufs : List (String × Nat)} {scope : List String}, body2 c2 cs bufs scope e = true →
      ∃ cs' bufs' scope', body2 c2 cs' bufs' scope' t = true := by
  induction ht with
  | refl => intro cs bufs scope h; exact ⟨_, _, _, h⟩
  | let_ x op _ ih =>
    intro cs bufs scope h
    obtain ⟨_, _, _, h'⟩ := body2_let_tail h
    exact ih h'
  | split a x y _ ih =>
    intro cs bufs scope h; simp only [body2, Bool.and_eq_true] at h; exact ih h.2
  | unpack a i x _ ih =>
    intro cs bufs scope h; simp only [body2, Bool.and_eq_true] at h; exact ih h.2
  | unpackT a α x _ ih =>
    intro cs bufs scope h; simp [body2] at h
  | yes a b no _ ih =>
    intro cs bufs scope h; simp only [body2, Bool.and_eq_true] at h; exact ih h.1.2
  | no a b yes _ ih =>
    intro cs bufs scope h; simp only [body2, Bool.and_eq_true] at h; exact ih h.2

/-- **A call at a `TailOf` an `Accepted2` body passes `body2`'s call
check**: the output extern's name with the extern, or an ordinary callee
(`callee2`). -/
theorem body2_callT {c2 : Cx2} {cs bufs : List (String × Nat)} {scope : List String} {e : Expr}
    {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e') e) (hb : body2 c2 cs bufs scope e = true) :
    (c2.ext && g == "print") = true ∨ callee2 c2 g = true := by
  obtain ⟨_, _, _, hb'⟩ := body2_tail ht hb
  simp only [body2, Bool.and_eq_true] at hb'
  have hc := hb'.1.1
  revert hc
  split
  · rename_i hh; intro _; left; simp only [Bool.and_eq_true]; exact hh
  · intro hc; right; simp only [Bool.and_eq_true] at hc; exact hc.1.1

/-- **A call on the lowering walk of an `Accepted2` body passes `body2`'s
call check**: the output extern's name with the extern, or an ordinary
callee (`callee2`). From any environment and counter, any known values,
buffers and scope; the walk's `if` covers both branches. -/
theorem body2_call {cx : Scc.Lower.Ctx} {c2 : Cx2} :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (cs bufs : List (String × Nat)) (scope : List String),
      body2 c2 cs bufs scope e = true → ∀ q ∈ lowerEnvs2 cx env n e, ∀ x g is a ts e',
        q.1 = .let_ x (.call g is a ts) e' → (c2.ext && g == "print") = true ∨ callee2 c2 g = true := by
  intro e
  induction e with
  | let_ y op e ih =>
    intro env n cs bufs scope hb q hq x g is a ts e' hq1
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp only [Expr.let_.injEq] at hq1
      obtain ⟨rfl, rfl, rfl⟩ := hq1
      simp only [body2, Bool.and_eq_true] at hb
      have hc := hb.1.1
      revert hc
      split
      · rename_i hh; intro _; left; simp only [Bool.and_eq_true]; exact hh
      · intro hc; right; simp only [Bool.and_eq_true] at hc; exact hc.1.1
    · obtain ⟨cs', bufs', scope', hb'⟩ := body2_let_tail hb
      revert hq; split
      · intro hq; exact ih _ _ _ _ _ hb' q hq x g is a ts e' hq1
      · simp
  | split a y z e ih =>
    intro env n cs bufs scope hb q hq x g is a' ts e' hq1
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · cases hq1
    · simp only [body2, Bool.and_eq_true] at hb
      revert hq; split
      · intro hq; exact ih _ _ _ _ _ hb.2 q hq x g is a' ts e' hq1
      · simp
  | unpack a i y e ih =>
    intro env n cs bufs scope hb q hq x g is a' ts e' hq1
    simp only [lowerEnvs2, List.mem_cons] at hq
    rcases hq with rfl | hq
    · cases hq1
    · simp only [body2, Bool.and_eq_true] at hb
      revert hq; split
      · intro hq; exact ih _ _ _ _ _ hb.2 q hq x g is a' ts e' hq1
      · simp
  | unpackT a α y e ih =>
    intro env n cs bufs scope hb
    simp [body2] at hb
  | ifeq a b yes no ihy ihn =>
    intro env n cs bufs scope hb q hq x g is a' ts e' hq1
    simp only [lowerEnvs2, List.mem_cons] at hq
    simp only [body2, Bool.and_eq_true] at hb
    rcases hq with rfl | hq
    · cases hq1
    · revert hq; split
      · intro hq
        rcases List.mem_append.1 hq with hq | hq
        · exact ihy _ _ _ _ _ hb.1.2 q hq x g is a' ts e' hq1
        · revert hq; split
          · intro hq; exact ihn _ _ _ _ _ hb.2 q hq x g is a' ts e' hq1
          · simp
      · simp
  | _ =>
    intro env n cs bufs scope _ q hq x g is a ts e' hq1
    simp only [lowerEnvs2, List.mem_singleton] at hq
    subst hq
    cases hq1

/-- **The `k`th block of a `decls2` program** (`p = A ++ d :: B`) is
`decl2` with the names of the blocks before it, latest first. -/
theorem decl2_of_split {s : Option Ty} {x : Bool} {d : Decl} {B : Prog} :
    ∀ (A : Prog) (E : List String), decls2 E s x (A ++ d :: B) = true →
      decl2 ((A.map (·.name)).reverse ++ E) s x d = true
  | [], E, h => by
    simp only [List.nil_append, decls2, Bool.and_eq_true] at h
    simpa using h.1
  | a :: A, E, h => by
    simp only [List.cons_append, decls2, Bool.and_eq_true] at h
    have := decl2_of_split A (a.name :: E) h.2
    simpa using this

/-- With the extern, `print` is among the frontend's externs. -/
theorem externs_print {p : Prog} (h : hasPrint p = true) :
    ((Scc.Frontend.externs p).find? (·.1 == "print")).isSome = true := by
  obtain ⟨d0, hd0, hp0⟩ := List.any_eq_true.1 h
  have hn : d0.name = "print" := by
    unfold Scc.Lower.isPrintExt at hp0; simp only [Bool.and_eq_true, beq_iff_eq] at hp0; exact hp0.1.1.1.1
  have hm : (d0.name, Scc.Frontend.Extern.print) ∈ Scc.Frontend.externs p :=
    List.mem_filterMap.2 ⟨d0, hd0, by rw [externOf_of_isPrintExt hp0]; rfl⟩
  rw [List.find?_isSome]
  exact ⟨_, hm, by simp [hn]⟩

/-- **The body check of a compiled block**: a block of an `Accepted2`
program not among the frontend's externs (`p = A ++ d :: B`) has an
`Accepted2` body, against the names of `A` (at most) and the program's
extern flag. -/
theorem body2_of_compiled {p : Prog} (hacc : Accepted2 p = true) {A B : Prog} {d : Decl} (hp : p = A ++ d :: B)
    (hc : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false) :
    ∃ (c2 : Cx2) (cs bufs : List (String × Nat)) (scope : List String),
      body2 c2 cs bufs scope d.body = true ∧ c2.ext = hasPrint p ∧
      ∀ g ∈ c2.earlier, g ∈ A.map (·.name) := by
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hacc; exact hacc.1.1.1.1.1.1.1.2
  have hdm : d ∈ p := by rw [hp]; simp
  have hds' : decls2 [] (setupOf p) (hasPrint p) (A ++ d :: B) = true := by rw [← hp]; exact hds
  have hE := decl2_of_split A [] hds'
  simp only [List.append_nil] at hE
  have hpe := isPrintExt_false_of_compiled hdm hc
  have hEs : ∀ g ∈ (A.map (·.name)).reverse, g ∈ A.map (·.name) := fun g h => List.mem_reverse.1 h
  unfold decl2 at hE
  simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hE
  split at hE
  · rename_i hl
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    have hx : Scc.Frontend.externOf d = some .print := by
      unfold Scc.Frontend.externOf
      have : (d.name == "print") = false := by rw [hl.2]; decide
      simp [hl.2, hE]
    have hm : (d.name, Scc.Frontend.Extern.print) ∈ Scc.Frontend.externs p :=
      List.mem_filterMap.2 ⟨d, hdm, by rw [hx]; rfl⟩
    have : ((Scc.Frontend.externs p).any (·.1 == d.name)) = true := List.any_eq_true.2 ⟨_, hm, by simp⟩
    rw [hc] at this; cases this
  split at hE
  · unfold main2 at hE
    simp only [Bool.and_eq_true] at hE
    exact ⟨_, _, _, _, hE.2, rfl, hEs⟩
  split at hE
  · split at hE
    · unfold setup2 at hE
      simp only [Bool.and_eq_true] at hE
      exact ⟨_, _, _, _, hE.2, rfl, fun g h => hEs g (List.erase_subset h)⟩
    · unfold plain2 at hE
      simp only [Bool.and_eq_true] at hE
      exact ⟨_, _, _, _, hE.2, rfl, hEs⟩
  · unfold plain2 at hE
    simp only [Bool.and_eq_true] at hE
    exact ⟨_, _, _, _, hE.2, rfl, hEs⟩

/-- **The call order of an `Accepted2` program**: at a call of `g` at a
`TailOf` the `j`th compiled block's body, `g` not among the frontend's
externs, the block `dg` named `g` is the `j'`th compiled block, `j' < j`. -/
theorem callOrder2T {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e') d.body)
    (hx : (Scc.Frontend.externs p).find? (·.1 == g) = none)
    {dg : Decl} (hf : p.find? (·.name == g) = some dg) :
    ∃ j', j' < j ∧ (compiled2 p)[j']? = some dg := by
  have hnd := nodup_of_accepted2 hacc
  have hjm := List.mem_of_getElem? hj
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 hjm
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hp⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, hext, hE⟩ := body2_of_compiled hacc hp hdc'
  rcases body2_callT ht hb with hpr | hcl
  · exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at hpr
    obtain ⟨hpe, rfl⟩ := hpr
    have := externs_print (hext ▸ hpe)
    rw [hx] at this; cases this
  · -- `g` is among the names before `d`: the block it names is in `A`, compiled.
    simp only [callee2, Scc.Lower.callee1, Bool.and_eq_true, List.contains_iff_mem] at hcl
    obtain ⟨ag, hag, hagn⟩ := List.mem_map.1 (hE g hcl.1.1)
    have hdgm := List.mem_of_find?_eq_some hf
    have hdgn : dg.name = g := by simpa using List.find?_some hf
    have hagp : ag ∈ p := by rw [hp]; simp [hag]
    have hag' : ag = dg := eq_of_name_nodup hnd hagp hdgm (hagn.trans hdgn.symm)
    subst hag'
    have hgc : (!((Scc.Frontend.externs p).any (·.1 == ag.name))) = true := by
      have := List.find?_eq_none.1 hx
      simp only [Bool.not_eq_true', List.any_eq_false]
      intro y hy; have := this y hy; rw [hagn]; simpa using this
    -- the compiled blocks: `A`'s, then `d`, then `B`'s
    have hP : compiled2 p = (A.filter fun d => !((Scc.Frontend.externs p).any (·.1 == d.name))) ++
        d :: (B.filter fun d => !((Scc.Frontend.externs p).any (·.1 == d.name))) := by
      unfold compiled2
      rw [congrArg (List.filter fun d => !((Scc.Frontend.externs p).any (·.1 == d.name))) hp,
        List.filter_append]
      congr 1
      exact List.filter_cons_of_pos hdc
    obtain ⟨j', hj'⟩ := List.getElem?_of_mem
      (List.mem_filter.2 ⟨hag, hgc⟩ : ag ∈ A.filter fun d => !((Scc.Frontend.externs p).any (·.1 == d.name)))
    have hlt : j' < (A.filter fun d => !((Scc.Frontend.externs p).any (·.1 == d.name))).length :=
      (List.getElem?_eq_some_iff.1 hj').1
    have hPn : ((compiled2 p).map (·.name)).Nodup := (List.filter_sublist.map _).nodup hnd
    have hjl : j = (A.filter fun d => !((Scc.Frontend.externs p).any (·.1 == d.name))).length := by
      have hjlt : j < (compiled2 p).length := (List.getElem?_eq_some_iff.1 hj).1
      have h1 : ((compiled2 p).map (·.name))[j]? = some d.name := by simp [hj]
      have h2 : ((compiled2 p).map (·.name))[(A.filter fun d =>
          !((Scc.Frontend.externs p).any (·.1 == d.name))).length]? = some d.name := by
        rw [hP]; simp
      exact (List.Nodup.getElem?_inj (by simpa using hjlt) hPn).1 (h1.trans h2.symm)
    refine ⟨j', hjl ▸ hlt, ?_⟩
    rw [hP, List.getElem?_append_left hlt]
    exact hj'

/-- **`callOrder2T` on the lowering walk**: at a call of `g` on the walk of
the `j`th compiled block's body (from any environment and counter, at a
context whose externs are the frontend's and do not include `g`). -/
theorem callOrder2 {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {cx : Scc.Lower.Ctx} (hcx : cx.externs = Scc.Frontend.externs p)
    {env : Scc.Lower.Env} {n : Nat} {q : Expr × Scc.Lower.Env × Nat} (hq : q ∈ lowerEnvs2 cx env n d.body)
    {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (hq1 : q.1 = .let_ x (.call g is a ts) e') (hx : cx.externs.find? (·.1 == g) = none)
    {dg : Decl} (hf : p.find? (·.name == g) = some dg) :
    ∃ j', j' < j ∧ (compiled2 p)[j']? = some dg :=
  callOrder2T hacc hj (hq1 ▸ lowerEnvs2_tail d.body env n q hq) (hcx ▸ hx) hf

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.callOrder2T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callOrder2T

/-- info: 'Spike.Lib.LowerNode.callOrder2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callOrder2
