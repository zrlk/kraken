import Scc.Lower.InvProg
import Scc.Lower.Inv1

/-!
# The whole-program lowering of one-block `Accepted1` programs

The twin of `Scc/Lower/InvProg.lean` for an `Accepted1` program with one
code block (necessarily `main(u : Unit) : Int`, with no earlier code block
to call, so its body is call-free: `let`s of atoms, checked `+`, saturating
`-`, integer `if`, `ret`). The lowering `lowerWithMarks` gives the runtime
functions followed by exactly one user function, `func1 main [] r` for the
body's closed form `r` (`Scc/Lower/Inv1.lean`), and one placement trace,
`marks1 d r`.

* `accepted1_main`: a one-block `Accepted1` program is `main(Unit) : Int`
  with a call-free body;
* `checkedOf_accepted1main`: its checked program;
* `lowerWithMarks_accepted1main[_ok]`, `lowerIR_accepted1main`: the
  whole-program statements, as for `Accepted0`.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

/-- An `Accepted1` body spawns nothing. -/
theorem spawnedE_body1 (earlier : List String) :
    ∀ (e : Expr) (scope : List String), body1 earlier scope e = true → spawnedE e = [] := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope hb
    cases op <;> simp only [body1, Bool.and_eq_true, reduceCtorEq] at hb <;>
      first
      | (simp only [spawnedE]; exact ih _ hb.2)
      | simp at hb
  | ifeq a b y n ihy ihn =>
    intro scope hb
    simp only [body1, Bool.and_eq_true] at hb
    simp only [spawnedE, ihy _ hb.1.2, ihn _ hb.2, List.append_nil]
  | ret a => intro _ _; rfl
  | _ => intro scope hb; simp [body1] at hb

/-- **A one-block `Accepted1` program** is `main(Unit) : Int` without type
or index parameters, and its body is `Accepted1` with no earlier code block
(so call-free), in the empty scope. -/
theorem accepted1_main {d : Decl} (hd : Accepted1 [d] = true) :
    d.name = "main" ∧ decl1 [] d = true ∧ d.tparams = [] ∧ d.idx = [] ∧ d.argTy = .unit ∧
      d.retTy = .int ∧ body1 [] [] d.body = true := by
  simp only [Accepted1, decls1, List.any_cons, List.any_nil, Bool.or_false, Bool.and_true,
    Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨-, hn⟩, hdl⟩, -⟩ := hd
  have hdl' := hdl
  simp only [decl1, hn, beq_self_eq_true, ite_true, Bool.and_eq_true, beq_iff_eq,
    List.isEmpty_iff] at hdl'
  obtain ⟨⟨⟨⟨ht, hi⟩, hr⟩, ha⟩, hb⟩ := hdl'
  refine ⟨hn, hdl, ht, hi, ha, hr, ?_⟩
  simpa [params1, ha] using hb

/-- **The checked program of a one-block `Accepted1` program**: entry
`main(Unit) : Int`, no externs. -/
theorem checkedOf_accepted1main {d : Decl} (hd : Accepted1 [d] = true) :
    checkedOf [d] = .ok { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } := by
  obtain ⟨hn, -, ht, hi, ha, hr, -⟩ := accepted1_main hd
  simp [checkedOf, Frontend.entryOf, Frontend.externs, externOf_main hn, hn, ht, hi, ha, hr,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- `main`'s parameter registers (a `Unit` parameter has none). -/
theorem params1R_main {d : Decl} (ha : d.argTy = .unit) : params1R d = [] := by
  simp [params1R, ha]

/-- `main`'s environment: its `Unit` parameter, no words. -/
theorem env1_main {d : Decl} (ha : d.argTy = .unit) : env1 d = [(d.arg, .unit, [])] := by
  simp [env1, params1R_main ha, ha]

/-- **The whole-program lowering of a one-block `Accepted1` program**: the
runtime functions, then `func1 main [] r` for the body's closed form `r`; the
trace of `main` is `marks1 d r`. -/
theorem lowerWithMarks_accepted1main (cfg : Config) {d : Decl} (hd : Accepted1 [d] = true)
    (hheap : cfg.layout.heapBytes < 2 ^ 32) {rt : List Func}
    (hrt : rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt) :
    ∃ r, lower1 [(d.arg, .unit, [])] 0 d.body = some r ∧
      lowerWithMarks cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } =
        .ok (progOf cfg.layout rt [func1 (Names.user "main") [] r],
          [(Names.user "main", marks1 d r)]) := by
  obtain ⟨hn, hdl, -, -, ha, -, hbody⟩ := accepted1_main hd
  obtain ⟨r, hr, hl⟩ := lowerDeclMarks_lower1 [d] [] cfg.layout.obj none hdl
  rw [env1_main ha] at hr
  rw [params1R_main ha] at hl
  refine ⟨r, hr, ?_⟩
  have hsp : spawnedE d.body = [] := spawnedE_body1 _ _ _ hbody
  have hh : ¬ (cfg.layout.heapBytes ≥ 2 ^ 32) := by omega
  unfold rtFuncs at hrt
  simp only [lowerWithMarks, hh, ite_false, List.any_nil, Bool.not_false, List.filter_cons_of_pos,
    List.filter_nil, List.mapM_cons, List.mapM_nil, hl, List.flatMap_cons, List.flatMap_nil, hsp,
    List.append_nil, List.eraseDups_nil, hrt, bind, Except.bind, pure, Except.pure, hn]
  rfl

/-- A successful `lowerWithMarks` of a one-block `Accepted1` program is the
one of `lowerWithMarks_accepted1main`. -/
theorem lowerWithMarks_accepted1main_ok (cfg : Config) {d : Decl} (hd : Accepted1 [d] = true)
    {x : IR.Program × List (Sym × Array (Node × Point))}
    (h : lowerWithMarks cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } =
      .ok x) :
    ∃ r rt, lower1 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      x = (progOf cfg.layout rt [func1 (Names.user "main") [] r],
        [(Names.user "main", marks1 d r)]) := by
  have hheap : cfg.layout.heapBytes < 2 ^ 32 := by
    refine Nat.lt_of_not_ge fun hc => ?_
    unfold lowerWithMarks at h
    simp only [hc, ↓reduceIte] at h
    cases h
  cases hrt : rtFuncs cfg.layout ⟨.unit, true⟩ 0 with
  | error e =>
    exfalso
    obtain ⟨hn, hdl, -, -, -, -, hbody⟩ := accepted1_main hd
    obtain ⟨r, -, hl⟩ := lowerDeclMarks_lower1 [d] [] cfg.layout.obj none hdl
    have hsp : spawnedE d.body = [] := spawnedE_body1 _ _ _ hbody
    have hh : ¬ (cfg.layout.heapBytes ≥ 2 ^ 32) := by omega
    unfold rtFuncs at hrt
    simp only [lowerWithMarks, hh, ite_false, List.any_nil, Bool.not_false, List.filter_cons_of_pos,
      List.filter_nil, List.mapM_cons, List.mapM_nil, hl, List.flatMap_cons, List.flatMap_nil, hsp,
      List.append_nil, List.eraseDups_nil, hrt, bind, Except.bind, pure, Except.pure, hn] at h
    cases h
  | ok rt =>
    obtain ⟨r, hr, hl⟩ := lowerWithMarks_accepted1main cfg hd hheap hrt
    rw [hl] at h
    cases h
    exact ⟨r, rt, hr, rfl, rfl⟩

/-- **The lowering `lowerAll` starts from, on a one-block `Accepted1`
program**: the runtime functions, then `func1 main [] r`; the trace of
`main` is `marks1 d r`. -/
theorem lowerIR_accepted1main (cfg : Config) {d : Decl} (hd : Accepted1 [d] = true)
    {l : Lowered} (hl : lowerIR cfg [d] = .ok l) :
    ∃ r rt, lower1 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      l.ir = progOf cfg.layout rt [func1 (Names.user "main") [] r] ∧
      l.marks = [(Names.user "main", marks1 d r)] := by
  unfold lowerIR at hl
  rw [checkedOf_accepted1main hd] at hl
  simp only [bind, Except.bind] at hl
  cases hb : stackBudget cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } with
  | error e => rw [hb] at hl; cases hl
  | ok b =>
    rw [hb] at hl
    cases hw : lowerWithMarks cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } with
    | error e => simp only [hw] at hl; cases hl
    | ok x =>
      obtain ⟨r, rt, hr, hrt, rfl⟩ := lowerWithMarks_accepted1main_ok cfg hd hw
      simp only [hw] at hl
      cases hl
      exact ⟨r, rt, hr, hrt, rfl, rfl⟩

end Scc.Lower.Inv
