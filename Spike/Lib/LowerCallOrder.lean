/-
**An `Accepted1` program calls only earlier code blocks** (ISA-neutral,
H7a calls): the order the induction over the program's declarations runs
in (every callee's specification before its caller's).

- `body1_callee_walkC`: at every point of an `Accepted1` body's lowering
  walk (`lowerEnvsC`), a call's callee is one of the `earlier` code blocks
  (`callee1`).
- `decl1_of_decls1`: the `j`th code block of a `decls1` program is `decl1`
  with the names of the code blocks before it as `earlier`.
- `find_earlier`: with distinct names, a code block named among the first
  `j` is found at an index below `j`.
- `callee_earlier`: together, for an `Accepted1` program: a callee at a
  point of the `j`th code block's walk is a code block at an index below
  `j`.
-/
import Scc.Lower.Spec1
import Spike.Lib.LowerEnvImmC1Of

namespace Spike.Lib.LowerCallOrder

open CoreLang CoreTerm
open Scc.Lower (body1 decl1 decls1 callee1 atom1 Accepted1)
open Spike.Lib.LowerNode (lowerEnvsC)

/-- **A call at a point of an `Accepted1` body's walk is to an earlier
code block.** -/
theorem body1_callee_walkC {earlier : List String} (frames : Option Nat) :
    ∀ (e : Expr) (scope : List String) (env : Scc.Lower.Env) (n : Nat), body1 earlier scope e = true →
      ∀ q ∈ lowerEnvsC frames env n e, ∀ x g is a ts e', q.1 = .let_ x (.call g is a ts) e' →
        callee1 earlier g = true := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n hb q hq y g is a0 ts e' hqe
    cases op with
    | atom a =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · split at hq
        · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
        · cases hq
    | add a b =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
    | sub a b =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
    | call g' is' a' ts' =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
        exact hb.1.1.1.1
      · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
    | _ => simp [body1] at hb
  | ifeq a b yes no ihy ihn =>
    intro scope env n hb q hq y g is a' ts e' hqe
    simp only [body1, Bool.and_eq_true] at hb
    simp only [lowerEnvsC, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · cases hqe
    · exact ihy _ _ _ hb.1.2 q hq y g is a' ts e' hqe
    · exact ihn _ _ _ hb.2 q hq y g is a' ts e' hqe
  | ret a =>
    intro scope env n _ q hq y g is a' ts e' hqe
    simp only [lowerEnvsC, List.mem_singleton] at hq
    subst hq
    cases hqe
  | _ => intro scope env n hb; simp [body1] at hb

/-- **A call at a point of an `Accepted1` body's walk is to an earlier
code block, with no index or type arguments.** -/
theorem body1_call_walkC {earlier : List String} (frames : Option Nat) :
    ∀ (e : Expr) (scope : List String) (env : Scc.Lower.Env) (n : Nat), body1 earlier scope e = true →
      ∀ q ∈ lowerEnvsC frames env n e, ∀ x g is a ts e', q.1 = .let_ x (.call g is a ts) e' →
        callee1 earlier g = true ∧ is = [] ∧ ts = [] := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n hb q hq y g is a0 ts e' hqe
    cases op with
    | atom a =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · split at hq
        · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
        · cases hq
    | add a b =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
    | sub a b =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
    | call g' is' a' ts' =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
        exact ⟨hb.1.1.1.1, List.isEmpty_iff.mp hb.1.1.1.2, List.isEmpty_iff.mp hb.1.1.2⟩
      · exact ih _ _ _ hb.2 q hq y g is a0 ts e' hqe
    | _ => simp [body1] at hb
  | ifeq a b yes no ihy ihn =>
    intro scope env n hb q hq y g is a' ts e' hqe
    simp only [body1, Bool.and_eq_true] at hb
    simp only [lowerEnvsC, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · cases hqe
    · exact ihy _ _ _ hb.1.2 q hq y g is a' ts e' hqe
    · exact ihn _ _ _ hb.2 q hq y g is a' ts e' hqe
  | ret a =>
    intro scope env n _ q hq y g is a' ts e' hqe
    simp only [lowerEnvsC, List.mem_singleton] at hq
    subst hq
    cases hqe
  | _ => intro scope env n hb; simp [body1] at hb

/-- **The `j`th code block of a `decls1` program is `decl1`**, the names of
the code blocks before it (latest first) prepended to `earlier`. -/
theorem decl1_of_decls1 :
    ∀ {p : Prog} {earlier : List String} {j : Nat} {d : Decl}, decls1 earlier p = true → p[j]? = some d →
      decl1 (((p.take j).map (·.name)).reverse ++ earlier) d = true
  | [], _, _, _, _, hj => by simp at hj
  | d' :: ds, earlier, 0, d, h, hj => by
    simp only [decls1, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    simpa using h.1
  | d' :: ds, earlier, j + 1, d, h, hj => by
    simp only [decls1, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at hj
    have := decl1_of_decls1 h.2 hj
    simpa [List.take_succ_cons, List.map_cons, List.reverse_cons, List.append_assoc] using this

/-- **A code block named among the first `j` is found below `j`** (the
names distinct). -/
theorem find_earlier {p : Prog} (hnd : (p.map (·.name)).Nodup) {j : Nat} {g : String}
    (hg : g ∈ (p.take j).map (·.name)) {dg : Decl} (hf : p.find? (·.name == g) = some dg) :
    ∃ j' < j, p[j']? = some dg := by
  obtain ⟨d1, hd1, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j1, hj1, e1⟩ := List.getElem_of_mem hd1
  rw [List.getElem_take] at e1
  have hj1p : j1 < p.length := by simp at hj1; omega
  have hj1j : j1 < j := by simp at hj1; omega
  have hdg := List.mem_of_find?_eq_some hf
  have hname : dg.name = d1.name := by simpa using List.find?_some hf
  obtain ⟨j2, hj2, e2⟩ := List.getElem_of_mem hdg
  have hnames : (p.map (·.name))[j2]'(by simpa using hj2) = (p.map (·.name))[j1]'(by simpa using hj1p) := by
    simp [e2, ← e1, hname]
  have hpw := List.pairwise_iff_getElem.mp hnd
  have : j2 = j1 := by
    rcases Nat.lt_trichotomy j2 j1 with h | h | h
    · exact absurd hnames (hpw j2 j1 (by simpa using hj2) (by simpa using hj1p) h)
    · exact h
    · exact absurd hnames.symm (hpw j1 j2 (by simpa using hj1p) (by simpa using hj2) h)
  subst this
  exact ⟨j2, hj1j, by rw [List.getElem?_eq_getElem hj2, e2]⟩

/-- **A callee of an `Accepted1` program's `j`th code block is at an index
below `j`**: at a point of the code block's lowering walk, the callee `g`
(found as `dg`) is the program's `j'`th code block, `j' < j`. -/
theorem callee_earlier {p : Prog} (hp : Accepted1 p = true) {j : Nat} {d : Decl} (hj : p[j]? = some d)
    (frames : Option Nat) (env : Scc.Lower.Env) (n : Nat)
    {q : Expr × Scc.Lower.Env × Nat} (hq : q ∈ lowerEnvsC frames env n d.body)
    {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr} (hqe : q.1 = .let_ x (.call g is a ts) e')
    {dg : Decl} (hf : p.find? (·.name == g) = some dg) :
    ∃ j' < j, p[j']? = some dg := by
  simp only [Accepted1, Bool.and_eq_true, decide_eq_true_eq] at hp
  have hd := decl1_of_decls1 hp.1.2 hj
  simp only [decl1, Bool.and_eq_true] at hd
  have hc := body1_callee_walkC frames d.body _ env n hd.2 q hq x g is a ts e' hqe
  simp only [callee1, Bool.and_eq_true, List.contains_iff_mem, List.append_nil] at hc
  exact find_earlier hp.1.1.1 (by simpa using hc.1) hf

/-- **A `ret` at a point of an `Accepted1` body's walk is of one word**
(the body's free variables bound to scalar words): the premise `RetOne` of
`bodyC_segS` on both ISAs. -/
theorem walkC_retOne {earlier : List String} (frames : Option Nat) :
    ∀ (e : Expr) (scope : List String) (env : Scc.Lower.Env) (n : Nat), body1 earlier scope e = true →
      Scc.Lower.Inv.EnvScalar scope env → ∀ q ∈ lowerEnvsC frames env n e,
        ∀ a, q.1 = .ret a → ∃ t w, Scc.Lower.Inv.atomV q.2.1 a = some (t, [w]) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n hb h q hq a0 hqe
    cases op with
    | atom a =>
      simp only [body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨t, w, ha, ht⟩ := Scc.Lower.Inv.atomV_of_atom0 hb.1 h
      simp only [lowerEnvsC, List.mem_cons, ha] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 (Scc.Lower.Inv.envScalar_cons h x w ht) q hq a0 hqe
    | add a b =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 (Scc.Lower.Inv.envScalar_cons h x _ rfl) q hq a0 hqe
    | sub a b =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 (Scc.Lower.Inv.envScalar_cons h x _ rfl) q hq a0 hqe
    | call g is a ts =>
      simp only [body1, Bool.and_eq_true] at hb
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · exact ih _ _ _ hb.2 (Scc.Lower.Inv.envScalar_cons h x _ rfl) q hq a0 hqe
    | _ => simp [body1] at hb
  | ifeq a b yes no ihy ihn =>
    intro scope env n hb h q hq a0 hqe
    simp only [body1, Bool.and_eq_true] at hb
    simp only [lowerEnvsC, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · cases hqe
    · exact ihy _ _ _ hb.1.2 h q hq a0 hqe
    · exact ihn _ _ _ hb.2 h q hq a0 hqe
  | ret a =>
    intro scope env n hb h q hq a0 hqe
    simp only [lowerEnvsC, List.mem_singleton] at hq
    subst hq
    cases hqe
    obtain ⟨t, w, ha, -⟩ := Scc.Lower.Inv.atomV_of_atom0 (by simpa [body1, Scc.Lower.atom1] using hb) h
    exact ⟨t, w, ha⟩
  | _ => intro scope env n hb; simp [body1] at hb

/-- **`g` is called at a point of the lowering walk of `e`** (from the
environment `env` and counter `n`). -/
def CallIn (frames : Option Nat) (env : Scc.Lower.Env) (n : Nat) (e : Expr) (g : String) : Prop :=
  ∃ q ∈ lowerEnvsC frames env n e, ∃ x is a ts e', q.1 = .let_ x (.call g is a ts) e'

/-- **Specifications by the call order**: for an `Accepted1` program, a
specification `Spec` of every code block follows from the step `hstep`
giving the `j`th code block's from those of its callees (each called at a
point of its walk from `framesOf j d`, `envOf j d`, `nOf j d`, found by `find?`, at its own
index). By strong induction on the index, `callee_earlier`. -/
theorem specs_of_callOrder {p : Prog} (hp : Accepted1 p = true) (framesOf : Nat → Decl → Option Nat)
    (envOf : Nat → Decl → Scc.Lower.Env) (nOf : Nat → Decl → Nat) {Spec : Nat → Decl → Prop}
    (hstep : ∀ j d, p[j]? = some d →
      (∀ g dg, CallIn (framesOf j d) (envOf j d) (nOf j d) d.body g → p.find? (·.name == g) = some dg →
        ∃ j', p[j']? = some dg ∧ Spec j' dg) → Spec j d) :
    ∀ j d, p[j]? = some d → Spec j d := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro d hd
    refine hstep j d hd fun g dg ⟨q, hq, x, is, a, ts, e', hqe⟩ hf => ?_
    obtain ⟨j', hj', hd'⟩ := callee_earlier hp hd _ _ _ hq hqe hf
    exact ⟨j', hd', ih j' hj' dg hd'⟩

/-- **`specs_of_callOrder` with the callee's index**: the step sees each
callee's spec at an index `j' < j` (`callee_earlier`), so a spec may carry a
bound decreasing along the calls (e.g. a call depth below `p.length - j`). -/
theorem specs_of_callOrderLt {p : Prog} (hp : Accepted1 p = true) (framesOf : Nat → Decl → Option Nat)
    (envOf : Nat → Decl → Scc.Lower.Env) (nOf : Nat → Decl → Nat) {Spec : Nat → Decl → Prop}
    (hstep : ∀ j d, p[j]? = some d →
      (∀ g dg, CallIn (framesOf j d) (envOf j d) (nOf j d) d.body g → p.find? (·.name == g) = some dg →
        ∃ j', j' < j ∧ p[j']? = some dg ∧ Spec j' dg) → Spec j d) :
    ∀ j d, p[j]? = some d → Spec j d := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro d hd
    refine hstep j d hd fun g dg ⟨q, hq, x, is, a, ts, e', hqe⟩ hf => ?_
    obtain ⟨j', hj', hd'⟩ := callee_earlier hp hd _ _ _ hq hqe hf
    exact ⟨j', hj', hd', ih j' hj' dg hd'⟩

end Spike.Lib.LowerCallOrder
