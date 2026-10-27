/-
**Distinct code block symbols from `PlaceOK`** (AArch64): on an
`Accepted1` program whose output passes `PlaceOK`, two code blocks with one
symbol (`Names.user`, which is not injective: `f'` and `f_u27_` are both
`wc_f_u27_`) are one code block, so a call names its callee exactly.

- `labNumL`, `labNumL_local`: the function index of a context's local label
  `.L<fi>_<f>.<suffix>` (`FnCtx.local`) is its digits after `.L`;
- `labelIdx_of_labelGap0`: a label right after another is at the next index;
- `stackCheck_of_fnPh1`: each code block's function's label is right before
  its stack check (`prologueIn`, A12's `fnOk1`);
- `user_inj_of_placeOK`: a code block's symbol determines its index: the
  first label of the symbol is followed by one stack check label only, whose
  index prefix is the function's;
- `calleeRow_name_of_fnPh1`: `calleeRow_of_fnPh1` with the callee's name,
  for a callee that is a code block's name.
-/
import Spike.Lib.LowerA64.CalleeRow

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.AArch64.Parser
open Scc.Emit.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Rt.A64 (labelIdx labelIdx_spec labelGap)
open Scc.Cert.Code1A64 (ctxOf fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.NeedA64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1 mem_progOf_funcs1)

/-! ## The function index of a local label -/

/-- The digits of a local label after its `.L`: the function index's. -/
def labNumL (l : String) : List Char := (l.toList.drop 2).takeWhile Char.isDigit

/-- **A context's local label carries its function index** (`FnCtx.local`):
`.L<fi>_…`, the index's digits ended by `_`. -/
theorem labNumL_local (c : FnCtx) (suffix : String) : labNumL (c.local suffix) = Nat.toDigits 10 c.fi := by
  have e : (c.local suffix).toList =
      ['.', 'L'] ++ (Nat.toDigits 10 c.fi ++ ('_' :: ((sanitize c.name).toList ++ '.' :: suffix.toList))) := by
    simp [FnCtx.local, FnCtx.prefix, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]
    rfl
  rw [labNumL, e]
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [List.takeWhile_append_of_pos (fun c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)]
  simp

/-- **Local labels of two contexts are distinct** when their function
indices are. -/
theorem local_inj {c c' : FnCtx} {s s' : String} (h : c.local s = c'.local s') : c.fi = c'.fi := by
  have := congrArg labNumL h
  rw [labNumL_local, labNumL_local] at this
  rw [← Nat.ofDigitChars_ten_toDigits (n := c.fi), ← Nat.ofDigitChars_ten_toDigits (n := c'.fi), this]

/-! ## Labels in a row -/

/-- **A label right after another** (`labelGap … 0`) is at the next index. -/
theorem labelIdx_of_labelGap0 {prog : List Directive} {a b : Label} (h : labelGap prog a b 0 = true) :
    ∃ i, labelIdx prog a = some i ∧ labelIdx prog b = some (i + 1) := by
  unfold labelGap at h
  split at h
  · next i j ha hb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨i, ha, by rw [hb, h.1]⟩
  · cases h

/-- **Two labels after one label are one label.** -/
theorem eq_of_labelGap0 {prog : List Directive} {a b b' : Label} (h : labelGap prog a b 0 = true)
    (h' : labelGap prog a b' 0 = true) : b = b' := by
  obtain ⟨i, ha, hb⟩ := labelIdx_of_labelGap0 h
  obtain ⟨i', ha', hb'⟩ := labelIdx_of_labelGap0 h'
  rw [ha] at ha'; cases ha'
  have e1 := (labelIdx_spec hb).1
  have e2 := (labelIdx_spec hb').1
  rw [e1] at e2
  cases e2
  rfl

/-! ## Distinct symbols -/

/-- **Each code block's function's label is right before its stack check**
from `PlaceOK` (`prologueIn`, A12's `fnOk1`), as `fnPh1_ofPlaceOK` numbers
them. -/
theorem stackCheck_of_fnPh1 {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    (j : Nat) (hj : j < p.length) :
    labelGap (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (Scc.Lower.Names.user p[j].name)
      ((ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
        (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) (rs[j]'(hrs.1 ▸ hj)))).local "stack_check")
      0 = true := by
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  have hmem : (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) (rs[j]'(hrs.1 ▸ hj)), rt.length + j) ∈
      (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    rw [hir]
    exact mem_progOf_funcs1 cfg.layout rt hrs j hj
  have hc1 := fnOk1_of_fnCode1Ok hc hmem rfl
  obtain ⟨ps, hps⟩ := spills_of_fnOk1 hc1
  obtain ⟨⟨entry, -, hpro⟩, -⟩ := fnOk1_facts hc1 rfl hps
  simp only [Spike.Lib.A64.Flow.prologueIn, Bool.and_eq_true] at hpro
  exact hpro.1.1.1.1.1

/-- **A code block's symbol determines it** on an `Accepted1` program
whose output passes `PlaceOK` (see the module docstring): two code blocks
with one `Names.user` symbol are at one index. -/
theorem user_inj_of_placeOK {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j j' : Nat} (hj : j < p.length) (hj' : j' < p.length)
    (he : Scc.Lower.Names.user p[j].name = Scc.Lower.Names.user p[j'].name) : j = j' := by
  have h1 := stackCheck_of_fnPh1 h hrs hir j hj
  have h2 := stackCheck_of_fnPh1 h hrs hir j' hj'
  rw [he] at h1
  have := local_inj (eq_of_labelGap0 h1 h2)
  have e : rt.length + j = rt.length + j' := this
  omega

/-- **A call site's rows with the callee's name**: `calleeRow_of_fnPh1` for
a call of `Names.user g` with `g` a code block's name; the callee is the
code block named `g` (by `user_inj_of_placeOK`). -/
theorem calleeRow_name_of_fnPh1 {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {fr : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fr) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) (hgp : g ∈ p.map (·.name)) :
    let tbl := (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧ dg.name = g ∧
      ∃ (a : String) (nd : Nat) (a' : String) (ng : Nat),
        let fd := (ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame
        let fg := (ctxOf ir (rt.length + j') (func1 (Scc.Lower.Names.user dg.name) (params1R dg) rg)).frame
        row? tbl (Scc.Lower.Names.user d.name) = some (a, fd, nd) ∧
        row? tbl (Scc.Lower.Names.user g) = some (a', fg, ng) ∧
        fd ≤ nd ∧ fg ≤ ng ∧ fd + ng ≤ nd := by
  intro tbl ir
  obtain ⟨j', dg, rg, hlt, hdg, hrg, hn, rest⟩ := calleeRow_of_fnPh1 hp h hrs hir hd hr hg
  refine ⟨j', dg, rg, hlt, hdg, hrg, ?_, rest⟩
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hdg
  obtain ⟨dk, hdk, hk⟩ := List.mem_map.mp hgp
  obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hdk
  have : j' = k := user_inj_of_placeOK h hrs hir hj' hk' (by rw [hn, hk])
  subst this
  exact hk

end Spike.Lib.LowerA64
