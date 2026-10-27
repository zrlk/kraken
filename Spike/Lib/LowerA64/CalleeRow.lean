/-
**A call site's rows of the stack need table from `PlaceOK`** (AArch64):
for a `call` of a code block in the closed form of an `Accepted1`
program's `j`th code block, the callee is a code block at a smaller index
`j'`, and the table has the caller's and the callee's rows, each with its
function's frame and a need at least that frame, the caller's need
covering its frame plus the callee's need.

- `needOk1_row`: a function's row from `needOk1`, and the bound on each
  callee with a row;
- `mem_callees_func1`: a `call` of a closed form is one of its function's
  callees (`callees`);
- `needOk1_of_fnPh1`: each code block's function passes `needOk1` at its
  context's frame;
- `calleeRow_of_fnPh1`: the call site's statement.

The callee is named up to its symbol (`Names.user dg.name = Names.user g`,
see `Spike/Lib/LowerCallee1.lean`).
-/
import Spike.Lib.LowerA64.CallSite1
import Spike.Lib.LowerCallee1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (needOk1 callees ctxOf fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.NeedA64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1 mem_progOf_funcs1 decls1_of_accepted1)
open Spike.Lib.LowerCallee (decl1_take mem_earlier_index lowerC_callOk user_ne_abort)

/-- **A function's row from `needOk1`**: its row has its frame and a need
`nf` at least that frame, and each callee with a row needs at most `nf`
less the frame. -/
theorem needOk1_row {tbl : List Scc.Cert.NeedA64.Row} {name : String} {frame : Nat} {f : Scc.IR.Func}
    (h : needOk1 tbl name frame f = true) :
    ∃ a nf, row? tbl name = some (a, frame, nf) ∧ frame ≤ nf ∧
      ∀ g ∈ (callees f).1, ∀ a' fg ng, row? tbl g = some (a', fg, ng) → frame + ng ≤ nf := by
  cases hrow : row? tbl name with
  | none => simp [needOk1, hrow] at h
  | some row =>
    obtain ⟨a, fr, nf⟩ := row
    simp only [needOk1, hrow, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨rfl, hle⟩, hc⟩, -⟩ := h
    refine ⟨a, nf, rfl, hle, fun g hg a' fg ng hg' => ?_⟩
    have := hc g hg
    rw [hg'] at this
    simpa using this

/-- **A `call` of a closed form is a callee of its function** (`callees`). -/
theorem mem_callees_func1 {name : Scc.IR.Sym} {ps : List Scc.IR.Reg} {r : Res1} {ds : List Scc.IR.Reg}
    {g : Scc.IR.Sym} {ws : List Scc.IR.Operand} (h : Scc.IR.Inst.call ds g ws ∈ allInsts r) :
    g ∈ (callees (func1 name ps r)).1 := by
  simp only [allInsts, List.mem_append, List.mem_flatMap] at h
  simp only [callees, func1, List.flatMap_cons, List.mem_append, List.mem_flatMap, List.mem_filterMap]
  rcases h with h | ⟨b, hb, h⟩
  · exact .inl ⟨_, h, rfl⟩
  · exact .inr ⟨b, hb, _, h, rfl⟩

/-- **Each code block's function passes `needOk1` from `PlaceOK`**, at its
context's frame, as `fnPh1_ofPlaceOK` numbers them. -/
theorem needOk1_of_fnPh1 {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    (j : Nat) (hj : j < p.length) :
    let f := func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) (rs[j]'(hrs.1 ▸ hj))
    needOk1 (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need f.name
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j) f).frame f = true := by
  intro f
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  have hmem : (f, rt.length + j) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    rw [hir]
    exact mem_progOf_funcs1 cfg.layout rt hrs j hj
  have hc1 := fnOk1_of_fnCode1Ok hc hmem rfl
  obtain ⟨ps, hps⟩ := spills_of_fnOk1 hc1
  exact (fnOk1_facts hc1 rfl hps).2.2.2.2.2.1

/-- **A call site's rows of the stack need table from `PlaceOK`** (see the
module docstring): on an `Accepted1` program whose lowered IR is the
runtime functions then `funcs1 p rs` (as `fnPh1_ofPlaceOK` gives), a `call`
of `Names.user g` in the closed form `r` of the `j`th code block `d` is
one of the `j'`th code block `dg` (`j' < j`, closed form `rg`, the same
symbol), and the table has `d`'s row with its function's frame `fd` and
need `nd`, and `g`'s with `dg`'s function's frame `fg` and need `ng`:
`fd ≤ nd`, `fg ≤ ng` and `fd + ng ≤ nd`. -/
theorem calleeRow_of_fnPh1 {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {fr : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fr) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) :
    let tbl := (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
    let ir := (Scc.Lower.A64.lowerAll cfg p).low.ir
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧
      Scc.Lower.Names.user dg.name = Scc.Lower.Names.user g ∧
      ∃ (a : String) (nd : Nat) (a' : String) (ng : Nat),
        let fd := (ctxOf ir (rt.length + j) (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame
        let fg := (ctxOf ir (rt.length + j') (func1 (Scc.Lower.Names.user dg.name) (params1R dg) rg)).frame
        row? tbl (Scc.Lower.Names.user d.name) = some (a, fd, nd) ∧
        row? tbl (Scc.Lower.Names.user g) = some (a', fg, ng) ∧
        fd ≤ nd ∧ fg ≤ ng ∧ fd + ng ≤ nd := by
  intro tbl ir
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  -- the callee is a code block before the caller
  have hd1 := decl1_take p [] (decls1_of_accepted1 hp) j hj
  have hb := (Scc.Lower.Inv.decl1_shape hd1).2.2
  rcases lowerC_callOk _ _ _ _ _ _ _ _ (hrs.get j hj) hb _ hg ds _ ws rfl with he | ⟨g0, hg0, he⟩
  · exact absurd he (user_ne_abort g)
  obtain ⟨j', hj', hlt, hn⟩ := mem_earlier_index hg0
  have hn' : Scc.Lower.Names.user p[j'].name = Scc.Lower.Names.user g := by rw [hn, he]
  -- the rows
  obtain ⟨a, nd, hrd, hled, hcd⟩ := needOk1_row (needOk1_of_fnPh1 h hrs hir j hj)
  obtain ⟨a', ng, hrg, hleg, -⟩ := needOk1_row (needOk1_of_fnPh1 h hrs hir j' hj')
  refine ⟨j', p[j'], rs[j']'(hrs.1 ▸ hj'), hlt, by simp [hj'], by simp [hrs.1, hj'], hn', a, nd, a', ng,
    hrd, ?_, hled, hleg, ?_⟩
  · rw [← hn']; exact hrg
  · exact hcd _ (mem_callees_func1 hg) a' _ ng (by rw [← hn']; exact hrg)

end Spike.Lib.LowerA64
