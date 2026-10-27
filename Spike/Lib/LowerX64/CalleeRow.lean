/-
**A call site's rows of the stack need table from `PlaceOK`** (x86-64),
the twin of `Spike/Lib/LowerA64/CalleeRow.lean`: for a `call` of a code
block in the closed form of an `Accepted1` program's `j`th code block, the
callee is a code block at a smaller index `j'`, and the table has the
caller's and the callee's rows, each with its function's frame (its frame
size `size` plus the saved `%rbp`, `size + 8`) and a need at least that, the
caller's need covering its frame, the return address and the callee's need.

- `needOk1_row`: a function's row from `needOk1`, and the bound on each
  callee with a row;
- `mem_callees_func1`: a `call` of a closed form is one of its function's
  callees (`callees`);
- `needOk1_of_fnPh1`: each code block's function passes `needOk1` at its
  frame's size;
- `calleeRow_of_fnPh1`: the call site's statement;
- `UserInj`, `calleeRow_name_of_fnPh1`: with distinct code block symbols (a
  hypothesis here, derived from `PlaceOK` in `Spike/Lib/LowerX64/UserInj.lean`:
  `userInj_of_placeOK`, `calleeRow_name_of_placeOK`), the callee by its name.

Where x86-64 differs from AArch64: `needOk1` takes the frame's size
(`(frOf ir f).size`), its row's frame is `size + 8`, and a callee's need
comes after the caller's frame and the call's return address
(`size + 8 + 8 + ng ≤ nd`). The callee is named up to its symbol
(`Names.user dg.name = Names.user g`, see `Spike/Lib/LowerCallee1.lean`).
-/
import Spike.Lib.LowerX64.CallSite1
import Spike.Lib.LowerCallee1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (needOk1 callees fnOk1_of_fnCode1Ok fnOk1_facts hasAddChk)
open Scc.Cert.NeedX64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1 mem_progOf_funcs1 decls1_of_accepted1)
open Spike.Lib.LowerCallee (decl1_take mem_earlier_index lowerC_callOk user_ne_abort)

/-- **A function's row from `needOk1`**: its row has its frame `size + 8`
and a need `nf` at least that, and each callee with a row needs at most
`nf` less the frame and the return address. -/
theorem needOk1_row {tbl : List Scc.Cert.NeedX64.Row} {name : String} {size : Nat} {f : Scc.IR.Func}
    (h : needOk1 tbl name size f = true) :
    ∃ a nf, row? tbl name = some (a, size + 8, nf) ∧ size + 8 ≤ nf ∧
      ∀ g ∈ (callees f).1, ∀ a' fg ng, row? tbl g = some (a', fg, ng) → size + 8 + 8 + ng ≤ nf := by
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

/-- **A function with an `addChk` in its closed form has a checked `+`**
(`hasAddChk`). -/
theorem hasAddChk_func1 {name : Scc.IR.Sym} {ps : List Scc.IR.Reg} {r : Res1} {i : Scc.IR.Inst}
    (hi : i ∈ allInsts r) {d : Scc.IR.Reg} {u v : Scc.IR.Operand} (he : i = .addChk d u v) :
    hasAddChk (func1 name ps r) = true := by
  subst he
  simp only [allInsts, List.mem_append, List.mem_flatMap] at hi
  simp only [hasAddChk, func1, List.any_cons, List.any_eq_true, Bool.or_eq_true]
  rcases hi with hi | ⟨b, hb, hi⟩
  · exact .inl ⟨_, hi, rfl⟩
  · exact .inr ⟨b, hb, _, hi, rfl⟩

/-- **Each code block's function passes `needOk1` from `PlaceOK`**, at its
frame's size, as `fnPh1_ofPlaceOK` numbers them. -/
theorem needOk1_of_fnPh1 {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    (j : Nat) (hj : j < p.length) :
    let f := func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) (rs[j]'(hrs.1 ▸ hj))
    needOk1 (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need f.name
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size f = true := by
  intro f
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)
  have hmem : (f, rt.length + j) ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    rw [hir]
    exact mem_progOf_funcs1 cfg.layout rt hrs j hj
  have hmemF : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs := by
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    exact List.mem_of_getElem? hmem
  obtain ⟨n, hn⟩ := mem_starts _ 0 hmemF
  have hc1 := fnOk1_of_fnCode1Ok hc hn rfl
  obtain ⟨zl, zf, z1, z2, zs, zps, ps, hz, hps⟩ := fnOk1_sizes hc1
  exact (fnOk1_facts hc1 rfl hz hps).2.2.2.2.2.2.1

/-- **A call site's rows of the stack need table from `PlaceOK`** (see the
module docstring): on an `Accepted1` program whose lowered IR is the
runtime functions then `funcs1 p rs` (as `fnPh1_ofPlaceOK` gives), a `call`
of `Names.user g` in the closed form `r` of the `j`th code block `d` is
one of the `j'`th code block `dg` (`j' < j`, closed form `rg`, the same
symbol), and the table has `d`'s row with its function's frame `sd + 8` and
need `nd`, and `g`'s with `dg`'s function's frame `sg + 8` and need `ng`
(`sd`, `sg` the frames' sizes): `sd + 8 ≤ nd`, `sg + 8 ≤ ng` and
`sd + 8 + 8 + ng ≤ nd`. -/
theorem calleeRow_of_fnPh1 {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {fr : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fr) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) :
    let tbl := (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧
      Scc.Lower.Names.user dg.name = Scc.Lower.Names.user g ∧
      ∃ (a : String) (nd : Nat) (a' : String) (ng : Nat),
        let sd := (frOf ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size
        let sg := (frOf ir (func1 (Scc.Lower.Names.user dg.name) (params1R dg) rg)).size
        row? tbl (Scc.Lower.Names.user d.name) = some (a, sd + 8, nd) ∧
        row? tbl (Scc.Lower.Names.user g) = some (a', sg + 8, ng) ∧
        sd + 8 ≤ nd ∧ sg + 8 ≤ ng ∧ sd + 8 + 8 + ng ≤ nd := by
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

/-- **Distinct code block symbols** (`Names.user` injective on the program's
code blocks): two code blocks with one symbol are at one index. On x86-64
this follows from `PlaceOK` (the listing's labels are distinct,
`labelsNodupL`) through the emitter's structure: `userInj_of_placeOK` in
`Spike/Lib/LowerX64/UserInj.lean`; here it is a hypothesis
(`calleeRow_name_of_fnPh1`). -/
def UserInj (p : Prog) : Prop :=
  ∀ (j j' : Nat) (hj : j < p.length) (hj' : j' < p.length),
    Scc.Lower.Names.user p[j].name = Scc.Lower.Names.user p[j'].name → j = j'

/-- **A call site's rows with the callee's name**: `calleeRow_of_fnPh1` for
a call of `Names.user g` with `g` a code block's name; the callee is the
code block named `g` (by `UserInj`, a hypothesis here; without it from
`PlaceOK`: `calleeRow_name_of_placeOK`). -/
theorem calleeRow_name_of_fnPh1 {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    (hinj : UserInj p)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {fr : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fr) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) (hgp : g ∈ p.map (·.name)) :
    let tbl := (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧ dg.name = g ∧
      ∃ (a : String) (nd : Nat) (a' : String) (ng : Nat),
        let sd := (frOf ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size
        let sg := (frOf ir (func1 (Scc.Lower.Names.user dg.name) (params1R dg) rg)).size
        row? tbl (Scc.Lower.Names.user d.name) = some (a, sd + 8, nd) ∧
        row? tbl (Scc.Lower.Names.user g) = some (a', sg + 8, ng) ∧
        sd + 8 ≤ nd ∧ sg + 8 ≤ ng ∧ sd + 8 + 8 + ng ≤ nd := by
  intro tbl ir
  obtain ⟨j', dg, rg, hlt, hdg, hrg, hn, rest⟩ := calleeRow_of_fnPh1 hp h hrs hir hd hr hg
  refine ⟨j', dg, rg, hlt, hdg, hrg, ?_, rest⟩
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hdg
  obtain ⟨dk, hdk, hk⟩ := List.mem_map.mp hgp
  obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hdk
  have : j' = k := hinj j' k hj' hk' (by rw [hn, hk])
  subst this
  exact hk

end Spike.Lib.LowerX64
