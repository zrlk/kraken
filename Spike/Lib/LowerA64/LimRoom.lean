/-
**The stack limit's room of a function and of its callees from `PlaceOK`**
(AArch64), the twin of `Spike/Lib/LowerX64/LimRoom.lean`: the stack check
passes when every value the runtime memory may hold at the thread's limit
word (a predicate `G` on values, `ms.G` at the word) is at most the
function's entry `sp` less its frame. A function's limit room `LimRoomA`
(its stack need table row's need `n` fits between the limit and its entry
`sp`) gives its own check and, at each call site, its callee's limit room
at the callee's entry `sp`.

- `LimRoomA`: the limit room of a function at its entry `sp`;
- `ownLim_of_placeOK`: the room covers the frame `fd` (its row's need is at
  least `fd`, `needOk1`), `v + fd ≤ sp`;
- `calleeLim_of_placeOK`: at a call of `Names.user g` the callee is the code
  block named `g`, with its limit room at its entry `sp'` right below the
  caller's frame (`sp' + fd = sp`), from the call site's rows
  `fd + ng ≤ nd` (`calleeRow_name_of_fnPh1`);
- `mainLim_of_rows`, `mainRow_of_placeOKAt`: `main`'s limit room from
  `scc_rt_main`'s row (frame `sg`, entered at the stack's top `top`), given
  a limit `lim` and a budget with `lim + budget ≤ top`: with the limit
  `stacksA + 4096` and the top `stacksA + 16384`, a budget of at most
  `12288`.

Where AArch64 differs from x86-64: no return address or saved frame pointer
sits between the caller's frame and the callee's entry `sp`, and the room
needs no alignment (the inequalities are on `Nat`).
-/
import Spike.Lib.LowerA64.CalleeRoom

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (needOk1 callees ctxOf fnOk1_of_fnCode1Ok)
open Scc.Cert.NeedA64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)

/-- **A function's limit room** at its entry `sp`: the function `name` has
a row of the stack need table `tbl` whose need `n` fits above every value
`G` admits at the limit word, `v + n ≤ sp`. -/
def LimRoomA (tbl : List Scc.Cert.NeedA64.Row) (name : String) (G : Kraken.Promising.Val → Prop) (sp : Nat) :
    Prop :=
  ∃ a f n, row? tbl name = some (a, f, n) ∧ ∀ v, G v → (v.setWidth 64).toNat + n ≤ sp

/-- A higher entry `sp` and fewer values keep the limit room. -/
theorem LimRoomA.mono {tbl : List Scc.Cert.NeedA64.Row} {name : String} {G G' : Kraken.Promising.Val → Prop}
    {sp sp' : Nat} (h : LimRoomA tbl name G sp) (hG : ∀ v, G' v → G v) (hsp : sp ≤ sp') :
    LimRoomA tbl name G' sp' := by
  obtain ⟨a, f, n, hr, hv⟩ := h
  exact ⟨a, f, n, hr, fun v hv' => by have := hv v (hG v hv'); omega⟩

/-- **A code block's limit room covers its frame** from `PlaceOK`: the
frame `fd` (its row's need is at least `fd`, `needOk1`). -/
theorem ownLim_of_placeOK {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {G : Kraken.Promising.Val → Prop} {sp : Nat}
    (hL : LimRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d.name) G sp) :
    ∀ v, G v → (v.setWidth 64).toNat + (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame ≤ sp := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨a, nf, hrow, hle, -⟩ := needOk1_row (needOk1_of_fnPh1 h hrs hir j hj)
  obtain ⟨a', f', n, hr', hv⟩ := hL
  have e : row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      (Scc.Lower.Names.user p[j].name) = _ := hrow
  rw [hr'] at e
  cases e
  intro v hv'
  have := hv v hv'
  omega

/-- **A call site's callee limit room** from `PlaceOK`: at a call of
`Names.user g` (`g` a code block's name) in the `j`th code block `d`, whose
limit room is at `sp`, the callee is the earlier code block `dg` named `g`,
with its limit room at its entry `sp'` right below the caller's frame `fd`
(`sp' + fd = sp`). -/
theorem calleeLim_of_placeOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {fo : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fo) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) (hgp : g ∈ p.map (·.name))
    {G : Kraken.Promising.Val → Prop} {sp sp' : Nat}
    (hsp : sp' + (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame = sp)
    (hL : LimRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d.name) G sp) :
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧ dg.name = g ∧
      LimRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user g) G sp' := by
  obtain ⟨j', dg, rg, hlt, hdg, hrg, hn, a, nd, a', ng, hrd, hrg', -, -, hc⟩ :=
    calleeRow_name_of_fnPh1 hp h hrs hir hd hr hg hgp
  refine ⟨j', dg, rg, hlt, hdg, hrg, hn, a', _, ng, hrg', ?_⟩
  obtain ⟨a1, f1, n1, hr1, hv⟩ := hL
  rw [hrd] at hr1
  cases hr1
  intro v hv'
  have := hv v hv'
  omega

/-- **`main`'s limit room from `scc_rt_main`'s row**: with every value at
the limit word at most `lim`, `scc_rt_main` (frame `sg`) calling `main`
(`sg + n ≤ budget`, its row bounded by the budget), and
`lim + budget ≤ top`, `main`'s need `n` fits at its entry `sp` below
`scc_rt_main`'s entry `top` and its frame (`sp + sg = top`). -/
theorem mainLim_of_rows {G : Kraken.Promising.Val → Prop} {lim top sp sg n budget : Nat}
    (hG : ∀ v, G v → (v.setWidth 64).toNat ≤ lim) (hrow : sg + n ≤ budget) (hb : lim + budget ≤ top)
    (hsp : sp + sg = top) :
    ∀ v, G v → (v.setWidth 64).toNat + n ≤ sp := by
  intro v hv
  have := hG v hv
  omega

/-- **`main`'s row and `scc_rt_main`'s bound from the placement check**:
for an `Accepted1` program lowered to `em` and an output passing
`placeOKAt` with `scc_rt_main` a thread entry, every stack-checked function
`f` of the IR at index `fi` named `main` has a row with its frame and a
need `n`, and `scc_rt_main` (at an index `m`, frame `sg`) with `n` fits the
budget, `sg + n ≤ budget`. -/
theorem mainRow_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hme : pcfg.entries.contains Scc.Lower.Names.mainThread = true) {f : Scc.IR.Func} {fi : Nat}
    (hf : (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx)
    (hname : f.name = Scc.Lower.Names.user "main") (hck : f.checkStack = true) :
    ∃ (m : Nat) (a : String) (n : Nat),
      (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0, m) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx ∧
      row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need f.name =
        some (a, (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame, n) ∧
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir m (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).frame + n ≤
        pcfg.needBudget := by
  obtain ⟨rs, rt, -, hrt, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted1_a64 cfg hp hlow
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  have hg : Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs := by
    rw [hir]; simp only [Scc.Lower.Inv.progOf]; exact List.mem_append_left _ (mainThread0_mem hrt)
  obtain ⟨m, hm⟩ := List.getElem_of_mem hg
  have hgz : (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0, m) ∈
      (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    obtain ⟨hlt, he⟩ := hm
    rw [List.mem_zipIdx_iff_getElem?]; exact List.getElem?_eq_some_iff.mpr ⟨hlt, he⟩
  obtain ⟨a, nf, hrf, -, -⟩ := needOk1_row (needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hf hck))
  obtain ⟨b, nr, hrr, -, hcall⟩ := needOk1_row (needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hgz rfl))
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedA64.needOk, Bool.and_eq_true] at hA
  have he := List.all_eq_true.mp hA.1 _ (List.contains_iff_mem.mp hme)
  have hrr' : row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      Scc.Lower.Names.mainThread = _ := hrr
  rw [hrr'] at he
  simp only [decide_eq_true_eq] at he
  have := hcall f.name (hname ▸ user_main_mem_calleesA) _ _ _ hrf
  exact ⟨m, a, nf, hgz, hrf, by omega⟩

end Spike.Lib.LowerA64
