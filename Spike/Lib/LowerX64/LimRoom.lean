/-
**The stack limit's room of a function and of its callees from `PlaceOK`**
(x86-64): the prologue's stack check passes when every value the runtime
memory may hold at the thread's limit word (a predicate `G` on values,
`ms.G` at the word) is at most the function's entry `%rsp` less `8` and its
frame. A function's limit room `LimRoomX` (its stack need table row's need
`n` fits between the limit and its entry `%rsp` `rsp` plus the return
address's `8`) gives its own check and, at each call site, its callee's
limit room at the callee's entry `%rsp`. Entry `%rsp`s are `8` above a
16-aligned boundary, frames and the limit word's values 16-aligned.

- `LimRoomX`: the limit room of a function at its entry `%rsp`;
- `frame16_of_fnPh1`: each code block's frame is 16-aligned (`fnOk1`);
- `frame_of_fnPh1`: each code block's frame is below `2 ^ 31` bytes;
- `ownLim_of_placeOK`, `ownLim_bv`, `ownLimBv_of_placeOK`: the room covers the frame and the saved
  `%rbp` (its row's need is at least `sd + 8`, rounded by the alignment), in
  the prologue's form `v ≤ rsp - 8 - size`;
- `calleeLim_of_placeOK`: at a call of `Names.user g` the callee is the code
  block named `g`, with its limit room at its entry `%rsp`
  `rsp' = rsp - sd - 16` (past the caller's frame, its saved `%rbp` and the
  return address), from the call site's rows `sd + 8 + 8 + ng ≤ nd`
  (`calleeRow_name_of_placeOK`);
- `mainLim_of_rows`, `mainRow_of_placeOKAt`: `main`'s limit room from
  `scc_rt_main`'s row (frame `sg`, entered at the stack's top `top` less
  the return address), given a limit `lim` and a budget with
  `lim + budget ≤ top`: with the limit `stacksA + 4096` and the top
  `stacksA + 16384`, a budget of at most `12288`.

Unlike the region's room (`Spike/Lib/LowerX64/CalleeRoom.lean`), the limit
room is relative to the limit word's values, which sit above the stack's
bottom by the guard: the budget bounds the depth below the guard.
-/
import Spike.Lib.LowerX64.CalleeRoom
import Spike.Lib.LowerX64.MainNeed

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (needOk1 callees fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.NeedX64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1 mem_progOf_funcs1)

/-- **A function's limit room** at its entry `%rsp` `rsp` (a return
address's 8 bytes above a 16-aligned boundary): the function `name` has a
row of the stack need table `tbl` whose need `n` fits above every value `G`
admits at the limit word, `v + n ≤ rsp + 8`. -/
def LimRoomX (tbl : List Scc.Cert.NeedX64.Row) (name : String) (G : Kraken.Promising.Val → Prop) (rsp : Nat) :
    Prop :=
  ∃ a f n, row? tbl name = some (a, f, n) ∧ ∀ v, G v → (v.setWidth 64).toNat + n ≤ rsp + 8

/-- A higher entry `%rsp` and fewer values keep the limit room. -/
theorem LimRoomX.mono {tbl : List Scc.Cert.NeedX64.Row} {name : String} {G G' : Kraken.Promising.Val → Prop}
    {rsp rsp' : Nat} (h : LimRoomX tbl name G rsp) (hG : ∀ v, G' v → G v) (hsp : rsp ≤ rsp') :
    LimRoomX tbl name G' rsp' := by
  obtain ⟨a, f, n, hr, hv⟩ := h
  exact ⟨a, f, n, hr, fun v hv' => by have := hv v (hG v hv'); omega⟩

/-- **Each code block's frame is below `2 ^ 31` bytes and 16-aligned**
from `PlaceOK` (`fnOk1`), as `fnPh1_ofPlaceOK` numbers them. -/
theorem frame_of_fnPh1 {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r) :
    (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size
        < 2 ^ 31 ∧
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size
        % 16 = 0 := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)
  have hmem : (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j], rt.length + j) ∈
      (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    rw [hir]
    exact mem_progOf_funcs1 cfg.layout rt hrs j hj
  have hmemF : func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) rs[j] ∈
      (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs := by
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    exact List.mem_of_getElem? hmem
  obtain ⟨n, hn⟩ := mem_starts _ 0 hmemF
  have hc1 := fnOk1_of_fnCode1Ok hc hn rfl
  obtain ⟨zl, zf, z1, z2, zs, zps, ps, hz, hps⟩ := fnOk1_sizes hc1
  have := fnOk1_facts hc1 rfl hz hps
  exact ⟨this.2.2.1, this.2.2.2.1⟩

/-- **Each code block's frame is 16-aligned** from `PlaceOK` (`fnOk1`). -/
theorem frame16_of_fnPh1 {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r) :
    (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size % 16
      = 0 :=
  (frame_of_fnPh1 h hrs hir hd hr).2

/-- **A code block's limit room covers its frame** from `PlaceOK`: at an
entry `%rsp` `8` above a 16-aligned boundary, with the limit word's values
16-aligned, the frame's size `sd` and the saved `%rbp` (its row's need is at
least `sd + 8`, `needOk1`; the frame 16-aligned). -/
theorem ownLim_of_placeOK {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {G : Kraken.Promising.Val → Prop} {rsp : Nat} (h8 : rsp % 16 = 8)
    (hG16 : ∀ v, G v → (v.setWidth 64).toNat % 16 = 0)
    (hL : LimRoomX (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user d.name) G rsp) :
    ∀ v, G v → (v.setWidth 64).toNat + (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size + 8 ≤ rsp := by
  have h16 := frame16_of_fnPh1 h hrs hir hd hr
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨a, nf, hrow, hle, -⟩ := needOk1_row (needOk1_of_fnPh1 h hrs hir j hj)
  obtain ⟨a', f', n, hr', hv⟩ := hL
  have e : row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user p[j].name) = _ := hrow
  rw [hr'] at e
  cases e
  intro v hv'
  have := hv v hv'
  have := hG16 v hv'
  omega

/-- **The prologue's form of the limit room**: values `v` with
`v + size + 8 ≤ rsp` are at most `rsp - 8 - size` (no wrap-around), for a
frame of at most `2 ^ 31` bytes. -/
theorem ownLim_bv {G : Kraken.Promising.Val → Prop} {rsp : BitVec 64} {size : Nat} (h1 : size ≤ 2 ^ 31)
    (h : ∀ v, G v → (v.setWidth 64).toNat + size + 8 ≤ rsp.toNat) :
    ∀ v, G v → (v.setWidth 64).toNat ≤ (rsp - 8#64 - (Int64.ofInt size).toBitVec).toNat := by
  intro v hv
  have hv' := h v hv
  have hf : (Int64.ofInt size).toBitVec.toNat = size := by
    rw [Int64.toBitVec_ofInt, BitVec.toNat_ofInt]
    omega
  simp only [BitVec.toNat_sub, hf, BitVec.toNat_ofNat]
  omega

/-- **A code block's stack check from its limit room**, in the prologue's
form: at an entry `%rsp` `rsp` `8` above a 16-aligned boundary, with the
limit word's values 16-aligned, every value is at most `rsp - 8 - sd`. -/
theorem ownLimBv_of_placeOK {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {G : Kraken.Promising.Val → Prop} {rsp : BitVec 64} (h8 : rsp.toNat % 16 = 8)
    (hG16 : ∀ v, G v → (v.setWidth 64).toNat % 16 = 0)
    (hL : LimRoomX (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user d.name) G rsp.toNat) :
    ∀ v, G v → (v.setWidth 64).toNat ≤ (rsp - 8#64 - (Int64.ofInt ((frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size : Int)).toBitVec).toNat :=
  ownLim_bv (Nat.le_of_lt (frame_of_fnPh1 h hrs hir hd hr).1) (ownLim_of_placeOK h hrs hir hd hr h8 hG16 hL)

/-- **A call site's callee limit room** from `PlaceOK`: at a call of
`Names.user g` (`g` a code block's name) in the `j`th code block `d`, whose
limit room is at `rsp`, the callee is the earlier code block `dg` named `g`,
with its limit room at its entry `%rsp` `rsp'` below the caller's frame
(`sd`), its saved `%rbp` and the return address (`rsp' + sd + 16 = rsp`),
`8` above a 16-aligned boundary as the caller's. -/
theorem calleeLim_of_placeOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {fo : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fo) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) (hgp : g ∈ p.map (·.name))
    {G : Kraken.Promising.Val → Prop} {rsp rsp' : Nat} (h8 : rsp % 16 = 8)
    (hrsp : rsp' + (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size + 16 = rsp)
    (hL : LimRoomX (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user d.name) G rsp) :
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧ dg.name = g ∧
      rsp' % 16 = 8 ∧
      LimRoomX (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
        (Scc.Lower.Names.user g) G rsp' := by
  have h16 := frame16_of_fnPh1 h hrs hir hd hr
  obtain ⟨j', dg, rg, hlt, hdg, hrg, hn, a, nd, a', ng, hrd, hrg', -, -, hc⟩ :=
    calleeRow_name_of_placeOK hp h hrs hir hd hr hg hgp
  refine ⟨j', dg, rg, hlt, hdg, hrg, hn, by omega, a', _, ng, hrg', ?_⟩
  obtain ⟨a1, f1, n1, hr1, hv⟩ := hL
  rw [hrd] at hr1
  cases hr1
  intro v hv'
  have := hv v hv'
  omega

/-- **`main`'s limit room from `scc_rt_main`'s row**: with every value at
the limit word at most `lim`, `scc_rt_main` (frame `sg`) calling `main`
(`sg + 8 + 8 + n ≤ budget`, its row bounded by the budget), and
`lim + budget ≤ top`, `main`'s need `n` fits at its entry `%rsp` `rsp`
below `scc_rt_main`'s entry `top - 8`, its frame, its saved `%rbp` and the
return address (`rsp + sg + 16 + 8 = top`). -/
theorem mainLim_of_rows {G : Kraken.Promising.Val → Prop} {lim top rsp sg n budget : Nat}
    (hG : ∀ v, G v → (v.setWidth 64).toNat ≤ lim) (hrow : sg + 8 + 8 + n ≤ budget) (hb : lim + budget ≤ top)
    (hrsp : rsp + sg + 16 + 8 = top) :
    ∀ v, G v → (v.setWidth 64).toNat + n ≤ rsp + 8 := by
  intro v hv
  have := hG v hv
  omega

/-- **`main`'s row and `scc_rt_main`'s bound from the placement check**:
for an `Accepted1` program lowered to `em` and an output passing
`placeOKAt` with `scc_rt_main` a thread entry, every stack-checked function
`f` of the IR named `main` has a row with its frame and a need `n`, and
`scc_rt_main`'s frame `sg` with the call and `n` fits the budget. -/
theorem mainRow_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hme : pcfg.entries.contains Scc.Lower.Names.mainThread = true) {f : Scc.IR.Func}
    (hf : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs) (hname : f.name = Scc.Lower.Names.user "main")
    (hck : f.checkStack = true) :
    ∃ a n, row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need f.name =
        some (a, (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size + 8, n) ∧
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).size + 8 + 8 + n ≤
        pcfg.needBudget := by
  obtain ⟨rs, rt, -, hrt, hir, -⟩ := lowerAll_accepted1_x64 cfg hp hlow
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)
  have hg : Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs := by
    rw [hir]; simp only [Scc.Lower.Inv.progOf]; exact List.mem_append_left _ (mainThread0_mem hrt)
  obtain ⟨n0, hn⟩ := mem_starts _ 0 hf
  obtain ⟨m, hm⟩ := mem_starts _ 0 hg
  obtain ⟨a, nf, hrf, -, -⟩ := needOk1_row (needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hn hck))
  obtain ⟨b, nr, hrr, -, hcall⟩ := needOk1_row (needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hm rfl))
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedX64.needOk, Bool.and_eq_true] at hA
  have he := List.all_eq_true.mp hA.1 _ (List.contains_iff_mem.mp hme)
  have hrr' : row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      Scc.Lower.Names.mainThread = _ := hrr
  rw [hrr'] at he
  simp only [decide_eq_true_eq] at he
  have := hcall f.name (hname ▸ user_main_mem_callees) _ _ _ hrf
  exact ⟨a, nf, hrf, by omega⟩

end Spike.Lib.LowerX64
