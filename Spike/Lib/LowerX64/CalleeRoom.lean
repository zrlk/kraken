/-
**The stack room of a function and of its callees from `PlaceOK`**
(x86-64): a function's room `NeedRoomX` (its stack need table row's need
`n` and a slack `s` fit above the region's lower bound `lo`, relative to
the function's entry `%rsp`) covers its own frame and, at each call
site, its callee's room at the callee's entry `%rsp`.

- `NeedRoomX`: the room of a function, on the region's lower bound `lo`
  (independent of the region's base);
- `ownRoom_of_placeOK`: the room covers the frame, the saved `%rbp` and the
  slack, `lo ≤ -(sd + 8 + s)` (at `s = 40`, `fnC_segS`'s and the overflow
  abort's `R.lo ≤ -(sd + 48)`);
- `calleeRoom_of_placeOK`: at a call of `Names.user g` the callee is the
  code block named `g`, with its room at `lo + sd + 16` (past the caller's
  frame, its saved `%rbp` and the return address), from the call site's
  rows `sd + 8 + 8 + ng ≤ nd` (`calleeRow_name_of_placeOK`);
- `mainRoom_of_row`: `main`'s room at `-needD fr n` (`userCallWS`'s region)
  at the slack `40`.
-/
import Spike.Lib.LowerX64.UserInj
import Spike.Lib.LowerX64.StartSegN

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.NeedX64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)

/-- **A function's stack room** at the region's lower bound `lo`
(relative to its entry `%rsp`): the function `name` has a row of the stack
need table `tbl` whose need `n` and the slack `s` fit, `lo ≤ -(n + s)`. -/
def NeedRoomX (tbl : List Scc.Cert.NeedX64.Row) (name : String) (s : Nat) (lo : Int) : Prop :=
  ∃ a f n, row? tbl name = some (a, f, n) ∧ lo ≤ -((n : Int) + s)

/-- A lower lower bound keeps the room. -/
theorem NeedRoomX.mono {tbl : List Scc.Cert.NeedX64.Row} {name : String} {s : Nat} {lo lo' : Int}
    (h : NeedRoomX tbl name s lo) (hle : lo' ≤ lo) : NeedRoomX tbl name s lo' := by
  obtain ⟨a, f, n, hr, hlo⟩ := h
  exact ⟨a, f, n, hr, by omega⟩

/-- **A code block's room covers its frame** from `PlaceOK`: the frame's
size `sd`, the saved `%rbp` and the slack (its row's need is at least
`sd + 8`, `needOk1`). -/
theorem ownRoom_of_placeOK {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r) {s : Nat} {lo : Int}
    (hR : NeedRoomX (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user d.name) s lo) :
    lo ≤ -(((frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size : Int) + 8 + s) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨a, nf, hrow, hle, -⟩ := needOk1_row (needOk1_of_fnPh1 h hrs hir j hj)
  obtain ⟨a', f', n, hr', hlo⟩ := hR
  have e : row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user p[j].name) = _ := hrow
  rw [hr'] at e
  cases e
  omega

/-- **A call site's callee room** from `PlaceOK`: at a call of
`Names.user g` (`g` a code block's name) in the `j`th code block `d`, whose
room is at `lo`, the callee is the earlier code block `dg` named `g`, with
its room at `lo + sd + 16`: the callee's entry `%rsp` is below the caller's
frame (`sd`), its saved `%rbp` and the return address. -/
theorem calleeRoom_of_placeOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {fo : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fo) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) (hgp : g ∈ p.map (·.name))
    {s : Nat} {lo : Int}
    (hR : NeedRoomX (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user d.name) s lo) :
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧ dg.name = g ∧
      NeedRoomX (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
        (Scc.Lower.Names.user g) s
        (lo + ((frOf (Scc.Lower.X64.lowerAll cfg p).low.ir
          (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size : Int) + 16) := by
  obtain ⟨j', dg, rg, hlt, hdg, hrg, hn, a, nd, a', ng, hrd, hrg', -, -, hc⟩ :=
    calleeRow_name_of_placeOK hp h hrs hir hd hr hg hgp
  refine ⟨j', dg, rg, hlt, hdg, hrg, hn, a', _, ng, hrg', ?_⟩
  obtain ⟨a1, f1, n1, hr1, hlo⟩ := hR
  rw [hrd] at hr1
  cases hr1
  omega

/-- **`main`'s room at `userCallWS`'s region**: at its row's need `n`, the
lower bound `-needD fr n` leaves the need and the slack `40`. -/
theorem mainRoom_of_row {tbl : List Scc.Cert.NeedX64.Row} {name a : String} {f n : Nat}
    (fr : Scc.Emit.X64.Frame) (hr : row? tbl name = some (a, f, n)) :
    NeedRoomX tbl name 40 (-needD fr n) :=
  ⟨a, f, n, hr, by unfold needD; omega⟩

end Spike.Lib.LowerX64
