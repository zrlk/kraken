/-
**The stack room of a function and of its callees from `PlaceOK`**
(AArch64), the twin of `Spike/Lib/LowerX64/CalleeRoom.lean`: a function's
room `NeedRoomA` (its stack need table row's need `n` and a slack `s` fit
above the region's lower bound `lo`, relative to the function's entry
`sp`) covers its own frame and, at each call site, its callee's room at
the callee's entry `sp`.

- `NeedRoomA`: the room of a function, on the region's lower bound `lo`
  (independent of the region's base);
- `frame16_of_fnPh1`: each code block's frame is 16-aligned (`fnOk1`);
- `ownRoom_of_placeOK`: the room covers the frame and the slack,
  `lo ≤ -(fd + s)` (at `s = 48`, the overflow abort's
  `R.lo ≤ -frame - 48`);
- `calleeRoom_of_placeOK`: at a call of `Names.user g` the callee is the
  code block named `g`; at an 8-aligned `lo` the callee's region below the
  caller's frame (`R.callee (-fd) (-D) 0`) has an explicit depth `D`,
  8-aligned, within the caller's region (`lo ≤ -fd - D`) and with the
  callee's room at `-D`, from the call site's rows `fd + ng ≤ nd`
  (`calleeRow_name_of_fnPh1`);
- `mainRoom_of_row`: `main`'s room at `-needDA n` at the slack `48`.

Where AArch64 differs from x86-64: no return address or saved frame
pointer sits between the caller's frame and the callee's entry `sp`, and
the callee's region is chosen by its depth `D` (`callPre_of`), rounded
up to 8 for the abort path.
-/
import Spike.Lib.LowerA64.UserInj
import Spike.Lib.LowerA64.MainNeed

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (ctxOf fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.NeedA64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1 mem_progOf_funcs1)

/-- **A function's stack room** at the region's lower bound `lo`
(relative to its entry `sp`): the function `name` has a row of the stack
need table `tbl` whose need `n` and the slack `s` fit, `lo ≤ -(n + s)`. -/
def NeedRoomA (tbl : List Scc.Cert.NeedA64.Row) (name : String) (s : Nat) (lo : Int) : Prop :=
  ∃ a f n, row? tbl name = some (a, f, n) ∧ lo ≤ -((n : Int) + s)

/-- A lower lower bound keeps the room. -/
theorem NeedRoomA.mono {tbl : List Scc.Cert.NeedA64.Row} {name : String} {s : Nat} {lo lo' : Int}
    (h : NeedRoomA tbl name s lo) (hle : lo' ≤ lo) : NeedRoomA tbl name s lo' := by
  obtain ⟨a, f, n, hr, hlo⟩ := h
  exact ⟨a, f, n, hr, by omega⟩

/-- **Each code block's frame is 16-aligned** from `PlaceOK` (`fnOk1`),
as `fnPh1_ofPlaceOK` numbers them. -/
theorem frame16_of_fnPh1 {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    (j : Nat) (hj : j < p.length) :
    (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) (rs[j]'(hrs.1 ▸ hj)))).frame % 16 = 0 := by
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  have hmem : (func1 (Scc.Lower.Names.user p[j].name) (params1R p[j]) (rs[j]'(hrs.1 ▸ hj)), rt.length + j) ∈
      (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    rw [hir]
    exact mem_progOf_funcs1 cfg.layout rt hrs j hj
  have hc1 := fnOk1_of_fnCode1Ok hc hmem rfl
  obtain ⟨ps, hps⟩ := spills_of_fnOk1 hc1
  exact (fnOk1_facts hc1 rfl hps).2.2.1

/-- **A code block's room covers its frame** from `PlaceOK`: the frame
`fd` and the slack (its row's need is at least `fd`, `needOk1`). -/
theorem ownRoom_of_placeOK {cfg : Scc.Config} {p : Prog} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r) {s : Nat} {lo : Int}
    (hR : NeedRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d.name) s lo) :
    lo ≤ -(((ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame : Int) + s) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨a, nf, hrow, hle, -⟩ := needOk1_row (needOk1_of_fnPh1 h hrs hir j hj)
  obtain ⟨a', f', n, hr', hlo⟩ := hR
  have e : row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      (Scc.Lower.Names.user p[j].name) = _ := hrow
  rw [hr'] at e
  cases e
  omega

/-- **A call site's callee room** from `PlaceOK`: at a call of
`Names.user g` (`g` a code block's name) in the `j`th code block `d`, whose
room is at an 8-aligned `lo`, the callee is the earlier code block `dg`
named `g`, and a depth `D` (the callee's need and the slack, rounded up to
8) fits below the caller's frame `fd` within `lo` with the callee's room
at `-D`: the plain call's (`CallC`) callee region `R.callee (-fd) (-D) 0`. -/
theorem calleeRoom_of_placeOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {fo : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fo) p rs)
    (hir : (Scc.Lower.A64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) (hgp : g ∈ p.map (·.name))
    {s : Nat} {lo : Int} (h8 : lo % 8 = 0)
    (hR : NeedRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d.name) s lo) :
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧ dg.name = g ∧
      ∃ D : Int, 0 ≤ D ∧ D % 8 = 0 ∧
        lo ≤ -((ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
          (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame : Int) - D ∧
        NeedRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user g) s (-D) := by
  have h16 : (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir (rt.length + j)
      (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).frame % 16 = 0 := by
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hjr, rfl⟩ := List.getElem?_eq_some_iff.mp hr
    exact frame16_of_fnPh1 h hrs hir j hj
  obtain ⟨j', dg, rg, hlt, hdg, hrg, hn, a, nd, a', ng, hrd, hrg', -, -, hc⟩ :=
    calleeRow_name_of_fnPh1 hp h hrs hir hd hr hg hgp
  refine ⟨j', dg, rg, hlt, hdg, hrg, hn, 8 * (((ng : Int) + s + 7) / 8), by omega, by omega, ?_,
    a', _, ng, hrg', by omega⟩
  obtain ⟨a1, f1, n1, hr1, hlo⟩ := hR
  rw [hrd] at hr1
  cases hr1
  omega

/-- **`main`'s room at its depth `needDA n`** (`MainNeed`): at its row's
need `n`, the lower bound `-needDA n` leaves the need and the slack `48`. -/
theorem mainRoom_of_row {tbl : List Scc.Cert.NeedA64.Row} {name a : String} {f n : Nat}
    (hr : row? tbl name = some (a, f, n)) : NeedRoomA tbl name 48 (-needDA n) :=
  ⟨a, f, n, hr, by unfold needDA; omega⟩

end Spike.Lib.LowerA64
