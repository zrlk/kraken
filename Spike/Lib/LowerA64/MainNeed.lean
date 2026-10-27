/-
**`main`'s stack need and callee room from the placement check**
(AArch64): the twin of `Spike/Lib/LowerX64/MainNeed.lean`, giving the
callee room `D` that `a64_start_segWS` takes (`0 ≤ D`, `D % 8 = 0`,
`D + 48 ≤ 16384`) together with the user side's lower bounds
(`cx.frame + 48 ≤ D`, `n + 48 ≤ D`).

`n` is `main`'s need, the row of the stack need table (`Scc.Lower.stackNeed`,
`NeedA64.Row`): the most stack bytes `main` uses below its entry stack
pointer until it returns, its frame (`cx.frame`, the frame record
included) and the deepest chain of stack-checked callees' frames after it
(AArch64 calls push nothing, `callCost = 0`). It does **not** include the
`48` bytes of room below a frame that the stack check's grow / overflow
path needs; `needDA n` adds them, rounded up to 8.

The chain: A12 (`fnCode1Ok`, `needOk1`) gives `main`'s row (frame
`cx.frame ≤ n`) and `scc_rt_main`'s row with its edge to `main`
(`frame + n ≤ nr`); A4 (`needOk`) gives `nr ≤ budget` for the thread entry
`scc_rt_main`, whose frame is at least `48` (`mainThread0_frameA`). A
budget of at most `12288` (`CfgNeedOkA`: the first stack less the limit's
`4096`-byte guard) then gives `n ≤ 12240`, so `main`'s frame stays above
the limit word's value, and `needDA n + 48 ≤ 16384`.

- `needDA`, `MainNeedOkA`, `needDA_ok`: the room from a need and its bounds.
- `mainThread0_frameA`: `scc_rt_main`'s frame is at least `48` bytes.
- `mainNeedOkA_of_rows`: the arithmetic, from the two rows and the budget.
- `mainNeedOkA_of_placeOKAt`: for the stack-checked `main` (at its index
  `fi`, context `ctxOf ir fi f`) of the IR of an `Accepted1` program passing
  `placeOKAt`, the row and `MainNeedOkA`.
- `mainRoom_of_placeOKAt`: the same, as the room `D = needDA n` with every
  bound `a64_start_segWS` and the user side take.
-/
import Scc.Cert.PlaceOKA64
import Scc.Cert.PlaceDataA64
import Spike.Lib.LowerProgC1
import Spike.Lib.RtMainMem

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (needOk1 callees fnCode1Ok fnOk1 ctxOf fnOk1_of_fnCode1Ok)

/-- **The callee room from `main`'s need `n`**: the need and the `48`
bytes below a frame the stack check's path needs, rounded up to 8. -/
def needDA (n : Nat) : Int := 8 * (((n : Int) + 48 + 7) / 8)

/-- **`main`'s room fits the first stack**: the row of `name` in `tbl` has
a need `n ≤ 12240` (the budget's `12288` less `scc_rt_main`'s frame of at
least `48`), so `needDA n + 48 ≤ 16384` (`room_of_mainNeedOkA`; decided on
`Nat`). -/
def MainNeedOkA (tbl : List Scc.Cert.NeedA64.Row) (name : String) : Bool :=
  match Scc.Cert.NeedA64.row? tbl name with
  | some (_, _, n) => decide (n ≤ 12240)
  | none => false

/-- `MainNeedOkA` at a row. -/
theorem mainNeedOkA_of_row {tbl : List Scc.Cert.NeedA64.Row} {name l : String} {fr n : Nat}
    (hr : Scc.Cert.NeedA64.row? tbl name = some (l, fr, n)) (h : n ≤ 12240) :
    MainNeedOkA tbl name = true := by
  simp only [MainNeedOkA, hr, decide_eq_true_eq]; exact h

/-- `MainNeedOkA` gives the row's room bound. -/
theorem room_of_mainNeedOkA {tbl : List Scc.Cert.NeedA64.Row} {name l : String} {fr n : Nat}
    (hr : Scc.Cert.NeedA64.row? tbl name = some (l, fr, n)) (h : MainNeedOkA tbl name = true) :
    needDA n + 48 ≤ 16384 := by
  simp only [MainNeedOkA, hr, decide_eq_true_eq] at h
  unfold needDA; omega

/-- **`needDA`'s bounds**: at least the need and `48`, 8-aligned,
nonnegative. -/
theorem needDA_ok (n : Nat) : (n : Int) + 48 ≤ needDA n ∧ needDA n % 8 = 0 ∧ 0 ≤ needDA n := by
  unfold needDA; omega

/-- **The configuration's side of `main`'s bound** (AArch64):
`scc_rt_main` is a thread entry and the budget is at most `12288`: the
first stack's `16384` bytes less the limit's `4096`-byte guard
(`Tcb.headroom`), so that the frames stay above the limit word's value;
within the `16288` that the room's `48` and the switch region's `48`
allow. -/
def CfgNeedOkA (pcfg : Scc.Cert.PlaceOK.Config) : Bool :=
  pcfg.entries.contains Scc.Lower.Names.mainThread && decide (pcfg.needBudget ≤ 12288)

/-- **`scc_rt_main`'s frame is at least `48` bytes** in any program, at
any index: its three registers and the frame record take `40` bytes,
16-aligned. -/
theorem mainThread0_frameA (ir : Scc.IR.Program) (fi : Nat) :
    48 ≤ (ctxOf ir fi (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).frame := by
  simp only [ctxOf, Scc.Emit.A64.fnCtx]
  have h3 : (Scc.Emit.A64.funcRegs (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).length = 3 := by decide
  rw [h3]
  have : Scc.Emit.A64.align16 (8 * 3 + 16) = 48 := by decide
  omega

/-- **`MainNeedOkA` and `main`'s row from the two rows and the budget**:
`main`'s row (`needOk1` at `main`, frame `frame`), `scc_rt_main`'s row
calling `main` at a frame `sg` of at least `48`, and A4's entry bound at a
budget of at most `12288`. -/
theorem mainNeedOkA_of_rows {tbl : List Scc.Cert.NeedA64.Row} {name : String} {frame : Nat}
    {f g : Scc.IR.Func} {sg budget : Nat} {entries : List String}
    (hf : needOk1 tbl name frame f = true) (hg : needOk1 tbl Scc.Lower.Names.mainThread sg g = true)
    (hsg : 48 ≤ sg) (hcall : name ∈ (callees g).1)
    (hent : entries.all (fun e => match Scc.Cert.NeedA64.row? tbl e with
      | some (_, _, n) => decide (n ≤ budget)
      | none => false) = true)
    (hme : entries.contains Scc.Lower.Names.mainThread = true) (hb : budget ≤ 12288) :
    ∃ l n, Scc.Cert.NeedA64.row? tbl name = some (l, frame, n) ∧ frame ≤ n ∧ n ≤ 12240 ∧
      MainNeedOkA tbl name = true := by
  unfold needOk1 at hf hg
  split at hf
  · next l1 f1 n1 hr1 =>
    split at hg
    · next l2 f2 n2 hr2 =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hf hg
      have he := List.all_eq_true.mp hent _ (List.contains_iff_mem.mp hme)
      rw [hr2] at he
      have hc := hg.1.2 name hcall
      rw [hr1] at hc
      simp only [decide_eq_true_eq] at he hc
      obtain ⟨⟨⟨hfr, hle⟩, -⟩, -⟩ := hf
      subst hfr
      have hn : n1 ≤ 12240 := by omega
      refine ⟨l1, n1, hr1, hle, hn, ?_⟩
      exact mainNeedOkA_of_row hr1 hn
    · simp at hg
  · simp at hf

/-- **`fnOk1`'s row**: a function passing `fnOk1` at its context `c`
passes `needOk1` at its name and frame. -/
theorem needOk1_of_fnOk1 {prog} {tbl : List Scc.Cert.NeedA64.Row}
    {c : Scc.Emit.A64.FnCtx} {f : Scc.IR.Func} (h : fnOk1 prog tbl c f = true) :
    needOk1 tbl f.name c.frame f = true := by
  unfold fnOk1 at h
  split at h
  · simp only [Bool.and_eq_true] at h; exact h.1.2
  · cases h

/-- **`scc_rt_main` calls `main`** (an entry returning an `Int`, no setup). -/
theorem user_main_mem_calleesA :
    Scc.Lower.Names.user "main" ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).1 := by
  simp [callees, Scc.Lower.Inv.mainThread0, Scc.Lower.Inv.mainInsts, Scc.Lower.mainSetup, Scc.Lower.Inv.mainArgs]

/-- **`main`'s row and `MainNeedOkA` from the placement check**: for an
`Accepted1` program `p` lowered to `em` and an output passing `placeOKAt`
at a configuration with `CfgNeedOkA`, every stack-checked function `f` of
the IR at index `fi` named `main` has a row of the output's stack need
table with its frame `(ctxOf ir fi f).frame` and a need `n` at least that
frame, and `MainNeedOkA`. -/
theorem mainNeedOkA_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hcfg : CfgNeedOkA pcfg = true) {f : Scc.IR.Func} {fi : Nat}
    (hf : (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx)
    (hname : f.name = Scc.Lower.Names.user "main") (hck : f.checkStack = true) :
    ∃ l n, Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need f.name =
        some (l, (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame, n) ∧
      (ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame ≤ n ∧ n ≤ 12240 ∧
      MainNeedOkA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need f.name = true := by
  obtain ⟨rs, rt, -, hrt, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted1_a64 cfg hp hlow
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  have hg : Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs := by
    rw [hir]; simp only [Scc.Lower.Inv.progOf]; exact List.mem_append_left _ (mainThread0_mem hrt)
  obtain ⟨m, hm⟩ := List.getElem_of_mem hg
  have hgz : (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0, m) ∈
      (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx := by
    obtain ⟨hlt, he⟩ := hm
    rw [List.mem_zipIdx_iff_getElem?]; exact List.getElem?_eq_some_iff.mpr ⟨hlt, he⟩
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hf hck)
  have h2 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hgz rfl)
  simp only [CfgNeedOkA, Bool.and_eq_true, decide_eq_true_eq] at hcfg
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedA64.needOk, Bool.and_eq_true] at hA
  exact mainNeedOkA_of_rows h1 h2 (mainThread0_frameA _ m) (hname ▸ user_main_mem_calleesA) hA.1 hcfg.1 hcfg.2

/-- **`main`'s callee room from the placement check** (`a64_start_segWS`'s
`D` and the user side's bounds): with `cx = ctxOf ir fi f` the context of
the stack-checked `main` and `n` its need (see the module docstring),
`D = needDA n` has `cx.frame + 48 ≤ D`, `n + 48 ≤ D`, `0 ≤ D`, `D % 8 = 0`
and `D + 48 ≤ 16384`. -/
theorem mainRoom_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg p = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hcfg : CfgNeedOkA pcfg = true) {f : Scc.IR.Func} {fi : Nat}
    (hf : (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx)
    (hname : f.name = Scc.Lower.Names.user "main") (hck : f.checkStack = true) :
    ∃ (cx : Scc.Emit.A64.FnCtx) (l : String) (n : Nat) (D : Int),
      cx = ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f ∧
      Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need f.name =
        some (l, cx.frame, n) ∧ D = needDA n ∧
      (cx.frame : Int) + 48 ≤ D ∧ (n : Int) + 48 ≤ D ∧ 0 ≤ D ∧ D % 8 = 0 ∧ D + 48 ≤ 16384 := by
  obtain ⟨l, n, hr, hle, -, hok⟩ := mainNeedOkA_of_placeOKAt hp hlow h hcfg hf hname hck
  have hD := room_of_mainNeedOkA hr hok
  obtain ⟨h1, h2, h3⟩ := needDA_ok n
  have h4 : (((ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame : Nat) : Int) + 48 ≤ needDA n := by
    have := Int.ofNat_le.mpr hle; omega
  exact ⟨_, l, n, needDA n, rfl, hr, rfl, h4, h1, h3, h2, hD⟩

end Spike.Lib.LowerA64
