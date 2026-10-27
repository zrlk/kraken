/-
**`main`'s stack need bound from the placement check** (x86-64):
`MainNeedOk` (`Spike/Lib/LowerX64/StartSegN.lean`), decided per program
there, follows from `placeOKAt` for every `Accepted1` program, given only
the configuration's thread entries and budget (`CfgNeedOk`, closed by
`decide` at a certificate's configuration).

The chain: A12 (`fnCode1Ok`, `needOk1`) gives `main`'s row with its
frame `fr.size + 8 ≤ n` and `scc_rt_main`'s row with the edge to `main`
(`size + 8 + 8 + n ≤ nr`: `scc_rt_main` calls `main`, `mainThread0`); A4
(`needOk`) gives `nr ≤ budget` for the thread entry `scc_rt_main`. A
budget of at most `16304` then fits `needD fr n + 56 ≤ 16384`; `CfgNeedOk`
asks at most `12288` (the first stack less the limit's `4096`-byte guard),
which also keeps `main`'s frame above the limit (`mainFrameU_of_placeOKAt`,
`Spike/Lib/LowerX64/MainRoomU.lean`).

- `mainNeedOk_of_rows`: the arithmetic, from the two rows and the budget.
- `user_main_mem_callees`: `scc_rt_main` (`Inv.mainThread0`, one of the
  runtime's functions: `Spike.Lib.mainThread0_mem`) calls `main`.
- `mainNeedOk_of_placeOKAt`: `MainNeedOk` for the stack-checked `main` of
  the IR of an `Accepted1` program passing `placeOKAt`.
-/
import Spike.Lib.LowerX64.StartSegN
import Spike.Lib.LowerX64.CallSite1
import Spike.Lib.RtMainMem

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (needOk1 callees fnCode1Ok fnOk1 starts fnOk1_of_fnCode1Ok)

/-- **The configuration's side of `main`'s bound**: `scc_rt_main` is a
thread entry (A4 bounds its need by the budget) and the budget is at most
`12288`: the first stack's `16384` bytes less the limit's `4096`-byte guard
(`Tcb.headroom`), so that the frames stay above the limit word's value
(`mainFrameU_of_placeOKAt`); within the `16304` that `needD`'s region needs
(the first stack less `scc_rt_main`'s call of `main`, the return address
and the switch region's `56`). -/
def CfgNeedOk (pcfg : Scc.Cert.PlaceOK.Config) : Bool :=
  pcfg.entries.contains Scc.Lower.Names.mainThread && decide (pcfg.needBudget ≤ 12288)

/-- **`MainNeedOk` from the two rows and the budget**: `main`'s row
(`needOk1` at `main`), `scc_rt_main`'s row calling `main` (`needOk1` at
`scc_rt_main`), and A4's entry bound. -/
theorem mainNeedOk_of_rows {tbl : List Scc.Cert.NeedX64.Row} {name : String} {fr : Scc.Emit.X64.Frame}
    {f g : Scc.IR.Func} {sg budget : Nat} {entries : List String}
    (hf : needOk1 tbl name fr.size f = true) (hg : needOk1 tbl Scc.Lower.Names.mainThread sg g = true)
    (hcall : name ∈ (callees g).1)
    (hent : entries.all (fun e => match Scc.Cert.NeedX64.row? tbl e with
      | some (_, _, n) => decide (n ≤ budget)
      | none => false) = true)
    (hme : entries.contains Scc.Lower.Names.mainThread = true) (hb : budget ≤ 16304) :
    MainNeedOk tbl name fr := by
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
      unfold MainNeedOk needD
      rw [hr1]
      simp only [decide_eq_true_eq]
      omega
    · simp at hg
  · simp at hf

/-- **`fnOk1`'s row**: a function passing `fnOk1` passes `needOk1` at its
name and frame (whatever its blocks). -/
theorem needOk1_of_fnOk1 {cells} {tbl : List Scc.Cert.NeedX64.Row}
    {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func} (h : fnOk1 cells tbl ir n f = true) :
    needOk1 tbl f.name (frOf ir f).size f = true := by
  unfold fnOk1 at h
  split at h
  · split at h
    · simp only [Bool.and_eq_true] at h; exact h.1.2
    · cases h
  · cases h

/-- **`scc_rt_main` calls `main`** (an entry returning an `Int`, no setup). -/
theorem user_main_mem_callees :
    Scc.Lower.Names.user "main" ∈ (callees (Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0)).1 := by
  simp [callees, Scc.Lower.Inv.mainThread0, Scc.Lower.Inv.mainInsts, Scc.Lower.mainSetup, Scc.Lower.Inv.mainArgs]

/-- **`MainNeedOk` from the placement check**: for an `Accepted1` program
`p` lowered to `em` and an output passing `placeOKAt` at a configuration
with `CfgNeedOk`, every stack-checked function `f` of the IR named
`main` (`Names.user "main"`) has `MainNeedOk` at the output's stack need
table and its frame. -/
theorem mainNeedOk_of_placeOKAt {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hcfg : CfgNeedOk pcfg = true) {f : Scc.IR.Func}
    (hf : f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs) (hname : f.name = Scc.Lower.Names.user "main")
    (hck : f.checkStack = true) :
    MainNeedOk (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need f.name
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f) := by
  obtain ⟨rs, rt, -, hrt, hir, -⟩ := lowerAll_accepted1_x64 cfg hp hlow
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p sizes labelOffs)
  have hg : Scc.Lower.Inv.mainThread0 ⟨.unit, true⟩ 0 ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs := by
    rw [hir]; simp only [Scc.Lower.Inv.progOf]; exact List.mem_append_left _ (mainThread0_mem hrt)
  obtain ⟨n, hn⟩ := mem_starts _ 0 hf
  obtain ⟨m, hm⟩ := mem_starts _ 0 hg
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hn hck)
  have h2 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hm rfl)
  simp only [CfgNeedOk, Bool.and_eq_true, decide_eq_true_eq] at hcfg
  have hA := needOk_of_placeOKAt h
  simp only [Scc.Cert.NeedX64.needOk, Bool.and_eq_true] at hA
  exact mainNeedOk_of_rows h1 h2 (hname ▸ user_main_mem_callees) hA.1 hcfg.1 (by omega)

end Spike.Lib.LowerX64
