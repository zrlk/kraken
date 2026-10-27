/-
**The grow stub's label in the code, from A12** (x86-64): A12's `fnOk1`
places the grow stub's first cell (`stkHead`) at the prologue's branch
target `proL`, so the target is a position of the code (`InRunB` at offset
`0`); at `scc_rt_main` after a setup block this is `h0In_of_setupFNP`'s
`hstk`, and for any function off the write abort's labels its `PosOff`.

- `inRunB_proL_of_fnOk1`: `proL`'s offset `0` is in its run;
- `posOff_proL_of_fnOk1`: `PosOff` at `proL`, the label off `abLabs`;
- `hstk_of_placeOKAt`: `scc_rt_main`'s grow stub label `.Lscc_rt_main.stk`
  in the run, for an `Accepted2` program with a setup block whose output
  passes `placeOKAt` (A12 at `mainThread0`).
-/
import Spike.Lib.LowerX64.SetupSwA12
import Spike.Lib.LowerX64.RtStartXOf
import Spike.Lib.LowerX64.StubAbW2

namespace Spike.Lib.LowerX64

open Scc.Cert.Code1X64 (fnOk1)

/-- **A12 places the grow stub at `proL`**: its offset `0` is in its run. -/
theorem inRunB_proL_of_fnOk1 {cells : List (Directive × Nat)} {tbl : List Scc.Cert.NeedX64.Row}
    {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func} (h : fnOk1 cells tbl ir n f = true) :
    Scc.Cert.Rt.X64.InRunB cells (proL (frOf ir f)) 0 := by
  have hb : Scc.Cert.Rt.X64.blockAtB cells (proL (frOf ir f)) 0 stkHead = true := by
    unfold fnOk1 at h
    split at h
    · split at h
      · simp only [Bool.and_eq_true] at h; exact h.2
      · cases h
    · cases h
  simpa [Spike.Lib.X64.cellOff] using inRunB_of_blockAtB hb (i := 0) (by simp [stkHead])

/-- **`proL` is a position off the write abort** when A12 passes and the
label is none of the write abort's. -/
theorem posOff_proL_of_fnOk1 {cells : List (Directive × Nat)} {tbl : List Scc.Cert.NeedX64.Row}
    {ir : Scc.IR.Program} {n : Nat} {f : Scc.IR.Func} (h : fnOk1 cells tbl ir n f = true)
    (hl : proL (frOf ir f) ∉ Spike.Lib.X64.AllocG.abLabs) (lab : Label → Int64) :
    PosOff cells lab (lab (proL (frOf ir f))) :=
  ⟨_, 0, inRunB_proL_of_fnOk1 h, hl, Spike.Lib.X64.Flow.ofNat_zero' _⟩

/-- **`scc_rt_main`'s grow stub label is in the code** (`h0In_of_setupFNP`'s
`hstk`): A12 at `mainThread0`, a stack-checked function of the lowered IR. -/
theorem hstk_of_placeOKAt {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) :
    Scc.Cert.Rt.X64.InRunB (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      ".Lscc_rt_main.stk" 0 := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_x64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.setupTid, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  rw [he] at hrt
  generalize hir' : (Scc.Lower.X64.lowerAll cfg p).low.ir = ir at hir
  have hf : Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p) ∈ ir.funcs := by
    rw [hir]
    exact List.mem_append_left _ (Spike.Lib.mainThread0_mem hrt)
  obtain ⟨n, hn⟩ := mem_starts ir 0 hf
  have h12 := Scc.Cert.PlaceOK.X64.fnCode1_of_placeOKAt h
    ((Scc.Cert.PlaceOK.X64.place_ir_ofEmitted _ _ _).trans (congrArg some hir'))
  exact inRunB_proL_of_fnOk1 (Scc.Cert.Code1X64.fnOk1_of_fnCode1Ok h12 hn rfl)

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.inRunB_proL_of_fnOk1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.inRunB_proL_of_fnOk1

/-- info: 'Spike.Lib.LowerX64.posOff_proL_of_fnOk1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_proL_of_fnOk1

/-- info: 'Spike.Lib.LowerX64.hstk_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hstk_of_placeOKAt
