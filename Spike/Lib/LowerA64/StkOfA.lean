/-
**The stack stub's label in the code, from A12** (AArch64; the twin of
`Spike/Lib/LowerX64/StkOf.lean`): A12's `fnOk1` places the stack stub's
first instruction (`stkHead`) at the prologue's branch target `proL`, so the
target is a position of the code (`InRun` at index `0`); at `scc_rt_main`
after a setup block this is `h0InA_of_setupFNP`'s `hstk`, and for any
function off the write abort's labels its `PosOff`.

- `inRun_proL_of_fnOk1`: `proL`'s index `0` is in its run;
- `posOff_proL_of_fnOk1`: `PosOff` at `proL`, the label off `abLabs`;
- `hstkA_of_placeOKAt`: `scc_rt_main`'s grow stub label
  `.L1_scc_rt_main.stack_grow` in the run, for an `Accepted2` program with a
  setup block whose output passes `placeOKAt` (A12 at `mainThread0`).
-/
import Spike.Lib.LowerA64.SetupSwA12A
import Spike.Lib.LowerA64.UserAb

namespace Spike.Lib.LowerA64

open Scc.Cert.Code1A64 (fnOk1 ctxOf)

/-- The stack stub's head is one instruction. -/
theorem stkHead_length (c : Scc.Emit.A64.FnCtx) : (stkHead c).length = 1 := by
  unfold stkHead
  cases c.maps <;> decide

/-- **A12 places the stack stub at `proL`**: its index `0` is in its run. -/
theorem inRun_proL_of_fnOk1 {prog : List Directive} {tbl : List Scc.Cert.NeedA64.Row}
    {c : Scc.Emit.A64.FnCtx} {f : Scc.IR.Func} (h : fnOk1 prog tbl c f = true) :
    Scc.Cert.Rt.A64.InRun prog (proL c) 0 := by
  have hb : Scc.Cert.Rt.A64.blockAt prog (proL c) 0 (stkHead c) = true := by
    unfold fnOk1 at h
    split at h
    · simp only [Bool.and_eq_true] at h; exact h.2
    · cases h
  exact Scc.Cert.Rt.A64.inRun_of_blockAt hb (i := 0) (by rw [stkHead_length]; omega)

/-- **`proL` is a position off the write abort** when A12 passes and the
label is none of the write abort's. -/
theorem posOff_proL_of_fnOk1 {prog : List Directive} {tbl : List Scc.Cert.NeedA64.Row}
    {c : Scc.Emit.A64.FnCtx} {f : Scc.IR.Func} (h : fnOk1 prog tbl c f = true)
    (hl : proL c ∉ Spike.Lib.A64.AllocG.abLabs) (lab : Label → Int64) :
    PosOff prog lab (lab (proL c)) :=
  ⟨_, 0, inRun_proL_of_fnOk1 h, hl, by simp⟩

/-- **`scc_rt_main`'s grow stub label is in the code**
(`h0InA_of_setupFNP`'s `hstk`): A12 at `mainThread0`, a function of the
lowered IR with stack growth. -/
theorem hstkA_of_placeOKAt {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))
      = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) :
    Scc.Cert.Rt.A64.InRun (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      ".L1_scc_rt_main.stack_grow" 0 := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨ws, rt, -, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.setupTid, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  rw [he] at hrt
  generalize hir' : (Scc.Lower.A64.lowerAll cfg p).low.ir = ir at hir
  generalize hf0 : Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p) = f0
  have hf : (f0, 1) ∈ ir.funcs.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, hir, ← hf0]
    simp only [Scc.Lower.Inv.progOf]
    have h1 := mainThread0_idx hrt
    have hlt : 1 < rt.length := (List.getElem?_eq_some_iff.mp h1).1
    rw [List.getElem?_append_left hlt, h1]
  have h12 := Scc.Cert.PlaceOK.A64.fnCode1_of_placeOKAt h
    ((Scc.Cert.PlaceOK.A64.place_ir_ofEmitted _).trans (congrArg some hir'))
  have hok := Scc.Cert.Code1A64.fnOk1_of_fnCode1Ok h12 hf (by rw [← hf0]; rfl)
  subst hf0
  have hm : (ctxOf ir 1 (Scc.Lower.Inv.mainThread0 ⟨.setupTid, true⟩ (Spike.Lib.LowerNode.setupWords2 p))).maps =
      true := by
    show ir.growth.isSome = true
    rw [hir]; rfl
  have hL := inRun_proL_of_fnOk1 hok
  simp only [proL, hm, ↓reduceIte, mainLocal] at hL
  exact hL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.inRun_proL_of_fnOk1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.inRun_proL_of_fnOk1

/-- info: 'Spike.Lib.LowerA64.posOff_proL_of_fnOk1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.posOff_proL_of_fnOk1

/-- info: 'Spike.Lib.LowerA64.hstkA_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hstkA_of_placeOKAt
