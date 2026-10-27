/-
**The held frame's result in a region cell** (AArch64): `retSlot_heldRN`'s
and `retHeld_hW`'s `hx` (`Spike/Lib/LowerA64/RetHeldW.lean`) at the held
call `let x = call g a in e` (`CallC2H`, `Spike/Lib/LowerA64/HeldC.lean`):
the continuation's symbolic environment `ofEnv2 ((x, .int, [.reg (regName
"r" n)]) :: env)` places `x` as the register operand `regName "r" n`, whose
cell the call's code stores to (`instsC2_call`, `cx.setReg`), a cell of the
frame (`rsOf_cell`) inside the region; the held frame's result variable is
`x` (`HeldC`'s `f.x = x`).

- `lookupS_held`: the continuation's symbolic environment places `x` as one
  register operand;
- `rsOf_of_instsC2_call`: the call's result register has a cell;
- `regionOff_of_rsOf`: a frame cell is in a region covering the frame;
- `hx_held`: `hx` at the held call.
-/
import Spike.Lib.LowerA64.RetHeldAb
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.LowerA64.AbortCall

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName)

/-- **The continuation's symbolic environment places `x` as one register
operand.** -/
theorem lookupS_held (x : String) (r : Scc.IR.Reg) (env : Scc.Lower.Env) :
    lookupS (ofEnv2 ((x, .int, [.reg r]) :: env)) x = some (.int, [.one (.reg r)]) := by
  simp [lookupS, ofEnv2, Spike.Lib.Form.group, Spike.Lib.Form.grp]

/-- **The call's result register has a cell** (`instsC2_call`, its store
`cx.setReg d .X0`). -/
theorem rsOf_of_instsC2_call {cx : FnCtx} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {k : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {g : String}
    {w : Scc.IR.Operand} (h : InstsC2 cx Cd Bl k pc [.call [d] (Scc.Lower.Names.user g) [w]] pc') :
    ∃ off, rsOf cx d = some off := by
  obtain ⟨lw, ls, -, hs, -⟩ := instsC2_call h
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  exact ⟨o - cx.frame, by simp [rsOf, ho]⟩

/-- **A frame cell is in a region covering the frame** (`rsOf_cell`). -/
theorem regionOff_of_rsOf {cx : FnCtx} (hf : FrameOk cx) {R : Region} (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {r : Scc.IR.Reg} {k : Int} (h : rsOf cx r = some k) : R.Off k := by
  obtain ⟨h8, h1, h2, -⟩ := rsOf_cell hf h
  exact ⟨h8, by omega, by omega⟩

/-- **`hx` at the held call** (`retSlot_heldRN`, `retHeld_hW`): the held
frame's result variable `x` (`hfx`, `HeldC`'s `f.x = x`), placed by the
continuation's symbolic environment as the call's result register, whose
cell the call's code stores to (`hcode`), in a region covering the frame
(`hlo`, `hhi`). -/
theorem hx_held {cx : FnCtx} (hf : FrameOk cx) {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {kk : Nat} {pc pc' : Int64} {n : Nat} {g : String} {w : Scc.IR.Operand}
    (hcode : InstsC2 cx Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] pc')
    {R : Region} (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) {x : String} {env : Scc.Lower.Env}
    {fs : List TermRun.Frame} (hfx : ∀ f, fs = [f] → f.x = x) :
    ∀ f, fs = [f] → ∃ t r, lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) f.x =
      some (t, [.one (.reg r)]) ∧ ∃ k, rsOf cx r = some k ∧ R.Off k := by
  intro f hf'
  obtain ⟨k, hk⟩ := rsOf_of_instsC2_call hcode
  rw [hfx f hf']
  exact ⟨.int, _, lookupS_held x _ env, k, hk, regionOff_of_rsOf hf hlo hhi hk⟩

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.hx_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hx_held
