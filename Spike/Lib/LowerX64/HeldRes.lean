/-
**The held frame's result in a region cell** (x86-64; the twin of
`Spike/Lib/LowerA64/HeldRes.lean`): `retSlot_bodyN2`'s `hx`
(`Spike/Lib/LowerX64/RetHeldW.lean`) at the held call `let x = call g a in
e`: the continuation's symbolic environment `ofEnv2 ((x, .int, [.reg
(regName "r" n)]) :: env)` places `x` as the register operand `regName "r"
n`, whose cell the call's code stores to (`instsC2_call`), a cell of the
frame (`rsOf_bounds`) inside the region; the held frame's result variable is
`x` (`HeldC`'s `f.x = x`).

- `lookupS_held`: the continuation's symbolic environment places `x` as one
  register operand;
- `regionOff_of_rsOf`: a frame cell is in a region covering the frame;
- `hx_held`: `hx` at the held call.
-/
import Spike.Lib.LowerX64.RetHeldW
import Spike.Lib.LowerX64.CallC2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Spike.Lib (Region)
open Scc.Lower.InvX64
open Spike.Lib.Form (lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName)

/-- **The continuation's symbolic environment places `x` as one register
operand.** -/
theorem lookupS_held (x : String) (r : Scc.IR.Reg) (env : Scc.Lower.Env) :
    lookupS (ofEnv2 ((x, .int, [.reg r]) :: env)) x = some (.int, [.one (.reg r)]) := by
  simp [lookupS, ofEnv2, Spike.Lib.Form.group, Spike.Lib.Form.grp]

/-- **A frame cell is in a region covering the frame** (`rsOf_bounds`). -/
theorem regionOff_of_rsOf {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {R : Region}
    (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 0 ≤ R.hi) {r : Scc.IR.Reg} {k : Int} (h : rsOf fr r = some k) :
    R.Off k := by
  obtain ⟨h1, h8, h2⟩ := rsOf_bounds hf h
  exact ⟨h8, by omega, by omega⟩

/-- **`hx` at the held call** (`retSlot_bodyN2`): the held frame's result
variable `x` (`hfx`, `HeldC`'s `f.x = x`), placed by the continuation's
symbolic environment as the call's result register, whose cell the call's
code stores to (`hcode`), in a region covering the frame (`hlo`, `hhi`). -/
theorem hx_held {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk kk' : Nat} {pc pc' : Int64} {n : Nat} {g : String}
    {w : Scc.IR.Operand}
    (hcode : InstsC2 fr Cd Bl kk pc [.call [regName "r" n] (Scc.Lower.Names.user g) [w]] kk' pc')
    {R : Region} (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 0 ≤ R.hi) {x : String} {env : Scc.Lower.Env}
    {fs : List TermRun.Frame} (hfx : ∀ f, fs = [f] → f.x = x) :
    ∀ f, fs = [f] → ∃ t r, lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) f.x =
      some (t, [.one (.reg r)]) ∧ ∃ k, rsOf fr r = some k ∧ R.Off k := by
  intro f hf'
  obtain ⟨-, k, -, -, -, -, hk, -⟩ := instsC2_call hcode
  rw [hfx f hf']
  exact ⟨.int, _, lookupS_held x _ env, k, hk, regionOff_of_rsOf hf hlo hhi hk⟩

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.hx_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hx_held
