/-
**The placement checks of a lowered function** (AArch64): the closed
Booleans `proInC` (the emitted prologue, `Spike/Lib/LowerA64/ProIn.lean`)
and `bodyIn` (the lowered body, `Spike/Lib/LowerA64/BodyIn.lean`), apart
from their soundness so that `PlaceOK` (`Scc/Cert/PlaceOKA64.lean`) reads
them without the segment proofs.
-/
import Spike.Lib.A64CodeSegs
import Scc.Emit.A64
import Scc.Lower.Inv

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64
open Scc.Cert.Rt.A64 (blockAt)

/-- The stack-limit branch's target in the emitted prologue. -/
def proL (c : FnCtx) : Label := c.local (if c.maps then "stack_grow" else "abort_stack")

/-- **The emitted prologue of `c`'s function is in `prog`**, `fn` its
label and `entry` its body's first label. -/
def proInC (prog : List Directive) (c : FnCtx) (fn entry : Label) : Bool :=
  prologueIn prog fn (c.local "stack_check") entry (Int64.ofInt c.frame)
    (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c) []

/-- The add construct's directives: both operands' loads, the checked add. -/
def addDirs (cx : FnCtx) (la lb : List Item) : List Directive :=
  directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))

/-- The slot store after the add. -/
def strDirs (off : Int) : List Directive :=
  directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)]

/-- **The function-local overflow block** the emitter places at
`cx.local "abort_overflow"` when the body has an `addChk`: `movz x0, #1;
bl scc_rt_abort` (the abort's code for overflow, then the call; the halt
loop after it is dead). -/
def ovfBlk : List Directive := directives (movImm .X0 1 ++ [call "scc_rt_abort"])

/-- **A lowered body's code is in `prog`** at `k` instructions after `l`. -/
def bodyIn (prog : List Directive) (cx : FnCtx) (l : Label) : Nat → List Scc.IR.Inst → List Scc.IR.Operand → Bool
  | k, [], [w] =>
    match cx.getOp .X0 w with
    | .ok lw => blockAt prog l k (directives (lw ++ cx.leave ++ [ret]))
    | .error _ => false
  | k, .addChk d a b :: is, ws =>
    match cx.getOp .X9 a, cx.getOp .X10 b, cx.slotOff d with
    | .ok la, .ok lb, .ok off =>
      blockAt prog l k (addDirs cx la lb) && blockAt prog l (k + (addDirs cx la lb).length) (strDirs off) &&
        bodyIn prog cx l (k + (addDirs cx la lb).length + 1) is ws
    | _, _, _ => false
  | _, _, _ => false

/-- **A lowered body's blocks** with their instruction offsets after the
body's label, from `k`: `bodyIn`'s blocks, in order. -/
def bodyBlks (cx : FnCtx) : Nat → List Scc.IR.Inst → List Scc.IR.Operand → List (Nat × List Directive)
  | k, [], [w] =>
    match cx.getOp .X0 w with
    | .ok lw => [(k, directives (lw ++ cx.leave ++ [ret]))]
    | .error _ => []
  | k, .addChk d a b :: is, ws =>
    match cx.getOp .X9 a, cx.getOp .X10 b, cx.slotOff d with
    | .ok la, .ok lb, .ok off =>
      (k, addDirs cx la lb) :: (k + (addDirs cx la lb).length, strDirs off) ::
        bodyBlks cx (k + (addDirs cx la lb).length + 1) is ws
    | _, _, _ => []
  | _, _, _ => []

/-- **A block of a lowered body** at `pc`: one of `bodyBlks`' blocks, at
its offset after the body's label `l`. -/
def InBody (lab : Label → Int64) (cx : FnCtx) (l : Label) (is : List Scc.IR.Inst) (ws : List Scc.IR.Operand)
    (pc : Int64) (blk : List Directive) : Prop :=
  ∃ j, pc = lab l + Int64.ofNat (4 * j) ∧ (j, blk) ∈ bodyBlks cx 0 is ws

/-- An `addChk` instruction (`lower0`'s only kind). -/
def isAddChk : Scc.IR.Inst → Bool
  | .addChk .. => true
  | _ => false

/-- **The placement of every `func0`-shaped function of `ir` in `prog`**
(the lowering's `Accepted0` code blocks: no parameters, the stack check,
one block `entry` ending in a return), each's context `fnCtx` recomputed
from `ir` as `emitItemsMaps` does: its prologue (`proInC`, from its name to
its entry label `prefix ++ "0_entry"`), its body (`bodyIn` after the
entry label) and, with at least one instruction, its local overflow block
(`ovfBlk` at `abort_overflow`). Only the shape `lower0`'s output has is checked (every
instruction an `addChk`, one result); other functions (the runtime's,
multi-block ones, a thread body returning `Unit`, code blocks outside
`Accepted0`) are not checked here. -/
def fnCodeOk (prog : List Directive) (ir : Scc.IR.Program) : Bool :=
  ir.funcs.zipIdx.all fun (f, fi) =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then
        let c := fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi f
        proInC prog c f.name (c.prefix ++ "0_entry") && bodyIn prog c (c.prefix ++ "0_entry") 0 is [w] &&
          (is.isEmpty || blockAt prog (c.local "abort_overflow") 0 ovfBlk)
      else true
    | _, _, _ => true

/-- **`fnCodeOk` at a lowered code block**: `func0 name r` the `fi`th
function of `ir`, its instructions `addChk`s and its result one operand,
has its prologue and body in `prog`, at its context recomputed from `ir`,
and with an instruction its local overflow block (`ovfBlk`). -/
theorem fnCodeOk_func0 {prog : List Directive} {ir : Scc.IR.Program} (h : fnCodeOk prog ir = true)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {fi : Nat} (hf : (Scc.Lower.Inv.func0 name r, fi) ∈ ir.funcs.zipIdx)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    let c := fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi (Scc.Lower.Inv.func0 name r)
    proInC prog c name (c.prefix ++ "0_entry") = true ∧ bodyIn prog c (c.prefix ++ "0_entry") 0 r.insts r.ret = true ∧
      (r.insts ≠ [] → blockAt prog (c.local "abort_overflow") 0 ovfBlk = true) := by
  have hall : r.insts.all isAddChk = true := by
    rw [List.all_eq_true]; intro i hi; obtain ⟨d, a, b, rfl⟩ := hI i hi; rfl
  have := List.all_eq_true.mp h _ hf
  obtain ⟨insts, ret, marked⟩ := r
  simp only at hw hall
  subst hw
  simp only [Scc.Lower.Inv.func0, hall, ite_true, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at this
  exact ⟨this.1.1, this.1.2, fun hne => this.2.resolve_left hne⟩

end Spike.Lib.LowerA64
