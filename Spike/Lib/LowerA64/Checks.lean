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
open Scc.Cert.Rt.A64 (blockAt labelGap)

/-- The stack-limit branch's target in the emitted prologue. -/
def proL (c : FnCtx) : Label := c.local (if c.maps then "stack_grow" else "abort_stack")

/-- **The stub's first instruction** the emitter places at `proL c`: with
growth the grow stub's `sub sp, sp, #80` (its save area), without it the
stack abort's load of its code into `x0`. -/
def stkHead (c : FnCtx) : List Directive :=
  (directives (if c.maps then addImm spW64 spW64 (-80) else movImm .X0 Scc.IR.AbortKind.stack.code)).take 1

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

/-- **The return site's label** (P5): the label `x{n}` the emitter places
after the `n`th instruction of a function (`FnCtx.inst`/`FnCtx.term` at
`n`: a checked `+`'s fall-through, a return's site). -/
def retL (cx : FnCtx) (n : Nat) : Label := cx.local s!"x{n}"

/-- The return's directives before its label (P5): the operand's load and
the frame's exit. -/
def tearDirs (cx : FnCtx) (lw : List Item) : List Directive := directives (lw ++ cx.leave)

/-- **A lowered body's code is in `prog`** (P5). The body's blocks are read
in the label-free runs the emitter's labels delimit: the current label `L`
(the body's label, then each fresh label), `o` instructions into its run;
`n` is the number of the next instruction, so of the next fresh label
(`retL cx n`). Each checked `+`'s add block ends `L`'s run, its
fall-through label `retL cx n` follows (`labelGap`) and starts the store's
run; the return's load and frame exit end the run and its label `retL cx n`
starts `[ret]`. -/
def bodyIn (prog : List Directive) (cx : FnCtx) :
    Label → Nat → Nat → List Scc.IR.Inst → List Scc.IR.Operand → Bool
  | L, n, o, [], [w] =>
    match cx.getOp .X0 w with
    | .ok lw =>
      blockAt prog L o (tearDirs cx lw) && labelGap prog L (retL cx n) (o + (tearDirs cx lw).length) &&
        blockAt prog (retL cx n) 0 (directives [ret])
    | .error _ => false
  | L, n, o, .addChk d a b :: is, ws =>
    match cx.getOp .X9 a, cx.getOp .X10 b, cx.slotOff d with
    | .ok la, .ok lb, .ok off =>
      blockAt prog L o (addDirs cx la lb) && labelGap prog L (retL cx n) (o + (addDirs cx la lb).length) &&
        blockAt prog (retL cx n) 0 (strDirs off) && bodyIn prog cx (retL cx n) (n + 1) 1 is ws
    | _, _, _ => false
  | _, _, _, _, _ => false

/-- **A lowered body's blocks** with their instruction offsets after the
body's label, from `k`: `bodyIn`'s blocks, in order. The fresh labels emit
nothing, so the offsets count instructions only; the return's block is the
load, the frame exit and `ret`, across the return site's label. -/
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
entry label, its fresh labels numbered by instruction from 0) and, with at least one instruction, its local overflow block
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
        proInC prog c f.name (c.prefix ++ "0_entry") && bodyIn prog c (c.prefix ++ "0_entry") 0 0 is [w] &&
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
    proInC prog c name (c.prefix ++ "0_entry") = true ∧ bodyIn prog c (c.prefix ++ "0_entry") 0 0 r.insts r.ret = true ∧
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
