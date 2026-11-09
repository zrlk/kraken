import Scc.IR.BlockLen

/-!
# Instruction shapes for the block-length byte bound

Every `Inst` and `Term` constructor, with the operand variations that change
an emitter's code size: registers and immediates (0 and a 64-bit pattern with
four non-zero halfwords, the longest to materialise on both ISAs), address
displacements in and out of each ISA's short forms, and every argument and
result count up to the IR's limits.  `Spike/Test/BlockLenX64.lean` and
`Spike/Test/BlockLenA64.lean` emit each shape and check that it takes at most
`bytesPerWeight` bytes per weight unit (`Scc.IR.instWeight`,
`Scc.IR.termWeight`).  Untrusted.
-/

namespace Scc.Test.BlockLen

open Scc.IR

/-- Operands: a register, a short and a long immediate. -/
def ops : List Operand := [.reg "a", .imm 0, .imm 0x123456789abcdef1]

/-- Address displacements: zero, short, scaled, beyond the short forms. -/
def disps : List Int := [0, 8, -8, 255, -256, 4088, 32760, 65536, -65536]

def widths : List Width := [.w8, .w16, .w32, .w64]
def binOps : List BinOp :=
  [.add, .sub, .mul, .umulh, .udiv, .sdiv, .urem, .srem, .and, .or, .xor, .shl, .lshr, .ashr]
def unOps : List UnOp := [.not, .neg, .ctz, .popcnt]
def syss : List Sys := [.write, .exit, .exitGroup, .futex, .rtSigaction]

/-- `n` arguments, all `o`. -/
def argsOf (o : Operand) (n : Nat) : List Operand := List.replicate n o
/-- `n` result registers. -/
def resOf (n : Nat) : List Reg := (List.range n).map (s!"r{·}")

/-- The instruction shapes. -/
def insts : List Inst :=
  ops.map (.mov "d" ·) ++
  binOps.flatMap (fun op => ops.flatMap fun a => ops.map fun b => .bin op "d" a b) ++
  unOps.flatMap (fun op => ops.map (.un op "d" ·)) ++
  [true, false].flatMap (fun s => widths.flatMap fun w => ops.map (.ext s w "d" ·)) ++
  ops.flatMap (fun a => ops.map fun b => .setc .eq "d" a b) ++
  ops.flatMap (fun a => ops.flatMap fun b => ops.flatMap fun t => ops.map fun f =>
    .select .ult "d" a b t f) ++
  ops.flatMap (fun a => ops.map fun b => .addChk "d" a b) ++
  ops.flatMap (fun a => ops.map fun b => .subSat "d" a b) ++
  [.la "d" "sym", .getTp "d"] ++
  [Order.plain, .acq].flatMap (fun o => widths.flatMap fun w => disps.map fun k =>
    .load o w "d" ⟨"b", k⟩) ++
  [Order.plain, .rel].flatMap (fun o => widths.flatMap fun w => disps.flatMap fun k =>
    ops.map fun v => .store o w ⟨"b", k⟩ v) ++
  [RmwOp.xchg, .add].flatMap (fun op => disps.flatMap fun k => ops.map fun v =>
    .rmw op "d" ⟨"b", k⟩ v) ++
  [Fence.ld, .st, .full].map .fence ++
  (List.range (maxArgs + 1)).flatMap (fun n => (List.range (maxRets + 1)).flatMap fun m =>
    [Operand.reg "a", .imm 0x123456789abcdef1].map fun o => .call (resOf m) "g" (argsOf o n)) ++
  syss.flatMap (fun nr => (List.range (maxRegArgs + 1)).flatMap fun n =>
    [none, some "lbl"].map fun l => .syscall "d" nr (argsOf (.imm 0x123456789abcdef1) n) l) ++
  ops.map (fun o => .clone "d" o o "g" o) ++
  [.slotAddr "d" "a"] ++
  (List.range (maxRegArgs + 1)).map (fun n => .site "site" (argsOf (.imm 0x123456789abcdef1) n)) ++
  [.comment "c"]

/-- The terminator shapes. -/
def terms : List Term :=
  (List.range (maxRets + 1)).flatMap (fun n => ops.map fun o => .ret (argsOf o n)) ++
  [.jmp "l"] ++
  ops.flatMap (fun a => ops.map fun b => .br .sge a b "t" "f") ++
  (List.range (maxArgs + 1)).flatMap (fun n => ops.map fun o => .tail "g" (argsOf o n)) ++
  ops.map (fun o => .switchTo o o "g" o) ++
  [.unreachable]

/-- The IR registers the shapes use (the frame gives each a slot). -/
def regs : List Reg := ["a", "b", "d"] ++ resOf maxRets ++ spawnRegs

/-- The block labels the shapes name. -/
def labels : List Label := ["l", "t", "f"]

end Scc.Test.BlockLen
