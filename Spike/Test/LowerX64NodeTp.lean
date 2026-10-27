import Spike.Lib.LowerX64.NodeTp

/-!
# Body nodes with the thread pointer on x86-64

`Spike/Lib/LowerX64/NodeTp.lean` at work: a register write keeps the `%fs`
base, a block's edge lifts to the nodes with the thread pointer, and the
axioms of the pieces.
-/

namespace Spike.Test.LowerX64NodeTp

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.LowerX64

/-- Writing `%rax` keeps the `%fs` base. -/
example (r : Reg64s) (v : BitVec 64) : (r.set64 .rax v).fsBase = r.fsBase := Reg64s.set64_fsBase r .rax v

/-- The empty block's run keeps the `%fs` base. -/
example (lab : String → Int64) (am : AM) : (arun lab [] am).σ.regs.fsBase = am.σ.regs.fsBase :=
  arun_fsBase lab [] am

/-- A node with the thread pointer has the node's pc. -/
example (n : ND) (tp : UInt64) : (n.withTp tp).pc = n.pc := rfl

/-- info: 'Spike.Lib.X64.arun_fsBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arun_fsBase

/-- info: 'Spike.Lib.LowerX64.BlkEdge.tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlkEdge.tp

/-- info: 'Spike.Lib.LowerX64.BlkEdge.seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlkEdge.seg

/-- info: 'Spike.Lib.LowerX64.BlkW.withTp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlkW.withTp

/-- info: 'Spike.Lib.LowerX64.BlkW.nodeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlkW.nodeW

/-- info: 'Spike.Lib.LowerX64.add_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms add_edge

/-- info: 'Spike.Lib.LowerX64.store_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms store_edge

/-- info: 'Spike.Lib.LowerX64.ret_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ret_edge

/-- info: 'Spike.Lib.LowerX64.sub_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_edge

/-- info: 'Spike.Lib.LowerX64.br_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms br_edge

/-- info: 'Spike.Lib.LowerX64.jmp_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms jmp_edge

end Spike.Test.LowerX64NodeTp
