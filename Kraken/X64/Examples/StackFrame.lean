module

public import Kraken.StateCfg
public import Kraken.SepCells
import Kraken.X64.Parser

/-!
A compiler's frame code, straight-line: the prologue, a spill of the argument,
a compare against it, a reload, a byte local written and read back, and the
epilogue. The proof exercises the stack and sub-register rules together with
the `=@`/`?@` cells: the saved frame pointer survives the local stores, the
locals are read back as written, and the frame comes back as owned bytes.
-/

open Kraken.X64.Parser
open Std.WP
open Std.ExtHashMap
open Mem
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true
set_option grind.warning false

namespace Kraken.Examples.StackFrame

def frame : Program := parse("
start:
  pushq %rbp
  movq %rsp, %rbp
  subq $16, %rsp
  movl %edi, -8(%rbp)
  cmpl $0, -8(%rbp)
  movl -8(%rbp), %edi
  movb $1, -1(%rbp)
  movb -1(%rbp), %al
  andb $1, %al
  addq $16, %rsp
  popq %rbp
")

/-- The cells of the frame below the entry stack pointer `r`, in front of the
rest `R`: the saved frame pointer's slot, the unused 8 bytes, the 4-byte
local, 3 unused bytes, the byte local. -/
abbrev FrameCells (r : BitVec 64) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 8) ⋆ (8 ?@ (r - 24) ⋆ (4 ?@ (r - 16) ⋆ (3 ?@ (r - 12) ⋆ (1 ?@ (r - 9) ⋆ R))))

/-- The postcondition. -/
abbrev Post (d s : MachineData) (R : Mem 64 → Prop) : Prop :=
  s.regs.get64 .rsp = d.regs.get64 .rsp
  ∧ s.regs.get64 .rbp = d.regs.get64 .rbp
  ∧ (s.regs.get64 .rdi).toNat = (d.regs.get64 .rdi).toNat % 2 ^ 32
  ∧ (s.regs.get64 .rax).toNat % 256 = 1
  ∧ s.dmem =⋆ FrameCells (d.regs.get64 .rsp) R

/-- The reloads read back what the stores wrote, at 4 bytes and at 1 byte. -/
theorem get!_loadInt_storeInt_4 (m : DataMem) (a : BitVec 64) (v : Int) :
    ((m.storeInt a 4 v).loadInt a 4).get! = Int.ofBytes (Int.toBytes 4 v) := by
  rw [Mem.loadInt_storeInt m a 4 v (by decide), Option.get!_some]

theorem get!_loadInt_storeInt_1 (m : DataMem) (a : BitVec 64) (v : Int) :
    ((m.storeInt a 1 v).loadInt a 1).get! = Int.ofBytes (Int.toBytes 1 v) := by
  rw [Mem.loadInt_storeInt m a 1 v (by decide), Option.get!_some]

theorem ofInt_ofBytes_toBytes_32 (v : Int) :
    BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v)) = BitVec.ofInt 32 v :=
  BitVec.ofInt_ofBytes_toBytes 32 4 rfl v

theorem ofInt_ofBytes_toBytes_64 (v : Int) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v)) = BitVec.ofInt 64 v :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl v

theorem ofBytes_toBytes_one : Int.ofBytes (Int.toBytes 1 1) = 1 := by decide

/-- `leave`-style address arithmetic as `kvcgen64` leaves it. -/
theorem add_sub_16 (x : BitVec 64) : 16#64 + (x - 16#64) = x := by grind

/-- The locals' stores below the saved frame pointer's slot at `r` leave it
alone. The displacements are spelled as `kvcgen64` leaves them. -/
theorem loadInt_storeInt_below_1 (m : DataMem) (r : BitVec 64) (v : Int) :
    (Mem.storeInt m (r + 18446744073709551615#64) 1 v).loadInt r 8 = m.loadInt r 8 := by
  have h : (r - (r + 18446744073709551615#64)).toNat = 1 := by
    rw [show r - (r + 18446744073709551615#64) = 1#64 by grind]; rfl
  exact Mem.loadInt_storeInt_of_above m _ r 1 8 v (by omega) (by omega)

theorem loadInt_storeInt_below_4 (m : DataMem) (r : BitVec 64) (v : Int) :
    (Mem.storeInt m (r + 18446744073709551608#64) 4 v).loadInt r 8 = m.loadInt r 8 := by
  have h : (r - (r + 18446744073709551608#64)).toNat = 8 := by
    rw [show r - (r + 18446744073709551608#64) = 8#64 by grind]; rfl
  exact Mem.loadInt_storeInt_of_above m _ r 4 8 v (by omega) (by omega)

/-- The low byte of a register after a byte write is the byte written. -/
theorem toNat_replaceLow_8 (x : BitVec 64) (v : BitVec 8) :
    (x.replaceLow v).toNat % 256 = v.toNat := by
  have h := congrArg BitVec.toNat (BitVec.take_replaceLow_8 x v)
  simpa [BitVec.take, BitVec.extractLsb'_toNat] using h

/-- The 32-bit reload, zero-extended, is the low half of the spilled register. -/
theorem toNat_setWidth_take_32 (x : BitVec 64) :
    (BitVec.setWidth 64 (x.take 32)).toNat = x.toNat % 4294967296 := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]; omega

attribute [local grind =] get!_loadInt_storeInt_4 get!_loadInt_storeInt_1
  ofInt_ofBytes_toBytes_32 ofInt_ofBytes_toBytes_64 ofBytes_toBytes_one add_sub_16
  loadInt_storeInt_below_1 loadInt_storeInt_below_4 toNat_replaceLow_8 BitVec.ofInt_toInt
  toNat_setWidth_take_32

/- The cell rules chain through the tree (a demand down to the cell, a split
back up, per access, then a walk of the goal's tree), so `finish` needs many
more E-matching rounds and a deeper generation bound than its defaults; see
`grind_cells` in `SepCells`. -/
theorem frame_correct [Host] [FunDecls] (d : MachineData) (R : Mem 64 → Prop)
    (hmem : d.dmem =⋆ FrameCells (d.regs.get64 .rsp) R) :
    WP.wp frame (fun _ s => Post d s R) (fun _ _ => False) d := by
  refine Program.WP.cfg (fun
      | .entry, t | .label "start", t => t = d
      | .exit, t => Post d t R
      | _, _ => False)
    (fun _ _ => 0) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish (ematch := 400) (gen := 400) (instances := 20000)

end Kraken.Examples.StackFrame
