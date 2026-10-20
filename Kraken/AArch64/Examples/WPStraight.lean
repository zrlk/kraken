/-
`vcgen` twins of the straight-line `kstep` examples of
`Kraken/AArch64/Examples/Examples.lean` (`swap`, `arith_shift`,
`move_2_regs_to_heap`, `reg_offset_example`), on the machine-founded wp with
the dictionary of `Kraken.AArch64.WP.Rules`. The walk applies one rule per
instruction; `simp` reduces the VC with the register and address API of
`Kraken.AArch64.WP.Specs`, and the arithmetic or memory fact left is closed by
hand.

The memory examples are stated on mapped memory, like x64's machine-founded
examples: the bytes the program accesses are readable (`Mem.loadInt … isSome`),
where the `kstep` originals assume a separating conjunction of their contents.
`arith_shift` was parked on the `kstep` side (`bv_decide` leaves
`BitVec.ofInt 64 (Int64.toInt c)` opaque); here the rules state immediates as
`c.toBitVec`, which `simp` folds to a literal, and `grind`'s ring closes the
goal, without `bv_decide`.

Each triple is also read at the machine (`Kraken.AArch64.WP.Bridge`): by
`Program.instrStep_of_triple` as the instruction-step judgment from the start
address to the end of the text, and by `Program.run_of_triple` as the baseline
judgment `Eventually (straightlineStep …)`.
-/
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.Bridge
import Kraken.AArch64.WP.Rules

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## Helpers -/

/-- A left shift is a multiplication by the power of two. -/
private theorem shiftLeft_eq_mul {w : Nat} (x : BitVec w) (k : Nat) :
    x <<< k = x * BitVec.ofNat w (2 ^ k) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow]

/-- A load at the address an 8-byte store wrote reads back the stored bytes. -/
private theorem loadInt_storeInt_same (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
  Mem.loadInt_storeInt m a 8 x (by decide)

/-- An 8-byte store leaves the 8 bytes above it alone. -/
private theorem loadInt_storeInt_above (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 8 x) (a + 8#64) 8 = Mem.loadInt m (a + 8#64) 8 :=
  Mem.loadInt_storeInt_of_above m a (a + 8#64) 8 8 x
    (by rw [show a + 8#64 - a = 8#64 by grind]; decide)
    (by rw [show a + 8#64 - a = 8#64 by grind]; decide)

/-- An 8-byte store leaves the 8 bytes below it alone. -/
private theorem loadInt_storeInt_below (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m (a + 8#64) 8 x) a 8 = Mem.loadInt m a 8 :=
  Mem.loadInt_storeInt_of_above m (a + 8#64) a 8 8 x
    (by rw [show a - (a + 8#64) = -8#64 by grind]; decide)
    (by rw [show a - (a + 8#64) = -8#64 by grind]; decide)

/-- A load at the address a 1-byte store wrote reads back the stored byte. -/
private theorem loadInt_storeInt_same1 (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 1 x) a 1 = some (Int.ofBytes (Int.toBytes 1 x)) :=
  Mem.loadInt_storeInt m a 1 x (by decide)

/-- The low byte of a register, read as a signed byte and re-encoded. -/
private theorem ofInt_bmod_toNat (x : UInt64) :
    BitVec.ofInt 8 ((x.toNat : Int).bmod 256) = x.toBitVec.setWidth 8 := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_setWidth]
  simp only [Int.bmod_bmod]
  rfl

/-- Sixteen below a 16-byte aligned address is 16-byte aligned. -/
private theorem aligned_sub16 (x : BitVec 64) (h : x % 16#64 = 0#64) :
    (x + 18446744073709551600#64) % 16#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_umod, BitVec.toNat_add] at *
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
  omega

/-! ## Programs -/

/-- Register swap with `EOR` (shifted-register form). -/
def swap : Program := parseAArch64("
  eor x0, x0, x1
  eor x1, x0, x1
  eor x0, x0, x1")

/-- `ADD` (immediate), `LSL` (the alias of `UBFM`), `SUB` (shifted register). -/
def arith_shift : Program := parseAArch64("
  add x0, x1, #42
  lsl x2, x0, #2
  sub x3, x2, x0
")

/-- `STR`/`LDR` at a base register plus an immediate offset. -/
def move_2_regs_to_heap : Program := parseAArch64("
    str x0, [x2]
    str x1, [x2, #8]
    ldr x3, [x2]
    ldr x4, [x2, #8]
")

/-- `STR`/`LDR` at a base register plus a shifted index register. -/
def reg_offset_example : Program := parseAArch64("
    mov x0, #42
    str x0, [x1, x2, lsl #3]
    mov x0, #0
    ldr x3, [x1, x2, lsl #3]
")

variable [layout : _root_.Layout]

/-! ## `swap` -/

section
/-- The ambient code of `swap`, laid out. -/
local instance swap.env : CodeEnv := ⟨layout swap⟩

theorem swap_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄
      swap
    ⦃ fun _ s => s.regs.getRegOrZr .X0 = d.regs.getRegOrZr .X1
        ∧ s.regs.getRegOrZr .X1 = d.regs.getRegOrZr .X0 ⦄ := by
  vcgen [swap]
  subst_vars
  simp [BitVec.xor_assoc]
  rw [BitVec.xor_comm, BitVec.xor_assoc]
  simp

/-- `swap_correct`, read at the machine as the instruction-step judgment. -/
theorem swap_instrStep [Executable.ValidLayout (layout swap)] (d : MachineData) :
    Eventually (layout swap).instrStep
      (fun st => st.2 = (layout swap).addrOf swap.length
        ∧ st.1.regs.getRegOrZr .X0 = d.regs.getRegOrZr .X1
        ∧ st.1.regs.getRegOrZr .X1 = d.regs.getRegOrZr .X0)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (swap_correct d) rfl

/-- `swap_correct`, read at the machine as the baseline judgment. -/
theorem swap_run [Executable.ValidLayout (layout swap)] (d : MachineData) :
    Eventually (straightlineStep (layout swap))
      (fun st => st.1.regs.getRegOrZr .X0 = d.regs.getRegOrZr .X1
        ∧ st.1.regs.getRegOrZr .X1 = d.regs.getRegOrZr .X0)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (swap_correct d) rfl
end

/-! ## `arith_shift` -/

section
/-- The ambient code of `arith_shift`, laid out. -/
local instance arith_shift.env : CodeEnv := ⟨layout arith_shift⟩

theorem arith_shift_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄
      arith_shift
    ⦃ fun _ s => s.regs.getRegOrZr .X3 = 3 * (d.regs.getRegOrZr .X1 + 42) ⦄ := by
  vcgen [arith_shift]
  subst_vars
  simp
  rw [shiftLeft_eq_mul]
  grind

/-- `arith_shift_correct`, read at the machine as the instruction-step judgment. -/
theorem arith_shift_instrStep [Executable.ValidLayout (layout arith_shift)] (d : MachineData) :
    Eventually (layout arith_shift).instrStep
      (fun st => st.2 = (layout arith_shift).addrOf arith_shift.length
        ∧ st.1.regs.getRegOrZr .X3 = 3 * (d.regs.getRegOrZr .X1 + 42))
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (arith_shift_correct d) rfl

/-- `arith_shift_correct`, read at the machine as the baseline judgment. -/
theorem arith_shift_run [Executable.ValidLayout (layout arith_shift)] (d : MachineData) :
    Eventually (straightlineStep (layout arith_shift))
      (fun st => st.1.regs.getRegOrZr .X3 = 3 * (d.regs.getRegOrZr .X1 + 42))
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (arith_shift_correct d) rfl
end

/-! ## `move_2_regs_to_heap` -/

section
/-- The ambient code of `move_2_regs_to_heap`, laid out. -/
local instance move_2_regs_to_heap.env : CodeEnv := ⟨layout move_2_regs_to_heap⟩

theorem move_2_regs_to_heap_correct (d : MachineData)
    (h0 : (Mem.loadInt d.dmem d.regs.X2.toBitVec 8).isSome)
    (h8 : (Mem.loadInt d.dmem (d.regs.X2.toBitVec + 8#64) 8).isSome) :
    ⦃ fun s => s = d ⦄
      move_2_regs_to_heap
    ⦃ fun _ s => s.regs.X3 = d.regs.X0 ∧ s.regs.X4 = d.regs.X1 ∧ s.regs.X2 = d.regs.X2 ⦄ := by
  vcgen [move_2_regs_to_heap]
  all_goals subst_vars
  all_goals simp_all [loadInt_storeInt_same, loadInt_storeInt_above, loadInt_storeInt_below]
  all_goals subst_vars
  all_goals simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

/-- `move_2_regs_to_heap_correct`, read at the machine as the instruction-step judgment. -/
theorem move_2_regs_to_heap_instrStep [Executable.ValidLayout (layout move_2_regs_to_heap)]
    (d : MachineData)
    (h0 : (Mem.loadInt d.dmem d.regs.X2.toBitVec 8).isSome)
    (h8 : (Mem.loadInt d.dmem (d.regs.X2.toBitVec + 8#64) 8).isSome) :
    Eventually (layout move_2_regs_to_heap).instrStep
      (fun st => st.2 = (layout move_2_regs_to_heap).addrOf move_2_regs_to_heap.length
        ∧ st.1.regs.X3 = d.regs.X0 ∧ st.1.regs.X4 = d.regs.X1 ∧ st.1.regs.X2 = d.regs.X2)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (move_2_regs_to_heap_correct d h0 h8) rfl

/-- `move_2_regs_to_heap_correct`, read at the machine as the baseline judgment. -/
theorem move_2_regs_to_heap_run [Executable.ValidLayout (layout move_2_regs_to_heap)]
    (d : MachineData)
    (h0 : (Mem.loadInt d.dmem d.regs.X2.toBitVec 8).isSome)
    (h8 : (Mem.loadInt d.dmem (d.regs.X2.toBitVec + 8#64) 8).isSome) :
    Eventually (straightlineStep (layout move_2_regs_to_heap))
      (fun st => st.1.regs.X3 = d.regs.X0 ∧ st.1.regs.X4 = d.regs.X1 ∧ st.1.regs.X2 = d.regs.X2)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (move_2_regs_to_heap_correct d h0 h8) rfl
end

/-! ## `reg_offset_example` -/

section
/-- The ambient code of `reg_offset_example`, laid out. -/
local instance reg_offset_example.env : CodeEnv := ⟨layout reg_offset_example⟩

theorem reg_offset_example_correct (d : MachineData)
    (h : (Mem.loadInt d.dmem (d.regs.X1.toBitVec + d.regs.X2.toBitVec <<< 3) 8).isSome) :
    ⦃ fun s => s = d ⦄
      reg_offset_example
    ⦃ fun _ s => s.regs.X3 = 42 ⦄ := by
  vcgen [reg_offset_example]
  all_goals subst_vars
  all_goals simp_all [loadInt_storeInt_same]
  all_goals subst_vars
  all_goals simp [BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl]
  all_goals rfl

/-- `reg_offset_example_correct`, read at the machine as the instruction-step judgment. -/
theorem reg_offset_example_instrStep [Executable.ValidLayout (layout reg_offset_example)]
    (d : MachineData)
    (h : (Mem.loadInt d.dmem (d.regs.X1.toBitVec + d.regs.X2.toBitVec <<< 3) 8).isSome) :
    Eventually (layout reg_offset_example).instrStep
      (fun st => st.2 = (layout reg_offset_example).addrOf reg_offset_example.length
        ∧ st.1.regs.X3 = 42)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (reg_offset_example_correct d h) rfl

/-- `reg_offset_example_correct`, read at the machine as the baseline judgment. -/
theorem reg_offset_example_run [Executable.ValidLayout (layout reg_offset_example)]
    (d : MachineData)
    (h : (Mem.loadInt d.dmem (d.regs.X1.toBitVec + d.regs.X2.toBitVec <<< 3) 8).isSome) :
    Eventually (straightlineStep (layout reg_offset_example))
      (fun st => st.1.regs.X3 = 42)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (reg_offset_example_correct d h) rfl
end

/-! ## Coverage tests

Small programs that exercise more of the dictionary under `vcgen`: `W`
registers, flags, conditional select and compare, writeback, pairs, bytes and
label addresses. -/

/-- `W` forms: move wide, `MOV`, `ADD`, the `LSR` alias. A `W` write zero-extends. -/
def wp_w32 : Program := parseAArch64("
  movz w0, #0xffff
  movk w0, #0x1234, lsl #16
  mov w1, w0
  add w2, w1, #1
  lsr w3, w0, #16
  asr x4, x5, #63
")

section
local instance wp_w32.env : CodeEnv := ⟨layout wp_w32⟩

theorem wp_w32_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄
      wp_w32
    ⦃ fun _ s => s.regs.X0 = 0x1234ffff ∧ s.regs.X1 = 0x1234ffff ∧ s.regs.X2 = 0x12350000
        ∧ s.regs.X3 = 0x1234 ∧ s.regs.X4.toBitVec = d.regs.X5.toBitVec.sshiftRight 63 ⦄ := by
  vcgen [wp_w32]
  all_goals subst_vars
  all_goals simp
end

/-- Flags: `CMP`, `CSEL`, `CCMP`, `CSET`. -/
def wp_flags : Program := parseAArch64("
  cmp x1, x2
  csel x3, x4, x5, eq
  ccmp x1, x2, #0, eq
  cset x6, eq
  madd x7, x1, x2, x4
")

section
local instance wp_flags.env : CodeEnv := ⟨layout wp_flags⟩

theorem wp_flags_correct (d : MachineData) (h : d.regs.X1 = d.regs.X2) :
    ⦃ fun s => s = d ⦄
      wp_flags
    ⦃ fun _ s => s.regs.X3 = d.regs.X4 ∧ s.regs.X6 = 1
        ∧ s.regs.X7 = d.regs.X1 * d.regs.X2 + d.regs.X4 ⦄ := by
  vcgen [wp_flags]
  all_goals subst_vars
  all_goals simp [h]
end

/-- A pair pushed with pre-index writeback and popped with post-index writeback. -/
def wp_pair : Program := parseAArch64("
  stp x0, x1, [sp, #-16]!
  ldp x2, x3, [sp], #16
")

section
local instance wp_pair.env : CodeEnv := ⟨layout wp_pair⟩

theorem wp_pair_correct (d : MachineData) (hal : d.regs.SP.toBitVec % 16#64 = 0#64)
    (h0 : (Mem.loadInt d.dmem (d.regs.SP.toBitVec - 16#64) 8).isSome)
    (h8 : (Mem.loadInt d.dmem (d.regs.SP.toBitVec - 16#64 + 8#64) 8).isSome) :
    ⦃ fun s => s = d ⦄
      wp_pair
    ⦃ fun _ s => s.regs.X2 = d.regs.X0 ∧ s.regs.X3 = d.regs.X1 ∧ s.regs.SP = d.regs.SP ⦄ := by
  have e : d.regs.SP.toBitVec - 16#64 = d.regs.SP.toBitVec + 18446744073709551600#64 := by grind
  rw [e] at h0 h8
  vcgen [wp_pair]
  all_goals subst_vars
  all_goals simp_all [loadInt_storeInt_same, loadInt_storeInt_above, loadInt_storeInt_below]
  all_goals subst_vars
  all_goals try simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  · exact aligned_sub16 _ hal
  · rw [UInt64.add_assoc]; exact UInt64.add_zero _
end

/-- A byte stored and loaded back; a label's address. -/
def wp_byte : Program := parseAArch64("
  strb w0, [x1, #1]
  ldrb w2, [x1, #1]
  adr x3, start
start:
  nop
")

section
local instance wp_byte.env : CodeEnv := ⟨layout wp_byte⟩

theorem wp_byte_correct (d : MachineData)
    (h : (Mem.loadInt d.dmem (d.regs.X1.toBitVec + 1#64) 1).isSome) :
    ⦃ fun s => s = d ⦄
      wp_byte
    ⦃ fun _ s => s.regs.X2.toBitVec = (d.regs.X0.toBitVec.setWidth 8).setWidth 64
        ∧ s.regs.X3.toBitVec = ((_root_.Executable.labels cenv).label "start").toBitVec ⦄ := by
  vcgen [wp_byte]
  all_goals subst_vars
  all_goals simp_all [loadInt_storeInt_same1]
  all_goals subst_vars
  all_goals simp [BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl]
  rw [ofInt_bmod_toNat]
end
