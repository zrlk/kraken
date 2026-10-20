/-
The single-threaded meaning of the x64 integer and double-precision vector
moves and of `cmpxchg16b` under `vcgen`, on parsed programs: the `MachineWP.*`
rules of Kraken/MachineWP.lean step through the instructions as the parser
produces them.

* Legacy SSE moves: `movdqa` (16-byte aligned) and `movdqu` (any alignment).
* VEX moves: `vmovdqu` (any alignment) and `vmovdqa` (aligned to the width).
* `lock cmpxchg16b`: on one thread a compare-and-swap of a 16-byte cell, which
  succeeds or fails on the compare alone.

Which of these accesses are single-copy atomic between threads (the 16-byte
aligned ones) is the Promising machine's business, not this file's.
-/
import Kraken.X64.Parser
import Kraken.MachineWP

open Std.WP
open Kraken
open Kraken.X64.Parser
open MachineWP

set_option experimental.vcgen true
set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- The low 128 bits of a register after `replaceLow` are the new bits. -/
private theorem take_replaceLow128 (x : BitVec 512) (v : BitVec 128) :
    (x.replaceLow v).take 128 = v := by
  simp only [BitVec.replaceLow, BitVec.drop, BitVec.take]
  ext i hi
  have : i < 512 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  simp
  rw [BitVec.getLsbD_append]
  simp [hi, this]

/-- The low 256 bits of a zero-extended 256-bit value are the value. -/
private theorem take_zeroExtend256 (v : BitVec 256) :
    (v.zeroExtend 512).take 256 = v := by
  simp only [BitVec.take]
  ext i hi
  have : i < 512 := by omega
  simp [this, BitVec.getLsbD_eq_getElem hi]

-- Each case is checked by unfolding, which meets a `2 ^ 512` that is not
-- evaluated under the default threshold.
set_option exponentiation.threshold 512 in
/-- Reading back the register a legacy (SSE) move wrote gives the value moved. -/
private theorem get_setLegacy_xmm (z : RegZmms) (r : RegMm) (v : BitVec 128) :
    (z.setLegacy (.xmm r) v).get (.xmm r) = v := by
  cases r <;> exact take_replaceLow128 _ v

-- Each case is checked by unfolding, which meets a `2 ^ 512` that is not
-- evaluated under the default threshold.
set_option exponentiation.threshold 512 in
/-- Reading back the register a VEX move wrote gives the value moved. -/
private theorem get_set_ymm (z : RegZmms) (r : RegMm) (v : BitVec 256) :
    (z.set (.ymm r) v).get (.ymm r) = v := by
  cases r <;> exact take_zeroExtend256 v

/-- Splitting a 128-bit value into its halves and joining them gives it back. -/
private theorem halves_append (x : BitVec 128) :
    x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x := by
  ext i hi
  rw [BitVec.getElem_append]
  split
  · simp [BitVec.getLsbD_eq_getElem hi]
  · have h : 64 + (i - 64) = i := by omega
    simp [h, BitVec.getLsbD_eq_getElem hi]

/-- A 16-byte load at the address a 16-byte store wrote reads back the bytes. -/
private theorem loadInt_storeInt16 (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 16 x) a 16 = some (Int.ofBytes (Int.toBytes 16 x)) :=
  Mem.loadInt_storeInt m a 16 x (by decide)

/-- A 32-byte load at the address a 32-byte store wrote reads back the bytes. -/
private theorem loadInt_storeInt32 (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 32 x) a 32 = some (Int.ofBytes (Int.toBytes 32 x)) :=
  Mem.loadInt_storeInt m a 32 x (by decide)

variable [layout : _root_.Layout]

/-! ## Legacy SSE moves -/

/-- Copy 16 bytes from an aligned source to an unaligned destination. -/
def sseCopy : Program := parse("
  movdqa (%rdi), %xmm1
  movdqu %xmm1, 3(%rsi)
")

local instance sseCopy.env : CodeEnv := ⟨layout sseCopy⟩

/-- The destination holds the source's 16 bytes. -/
theorem sseCopy_correct (d : MachineData) (v : Int)
    (h_al : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_src : Mem.loadInt d.dmem (d.regs.get64 .rdi) 16 = some v)
    (h_dst : (Mem.loadInt d.dmem (d.regs.get64 .rsi + 3#64) 16).isSome = true) :
    ⦃ fun s => s = d ⦄
      sseCopy
    ⦃ fun _ s => (Mem.loadInt s.dmem (d.regs.get64 .rsi + 3#64) 16).map (BitVec.ofInt 128)
        = some (BitVec.ofInt 128 v) ⦄ := by
  vcgen [sseCopy]
  all_goals simp_all [get_setLegacy_xmm, loadInt_storeInt16,
    BitVec.ofInt_ofBytes_toBytes, -BitVec.toInt_ofInt]

/-! ## VEX moves -/

/-- Copy 32 bytes from an unaligned source to a 32-byte aligned destination. -/
def avxCopy : Program := parse("
  vmovdqu 1(%rdi), %ymm0
  vmovdqa %ymm0, (%rsi)
")

local instance avxCopy.env : CodeEnv := ⟨layout avxCopy⟩

/-- The destination holds the source's 32 bytes. -/
theorem avxCopy_correct (d : MachineData) (v : Int)
    (h_src : Mem.loadInt d.dmem (d.regs.get64 .rdi + 1#64) 32 = some v)
    (h_al : isAligned 32 (d.regs.get64 .rsi) = true)
    (h_dst : (Mem.loadInt d.dmem (d.regs.get64 .rsi) 32).isSome = true) :
    ⦃ fun s => s = d ⦄
      avxCopy
    ⦃ fun _ s => (Mem.loadInt s.dmem (d.regs.get64 .rsi) 32).map (BitVec.ofInt 256)
        = some (BitVec.ofInt 256 v) ⦄ := by
  vcgen [avxCopy]
  all_goals simp_all [get_set_ymm, loadInt_storeInt32,
    BitVec.ofInt_ofBytes_toBytes, -BitVec.toInt_ofInt]

/-! ## `cmpxchg16b` -/

/-- A 16-byte compare-and-swap of `(%rdi)`: `rdx:rax` is the expected value,
`rcx:rbx` the new one. -/
def cas16 : Program := parse("
  lock cmpxchg16b (%rdi)
")

local instance cas16.env : CodeEnv := ⟨layout cas16⟩

/-- When the cell holds `rdx:rax` the swap succeeds: the cell holds `rcx:rbx`
and ZF is set. -/
theorem cas16_success (d : MachineData) (v : Int)
    (h_al : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_cell : Mem.loadInt d.dmem (d.regs.get64 .rdi) 16 = some v)
    (h_eq : BitVec.ofInt 128 v = d.regs.get64 .rdx ++ d.regs.get64 .rax) :
    ⦃ fun s => s = d ⦄
      cas16
    ⦃ fun _ s => s.status.zf = true
        ∧ (Mem.loadInt s.dmem (d.regs.get64 .rdi) 16).map (BitVec.ofInt 128)
            = some (d.regs.get64 .rcx ++ d.regs.get64 .rbx) ⦄ := by
  vcgen [cas16]
  all_goals simp_all [loadInt_storeInt16, BitVec.ofInt_ofBytes_toBytes, -BitVec.toInt_ofInt]

/-- When the cell does not hold `rdx:rax` the swap fails: the cell is left alone,
`rdx:rax` receives its value and ZF is clear. -/
theorem cas16_failure (d : MachineData) (v : Int)
    (h_al : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_cell : Mem.loadInt d.dmem (d.regs.get64 .rdi) 16 = some v)
    (h_ne : BitVec.ofInt 128 v ≠ d.regs.get64 .rdx ++ d.regs.get64 .rax) :
    ⦃ fun s => s = d ⦄
      cas16
    ⦃ fun _ s => s.status.zf = false ∧ s.dmem = d.dmem
        ∧ s.regs.get64 .rdx ++ s.regs.get64 .rax = BitVec.ofInt 128 v ⦄ := by
  vcgen [cas16]
  all_goals simp_all [halves_append]
