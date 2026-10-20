/-
The single-threaded meaning of the x64 atomics and barriers under `vcgen`, in
both of its x64 logics: on mapped memory a locked read-modify-write is its load
and its store, and `mfence` is a no-op.

* The X64M spec monad: the `Op.*_spec` triples of Kraken/X64M.lean step through
  the encoded primitives, and `easm` reads each load off the preceding store.
* The machine-founded wp on a parsed program: the `MachineWP.*` rules of
  Kraken/MachineWP.lean step through the instructions as the parser produces
  them.

The weak-memory meaning (what `lock` and `mfence` order between threads) is the
Promising machine's, in Kraken/X64/Examples/WeakMemory.lean.
-/
import Kraken.X64M
import Kraken.Easm
import Kraken.X64.Parser
import Kraken.MachineWP

open Std.WP
open Kraken

set_option mvcgen.warning false
set_option grind.warning false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-- A load at the address an 8-byte store wrote reads back the stored bytes. -/
private theorem loadInt_storeInt8 (m : DataMem) (a : BitVec 64) (x : Int) :
    Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
  Mem.loadInt_storeInt m a 8 x (by decide)

/-! ## The X64M spec monad -/

abbrev aeRdi : AddrExpr := { base := some (.reg .rdi), idx := none, disp := .int64 0 }

/-- `xchg %rax, (%rdi)`; `lock addq $5, (%rdi)`; `lock xaddq %rbx, (%rdi)`;
`mfence`. -/
def atomicsProg : X64M Unit Unit := do
  Op.xchg (.low .rax .W64) (.mem aeRdi)
  Op.lockBin .add aeRdi (.imm (.int64 5))
  Op.xadd true (.mem aeRdi) (.low .rbx .W64)
  Op.fence

/-- `xchg` hands the old slot to `rax` and leaves 10; `lock add` makes it 15;
`lock xadd` hands 15 to `rbx` and leaves 115. -/
theorem atomics_correct (env₀ : Env) (s₀ : MachineData) (v : Int)
    (h_rax : s₀.regs.get64 .rax = 10#64) (h_rbx : s₀.regs.get64 .rbx = 100#64)
    (h_mapped : Mem.loadInt s₀.dmem
        (AddrExpr.interp64 env₀.labels aeRdi s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some v) :
    ⦃fun env rip sd => env = env₀ ∧ rip = 0 ∧ sd = ⟨s₀, ()⟩⦄ atomicsProg
      ⦃fun _ _ _ s => s.machine.regs.get64 .rax = BitVec.ofInt 64 v ∧ s.machine.regs.get64 .rbx = 15#64 ∧
          Mem.loadInt s.machine.dmem (s₀.regs.get64 .rdi) 8 = some 115; fun _ _ => True⦄ := by
  -- `easm` reads a load off the local context; this puts the read-back there.
  have h_rt := @loadInt_storeInt8
  vcgen [atomicsProg] with (first (easm) (skip))
  all_goals simp_all [AddrExpr.interp64, AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
    BitVec.take, BitVec.extractLsb'_eq_self, BitVec.ofInt_ofBytes_toBytes_eq]
  all_goals decide

/-- `lock cmpxchgq %rcx, (%rdi)`; `mfence`. -/
def casProg : X64M Unit Unit := do
  Op.cmpxchg true (.mem aeRdi) (.low .rcx .W64)
  Op.fence

/-- Whether or not the compare succeeds, `rax` ends up holding the slot's old
value; when it succeeds the slot holds `rcx`. -/
theorem cas_correct (env₀ : Env) (s₀ : MachineData) (v : Int)
    (h_mapped : Mem.loadInt s₀.dmem
        (AddrExpr.interp64 env₀.labels aeRdi s₀.regs (.mk 0 (0 + Int64.ofNat env₀.curSize))) 8 = some v) :
    ⦃fun env rip sd => env = env₀ ∧ rip = 0 ∧ sd = ⟨s₀, ()⟩⦄ casProg
      ⦃fun _ _ _ s => s.machine.regs.get64 .rax = BitVec.ofInt 64 v ∧
          (BitVec.ofInt 64 v = s₀.regs.get64 .rax →
            (Mem.loadInt s.machine.dmem (s₀.regs.get64 .rdi) 8).map (BitVec.ofInt 64)
              = some (s₀.regs.get64 .rcx)); fun _ _ => True⦄ := by
  have h_rt := @loadInt_storeInt8
  vcgen [casProg] with (first (easm) (skip))
  all_goals simp_all [AddrExpr.interp64, AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
    BitVec.take, BitVec.extractLsb'_eq_self, BitVec.ofInt_ofBytes_toBytes]

/-! ## The machine-founded wp on a parsed program -/

section MachineWP

open Kraken.X64.Parser
open MachineWP

variable [layout : _root_.Layout]

/-- The program of `atomics_correct`, as text. -/
def atomics : Program := parse("
  movq $10, %rax
  xchgq %rax, (%rdi)
  lock addq $5, (%rdi)
  movq $100, %rbx
  lock xaddq %rbx, (%rdi)
  mfence
")

local instance atomics.env : CodeEnv := ⟨layout atomics⟩

theorem atomics_wp_correct (d : MachineData) (v : Int)
    (h_mapped : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 = some v) :
    ⦃ fun s => s = d ⦄
      atomics
    ⦃ fun _ s => s.regs.get64 .rax = BitVec.ofInt 64 v ∧ s.regs.get64 .rbx = 15#64
        ∧ Mem.loadInt s.dmem (d.regs.get64 .rdi) 8 = some 115 ⦄ := by
  vcgen [atomics]
  all_goals simp_all [loadInt_storeInt8, LockBinOp.eval, ofBytes_toBytes, Int.take]
  all_goals (subst_vars; decide)

/-- The swap of a compare-and-swap increment of `(%rdi)`, after `rax` has read
the slot: compute the successor and swap it in if the slot still holds `rax`. -/
def casIncr : Program := parse("
  leaq 1(%rax), %rcx
  lock cmpxchgq %rcx, (%rdi)
")

local instance casIncr.env : CodeEnv := ⟨layout casIncr⟩

/-- With no other thread nothing has changed the slot since `rax` read it, so
the compare succeeds: the slot holds its successor and `rax` its old value. -/
theorem casIncr_correct (d : MachineData) (v : Int)
    (h_mapped : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 = some v)
    (h_rax : d.regs.get64 .rax = BitVec.ofInt 64 v) :
    ⦃ fun s => s = d ⦄
      casIncr
    ⦃ fun _ s => s.regs.get64 .rax = BitVec.ofInt 64 v
        ∧ (Mem.loadInt s.dmem (d.regs.get64 .rdi) 8).map (BitVec.ofInt 64)
            = some (BitVec.ofInt 64 v + 1) ⦄ := by
  vcgen [casIncr]
  -- Keep `toInt` folded so the read-back cancels against the store.
  all_goals simp_all [loadInt_storeInt8, BitVec.ofInt_ofBytes_toBytes, -BitVec.toInt_add,
    -BitVec.toInt_ofInt]

end MachineWP
