/-
**The allocator's exits with the heap abort's return address** (x86-64, hello): `Alloc.E`'s exits with the heap
abort's pushed return address, the word past `.full`'s `call scc_rt_abort` in the slot it pushes (`-160`, as
`Alloc.EB .abort`), at a buffer allocation. The x86-64 twin of `Spike/Lib/A64HelloAllocEA.lean` (same name; there
the return address is `x30`).

- `Alloc.EX30`: `E`'s return, `EB`'s abort (the pushed return address kept). The name is AArch64's.
-/
import Spike.Lib.X64AllocBox

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64

section Spec

variable (lab : Label → Int64) (ms : MemSide isa) (q : Call)

/-- **The exits with the heap abort's return address**: `E`'s return, and the heap abort as `E`'s with the return
address of `.full`'s `call scc_rt_abort` in the slot it pushes (`-160`; `EB .abort`'s facts). -/
def EX30 (lbl : WeakMem.AllocLabel → Option Nat) : AX → ND
  | .ret => E lab ms q lbl .ret
  | .abort => ⟨lab "scc_rt_abort", ⟨-160, [(.rbp, -8)]⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧ Jfull ms q c ∧
      σ.slot (-160) = (lab fullL + 12).toBitVec⟩

/-- `EX30`'s abort is `EB`'s. -/
theorem EX30_abort (lbl : WeakMem.AllocLabel → Option Nat) : EX30 lab ms q lbl .abort = EB lab ms q .abort := rfl

end Spec

end Spike.Lib.X64.Alloc

/-- info: 'Spike.Lib.X64.Alloc.EX30_abort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Alloc.EX30_abort
