/-
**Part 8: a concrete instance of
`x64_takeMp_public`** (the concrete instances' `ConcreteX64.lean` pattern): non-vacuity of
its start hypotheses (`StartWX`/`StartTX`, each with its `Split`).

The writer is `ConcreteX64`'s (`wLayoutX`, `writerX0` at `0x100000`, flag
`0x1000`, data `0x1100`, `initMemX`); the writing reader is laid out as the
`.kl` runner lays it out (`klLayout`: labels 0 bytes, every other directive
1) at `0x200000`, with an empty private memory (`Split.empty`) and the
address registers set. Every hypothesis is discharged by `decide`, `rfl` or
`Split.empty` (no `native_decide`).
-/
import Kraken.Promising.SLR.EnvG.X64TakeMpPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64

namespace Kraken.Promising.X64.EnvG.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.MpPublic Kraken.Promising.X64.EnvG.TakeMp

/-- The writing reader's layout: text at `0x200000`. -/
@[reducible] def tLayoutX : _root_.Layout := klLayout takeReaderX 0x200000

theorem tLayoutX_cells : ((tLayoutX takeReaderX).2.map (·.2)) = [0, 1, 1, 1, 1, 1, 0] := by decide

instance tValidX : Executable.ValidLayout (tLayoutX takeReaderX) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The writing reader's initial state: `%rdi = flag`, `%rsi = data`, at
`0x200000` (the label `spin`), halting at the end of its text
(`0x200000 + 5`); empty private memory. -/
def takeReaderX0 : X64.State where
  exe := tLayoutX takeReaderX
  endPc := 0x200000 + 5
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1000).set64 .rsi 0x1100 }, 0x200000)

section
attribute [local instance] tLayoutX

theorem takeReaderX0_start : StartTX flagAddrX dataAddrX takeReaderX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, Split.empty _⟩

end

/-- **x64 message passing with a writing reader under `Arch.tso`**, concrete
instance of `x64_takeMp_public`: every reachable final configuration has the
reader's `ebx` at `43` and the data word at `43`. -/
theorem x64_takeMp_public_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [writerX0, takeReaderX0] initMemX) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨dataAddrX, 4⟩ = 43#128 :=
  x64_takeMp_public wLayoutX tLayoutX flagAddrX dataAddrX (by decide) writerX0_start takeReaderX0_start
    (by decide) hc hf

end Kraken.Promising.X64.EnvG.Concrete

#print axioms Kraken.Promising.X64.EnvG.Concrete.x64_takeMp_public_concrete
