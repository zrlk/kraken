/-
**A concrete instance of
`x64_mp_incl_envG`** (the concrete instances' `ConcreteX64.lean` pattern): non-vacuity of
its start hypotheses (`StartWIX`/`StartRX`, each with its `Split`).

The reader is `ConcreteX64`'s (`rLayoutX`, `readerX0` at `0x200000`, flag
`0x1000`, data `0x1100`, `initMemX`); the `incl` writer is laid out as the
`.kl` runner lays it out (`klLayout`: labels 0 bytes, every other directive
1) at `0x100000`, with an empty private memory (`Split.empty`) and the
address registers set. Every hypothesis is discharged by `decide`, `rfl` or
`Split.empty` (no `native_decide`).
-/
import Kraken.Promising.SLR.EnvG.X64MpIncPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64

namespace Kraken.Promising.X64.EnvG.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.MpPublic Kraken.Promising.X64.EnvG.MpInc

/-- The `incl` writer's layout: text at `0x100000`. -/
@[reducible] def iLayoutX : _root_.Layout := klLayout mpIncWriterX 0x100000

theorem iLayoutX_cells : ((iLayoutX mpIncWriterX).2.map (·.2)) = [1, 1] := by decide

instance iValidX : Executable.ValidLayout (iLayoutX mpIncWriterX) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The `incl` writer's initial state: `%rdi = flag`, `%rsi = data`, at
`0x100000`, halting at the end of its text (`0x100000 + 2`); empty private
memory. -/
def incWriterX0 : X64.State where
  exe := iLayoutX mpIncWriterX
  endPc := 0x100000 + 2
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1000).set64 .rsi 0x1100 }, 0x100000)

section
attribute [local instance] iLayoutX

theorem incWriterX0_start : StartWIX flagAddrX dataAddrX incWriterX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, Split.empty _⟩

end

/-- **x64 message passing with an unlocked `incl` release under
`Arch.tso`**, concrete instance of `x64_mp_incl_envG`: every reachable final
configuration has the reader's `ebx` at `42` and the data word at `42`. -/
theorem x64_mp_incl_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [incWriterX0, readerX0] initMemX) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨dataAddrX, 4⟩ = 42#128 :=
  x64_mp_incl_envG iLayoutX rLayoutX flagAddrX dataAddrX (by decide) incWriterX0_start readerX0_start
    (by decide) hc hf

end Kraken.Promising.X64.EnvG.Concrete

#print axioms Kraken.Promising.X64.EnvG.Concrete.x64_mp_incl_envG_concrete
