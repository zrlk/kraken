/-
**Part 7: a concrete instance of
`mp_relay3_xchg_envG`** (the concrete instances' `ConcreteX64.lean` pattern, as
`X64TakeMpConcrete.lean`): non-vacuity of its start hypotheses
(`StartWX`/`StartYX`/`StartRX`, each with its `Split`).

The writer is `ConcreteX64`'s (`wLayoutX`, `writerX0` at `0x100000`, flag
`f1 = 0x1000`, data `0x1100`); the reader is x64 MP's reader text laid out as
in `ConcreteX64` (`rLayoutX`, at `0x200000`) on the second flag
`f2 = 0x1200`; the relay is laid out as the `.kl` runner lays it out
(`klLayout`) at `0x300000`. Empty private memories (`Split.empty`), the
address registers set. Every hypothesis is discharged by `decide`, `rfl` or
`Split.empty` (no `native_decide`).
-/
import Kraken.Promising.SLR.EnvG.X64RelayXchgPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64

namespace Kraken.Promising.X64.EnvG.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.MpPublic Kraken.Promising.X64.EnvG.RelayX

/-- The second flag word's address. -/
def flag2AddrX : BitVec 64 := 0x1200

/-- The relay's layout: text at `0x300000`. -/
@[reducible] def yLayoutX : _root_.Layout := klLayout relayX 0x300000

theorem yLayoutX_cells : ((yLayoutX relayX).2.map (·.2)) = [0, 1, 1, 1, 1, 1, 1, 0] := by decide

instance yValidX : Executable.ValidLayout (yLayoutX relayX) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The relay's initial state: `%rdi = f1`, `%rsi = data`, `%rdx = f2`, at
`0x300000` (the label `spin`), halting at the end of its text
(`0x300000 + 6`); empty private memory. -/
def relayX0 : X64.State where
  exe := yLayoutX relayX
  endPc := 0x300000 + 6
  st := ({ regs := ((({} : Reg64s).set64 .rdi 0x1000).set64 .rsi 0x1100).set64 .rdx 0x1200 }, 0x300000)

/-- The reader's initial state on `f2`: `%rdi = f2`, `%rsi = data`, at
`0x200000`, as `readerX0`. -/
def readerX2 : X64.State where
  exe := rLayoutX mpReaderX
  endPc := 0x200000 + 4
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1200).set64 .rsi 0x1100 }, 0x200000)

/-- The initial memory: both flags and the data at `0`. -/
def initMemY : List (Loc × Val) := [(⟨flagAddrX, 4⟩, 0), (⟨dataAddrX, 4⟩, 0), (⟨flag2AddrX, 4⟩, 0)]

section
attribute [local instance] yLayoutX

theorem relayX0_start : StartYX flagAddrX flag2AddrX dataAddrX relayX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, Split.empty _⟩

end

section
attribute [local instance] rLayoutX

theorem readerX2_start : StartRX flag2AddrX dataAddrX readerX2 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, Split.empty _⟩

end

/-- **The x64 three-thread relay through `xchg` under `Arch.tso`**, concrete
instance of `mp_relay3_xchg_envG`: every reachable final configuration has
the reader's `ebx` at `43` and the data word at `43`. -/
theorem mp_relay3_xchg_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [writerX0, relayX0, readerX2] initMemY) c) (hf : c.final = true) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨dataAddrX, 4⟩ = 43#128 :=
  mp_relay3_xchg_envG wLayoutX yLayoutX rLayoutX flagAddrX flag2AddrX dataAddrX
    ⟨by decide, by decide, by decide⟩ writerX0_start relayX0_start readerX2_start (by decide) (by decide) hc hf

end Kraken.Promising.X64.EnvG.Concrete

#print axioms Kraken.Promising.X64.EnvG.Concrete.mp_relay3_xchg_envG_concrete
