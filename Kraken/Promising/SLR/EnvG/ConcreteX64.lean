/-
**Concrete instances of the x64 public theorems**: non-vacuity of their start
hypotheses (`StartWX`/`StartRX`,
`StartStateG`, each with its `Split`). Text laid out as the `.kl` runner lays
it out (`Kraken.Litmus.X64.prepareProgram`: labels 0 bytes, every other
directive 1, as `SLR/X64SpinConcrete.lean`); start states with empty private
memory (`Split.empty`) and the address registers set. Every hypothesis is
discharged by `decide`, `rfl` or `simp` (no `native_decide`).

- `x64_mp_public_concrete` (`MpPublic.x64_mp_public`, `Arch.tso`): writer at
  `0x100000`, reader at `0x200000`, flag `0x1000`, data `0x1100`;
- `x64_spin_counter_envG_concreteN`/`_concrete2`
  (`SpinPublicG.x64_spin_counter_envG`, `Arch.tso`): `spinWorkerG` at
  `0x100000`, lock `0x1000000`, counter `0x1000100`; general `N < 2 ^ 32`
  and `N = 2`.

`klLayout`/`cellOk`/`validLayout_of_cells` (a generic copy of
`X64SpinConcrete`'s private `spinLayout`/`spinValid` argument, for any program
and start) are in `EnvG/ConcreteX64Layout.lean` (same names);
`Config.init_mem` is in `EnvG/ConcreteCommon.lean`.
-/
import Kraken.Promising.SLR.EnvG.X64MpPublic
import Kraken.Promising.SLR.EnvG.X64SpinPublicG
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon

namespace Kraken.Promising.X64.EnvG.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64

/-! ## `x64_mp_public` -/

section Mp

open Kraken.Promising.X64.EnvG.MpSmoke Kraken.Promising.X64.EnvG.MpPublic

/-- The writer's layout: text at `0x100000`. -/
@[reducible] def wLayoutX : _root_.Layout := klLayout mpWriterX 0x100000
/-- The reader's layout: text at `0x200000`. -/
@[reducible] def rLayoutX : _root_.Layout := klLayout mpReaderX 0x200000

theorem wLayoutX_cells : ((wLayoutX mpWriterX).2.map (·.2)) = [1, 1, 1, 1] := by decide
theorem rLayoutX_cells : ((rLayoutX mpReaderX).2.map (·.2)) = [0, 1, 1, 1, 1, 0] := by decide

instance wValidX : Executable.ValidLayout (wLayoutX mpWriterX) :=
  validLayout_of_cells _ (by decide) (by decide)

instance rValidX : Executable.ValidLayout (rLayoutX mpReaderX) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The flag word's address. -/
def flagAddrX : BitVec 64 := 0x1000
/-- The data word's address. -/
def dataAddrX : BitVec 64 := 0x1100

/-- The writer's initial state: `%rdi = flag`, `%rsi = data`, at `0x100000`,
halting at the end of its text (`0x100000 + 4`); empty private memory. -/
def writerX0 : X64.State where
  exe := wLayoutX mpWriterX
  endPc := 0x100000 + 4
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1000).set64 .rsi 0x1100 }, 0x100000)

/-- The reader's initial state: `%rdi = flag`, `%rsi = data`, at `0x200000`
(the label `spin`), halting at the end of its text (`0x200000 + 4`). -/
def readerX0 : X64.State where
  exe := rLayoutX mpReaderX
  endPc := 0x200000 + 4
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1000).set64 .rsi 0x1100 }, 0x200000)

/-- The initial memory: `flag = 0`, `data = 0`. -/
def initMemX : List (Loc × Val) := [(⟨flagAddrX, 4⟩, 0), (⟨dataAddrX, 4⟩, 0)]

section
attribute [local instance] wLayoutX

theorem writerX0_start : StartWX flagAddrX dataAddrX writerX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, Split.empty _⟩

end

section
attribute [local instance] rLayoutX

theorem readerX0_start : StartRX flagAddrX dataAddrX readerX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, Split.empty _⟩

end

/-- **x64 message passing under `Arch.tso`**, concrete instance of
`x64_mp_public`: every reachable final configuration has the reader's `ebx`
at `42` and the data word at `42`. -/
theorem x64_mp_public_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [writerX0, readerX0] initMemX) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal ⟨dataAddrX, 4⟩ = 42#128 :=
  x64_mp_public wLayoutX rLayoutX flagAddrX dataAddrX (by decide) writerX0_start readerX0_start
    (by decide) hc hf

end Mp

/-! ## `x64_spin_counter_envG` -/

section Spin

open Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinPublicG

/-- The worker's layout: text at `0x100000`. -/
@[reducible] def spinLayoutG : _root_.Layout := klLayout spinWorkerG 0x100000

theorem spinLayoutG_cells :
    ((spinLayoutG spinWorkerG).2.map (·.2)) = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
  decide

instance spinValidG : Executable.ValidLayout (spinLayoutG spinWorkerG) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The lock word's address. -/
def lockAddrX : BitVec 64 := 0x1000000
/-- The counter word's address. -/
def counterAddrX : BitVec 64 := 0x1000100

/-- A worker's initial state: `%rdi = lock`, `%rsi = counter`, at the start
label `worker`, halting at `done` (the end of the text, `0x100000 + 12`); no
declarations, empty private memory. -/
def spinWorker0 : X64.State where
  exe := spinLayoutG spinWorkerG
  endPc := 0x100000 + 12
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1000000).set64 .rsi 0x1000100 }, 0x100000)

/-- The initial memory: `lock = 0`, `counter = 0`. -/
def spinInitMem : List (Loc × Val) := [(⟨lockAddrX, 4⟩, 0), (⟨counterAddrX, 4⟩, 0)]

section
attribute [local instance] spinLayoutG

theorem spinWorker0_start : StartStateG lockAddrX counterAddrX spinWorker0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, Split.empty _⟩

end

/-- **`counter = N`** for `N < 2 ^ 32` x64 xchg-spinlock workers under
`Arch.tso`, concrete instance of `x64_spin_counter_envG`. -/
theorem x64_spin_counter_envG_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init (List.replicate N spinWorker0) spinInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddrX, 4⟩ = BitVec.ofNat 128 N :=
  x64_spin_counter_envG (layout := spinLayoutG) N lockAddrX counterAddrX (by decide) hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorker0_start) List.length_replicate
    (by simp only [Config.init_mem]; decide) (by simp only [Config.init_mem]; decide) hc hf

/-- **`counter = 2`** for two x64 xchg-spinlock workers under `Arch.tso`. -/
theorem x64_spin_counter_envG_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [spinWorker0, spinWorker0] spinInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddrX, 4⟩ = 2 :=
  x64_spin_counter_envG_concreteN 2 (by decide) hc hf

end Spin

end Kraken.Promising.X64.EnvG.Concrete

#print axioms Kraken.Promising.X64.EnvG.Concrete.x64_mp_public_concrete
#print axioms Kraken.Promising.X64.EnvG.Concrete.x64_spin_counter_envG_concreteN
#print axioms Kraken.Promising.X64.EnvG.Concrete.x64_spin_counter_envG_concrete2
