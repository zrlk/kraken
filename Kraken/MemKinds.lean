/-
Memory-event kinds shared by the ISA semantics and the weak-memory layer.

The ISA interpreters (`Kraken/X64/Semantics.lean`, `Kraken/AArch64/Semantics.lean`)
tag the memory effects they emit with these kinds; `Kraken/Promising/` gives
them meaning under an architecture profile. The sequential semantics treats
every kind alike (a load is a load, a fence is a skip), so this file has no
semantic content of its own. The names follow Promising-ARM/RISC-V
(Pulte et al., PLDI 2019), appendix A.
-/

namespace Kraken

/-- Ordering of a load. `acq` is a strong acquire (`LDAR`): ordered after
program-order-earlier release stores. `acqPc` is RCpc (`LDAPR`): ordered
before later accesses only. -/
inductive LoadKind | plain | acq | acqPc
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Ordering of a store. `rel` is a release (`STLR`). `nt` is x86's
non-temporal store (`movnti`): weakly ordered even under TSO (SDM vol. 3A
§8.2.2), ordered before later stores only by `sfence`, `mfence` and locked
instructions; a profile without such stores treats it as `plain`. -/
inductive StoreKind | plain | rel | nt
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Ordering of a read-modify-write (`CAS`, `SWP`, `LDADD`, x86 `lock`). -/
inductive RmwKind | plain | acq | rel | acqRel
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Barriers. `sy`: full (`DMB SY`, `MFENCE`); `ld`: `DMB LD` (earlier loads
before later accesses); `st`: `DMB ST` (earlier stores before later stores);
`stAll`: `DSB ST` (earlier stores before later accesses); `isb`: instruction
barrier, which orders through control/address dependencies. -/
inductive FenceKind | sy | ld | st | stAll | isb
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

namespace LoadKind
/-- The load imposes acquire ordering on later accesses. -/
def isAcquire : LoadKind → Bool | plain => false | acq => true | acqPc => true
end LoadKind

namespace RmwKind
def loadKind : RmwKind → LoadKind
  | plain => .plain | acq => .acq | rel => .plain | acqRel => .acq
def storeKind : RmwKind → StoreKind
  | plain => .plain | acq => .plain | rel => .rel | acqRel => .rel
end RmwKind

/-- The syntactic register dependencies of one instruction, as the architecture
defines them (an `EOR X1, X1, X1` keeps the dependency on `X1`). The weak-memory
layer keeps a *view* per register and uses this to propagate views; the ISA
provides it as a total function on its instruction type, written next to the
instruction's `interp`. `RegId` is the ISA's register identity (an AArch64 `W`
register maps to its `X`; `nzcv`/`rflags` is a register here). -/
structure InstrDeps (RegId : Type) where
  /-- Registers that feed a memory address. -/
  addrRegs : List RegId := []
  /-- Registers that feed store data, or an ALU/compare input. -/
  dataRegs : List RegId := []
  /-- For an instruction that performs several stores (`STP`), the data
  registers of each store, in the order the stores are performed; `dataRegs`
  is then their union (for the coverage tests), and the data feeds the stores
  only, not a written-back base. Empty (the default) means every store's data
  is `dataRegs`, which also feeds the other results. herd tracks data
  dependencies per access, so the second write of `STP X4, X5, [X0]` does not
  depend on `X4`, and `STP`'s write-back (`stp_wback`) on neither. -/
  dataRegsPer : List (List RegId) := []
  /-- Registers (including flags) read by a conditional branch, the `CSEL`
  family, or `CCMP`. -/
  condRegs : List RegId := []
  /-- Registers written with a loaded value. -/
  loadDefs : List RegId := []
  /-- The success register of a store exclusive. -/
  statusDefs : List RegId := []
  /-- Every other register written: ALU results, flags, address write-back. -/
  defs : List RegId := []
  /-- The instruction is a conditional control transfer on `condRegs`. -/
  isBranch : Bool := false
  /-- The result is picked among sources by `condRegs` (`CSEL` family): the
  ISA lists only the *selected* source in `dataRegs`, and the condition's
  dependency is a "pick" dependency (Arm ARM B2.3.2, herd's
  `aarch64deps.cat`), which orders later writes but not later reads. -/
  isPick : Bool := false
  /-- A compare-and-swap: `condRegs` holds the comparand, which orders the
  write without being its data, and `loadDefs` (the comparand register)
  keeps its old dependency when the compare succeeds, as herd has it. -/
  casLike : Bool := false
  deriving Repr, BEq, Inhabited

end Kraken
