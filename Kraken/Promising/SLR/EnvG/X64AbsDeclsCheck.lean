/-
**The runner's declarations against the verbatim theorems' start states**
.

The runner's thread states carry declarations (`Promising.X64.State.decls`)
that differ from the verbatim theorems' `decls = {}`, and its initial memory
names other footprints. Declarations are semantic: `exec`
(`Promising/X64.lean`, `toEv s.decls`) resolves every access through
`Decls.resolve` (`Promising/Basic.lean`), which fixes the event's location.
For untyped `.kl` files the runner is in legacy mode
(`MemLayout.decls`, `Litmus/Layout.lean`: `unsizedDefault := !l.sized`, and
every symbol unsized), so the runner's events access `⟨a, 0⟩` where the
theorems' access `⟨a, 4⟩`. **These three `.kl` headers
are typed (`uint32_t`)**, so the runner is strict and sized: its declarations
are the symbols' 4-byte words and its initial memory names those (the
theorems' footprints). `runnerDecls` below records the legacy shape it had
(now `false`) and `runnerDeclsSized` the typed one (`true`); the explorer's
projections read the sized footprints.

This file records, by `#guard_msgs`, for each verbatim program:
- `runnerDecls`: the runner's declarations were legacy (the symbols unsized)
  with the unsized footprints at `0` in the initial memory — no longer
  (`false` since the headers are typed); `runnerDeclsSized`: they are the
  symbols' 4-byte words (strict), at `0` in the initial memory;
- `finalsRunner`/`finalsTheorem`: the explorer's final projections of the
  `.kl`'s observables from the runner's own initial configuration and from
  the theorem's (no declarations, 4-byte footprints): equal, no fault, no
  bound hit.
-/
import Kraken.Promising.SLR.EnvG.X64SpscAbsConcrete
import Kraken.Promising.SLR.EnvG.X64RelayAbsConcrete
import Kraken.Promising.SLR.EnvG.X64MpInclAbsConcrete

namespace Kraken.Promising.X64.EnvG.AbsDecls

open Kraken Kraken.Promising Kraken.Promising.X64

/-- The runner's prepared configuration of a `.kl` source. -/
def runnerConfig (src : String) : Option (Config isa) :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => none
  | .ok pr => some pr.config

/-- The runner's declarations are legacy with the symbols at `addrs` unsized,
and its initial memory is those footprints at `0` (the untyped headers,
before the declarations proofs). -/
def runnerDecls (src : String) (addrs : List (BitVec 64)) : Bool :=
  match runnerConfig src with
  | none => false
  | some c =>
    let ls : List Loc := addrs.map (⟨·, 0⟩)
    c.threads.all (fun t => t.st.decls == { locs := ls, unsizedDefault := true }) && c.mem.init == ls.map (·, 0)

/-- The runner's declarations are strict with the symbols at `addrs` 4-byte
words, and its initial memory is those words at `0` (the typed headers). -/
def runnerDeclsSized (src : String) (addrs : List (BitVec 64)) : Bool :=
  match runnerConfig src with
  | none => false
  | some c =>
    let ls : List Loc := addrs.map (⟨·, 4⟩)
    c.threads.all (fun t => t.st.decls == { locs := ls, unsizedDefault := false }) && c.mem.init == ls.map (·, 0)

/-- The explorer's final projections from `c` (with the fault and bound
flags). -/
def finals {α : Type} [BEq α] [Hashable α] (c : Config isa) (proj : Config isa → α) : List α × Bool :=
  let r := explore Arch.tso c proj { fuel := 300 }
  (r.finals, r.boundHit || !r.faults.isEmpty)

/-! ## `mp_incl.kl` (`1:ebx`, `[d]`, `[f]`) -/

section MpIncl
open Kraken.Promising.X64.EnvG.MpInclAbs.Concrete

-- Legacy until the declarations proofs typed the header (was `true`).
/-- info: false -/
#guard_msgs in
#eval runnerDecls mpInclKl [0x1000000, 0x1000100]

/-- info: true -/
#guard_msgs in
#eval runnerDeclsSized mpInclKl [0x1000000, 0x1000100]

def projMpIncl (w : Nat) (c : Config isa) : Nat × Nat × Nat :=
  ((c.threads[1]?.map fun t => (t.st.st.1.regs.get64 .rbx).setWidth 32 |>.toNat).getD 0,
   (c.mem.finalVal ⟨0x1000000, w⟩).toNat, (c.mem.finalVal ⟨0x1000100, w⟩).toNat)

/-- info: some ([(42, 42, 1)], false) -/
#guard_msgs in
#eval (runnerConfig mpInclKl).map fun c => finals c (projMpIncl 4)

/-- info: ([(42, 42, 1)], false) -/
#guard_msgs in
#eval finals (Config.init [mpInclW0, mpInclR1] mpInclInitMemV) (projMpIncl 4)

end MpIncl

/-! ## `spsc_queue.kl` (`1:r12d`, `1:r13d`, `1:r14d`) -/

section Spsc
open Kraken.Promising.X64.EnvG.SpscAbs.Concrete

-- Legacy until the declarations proofs typed the header (was `true`).
/-- info: false -/
#guard_msgs in
#eval runnerDecls spscKl [0x1000000, 0x1000100, 0x1000200, 0x1000300]

/-- info: true -/
#guard_msgs in
#eval runnerDeclsSized spscKl [0x1000000, 0x1000100, 0x1000200, 0x1000300]

def projSpsc (c : Config isa) : Nat × Nat × Nat :=
  let r (x : Reg64) := (c.threads[1]?.map fun t => (t.st.st.1.regs.get64 x).setWidth 32 |>.toNat).getD 0
  (r .r12, r .r13, r .r14)

/-- info: some ([(1, 2, 3)], false) -/
#guard_msgs in
#eval (runnerConfig spscKl).map fun c => finals c projSpsc

/-- info: ([(1, 2, 3)], false) -/
#guard_msgs in
#eval finals (Config.init [spscP0, spscC1] spscInitMemV) projSpsc

end Spsc

/-! ## `mp_relay3_xchg.kl` (`2:ebx`, `[d]`) -/

section Relay
open Kraken.Promising.X64.EnvG.RelayAbs.Concrete

-- Legacy until the declarations proofs typed the header (was `true`).
/-- info: false -/
#guard_msgs in
#eval runnerDecls relayKl [0x1000000, 0x1000100, 0x1000200]

/-- info: true -/
#guard_msgs in
#eval runnerDeclsSized relayKl [0x1000000, 0x1000100, 0x1000200]

def projRelay (w : Nat) (c : Config isa) : Nat × Nat :=
  ((c.threads[2]?.map fun t => (t.st.st.1.regs.get64 .rbx).setWidth 32 |>.toNat).getD 0,
   (c.mem.finalVal ⟨0x1000000, w⟩).toNat)

/-- info: some ([(43, 43)], false) -/
#guard_msgs in
#eval (runnerConfig relayKl).map fun c => finals c (projRelay 4)

/-- info: ([(43, 43)], false) -/
#guard_msgs in
#eval finals (Config.init [relayW0, relayY1, relayR2] relayInitMemV) (projRelay 4)

end Relay

end Kraken.Promising.X64.EnvG.AbsDecls
