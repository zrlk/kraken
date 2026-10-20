/-
**Concrete instance of `TicketLock.ticket_al_counter_envG`** (item 2;
`ConcreteSwpl.lean` for the `ldaddal` ticket
lock): non-vacuity of its start hypotheses, and the whole image. The worker
`tkWorkerAl` laid out at `0x100000` (each directive its `fakeSize`, as the
`.kl` runner lays out text), `next` at `0x1000`, `owner` at `0x1100`, the
counter at `0x1200`, all initially `0`; every thread starts at `worker` with
`X0 = next`, `X1 = owner`, `X2 = counter`. Every hypothesis is discharged by
`decide`, `rfl` or `simp` (no `native_decide`).

- `ticket_al_counter_envG_concreteN` (`N + 1 < 2 ^ 32` workers, `counter =
  N`), `ticket_al_counter_envG_concrete2`, `ticket_al_counter_envG_concrete3`;
- `codeMatches`: the `code` blocks of `ticketlock_al2.kl` and
  `ticketlock_al3.kl` parse to `tkWorkerAl`;
- `runnerMatches` (`A64WholeCounters.runnerWhole`): every thread the runner
  prepares for those files runs `tkWorkerAl` whole, at this layout, with
  these registers (so the public theorem is whole-image), and `sameAs`: the
  runner's threads are `tkAlWorker0`.
-/
import Kraken.Promising.SLR.EnvG.TicketAlPublic
import Kraken.Promising.SLR.EnvG.A64WholeCounters
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.ConcreteTicketAl

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.TicketLock

/-! ## The layout -/

/-- The worker's layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def tkAlLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize tkWorkerAl

theorem tkAlLayout_cells :
    ((tkAlLayout tkWorkerAl).2.map (·.2)) = [0, 4, 4, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0] := by
  decide

instance tkAlValid : Executable.ValidLayout (tkAlLayout tkWorkerAl) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- The `next` word's address. -/
def nextAddr : BitVec 64 := 0x1000
/-- The `owner` word's address. -/
def ownerAddr : BitVec 64 := 0x1100
/-- The counter word's address. -/
def counterAddr : BitVec 64 := 0x1200

/-- A worker's initial state: `X0 = next`, `X1 = owner`, `X2 = counter`, at
the start label `worker`, halting at `done` (the end of the text,
`0x100000 + 44`); no declarations, empty private memory. -/
def tkAlWorker0 : AArch64.State where
  exe := tkAlLayout tkWorkerAl
  endPc := 0x100000 + 44
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X2 := 0x1200 } }, 0x100000)

/-- The initial memory: `next = owner = counter = 0`. -/
def tkAlInitMem : List (Loc × Val) := [(⟨nextAddr, 4⟩, 0), (⟨ownerAddr, 4⟩, 0), (⟨counterAddr, 4⟩, 0)]

section
attribute [local instance] tkAlLayout

theorem tkAlWorker0_start : StartStateAl nextAddr ownerAddr counterAddr tkAlWorker0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
    simp [tkAlWorker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, nextAddr, ownerAddr,
      counterAddr]

end

theorem tkAl_disj_xo : Decls.overlaps nextAddr 4 ownerAddr 4 = false := by decide
theorem tkAl_disj_xc : Decls.overlaps nextAddr 4 counterAddr 4 = false := by decide
theorem tkAl_disj_oc : Decls.overlaps ownerAddr 4 counterAddr 4 = false := by decide

/-! ## The `.kl` files run this worker, whole -/

/-- The `.kl` sources. -/
def tkAl2Kl : String := include_str "../../../Examples/LockFree/AArch64/ticketlock_al2.kl"
def tkAl3Kl : String := include_str "../../../Examples/LockFree/AArch64/ticketlock_al3.kl"

/-- The `code` block of a `.kl` source parses to `tkWorkerAl`
(`ConcreteSwpl.codeMatches`). -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == tkWorkerAl
    | .error _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval (codeMatches tkAl2Kl, codeMatches tkAl3Kl)

/-- **The runner runs `tkWorkerAl` whole** for both files (two and three
threads; `next`, `owner`, `counter` at `0x1000`, `0x1100`, `0x1200`). -/
def runnerMatches : Bool :=
  A64WholeCounters.runnerWhole tkAl2Kl tkWorkerAl 2 (0x1000, 0x1100, 0x1200) &&
    A64WholeCounters.runnerWhole tkAl3Kl tkWorkerAl 3 (0x1000, 0x1100, 0x1200)

/-- info: true -/
#guard_msgs in
#eval runnerMatches

/-- info: (true, true) -/
#guard_msgs in
#eval (A64WholeCounters.sameAs tkAl2Kl tkAlWorker0, A64WholeCounters.sameAs tkAl3Kl tkAlWorker0)

/-! ## The instances -/

/-- **`counter = N`** for `N + 1 < 2 ^ 32` `ldaddal` ticket-lock workers under
`Arch.armv8`, concrete instance of `ticket_al_counter_envG`. -/
theorem ticket_al_counter_envG_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate N tkAlWorker0) tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N :=
  ticket_al_counter_envG (layout := tkAlLayout) N nextAddr ownerAddr counterAddr tkAl_disj_xo tkAl_disj_xc
    tkAl_disj_oc hN32 (fun s hs => (List.eq_of_mem_replicate hs) ▸ tkAlWorker0_start) List.length_replicate
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)
    hc hf

/-- **`counter = 2`** for two `ldaddal` ticket-lock workers (`ticketlock_al2.kl`). -/
theorem ticket_al_counter_envG_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [tkAlWorker0, tkAlWorker0] tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 2 :=
  ticket_al_counter_envG_concreteN 2 (by decide) hc hf

/-- **`counter = 3`** for three `ldaddal` ticket-lock workers (`ticketlock_al3.kl`). -/
theorem ticket_al_counter_envG_concrete3 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [tkAlWorker0, tkAlWorker0, tkAlWorker0] tkAlInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 3 :=
  ticket_al_counter_envG_concreteN 3 (by decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteTicketAl

#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketAl.ticket_al_counter_envG_concreteN
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketAl.ticket_al_counter_envG_concrete2
#print axioms Kraken.Promising.SLR.EnvG.ConcreteTicketAl.ticket_al_counter_envG_concrete3
