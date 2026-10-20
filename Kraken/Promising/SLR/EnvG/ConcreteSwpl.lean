/-
**Concrete instance of `SwplLock.swpl_counter_envG`**:
non-vacuity of its start hypotheses. The worker `swplWorker` laid out at `0x100000` (each directive its `fakeSize`, as the
`.kl` runner lays out text), the lock at `0x1000`, the counter at `0x1100`,
both initially `0`; every thread starts at `worker` with `X0 = lock`,
`X1 = counter`. Every hypothesis is discharged by `decide`, `rfl` or `simp`
(no `native_decide`).

- `swpl_counter_envG_concrete2`: two workers, `counter = 2`;
- `swpl_counter_envG_concreteN`: `N < 2 ^ 32` workers, `counter = N`;
- `codeMatches`: the `code` blocks of `spinlock_swpl2.kl` and
  `spinlock_swpl3.kl` parse to `swplWorker`.
-/
import Kraken.Promising.SLR.EnvG.SwplLockPublic
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.ConcreteSwpl

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.SwplLock

/-! ## The layout -/

/-- The worker's layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def swplLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize swplWorker

theorem swplLayout_cells :
    ((swplLayout swplWorker).2.map (·.2)) = [0, 4, 0, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0] := by
  decide

instance swplValid : Executable.ValidLayout (swplLayout swplWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- The lock word's address. -/
def lockAddr : BitVec 64 := 0x1000
/-- The counter word's address. -/
def counterAddr : BitVec 64 := 0x1100

/-- A worker's initial state: `X0 = lock`, `X1 = counter`, at the start label
`worker`, halting at `done` (the end of the text, `0x100000 + 44`); no
declarations, empty private memory. -/
def swplWorker0 : AArch64.State where
  exe := swplLayout swplWorker
  endPc := 0x100000 + 44
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x100000)

/-- The initial memory: `lock = 0`, `counter = 0`. -/
def swplInitMem : List (Loc × Val) := [(⟨lockAddr, 4⟩, 0), (⟨counterAddr, 4⟩, 0)]

section
attribute [local instance] swplLayout

theorem swplWorker0_start : StartState lockAddr counterAddr swplWorker0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_⟩ <;>
    simp [swplWorker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, lockAddr, counterAddr]

end

theorem swpl_disj : Decls.overlaps lockAddr 4 counterAddr 4 = false := by decide

/-! ## The `.kl` files run this worker -/

/-- The `.kl` sources. -/
def swpl2Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_swpl2.kl"
def swpl3Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_swpl3.kl"

/-- The `code` block of a `.kl` source parses to `swplWorker`
(`SwpConcrete.codeMatches`). -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == swplWorker
    | .error _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval (codeMatches swpl2Kl, codeMatches swpl3Kl)

/-! ## The instances -/

/-- **`counter = N`** for `N < 2 ^ 32` `swpl`-released SWP-spinlock workers under
`Arch.armv8`, concrete instance of `swpl_counter_envG`. -/
theorem swpl_counter_envG_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate N swplWorker0) swplInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N :=
  swpl_counter_envG (layout := swplLayout) N lockAddr counterAddr swpl_disj hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ swplWorker0_start) List.length_replicate
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

/-- **`counter = 2`** for two `swpl`-released SWP-spinlock workers under `Arch.armv8`. -/
theorem swpl_counter_envG_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [swplWorker0, swplWorker0] swplInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 2 :=
  swpl_counter_envG_concreteN 2 (by decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteSwpl

#print axioms Kraken.Promising.SLR.EnvG.ConcreteSwpl.swpl_counter_envG_concreteN
#print axioms Kraken.Promising.SLR.EnvG.ConcreteSwpl.swpl_counter_envG_concrete2
