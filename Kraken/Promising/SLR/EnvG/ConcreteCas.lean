/-
**Concrete instance of `CasSmoke.cas_counter_envG`**: non-vacuity of its start hypotheses. The CAS spinlock worker
`casTtasWorker` laid out at `0x100000` (each directive its `fakeSize`, as the
`.kl` runner lays out text), the lock at `0x1000`, the counter at `0x1100`,
both initially `0`; every thread starts at `worker` with `X0 = lock`,
`X1 = counter`. Every hypothesis is discharged by `decide`, `rfl` or `simp`
(no `native_decide`).

- `cas_counter_envG_concrete2`: two workers, `counter = 2`;
- `cas_counter_envG_concreteN`: `N < 2 ^ 32` workers, `counter = N`.
-/
import Kraken.Promising.SLR.EnvG.CasPublic
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.SLR.EnvG.ConcreteCas

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.CasSmoke

/-! ## The layout -/

/-- The worker's layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def casLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize casTtasWorker

theorem casLayout_cells :
    ((casLayout casTtasWorker).2.map (·.2)) = [0, 4, 0, 4, 4, 4, 0, 4, 4, 4, 0, 4, 4, 4, 4, 4, 0] := by
  decide

instance casValid : Executable.ValidLayout (casLayout casTtasWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- The lock word's address. -/
def lockAddr : BitVec 64 := 0x1000
/-- The counter word's address. -/
def counterAddr : BitVec 64 := 0x1100

/-- A worker's initial state: `X0 = lock`, `X1 = counter`, at the start label
`worker`, halting at `done` (the end of the text, `0x100000 + 48`); no
declarations, empty private memory. -/
def casWorker0 : AArch64.State where
  exe := casLayout casTtasWorker
  endPc := 0x100000 + 48
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x100000)

/-- The initial memory: `lock = 0`, `counter = 0`. -/
def casInitMem : List (Loc × Val) := [(⟨lockAddr, 4⟩, 0), (⟨counterAddr, 4⟩, 0)]

section
attribute [local instance] casLayout

theorem casWorker0_start : StartState lockAddr counterAddr casWorker0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_⟩ <;>
    simp [casWorker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, lockAddr, counterAddr]

end

theorem cas_disj : Decls.overlaps lockAddr 4 counterAddr 4 = false := by decide

/-! ## The instances -/

/-- **`counter = N`** for `N < 2 ^ 32` CAS-spinlock workers under
`Arch.armv8`, concrete instance of `cas_counter_envG`. -/
theorem cas_counter_envG_concreteN (N : Nat) (hN32 : N < 2 ^ 32) {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init (List.replicate N casWorker0) casInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = BitVec.ofNat 128 N :=
  cas_counter_envG (layout := casLayout) N lockAddr counterAddr cas_disj hN32
    (fun s hs => (List.eq_of_mem_replicate hs) ▸ casWorker0_start) List.length_replicate
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

/-- **`counter = 2`** for two CAS-spinlock workers under `Arch.armv8`. -/
theorem cas_counter_envG_concrete2 {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [casWorker0, casWorker0] casInitMem) c)
    (hf : c.final = true) :
    c.mem.finalVal ⟨counterAddr, 4⟩ = 2 :=
  cas_counter_envG_concreteN 2 (by decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteCas

#print axioms Kraken.Promising.SLR.EnvG.ConcreteCas.cas_counter_envG_concreteN
#print axioms Kraken.Promising.SLR.EnvG.ConcreteCas.cas_counter_envG_concrete2
