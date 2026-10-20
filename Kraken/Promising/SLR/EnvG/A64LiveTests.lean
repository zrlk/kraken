/-
Tests of the AArch64 static `RmwLive` check (`EnvG/A64Live.lean`): the
programs the SLR proofs use pass it by `decide`; `noRet` atomics (zero-register
destination) fail it.
-/
import Kraken.Promising.SLR.EnvG.A64Live
import Kraken.Promising.SLR.MpTrees
import Kraken.AArch64.Examples.InvEnv
import Kraken.AArch64.Examples.EnvLSELoops
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.A64LiveTests

open Kraken Kraken.Promising.SLR.MpTrees Kraken.AArch64.Examples.InvEnv

/-! ## The programs of the SLR proofs -/

/-- The MP writer and reader (`MpTrees`): no RMW at all. -/
theorem mpWriter_rmwLive : mpWriter.rmwLive = true := by decide
theorem mpReader_rmwLive : mpReader.rmwLive = true := by decide

/-- The `SWP` spinlock worker (`spinlock_swp2.kl`, `InvEnv.swpWorker`):
`swpa w3, w2, [x0]` returns into `w2`. -/
theorem swpWorker_rmwLive : swpWorker.rmwLive = true := by decide

/-- Laid out at any layout. -/
theorem swpWorker_layout_rmwLive (l : Kraken.Layout Directive) : (l swpWorker).rmwLive = true := by
  rw [Layout.apply_rmwLive]; exact swpWorker_rmwLive

/-- A `CAS` spinlock worker (acquire with `casa`, expected `0` in `w2`, new
`1` in `w3`; plain increment; `stlr wzr` release). The comparand `w2`
receives the old value, so the `casa` is live. -/
def casWorker : Program := parseAArch64("
worker:
    mov w3, #1
try:
    mov w2, #0
    casa w2, w3, [x0]
    cbnz w2, try
    ldr w5, [x1]
    add w5, w5, #1
    str w5, [x1]
    stlr wzr, [x0]
done:
")

theorem casWorker_rmwLive : casWorker.rmwLive = true := by decide

/-- The `LSE` loops of `EnvLSELoops`: `casal x1, …`, `ldaddal x1, x2, …`,
`swpal w1, w2, …`, `swpa w3, w2, …`. -/
theorem lseLoops_rmwLive :
    MachineWP.casInc.rmwLive = true ∧
      MachineWP.fetchInc.rmwLive = true ∧
      MachineWP.tas.rmwLive = true ∧
      MachineWP.swpAcquire.rmwLive = true := by
  decide

/-! ## `noRet` atomics fail the check -/

/-- `stadd` (= `ldadd` into `wzr`), `swp` into `wzr`, `cas` with comparand
`wzr`: each is a `noRet` RMW. -/
theorem noRet_not_rmwLive :
    Program.rmwLive (parseAArch64("
    stadd w1, [x0]
")) = false ∧
    Program.rmwLive (parseAArch64("
    swp w1, wzr, [x0]
")) = false ∧
    Program.rmwLive (parseAArch64("
    cas wzr, w1, [x0]
")) = false := by
  decide

/-- `casp` has no `noRet` form (`rmwPairK` passes `false`), even with zero
registers. -/
theorem casp_rmwLive : Program.rmwLive (parseAArch64("
    casp x2, x3, x4, x5, [x0]
")) = true := by decide

/-! ## The `.kl` lock programs -/

/-- The `code` block of a `.kl` file passes the check (`none`: it does not
parse). -/
def klRmwLive (src : String) : Option Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => none
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => some prog.rmwLive
    | .error _ => none

/-- `spinlock2.kl` (LL/SC: no RMW), `spinlock_swp2.kl` (`swpa`). -/
def spinlock2Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock2.kl"
def spinlockSwp2Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_swp2.kl"

/-- info: (some true, some true) -/
#guard_msgs in
#eval (klRmwLive spinlock2Kl, klRmwLive spinlockSwp2Kl)

/-- `spinlock_cas2.kl`, `spinlock_cas3.kl` (`casa`, test-and-test-and-set):
the third lock. -/
def spinlockCas2Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_cas2.kl"
def spinlockCas3Kl : String := include_str "../../../Examples/LockFree/AArch64/spinlock_cas3.kl"

/-- info: (some true, some true) -/
#guard_msgs in
#eval (klRmwLive spinlockCas2Kl, klRmwLive spinlockCas3Kl)

/-- The worker of `spinlock_cas2.kl`/`spinlock_cas3.kl`, by `decide`. -/
theorem casTtasWorker_rmwLive : Program.rmwLive (parseAArch64("
worker:
    mov w3, #1
try:
    mov w2, #0
    casa w2, w3, [x0]
    cbz w2, cs
spin:
    ldr w2, [x0]
    cbnz w2, spin
    b try
cs:
    ldr w5, [x1]
    add w5, w5, #1
    str w5, [x1]
    stlr wzr, [x0]
    b done
done:
")) = true := by decide

end Kraken.Promising.SLR.EnvG.A64LiveTests
