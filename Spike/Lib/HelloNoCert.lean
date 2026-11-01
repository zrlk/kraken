/-
**No certification across a `write`** (WeakCore 621ec97a: no promise spans
an emit). `certSem` has no step at a `write` system call off the sites, so a
thread certified there has no promise.

- `no_cstep_write`: no certification step at a `write(1, …)` off the sites.
- `prom_nil_of_certOkC_write`: a thread certified at a `write(1, …)` off
  the sites has no promise.
-/
import Scc.Sem.CertStep
import Scc.Sem.TargetA64
import Kraken.Promising.AArch64

namespace Spike.Lib.HelloNoCert

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel

variable {μ : Marks}

/-- **No certification step at a `write`**: `certSem` has no step at a
`write` system call off the sites (`HelloProm1.cstep_shapeH`'s emit case). -/
theorem no_cstep_write {k : KState} {x y : Thread isaLSE2 × Memory} {buf n : Nat}
    (hsite : siteAt abi μ x.1.st = none) (ha : abi.atSys x.1.st = true)
    (hd : decode abi.nrs (abi.nr x.1.st) (abi.arg x.1.st) = some (.write 1 buf n)) :
    ¬ ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 x y := by
  rintro ⟨outs, o, hso, ho, rfl⟩
  obtain ⟨tree, st, c', hex, hr, -, -⟩ := stepOneWith_runOut Arch.armv8 hso ho
  have hex' : (certSem abi Arch.armv8 μ k 1).exec x.1.st = some (leaves []) := by
    change soloExec abi Arch.armv8 μ k 1 x.1.st = _
    simp only [soloExec, hsite, ha, ite_true, hd]
  rw [hex'] at hex
  cases hex
  obtain ⟨i, -⟩ := (Lower.run_choose_iff Arch.armv8 1 _).mp hr
  exact i.elim0

/-- A thread certified at a `write(1, …)` off the sites has no promise. -/
theorem prom_nil_of_certOkC_write {k : KState} {t : Thread isaLSE2} {mem : Memory} {buf n : Nat}
    (hsite : siteAt abi μ t.st = none) (ha : abi.atSys t.st = true)
    (hd : decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.write 1 buf n))
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 t mem) : t.prom = [] := by
  obtain ⟨t', mem', hr, he⟩ := hc
  cases hr with
  | refl => exact he
  | step hs _ => exact (no_cstep_write hsite ha hd hs).elim

end Spike.Lib.HelloNoCert

/-- info: 'Spike.Lib.HelloNoCert.no_cstep_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloNoCert.no_cstep_write

/-- info: 'Spike.Lib.HelloNoCert.prom_nil_of_certOkC_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloNoCert.prom_nil_of_certOkC_write
