/-
**No certification across a `write`** (x86-64; the twin of `Spike/Lib/HelloNoCert.lean`; no promise spans an
emit). `certSem` has no step at a `write` system call off the sites, so a thread certified there has no promise.

- `no_cstep_write`: no certification step at a `write(1, …)` off the sites.
- `prom_nil_of_certOkC_write`: a thread certified at a `write(1, …)` off the sites has no promise.

Unlike AArch64, the model is x86-64's (`Arch.tso`, `isa`, `Scc.Sem.X64.abi`), and the thread id `tid` is a
parameter (AArch64 states it at the worker's `1`); the proofs are the AArch64 ones.
-/
import Scc.Sem.CertStep
import Scc.Sem.TargetX64
import Kraken.Promising.X64

namespace Spike.Lib.X64HelloNoCert

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel

variable {μ : Marks}

/-- **No certification step at a `write`**: `certSem` has no step at a `write` system call off the sites. -/
theorem no_cstep_write {k : KState} {tid : Nat} {x y : Thread isa × Memory} {buf n : Nat}
    (hsite : siteAt abi μ x.1.st = none) (ha : abi.atSys x.1.st = true)
    (hd : decode abi.nrs (abi.nr x.1.st) (abi.arg x.1.st) = some (.write 1 buf n)) :
    ¬ ThreadStepC Arch.tso (certSem abi Arch.tso μ k tid) tid x y := by
  rintro ⟨outs, o, hso, ho, rfl⟩
  obtain ⟨tree, st, c', hex, hr, -, -⟩ := stepOneWith_runOut Arch.tso hso ho
  have hex' : (certSem abi Arch.tso μ k tid).exec x.1.st = some (leaves []) := by
    change soloExec abi Arch.tso μ k tid x.1.st = _
    simp only [soloExec, hsite, ha, ite_true, hd]
  rw [hex'] at hex
  cases hex
  obtain ⟨i, -⟩ := (Lower.run_choose_iff Arch.tso tid _).mp hr
  exact i.elim0

/-- A thread certified at a `write(1, …)` off the sites has no promise. -/
theorem prom_nil_of_certOkC_write {k : KState} {tid : Nat} {t : Thread isa} {mem : Memory} {buf n : Nat}
    (hsite : siteAt abi μ t.st = none) (ha : abi.atSys t.st = true)
    (hd : decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.write 1 buf n))
    (hc : CertOkC Arch.tso (certSem abi Arch.tso μ k tid) tid t mem) : t.prom = [] := by
  obtain ⟨t', mem', hr, he⟩ := hc
  cases hr with
  | refl => exact he
  | step hs _ => exact (no_cstep_write hsite ha hd hs).elim

end Spike.Lib.X64HelloNoCert

/-- info: 'Spike.Lib.X64HelloNoCert.no_cstep_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloNoCert.no_cstep_write

/--
info: 'Spike.Lib.X64HelloNoCert.prom_nil_of_certOkC_write' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64HelloNoCert.prom_nil_of_certOkC_write
