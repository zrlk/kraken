/-
**Smoke test of the x64 phase-2 link** (`MultiX64.lean`): a
`movups` load from memory (two 8-byte TSO loads, a load-prefix tree) passes
`dirs_phase2X` and fails `dirs_phase1X`, and instantiates the x64 phase-2
rule `ThreadRuleRX.ofSafelyEnvG2X`. It is not fault-free (a piece crossing a
cache line faults), so the structural no-fault rule does not apply.

A `movups` store to memory (two release-kind TSO stores) fails `dirs_phase2X`:
x64 multi-write trees are out of scope (release-kind, `NoRelWrite`).
-/
import Kraken.Promising.SLR.EnvG.MultiX64
import Kraken.Promising.EnvLinkTermX64
import Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.MultiSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

/-- A vector load: `movups (%rdi), %xmm0`, then a scalar load. -/
def movupsLoad : Program := parse("
  movups (%rdi), %xmm0
  movl (%rsi), %eax
")

/-- A 32-byte vector load (four pieces) and a 16-byte one. -/
def vmovupsLoad : Program := parse("
  vmovups (%rdi), %ymm1
  movdqu 16(%rsi), %xmm2
")

/-- A vector store: `movups %xmm0, (%rdi)`. -/
def movupsStore : Program := parse("
  movups %xmm0, (%rdi)
")

variable [layout : _root_.Layout]

/-- The vector load is not phase-1 (two loads). -/
example : True := by
  fail_if_success (have : DirsPhase1X Arch.tso (layout movupsLoad) := by dirs_phase1X movupsLoad)
  trivial

/-- **The vector load is phase-2.** -/
theorem movupsLoad_phase2 : DirsPhase2X Arch.tso (layout movupsLoad) := by dirs_phase2X movupsLoad

/-- Four-piece and `movdqu` loads are phase-2. -/
theorem vmovupsLoad_phase2 : DirsPhase2X Arch.tso (layout vmovupsLoad) := by dirs_phase2X vmovupsLoad

/-- The vector store is neither (release-kind TSO stores). -/
example : True := by
  fail_if_success (have : DirsPhase2X Arch.tso (layout movupsStore) := by dirs_phase2X movupsStore)
  trivial

/-- The vector load is not fault-free (a piece may cross a cache line):
`dirs_no_fault` fails, so the structural no-fault rule
(`noFaultRule_ofSafelyEnvG2X_struct`) does not apply to it. -/
example : True := by
  fail_if_success (have : DirsNoFault (layout movupsLoad) := by dirs_no_fault movupsLoad)
  trivial

section Rule

variable [Kraken.Executable.ValidLayout (layout movupsLoad)] {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}
  {post : MachineState × EStateX → Prop} {B : Config isa → (model isa).R → (model isa).Ghost → Prop}

/-- **The vector load's phase-2 rule**, for every `Safely` judgment of
`EnvGX` ending at the end of the text. -/
def movupsLoadRule (hpl : pl.Valid) (hS : Le16 S)
    (hpost : ∀ y, post y → y.1.2 = (layout movupsLoad).1)
    (hstuck : ∀ x R, x.1.2 = (layout movupsLoad).1 →
      ¬ Kraken.Executable.instrStepEnv (layout movupsLoad) (EnvGX Arch.tso tid pl S) x R)
    (hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX Arch.tso B tid :=
  ThreadRuleRX.ofSafelyEnvG2X hpl hS (phase2TreeX_of_dirs movupsLoad_phase2) hpost hstuck hB

end Rule

#print axioms movupsLoad_phase2
#print axioms movupsLoadRule
end Kraken.Promising.X64.EnvG.MultiSmoke
