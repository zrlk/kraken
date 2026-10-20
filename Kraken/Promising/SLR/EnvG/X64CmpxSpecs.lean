/-
**The `vcgen` rule for `lock cmpxchgl`**: the 32-bit
`lock cmpxchgl %r32, d(%b)` on a location outside `dmem`, the instruction of
`spinlock_cmpxchg2.kl`'s worker that has no `vcgen` rule yet. Not specific to
`EnvG`: a plain `EnvProgram` rule, proved from the interpreter as its 64-bit
sibling `MachineWP.lock_cmpxchg_shared_spec` (`Kraken/EnvVCGen.lean`,
`lock_cmpxchg_shared` in `Kraken/EnvWPRules.lean`) and `xchg32_shared_spec`
(`EnvG/X64SpinSpecs.lean`).

One `rmw .acqRel` of 4 bytes whose operation writes the low word of `r` iff
the old low word equals `eax`, and fails (writes nothing) otherwise. Both
outcomes are VCs: on a match (`old = acc`) only the flags change; on a
mismatch the old word lands in `eax`, zero-extended into `rax`.

**Moved.** The rule now lives next to its siblings, with `@[spec]`,
as `MachineWP.lock_cmpxchg32_shared_spec` (`Kraken/EnvVCGen.lean`). The name
here is a statement-preserving alias of it (`hoist_alias`, `EnvG/Alias.lean`),
without `@[spec]` (the rule is registered once, under the `MachineWP` name).
-/
import Kraken.Promising.SLR.EnvG.X64SpinSpecs
import Kraken.Promising.SLR.EnvG.Alias

open Kraken Std.WP Lean.Order

/-! The rule under its x64 name (an alias of the `MachineWP` rule). -/
hoist_alias [
  MachineWP.lock_cmpxchg32_shared_spec ↦ Kraken.Promising.X64.EnvG.CmpxSpecs.lock_cmpxchg32_shared_spec]
