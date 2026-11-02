import Spike.Lib.X64HelloSrc
import Spike.Lib.X64WakeW1
import Spike.Lib.X64WakeM0

/-!
# The content facts of `WSide.p` / `MSide.p` at `hello.w` (x86-64)

The x86-64 twin of `Spike/Lib/HelloB7b.lean`. The worker's and main's sides of
wake's relation take the source program (`X64WakeW1.WSide.p`,
`X64WakeM0.MSide.p`, `wakeSrc` by default) with the facts about it their lemmas
use as fields: `WSide.wk` (before its split the worker runs `wakeSrc`'s
`worker`) and `MSide.wl` (`waitLoop` is `wakeSrc`'s).

At `helloSrc`:
- `waitLoop` is `wakeSrc`'s (`hello_wl`, by `rfl`), so `MSide.wl` is discharged
  by its default;
- `worker` is not (`hello_not_wk`: its part before the store prints), so
  `WSide.wk` is discharged by a side whose invariant is never before the split
  (`wk_of_noPre`), as hello's store-phase side is.

Differences from the AArch64 file: the program is `X64HelloSrc.helloSrc`, the
sides are `X64WakeW1`/`X64WakeM0`'s, and fragments are over `X64.isa`.

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only
live constants): `hello_not_wk`.
-/

namespace Spike.Lib.X64HelloB7b

open Spike.Lib.X64HelloSrc

/-- **hello.w's `waitLoop` is wake.w's.** -/
theorem hello_wl : X64WakeM0.WlDecl helloSrc := rfl

/-- **`WSide.wk` for an invariant never before the split**, at any program. -/
theorem wk_of_noPre {ι : Type} {p : CoreTerm.Prog} {Wi : ι → Spike.Lib.Frag Kraken.Promising.X64.isa}
    (h : ∀ w s c, Wi w s c → ¬ X64WakeW1.PreSplit c.term) :
    ∀ w s c, Wi w s c → X64WakeW1.PreSplit c.term → X64WakeW1.WkDecl p :=
  fun w s c hw hp => (h w s c hw hp).elim

/-- `wk_of_noPre` is not vacuous: the empty invariant is never before the split. -/
example : ∀ (w : Unit) s c, (fun (_ : Unit) (_ : Kraken.Promising.X64.isa.State) (_ : Spike.Lib.Ctl) => False) w s c →
    X64WakeW1.PreSplit c.term → X64WakeW1.WkDecl helloSrc :=
  wk_of_noPre fun _ _ _ h => h.elim

end Spike.Lib.X64HelloB7b

/-- info: 'Spike.Lib.X64HelloB7b.hello_wl' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloB7b.hello_wl

/-- info: 'Spike.Lib.X64HelloB7b.wk_of_noPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloB7b.wk_of_noPre
