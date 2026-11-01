import Spike.Lib.HelloSrc
import Spike.Lib.WakeW1
import Spike.Lib.WakeM0

/-!
# The content facts of `WSide.p` / `MSide.p` at `hello.w`

The worker's and main's sides of wake's relation take the source program
(`WakeW1.WSide.p`, `WakeM0.MSide.p`, `wakeSrc` by default) with the facts
about it their lemmas use as fields: `WSide.wk` (before its split the worker
runs `wakeSrc`'s `worker`) and `MSide.wl` (`waitLoop` is `wakeSrc`'s).

At `helloSrc`:
- `waitLoop` is `wakeSrc`'s (`hello_wl`, by `rfl`), so `MSide.wl` is discharged
  by its default;
- `worker` is not (`hello_not_wk`: its part before the store prints), so
  `WSide.wk` is discharged by a side whose invariant is never before the split
  (`wk_of_noPre`), as hello's store-phase side is.
-/

namespace Spike.Lib.HelloB7b

open Spike.Lib.HelloSrc

/-- **hello.w's `waitLoop` is wake.w's.** -/
theorem hello_wl : WakeM0.WlDecl helloSrc := rfl

/-- **hello.w's `worker` is not wake.w's.** -/
theorem hello_not_wk : ¬ WakeW1.WkDecl helloSrc := by
  intro h
  have := congrArg (Option.map fun d => match d.body with | .split _ x _ _ => x | _ => "") h
  exact absurd this (by decide)

/-- **`WSide.wk` for an invariant never before the split**, at any program. -/
theorem wk_of_noPre {ι : Type} {p : CoreTerm.Prog} {Wi : ι → Spike.Lib.Frag Kraken.Promising.AArch64.isaLSE2}
    (h : ∀ w s c, Wi w s c → ¬ WakeW1.PreSplit c.term) :
    ∀ w s c, Wi w s c → WakeW1.PreSplit c.term → WakeW1.WkDecl p :=
  fun w s c hw hp => (h w s c hw hp).elim

end Spike.Lib.HelloB7b
