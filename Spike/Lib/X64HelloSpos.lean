/-
**hello.w on x86-64, the records: the source memory nonempty at every record**
(`X64WakeW1.WCompat.Spos` / `X64HelloW1StoreX.WStoreX.Spos` at hello's root
records `ι := {g : Gh // X64HelloOkHR.okHR Λ lB T W g}`, `SR w :=
X64WakeInst.wakeSR w.1`):

- `sposH`: `Spos` at hello's root records (`X64HelloOkHR.okHR_Spos`).

The record built at the clone satisfies `okHR` by
`X64HelloOkHR.okHR_recW`.

x86-64 twin of `Spike/Lib/HelloSpos.lean` (same names, namespaces with the `X64` prefix).
Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only
live constants): `spos_of`.
-/
import Spike.Lib.X64HelloOkHR

namespace Spike.Lib.X64HelloSpos

open Kraken.Promising Scc.Sem
open Spike.Lib Spike.Lib.X64WakeInst
open Spike.Lib.X64HelloOkHR (okHR okHR_Spos)

/-- **`Spos` at hello's root records.** -/
theorem sposH {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} {T W : BitVec 64} :
    ∀ w : {g : Gh // okHR Λ lB T W g}, 0 < (wakeSR w.1).S :=
  fun w => okHR_Spos w

end Spike.Lib.X64HelloSpos

/-- info: 'Spike.Lib.X64HelloSpos.sposH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSpos.sposH

