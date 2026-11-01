/-
**hello.w's records: the source memory nonempty at every record**
(`WakeW1.WCompat.Spos` / `HelloW1StoreX.WStoreX.Spos` at hello's root
records `ι := {g : Gh // HelloOkHR.okHR Λ lB g}`, `SR w :=
WakeInst.wakeSR w.1`):

- `spos_of`: `Spos` at any record subtype `{g // ok g}` whose predicate
  gives `0 < g.S`;
- `sposH`: `Spos` at hello's root records (`HelloOkHR.okHR_Spos`).

The record built at the clone satisfies `okHR` by
`HelloOkHR.okHR_recW`.
-/
import Spike.Lib.HelloOkHR

namespace Spike.Lib.HelloSpos

open Kraken.Promising Scc.Sem
open Spike.Lib Spike.Lib.WakeInst
open Spike.Lib.HelloOkHR (okHR okHR_Spos)

/-- **`Spos` at a record subtype** whose predicate gives a nonempty source
memory. -/
theorem spos_of {ok : Gh → Prop} (h : ∀ g, ok g → 0 < g.S) : ∀ w : {g : Gh // ok g}, 0 < (wakeSR w.1).S :=
  fun w => h w.1 w.2

/-- **`Spos` at hello's root records.** -/
theorem sposH {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} :
    ∀ w : {g : Gh // okHR Λ lB g}, 0 < (wakeSR w.1).S :=
  fun w => okHR_Spos w

end Spike.Lib.HelloSpos

/-- info: 'Spike.Lib.HelloSpos.spos_of' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.HelloSpos.spos_of

/-- info: 'Spike.Lib.HelloSpos.sposH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.HelloSpos.sposH

