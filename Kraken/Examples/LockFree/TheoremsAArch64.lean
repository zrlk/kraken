/-
Fixed-instance theorems by evaluation: a `.kl`
example's verdict, decided by running the explorer. These trust the
compiled explorer (`native_decide`), so they are regression tests with a
theorem's shape, nothing more; the `Reachable`-level theorems for arbitrary
thread counts are Stage 2. One module per ISA, since the two ISA
semantics cannot be imported together.
-/
import Kraken.Litmus.AArch64

namespace Kraken.Examples.LockFree

open Kraken.Litmus

/-- The verdict of an AArch64 `.kl` program: `some true` if its expectation
holds of every reachable final state (and no certification budget was hit),
`some false` if not, `none` if it could not be run. -/
def verdictAArch64 (src : String) (o : Promising.ExploreOpts := {}) : Option Bool :=
  match parseProgram src with
  | .error _ => none
  | .ok p => match AArch64.runProgram p none o with
    | .error _ => none
    | .ok r => some (r.ok && !r.boundHit)

/-- Two threads through an `LDAXR/STXR` spinlock each increment a counter:
the counter always ends at 2. -/
theorem spinlock2_aarch64 :
    verdictAArch64 (include_str "AArch64/spinlock2.kl") { fuel := 300, symmetric := true } = some true := by
  native_decide

/-- The same lock released with a plain `STR` loses an increment. -/
theorem spinlock2_relaxed_aarch64 :
    verdictAArch64 (include_str "AArch64/spinlock_relaxed2.kl") { fuel := 300, symmetric := true } = some false := by
  native_decide

/-- Ticket lock (`LDADDA`, `LDAR` spin, `STLR` release), two threads. -/
theorem ticketlock2_aarch64 :
    verdictAArch64 (include_str "AArch64/ticketlock2.kl") { fuel := 300, symmetric := true } = some true := by
  native_decide

/-- Michael–Scott queue, one enqueuer and one dequeuer: the dequeued value is
the enqueued one. -/
theorem msqueue1_aarch64 :
    verdictAArch64 (include_str "AArch64/msqueue1.kl") { fuel := 300 } = some true := by
  native_decide

/-- The paper's bug: with the node's data written by a plain store before the
release link, the dequeuer can read stale data. -/
theorem msqueue1_relaxed_aarch64 :
    verdictAArch64 (include_str "AArch64/msqueue_relaxed1.kl") { fuel := 300 } = some false := by
  native_decide

/-- Single-producer single-consumer ring with `STLR`/`LDAR` on the indices. -/
theorem spsc_queue_aarch64 :
    verdictAArch64 (include_str "AArch64/spsc_queue.kl") { fuel := 300 } = some true := by
  native_decide

/-- Treiber push ∥ pop with a plain `CAS` on push: the popper can see a node
whose data is not yet written. -/
theorem treiber_pp_relaxed_aarch64 :
    verdictAArch64 (include_str "AArch64/treiber_pp_relaxed.kl") { fuel := 300 } = some false := by
  native_decide

end Kraken.Examples.LockFree
