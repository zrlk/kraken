/-
Fixed-instance theorems by evaluation for the x64 examples; see
`TheoremsAArch64.lean`.
-/
import Kraken.Litmus.X64

namespace Kraken.Examples.LockFree

open Kraken.Litmus

def verdictX64 (src : String) (o : Promising.ExploreOpts := {}) : Option Bool :=
  match parseProgram src with
  | .error _ => none
  | .ok p => match X64.runProgram p none o with
    | .error _ => none
    | .ok r => some (r.ok && !r.boundHit)

/-- `xchg` test-and-test-and-set spinlock, plain-store release (correct on TSO). -/
theorem spinlock2_x64 :
    verdictX64 (include_str "X64/spinlock2.kl") { fuel := 300, symmetric := true } = some true := by
  native_decide

/-- Dekker-style entry with plain stores and loads: both threads can enter
(store buffering, the one weak behaviour of TSO). -/
theorem dekker_broken_x64 :
    verdictX64 (include_str "X64/dekker_broken.kl") { fuel := 300 } = some false := by
  native_decide

/-- The same with `mfence` between the store and the load: mutual exclusion. -/
theorem dekker_mfence_x64 :
    verdictX64 (include_str "X64/dekker_mfence.kl") { fuel := 300 } = some true := by
  native_decide

/-- Ticket lock with `lock xadd`, two threads. -/
theorem ticketlock2_x64 :
    verdictX64 (include_str "X64/ticketlock2.kl") { fuel := 300, symmetric := true } = some true := by
  native_decide

/-- Treiber stack with `lock cmpxchg`, two threads pushing and popping. -/
theorem treiber2_x64 :
    verdictX64 (include_str "X64/treiber2.kl") { fuel := 300 } = some true := by
  native_decide

/-- Single-producer single-consumer ring with plain moves (correct on TSO). -/
theorem spsc_queue_x64 :
    verdictX64 (include_str "X64/spsc_queue.kl") { fuel := 300 } = some true := by
  native_decide

end Kraken.Examples.LockFree
