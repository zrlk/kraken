/-
**The x86-64 allocation-capable consumer at any source start**
(`Spike/Lib/X64ConsumerAStart.lean`): `StartOk.s0` at `s0 P.cap`, and the
axioms of the start-parametric load, simulation and `Correct`.
-/
import Spike.Lib.X64ConsumerAStart

open Spike.Lib.X64ConsumerA

/-- `s0 P.cap` is a start, with heap use 0. -/
example (cap : Nat) : Scc.Sem.heapUse (Spike.Lib.X64Consumer.s0 cap) = 0 :=
  (StartOk.s0 cap).heapUse

/--
info: 'Spike.Lib.X64ConsumerA.stepSimA'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms stepSimA'

/--
info: 'Spike.Lib.X64ConsumerA.correctKA'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms correctKA'

/--
info: 'Spike.Lib.X64ConsumerA.correctKA_of'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms correctKA_of'
