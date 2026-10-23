import Kraken.Promising.ReachCertCore
import Kraken.Promising.CertifyToy
import Kraken.Promising.StepSemOfSuccs
import Kraken.Promising.LiveSemInf

/-!
# A target run that reads through a promised pointer before allocation

This file is evidence for a gap in the view relation of the M2 simulation. It
shows that a run is reachable in Kraken's fuel-free promising semantics, both
on ARMv8 and on TSO. In this run a second thread follows a pointer that the
allocating thread has only *promised*: the allocating thread has not yet run
any instruction at all.

The program is a toy-ISA model of a bump allocation followed by a publish.
The locations are `cur = 0` (the allocation cursor, initially `8`), `S = 1` (a
shared pointer slot) and `X = 2` (the cell inside the new block).

* T1: `r0 := rmw.acqRel [cur] (+16)` takes the old cursor as the block's base.
  Then `[X] := 5`, with an address dependency on `r0` (the initialising store
  into the block). Then `[S] := r0` (the publish, plain).
* T2: `r0 := [S]`, then `r1 := [X]` with an address dependency on `r0`.

The run promises T1's three writes before T1 executes anything: `cur := 24`,
`S := 8` and `X := 5`. T2 then reads `S = 8` and `X = 5`. Every step is a
`StepSemInf` step, so each promise is certified (`CertOk`) by T1's solo run.
That run fulfils the cursor write with the RMW (which reads `8`), and then
fulfils the other two.

Promise order on each architecture:

* **ARMv8:** `cur` at timestamp 1, `S` at 2, `X` at 3. The publish may be
  promised below the initialising store, because ARM does not order
  store→store without a barrier or dependency.
* **TSO:** the order of the last two is forced: `X` at 2, `S` at 3. TSO stores
  are releases, so the publish's view covers the initialising store, and the
  certification run can only fulfil `S` above `X`. The ARMv8 order is rejected
  on TSO; the `#guard` below checks this.

The source side (the reason no source run can match this configuration) and
the candidate resolutions are in `Scc/DESIGN.md` §9.0, under "Open problem
for M2: promises into a not-yet-allocated block".
-/

namespace Scc.Test.M2Hole

open Kraken Kraken.Promising Kraken.Promising.Toy Instr Kraken.Promising.Live.Inf
  Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge

/-- T1: bump the cursor, initialise the block's cell, publish its base. -/
def t1 : List Instr :=
  [rmw .acqRel 0 0 (.i 16), st .plain false 2 (.i 5) (addrDep := [0]),
   st .plain false 1 (.r 0)]

/-- T2: read the published pointer, then the cell through it. -/
def t2 : List Instr := [ld .plain false 0 1, ld .plain false 1 2 (addrDep := [0])]

/-- Both threads at their start, with the cursor at `8`. -/
def c0 : Config isa :=
  Config.init [({ prog := t1.toArray } : State), ({ prog := t2.toArray } : State)]
    [(loc 0, 8)]

/-- The ARMv8 run: three promises by T1 (cursor, `S`, `X`), then T2's two
loads, which read timestamps 2 and 3. -/
def trArm : List ReachPStep :=
  [.promise 0 (loc 0).addr 24, .promise 0 (loc 1).addr 8, .promise 0 (loc 2).addr 5,
   .instr 1 [2], .instr 1 [3]]

/-- The TSO run: as `trArm`, but with `X` promised below `S`. -/
def trTso : List ReachPStep :=
  [.promise 0 (loc 0).addr 24, .promise 0 (loc 2).addr 5, .promise 0 (loc 1).addr 8,
   .instr 1 [3], .instr 1 [2]]

/-- The configuration reached, with `S` at timestamp `tS` and `X` at `tX`.
T1 has run nothing and still holds all three promises. T2 is done, holding
the pointer `8` and the value `5` read through it. -/
def holds (tS tX : Time) (c : Config isa) : Bool :=
  match c.threads[0]?, c.threads[1]? with
  | some a, some b =>
    a.st.pc == 0 && a.prom == [1, 2, 3] && b.st.pc == 2 && b.st.regs == #[8, 5, 0, 0] &&
    (match c.mem.get? 1 with
     | some m => m.loc == loc 0 && m.val == 24 && m.tid == 0 | none => false) &&
    (match c.mem.get? tS with
     | some m => m.loc == loc 1 && m.val == 8 && m.tid == 0 | none => false) &&
    (match c.mem.get? tX with
     | some m => m.loc == loc 2 && m.val == 5 && m.tid == 0 | none => false)
  | _, _ => false

/-- Run `tr` with the executable checker (certification fuel `8`), then test
`holds`. -/
def check (A : Arch) (tr : List ReachPStep) (tS tX : Time) : Bool :=
  match reachPRun isa.exec isa.deps A 8 c0 tr with
  | some c => holds tS tX c
  | none => false

/-- A successful `check` gives a reachable configuration in the fuel-free
semantics. -/
theorem witness_of_check {A : Arch} {tr : List ReachPStep} {tS tX : Time}
    (h : check A tr tS tX = true) :
    ∃ c, ReachableSemInf A c0 c ∧ holds tS tX c = true := by
  unfold check at h
  split at h
  · rename_i c hc
    exact ⟨c, ReachableSemInf.of_reachableSem
      (reachableSem_of_reachable' (Config.init_bnd _ _) (reachPRun_sound A 8 hc)), h⟩
  · cases h

/-- **ARMv8**: T2 reads through the promised pointer. -/
theorem hole_armv8 : ∃ c, ReachableSemInf Arch.armv8 c0 c ∧ holds 2 3 c = true :=
  witness_of_check (tr := trArm) (by decide +kernel)

/-- **TSO**: the same, with `X` promised below `S`. -/
theorem hole_tso : ∃ c, ReachableSemInf Arch.tso c0 c ∧ holds 3 2 c = true :=
  witness_of_check (tr := trTso) (by decide +kernel)

-- On TSO the ARMv8 promise order is not a run: the publish cannot be
-- certified below the initialising store.
#guard (reachPRun isa.exec isa.deps .tso 8 c0 trArm).isNone

/--
info: 'Scc.Test.M2Hole.hole_armv8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hole_armv8

/--
info: 'Scc.Test.M2Hole.hole_tso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hole_tso

end Scc.Test.M2Hole
