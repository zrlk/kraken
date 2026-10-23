/-
**The take's phase against the run** (`Spike/Lib/A64Ret0I.lean`): `Tk` and
`own` are functions of the pc, so they are sound only if, at every pc the
run reaches, the run's state is in the phase the pc names. The canonical
target's run of `ret0Asm`'s load checks this at every step: the kernel
holds a stack range exactly when the pc is past the take (`bT` false), and
the four owned counters have the values `ownOf (ph pc)` names (the newest
message to each, else its initial value).
-/
import Spike.Lib.A64Ret0I
import Scc.Sem.Test.Run

namespace Spike.Test.A64Ret0Phase

open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.A64Consumer (T)
open Spike.Lib.A64.Flow.Ret0.Inst (μ0 bT ph ownOf)
open SccCode (ret0Λ ret0Asm)

/-- The current value of the shared location `L`: its newest message's,
else its initial value. -/
def curVal (m : Memory) (L : Loc) : Val :=
  ((m.msgs.toList.filter (·.loc == L)).getLast?.map (·.val)).getD (m.initVal L)

/-- **The run's state is in its pc's phase**: thread 0's pc is past the
take exactly when the kernel holds a range, and the owned words have the
values the pc's phase names. -/
def phaseOk (c : Config isaLSE2 × Kernel.KState) : Bool :=
  match c.1.threads[0]? with
  | none => true
  | some t =>
    let pc := pcOf t.st
    (c.2.held.isEmpty == bT pc) && (ownOf (ph pc)).all fun (L, v) => curVal c.1.mem L == v

/-- The run of the load, stopped at the first step whose configuration is
not in its pc's phase (`stop=condition`). -/
def phaseRun : String :=
  match T.load ret0Asm ret0Λ with
  | some c =>
    let μ := Scc.Sem.Test.RunMarks.mk (μ0.site .take) (μ0.site .release) μ0.abortAt false
    let r := Scc.Sem.Test.runUntil abi Arch.armv8 pcOf μ (fun c => !phaseOk c) 400 0 { cfg := c }
    s!"stop={r.stop} steps={r.steps}"
  | none => "load refused"

/-- info: "stop=exited steps=294" -/
#guard_msgs in
#eval phaseRun

end Spike.Test.A64Ret0Phase
