/-
**The platform interface**.

**Scaffolding.** Nothing in the trusted statement mentions this file: the
release statement is `CorrectE` (`Scc/Sem/CorrectEA64.lean`,
`Scc/Sem/CorrectEX64.lean`), which is `CorrectP` at the Linux platform by
`rfl` (`Scc/Sem/PlatformA64.lean`, `Scc/Sem/PlatformX64.lean`). The
structure here stays scaffolding until a theorem about a raw (non-Linux)
platform is stated against it.

A platform for an ISA `I` and a program image type `Img`:

- `Platform.X`: the platform's own state beside the Kraken configuration;
- `Platform.boot`: the initial configuration of `n` thread slots under an
  environment (`Entry`) and a layout, or a refusal;
- `Platform.EnvOk`: the admissible environments (Linux: `Entry.Ok`);
- `Platform.routines`: a specification list, one `RoutineSpec` per
  `RoutineCall`;
- `Platform.hooks`: the machine extension, a field (not generated from
  `routines`); `Platform.hooksX` ties its extension state to `X`.

`CorrectP` (per ISA, because the target and its text type are per ISA:
`Scc.Sem.A64.CorrectP`, `Scc.Sem.X64.CorrectP`) is `Correct` at the
platform's hooks for every admissible environment.

**The §3 obligations** are stated below as separate named `Prop`s over
(`hooks`, `routines`, `boot`), so that each can be discharged on its own.
None is proved here, and none is claimed for the Linux platform:
`linuxPlatform`'s `routines` is `[]`. The obligations stated:

- `RoutinesNodup`, `RoutinesCover` (§1: one spec per `RoutineCall`);
- `BoundaryTable` (§2: the boundary column), `BoundaryEndsCert`
  (§3.2: a boundary routine ends a certification run);
- `RegsPreserved` (§3.2: register preservation per `results`);
- `StepsLocal` (§3.1: a routine step other than `spawn` touches only the
  calling thread);
- `StepsAreHookSteps` (§1: routine steps are steps of the hooks);
- `SoloSound` (§3.2: a non-boundary routine's solo results cover the
  states its step may resume the caller in);
- `StackStepsDisjoint` (§3.4 `stackTake` / `stackRelease`: the threads'
  stack ranges stay pairwise disjoint);
- `BootInit` (§3.6: boot starts from the hooks' initial state).

**Deferred** (they need vocabulary the model does not have yet: TCB words,
context switches, safe points, checkpoints, the MMU):

- §3.1: invisible context switches, the full barrier at switch-out, the one
  resume path, the TCB installed before the first compiled instruction,
  restricted interrupt handlers, prompt scheduling of checkpoint-pending
  threads. ("No scheduler assumption" needs no `Prop`: `Correct`
  quantifies over every run.)
- §3.2: the barrier before a boundary routine's call (a property of the
  runtime code).
- §3.3: every row (safe points, reaching one, the checkpoint action,
  kernel-held references, the view invariant, tag bits, per-core blocks,
  `allocRefill`).
- §3.4: the two stack tiers, overflow, the boot thread's stack from
  `stackTake`.
- §3.5: memory attributes and MMU ownership.
- §3.6: the TCB slot 0 contents, heap aliases, per-core blocks.
-/
import Scc.Sem.Target

namespace Scc.Sem

open Kraken.Promising

/-- **The routine calls** (arguments omitted: a
`RoutineSpec`'s `step` reads them from the calling thread's registers). -/
inductive RoutineCall where
  | spawn
  | print
  | exitProcess
  | exitThread
  | park
  | unpark
  | abort
  | stackTake
  | stackRelease
  | stackResize
  | allocRefill
  deriving DecidableEq, Repr

/-- Every routine call, once. -/
def RoutineCall.all : List RoutineCall :=
  [.spawn, .print, .exitProcess, .exitThread, .park, .unpark, .abort, .stackTake, .stackRelease, .stackResize,
    .allocRefill]

/-- **The boundary column** of the routine table (Linux's boundary set mapped
routine by routine): `spawn` (`clone`), `print` (`write`), `exitProcess`
(`exit_group`) and `allocRefill` end a certification run; the others do not. -/
def RoutineCall.boundary : RoutineCall → Bool
  | .spawn | .print | .exitProcess | .allocRefill => true
  | _ => false

/-- The runtime symbol a routine call goes through. -/
abbrev Symbol : Type := String

/-- **Solo results** of a routine: the states the calling thread `tid` (at
state `s`, with code marks `μ` and platform state `x`) may resume in, run
alone; the certification semantics branches over them (`certSemP`,
`Scc/Sem/CertSemP.lean`). -/
def SoloResults (I : ISA) (X : Type) : Type := Marks → X → Nat → I.State → List I.State

/-- **The specification of one routine call** on a platform with state `X`:
the call, its symbol, whether it ends a certification run, the registers it
may write (`results`), its solo results, and its step (calling thread, then
before, events, after). -/
structure RoutineSpec (I : ISA) (X : Type) where
  call : RoutineCall
  site : Symbol
  boundary : Bool
  results : List I.RegId
  solo : SoloResults I X
  step : Nat → Config I × X → List Ev → Config I × X → Prop

/-- **A platform** for the ISA `I` and the image type `Img`. See the module
docstring. -/
structure Platform (I : ISA) (Img : Type) where
  /-- The platform's state beside the Kraken configuration. -/
  X : Type
  /-- The initial configuration with `n` thread slots under the environment
  and the layout, or a refusal. -/
  boot : Nat → Entry → Layout → Img → Option (Config I × X)
  /-- The admissible environments for a layout. -/
  EnvOk : Entry → Layout → Prop
  /-- The routine specifications (one per `RoutineCall`, `RoutinesCover`). -/
  routines : List (RoutineSpec I X)
  /-- The machine extension with `n` thread slots. -/
  hooks : Nat → Hooks I
  /-- The hooks' extension state is the platform's. -/
  hooksX : ∀ n, (hooks n).X = X

namespace Platform

variable {I : ISA} {Img : Type} (P : Platform I Img)

/-- A platform configuration as a configuration of the hooks with `n` slots. -/
def toH (n : Nat) (c : Config I × P.X) : Config I × (P.hooks n).X := (c.1, cast (P.hooksX n).symm c.2)

/-! ## The §3 obligations (stated, not proved) -/

/-- §1: no routine call has two specifications. -/
def RoutinesNodup : Prop := (P.routines.map (·.call)).Nodup

/-- §1: every routine call has a specification. -/
def RoutinesCover : Prop := ∀ k : RoutineCall, ∃ r ∈ P.routines, r.call = k

/-- §2: each specification's boundary flag is the table's. -/
def BoundaryTable : Prop := ∀ r ∈ P.routines, r.boundary = r.call.boundary

/-- §3.2: a boundary routine ends a certification run (no solo result). -/
def BoundaryEndsCert : Prop := ∀ r ∈ P.routines, r.boundary = true → ∀ μ x tid s, r.solo μ x tid s = []

/-- §3.2: a routine step writes no register of the calling thread outside
its `results` (registers read through `regVal`). -/
def RegsPreserved (regVal : I.State → I.RegId → BitVec 64) : Prop :=
  ∀ r ∈ P.routines, ∀ tid c es c', r.step tid c es c' → ∀ t t', c.1.threads[tid]? = some t →
    c'.1.threads[tid]? = some t' → ∀ g, g ∉ r.results → regVal t'.st g = regVal t.st g

/-- §3.1: a routine step other than `spawn` leaves every other thread as it
was. -/
def StepsLocal : Prop :=
  ∀ r ∈ P.routines, r.call ≠ .spawn → ∀ tid c es c', r.step tid c es c' → ∀ j, j ≠ tid →
    c'.1.threads[j]? = c.1.threads[j]?

/-- §1: a routine step is a step of the hooks with `n` slots (a system-call
step, a `spawn`, or a range transfer, the last two with no event), under
some code marks. -/
def StepsAreHookSteps : Prop :=
  ∀ n, ∀ r ∈ P.routines, ∀ tid c es c', r.step tid c es c' → ∃ μ,
    (P.hooks n).sys μ tid (P.toH n c) es (P.toH n c') ∨
    (es = [] ∧ (P.hooks n).spawn μ tid (P.toH n c) (P.toH n c')) ∨
    (es = [] ∧ ∃ k, (P.hooks n).xfer k tid (P.toH n c) (P.toH n c'))

/-- §3.2: a non-boundary routine's solo results contain every state its
step may resume the calling thread in, under every code marks. -/
def SoloSound : Prop :=
  ∀ r ∈ P.routines, r.boundary = false → ∀ tid c es c', r.step tid c es c' → ∀ t t',
    c.1.threads[tid]? = some t → c'.1.threads[tid]? = some t' → ∀ μ, t'.st ∈ r.solo μ c.2 tid t.st

/-- §3.4: a routine step keeps the threads' current stack ranges (under the
hooks with `n` slots) pairwise disjoint. -/
def StackStepsDisjoint : Prop :=
  ∀ n, ∀ r ∈ P.routines, ∀ tid c es c', r.step tid c es c' →
    (∀ i j ri rj, i ≠ j → (P.hooks n).stackRange (P.toH n c) i = some ri →
      (P.hooks n).stackRange (P.toH n c) j = some rj → ri.Disjoint rj) →
    ∀ i j ri rj, i ≠ j → (P.hooks n).stackRange (P.toH n c') i = some ri →
      (P.hooks n).stackRange (P.toH n c') j = some rj → ri.Disjoint rj

/-- §3.6: boot starts from the hooks' initial extension state. -/
def BootInit : Prop :=
  ∀ n E Λ img c, P.boot n E Λ img = some c → P.toH n c = (c.1, (P.hooks n).init E Λ)

end Platform

/-! ## Tests -/

/-- info: [true, true, true, false, false, false, false, false, false, false, true] -/
#guard_msgs in #eval RoutineCall.all.map RoutineCall.boundary

#guard RoutineCall.all.Nodup

end Scc.Sem
