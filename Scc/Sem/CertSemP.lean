/-
**Certification generic over the boundary routines** (scaffolding, see
`Scc/Sem/Platform.lean`).

`certSemP` is the certification semantics of a platform, given:

- `routineAt μ s`: the routine call (of some kind type `ρ`) the thread at
  state `s` makes under the code marks `μ`, if any;
- `boundary`: the routine calls that end a certification run (no branch);
- `solo`: the other routines' solo results (`SoloResults`), the states the
  calling thread may resume in run alone;
- `atSys`, `sysDeps`: where the platform's register dependencies replace
  the ISA's, and what they are.

Elsewhere it is the ISA's `exec` and `deps`.

The Linux instance (`linuxRoutineAt`, `linuxBoundary`, `linuxSolo`, generic
in the kernel model's `Abi`, so one instance serves both ISAs) has as
routine calls the transfer sites and the supported system calls, as
boundaries `clone`, `write` and `exit_group` (the routine calls `spawn`,
`print`, `exitProcess` of `RoutineCall`), and as solo results `Kernel.soloExec`'s.
`certSemP_linux` (untrusted, not used by any statement): the instance is
`Kernel.certSem`, which `Scc/Sem/Kernel.lean` defines and this file does not
change.
-/
import Scc.Sem.Platform
import Scc.Sem.Kernel

namespace Scc.Sem

open Kraken.Promising

/-- **The certification semantics of a platform** (generic over the
boundary set): at a routine call `r` (`routineAt`), a choice among its solo
results, none if `r` is a boundary; elsewhere the ISA's `exec`. The
dependencies are `sysDeps` where `atSys` holds, the ISA's elsewhere. -/
def certSemP {I : ISA} {X ρ : Type} (routineAt : Marks → I.State → Option ρ) (boundary : ρ → Bool)
    (solo : ρ → SoloResults I X) (atSys : I.State → Bool) (sysDeps : Kraken.InstrDeps I.RegId)
    (μ : Marks) (x : X) (tid : Nat) : CertSem I :=
  ⟨fun s => match routineAt μ s with
    | some r => some (Kernel.leaves (if boundary r then [] else solo r μ x tid s))
    | none => I.exec s,
   fun s => if atSys s then sysDeps else I.deps s⟩

namespace Kernel

variable {I : ISA} (K : Abi I)

/-- **The Linux routine calls**: a transfer site (`siteAt`), else a
supported system call (`decode`). -/
def linuxRoutineAt (μ : Marks) (s : I.State) : Option (XferKind ⊕ Call) :=
  match siteAt K μ s with
  | some k => some (.inl k)
  | none => if K.atSys s then (decode K.nrs (K.nr s) (K.arg s)).map .inr else none

/-- **The Linux boundary set**: `clone`, `write` and `exit_group`. -/
def linuxBoundary : XferKind ⊕ Call → Bool
  | .inr (.clone _ _) | .inr (.write _ _ _) | .inr (.exitGroup _) => true
  | _ => false

/-- **The Linux solo results** under the memory model `A`: at a transfer
site the state `xferStep` leaves the thread in, at a system call the states
`sysStep` (`.ret`) leaves it in, each run alone (`solo`). -/
def linuxSolo (A : Arch) : XferKind ⊕ Call → SoloResults I KState
  | .inl k => fun _ x tid s => ((xferStep K k tid (solo K (some k) x tid s)).bind (stOf tid)).toList
  | .inr call => fun _ x tid s =>
    (results call).filterMap fun r => (sysStep K A tid (solo K none x tid s) (.ret r)).bind fun (_, c') => stOf tid c'

/-- **The generic certification at the Linux instance is `certSem`.** -/
theorem certSemP_linux (A : Arch) (μ : Marks) (x : KState) (tid : Nat) :
    certSemP (linuxRoutineAt K) linuxBoundary (linuxSolo K A) K.atSys (svcDeps K) μ x tid = certSem K A μ x tid := by
  simp only [certSemP, certSem, CertSem.mk.injEq]
  refine ⟨?_, rfl⟩
  funext s
  unfold soloExec linuxRoutineAt
  rcases siteAt K μ s with _ | k
  · cases K.atSys s
    · rfl
    · simp only [ite_true]
      rcases decode K.nrs (K.nr s) (K.arg s) with _ | call
      · rfl
      · cases call <;> rfl
  · rfl

end Kernel

end Scc.Sem

/-- info: 'Scc.Sem.Kernel.certSemP_linux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Scc.Sem.Kernel.certSemP_linux
