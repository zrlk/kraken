/-
**hello.w's clone refusal and `h2`'s indices** (AArch64): the root-independent definitions `HelloRootPrem` and the
start's thread-init twin (`StartH0Ti.htiWH_place`) share, split off
`Spike/Lib/A64HelloRootPrem.lean` so the root may import the callee's
discharger (`HelloH1A`, which reaches `StartH0Ti`) without a cycle.

- `Fresh2H`: the indices of `h2` (`H2StmtH`'s freshness and landings).
- `ClH`, `ClH.pc`, `ClH.cl`: main's `clone` call, the refusal's states (wake's
  `WakeOD.ClW`).
- `lbl2H`: `h2`'s placement.
-/
import Spike.Lib.A64HelloWcInv3

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64

open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.HeapLand (AllocLand)

/-- **`h2`'s indices** at the arena `ar` and the start's labels `L0`:
rodata's label `l` fresh at `L0` landing at `b` with `n` words, the box's
`l'` fresh at `upd L0 l b` landing at `b'` with `n'` (`H2StmtH`'s
hypotheses; wake's `L0T Λ l = none`, `AllocLand`). -/
def Fresh2H (ar : Spike.Lib.Arena) (L0 : Lbl) (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel)
    (b' n' : Nat) : Prop :=
  L0 l = none ∧ AllocLand ar.heap ar.cells b n ∧ Spike.Lib.A64ConsumerA.upd L0 l b l' = none ∧
    AllocLand ar.heap ar.cells b' n'

/-- **main's `clone` call** (the clone refusal's states, `TakeCKS`'s `Cl`;
wake's `WakeOD.ClW`): at `clonePcH`, a system call decoding to a `clone`.
The decode conjunct is what the negative sites (`AcSt.acSys`, the abort
paths) consume, as at wake. -/
def ClH (L : RuntimeLayout) (s : State) : Prop :=
  Scc.Sem.A64.pcOf s = clonePcH L ∧ Scc.Sem.A64.abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl)

/-- `ClH` only at the clone's pc (`hmid_boxH`'s `hCl`). -/
theorem ClH.pc {L : RuntimeLayout} {s : State} (h : ClH L s) : Scc.Sem.A64.pcOf s = clonePcH L := h.1

/-- `ClH`'s system call decodes to a `clone` (the start segments' `hcl`). -/
theorem ClH.cl {L : RuntimeLayout} : ∀ s, ClH L s → Scc.Sem.A64.abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl) :=
  fun _ h => h.2

/-- `h2`'s placement: `L0` twice extended. -/
abbrev lbl2H (L0 : Lbl) (l : WeakMem.AllocLabel) (b : Nat) (l' : WeakMem.AllocLabel) (b' : Nat) : Lbl :=
  Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd L0 l b) l' b'

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.ClH.pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ClH.pc

/-- info: 'Spike.Lib.A64.HelloPh.ClH.cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ClH.cl
