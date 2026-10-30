/-
**wake's pre-spawn instance data `wakeD`** (AArch64): the one
`WakeO.OData` the root takes at every admissible entry `E`, at the runtime's
layout `L := RuntimeLayout.ofPlaceW hp i` of an output with wake's placement
facts.

Fixed here:
- `G := WakeOG.gW hp i cT` (`wakeG (GOf2 L m0) cT`, main's and the
  worker's value invariant after the spawn too, `WakeInst.wakeMs`);
- `ar := arW hp i` (`Rt.arOf L.Λ`, the allocator's arena of the layout:
  base `Λ.heap.lo`, `allocCells` cells, the counter at `scc_rt_heap_use`;
  with box rows admitted, `newOk := True`, since wake allocates a box, and
  the source's publication admitted, `pub := True`, since it publishes it);
- `own := fun s _ => A64.WakePh.ownG L (Rt.Reserve.ntA L.lab) s` (the owned words, `SFactsACH.ofSt`'s shape);
- `L0 := WakeLoadT.L0T L.Λ`, `ls0 := WakeLoadT.ls0T ls0` (the start's
  labels: none static, main's `ThreadId` box at its control block
  `WakeLoadT.tcb0`, no cells; `WakeLoadT.wake_initT`'s `I`);
- `rd := fun _ => True` (the source's reads unconstrained, so `OPrem.hrd`
  is `hrd_W`, `SrcRd.of_all`): `SrcRd` at `IsNum` is false for wake, since
  before the spawn the flag cell holds `new`'s `.undef`; and `rd`'s only use,
  `Out.load`'s continuation, never fires before the spawn (pre-spawn
  `main` has no source load and no exchange);
- `Cl := ClW hp i`: main's `clone` call, at `WakeWc.clonePc L`, a system
  call decoding to a `clone` (so `OPrem.hClc` is `hClc_W`);
- `a := WakeOSide.aW hp i E` (the take label of the loaded thread);
- `r0 := WakeOSide.r0W hp i`, `r1 := WakeOSide.r1W hp i` (the first two
  16 KiB stacks at `scc_rt_stacks`).

Named parameters, open until their owners fix them (`Dt`,
`ls0`: `W0`, `inv0`, `W1`, `inv1`): see `wakeD`.

The root's abort phases (`Pre1T`'s `Ab`, `Ac`, not `OData` fields):
- `AbW hp i := WriteAb.Ab L.lab` (the write abort's phase, as hello1's);
- `AcW hp i := ThreadsAb.Ac L.lab pfxM` (the threads abort's phase over
  main's spawn failure, `Worker.Wake.Child.pfxM`).
-/
import Spike.Lib.WakeOSide
import Spike.Lib.Rt.A64ArenaOfPlaceW
import Spike.Lib.A64WakeOwnG
import Spike.Lib.A64ThreadsAb
import Spike.Lib.A64SpawnFailAC
import Spike.Lib.A64WakeWcInv
import Spike.Lib.WakeLoadT

namespace Spike.Lib.WakeOD

open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Rt (RuntimeLayout)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}

/-- **main's `clone` call**: at `clonePc`, a system call decoding to a
`clone`.

The decode conjunct makes `OPrem.hClc` hold outright (`hClc_W`). In return,
the negative sites (`NodesA`'s rows, `AbortPathSC.sysC`, `AcSt.acSys`) need
every `inv1` state with `pc = clonePc ∧ atSys` to decode to a `clone`.
That is `h1`'s obligation (`CloneInv`, `WakeWc.clone_decode`). -/
def ClW (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (s : State) : Prop :=
  Scc.Sem.A64.pcOf s = Spike.Lib.A64.Flow.WakeWc.clonePc (RuntimeLayout.ofPlaceW hp i) ∧
    Scc.Sem.A64.abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl)

/-- **wake's arena**: the allocator's arena of the layout (`Rt.arOf`) with
box rows admitted (`Arena.newOk := True`). This is the truthful setting, not
a hypothesis: wake's `main` allocates a box (`let o = new z`), so its counter
add sits at a box allocation site (`CtrRow`'s `AllocSite ar.newOk`), the
box's header and initialising store are rows of the memory side
(`ArenaW`'s box-header case, `NewStM`), and the memory side's `newOk`
(`msOfA`'s, from the arena) must hold there. `Arena.OK` does not read
`newOk` (`hok_W`). hello1's arenas, with no box, keep the default `False`.

It also admits the source's publication at a fence (`Arena.pub := True`),
for the same reason: wake's `main` publishes the box (`let c = publish o`)
at `wc_main`'s `dmb ishst`, inside `h1`'s segment, so that fence's row is
the source's publication step (`FenceRun.pub`), which only a memory side
with `pub` (`msOfA`'s, from the arena) admits. `Arena.OK` does not read
`pub`. hello1's arenas, with no publication, keep the default `False`. -/
def arW (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : Arena :=
  { Spike.Lib.A64.Rt.arOf (RuntimeLayout.ofPlaceW hp i).Λ with newOk := True, pub := True }

/-- `arW` admits box rows. -/
theorem arW_newOk (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : (arW hp i).newOk :=
  trivial

/-- `arW` admits the source's publication at a fence. -/
theorem arW_pub (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : (arW hp i).pub :=
  trivial

/-- **wake's pre-spawn instance data at entry `E`** (see the module doc),
the flag's word `cT`, the open fields as parameters. -/
def wakeD (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isaLSE2) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : WakeO.OData where
  rd := fun _ => True
  G := WakeOG.gW hp i cT
  own := fun s _ => Spike.Lib.A64.WakePh.ownG (RuntimeLayout.ofPlaceW hp i)
    (Spike.Lib.A64.Rt.Reserve.ntA (RuntimeLayout.ofPlaceW hp i).lab) s
  ar := arW hp i
  Cl := ClW hp i
  Dt := Dt
  L0 := Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hp i).Λ
  ls0 := Spike.Lib.WakeLoadT.ls0T ls0
  a := WakeOSide.aW hp i E
  W0 := W0
  inv0 := inv0
  W1 := W1
  inv1 := inv1
  r0 := WakeOSide.r0W hp i
  r1 := WakeOSide.r1W hp i

/-- **The root's write abort phase.** -/
def AbW (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : State → Prop :=
  Spike.Lib.A64.WriteAb.Ab (RuntimeLayout.ofPlaceW hp i).lab

/-- **The root's threads abort phase** (main's spawn failure). -/
def AcW (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : State → Prop :=
  Spike.Lib.A64.ThreadsAb.Ac (RuntimeLayout.ofPlaceW hp i).lab Spike.Lib.A64.Flow.Worker.Wake.Child.pfxM

/-- **`OPrem.hok` at `wakeD`**: the arena's facts, given the counter's zeroed
item (`CtrZ`, a fact of the emitted sections); `Rt.arOf`'s, as `Arena.OK`
does not read `newOk`. -/
theorem hok_W (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isaLSE2) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (hc : Spike.Lib.A64.Rt.CtrZ o) : (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.OK :=
  let h := Spike.Lib.A64.Rt.ArenaW.arOf_ok (PlaceW.link i hp) hc
  ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩

/-- **`OPrem.hB` at `wakeD`**: a budget of `allocCells` cells. -/
theorem hB_W (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isaLSE2) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    B.cells = (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.cells := hB

/-- **`OPrem.hClc` at `wakeD`.** -/
theorem hClc_W (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isaLSE2) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) :
    ∀ s, (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).Cl s →
      ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
        some (.clone st tl) :=
  fun _ h => h.2.2

/-- **`OPrem.hrd` at `wakeD`**: every word is admitted. -/
theorem hrd_W (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isaLSE2) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (arch : WeakMem.Arch) :
    Spike.Lib.Consumer1.SrcRd (Spike.Lib.WakeT1.srcPo 2 arch Spike.Lib.WakeT1.wakeSrc) Spike.Lib.WakeT1.wakeSrc
      (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).rd :=
  Spike.Lib.Consumer1.SrcRd.of_all fun _ => trivial

/-- info: 'Spike.Lib.WakeOD.hrd_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hrd_W

/-- info: 'Spike.Lib.WakeOD.hok_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hok_W

end Spike.Lib.WakeOD
