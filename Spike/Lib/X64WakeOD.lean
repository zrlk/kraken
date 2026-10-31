/-
**wake's arena** (x86-64; the arena part of `Spike/Lib/WakeOD.lean`):
`arW hp i`, the allocator's arena of the layout (`Rt.arOf L.Λ` at
`RuntimeLayout.ofPlaceWX hp i`: base `Λ.heap.lo`, `allocCells` cells, the
counter at `scc_rt_heap_use`), with box rows admitted (`newOk := True`, since
wake allocates a box) and the source's publication admitted
(`pub := True`, since it publishes it).

- `arW`, `arW_newOk`, `arW_pub`: the arena and its two flags.

- `ClW`: main's `clone` call, at `WakeWc.clonePc L`, a system call decoding
  to a `clone` (so `OPrem.hClc` is `hClc_W`).
- `wakeD`: wake's pre-spawn instance data `X64WakeO.OData` at entry `E`:
  `G := X64WakeOG.gW hp i cT`, `ar := arW hp i`, `own := WakePh.ownGXW L
  (Reserve.ntA L.lab)` (`ownG` with main's and, until the `clone`, the
  worker's TCB self words, `X64WakeOwnT2`; X64-OwnW), `L0 := X64WakeLoadT.L0T L.Λ`, `ls0 := ls0T ls0`,
  `rd := fun _ => True`, `Cl := ClW hp i`, `a := X64WakeOSide.aW hp i E`,
  `r0`, `r1 := X64WakeOSide.r0W`, `r1W`; open as parameters (`Dt`,
  `ls0`, `W0`, `inv0`, `W1`, `inv1`).
- `AbW`, `AcW`: the root's abort phases (`WriteAb.Ab L.lab`,
  `ThreadsAb.Ac L.lab pfxM`).
- `hok_W`, `hB_W`, `hClc_W`, `hrd_W`: `OPrem.hok`, `hB`, `hClc`, `hrd` at
  `wakeD`.

Where x86-64 differs from AArch64: the layout is `RuntimeLayout.ofPlaceWX`
at `PlaceWX` (`Spike/Lib/X64PlaceW.lean`); `aW` is the take label in the
loaded thread of `o.prog` (`X64WakeOSide`); `AcW`'s prefix is
`X64.WakePh.StartWf.pfxM` (`.Lwc_main`; A64 `Worker.Wake.Child.pfxM`). On
x86-64 the publication's fence is `wc_main`'s `mfence` (`Out.fence .sy`,
`FenceRun.pub`), where A64's is its `dmb ishst`. Namespace
`Spike.Lib.X64.WakeOD`, names A64's.
-/
import Spike.Lib.X64PlaceWRt
import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Spike.Lib.Rt.X64ArenaOfPlaceW
import Spike.Lib.X64WakeOSide
import Spike.Lib.X64WakeOwnG
import Spike.Lib.X64WakeOwnT2
import Spike.Lib.X64ThreadsAb
import Spike.Lib.X64WakeWcClonePc
import Spike.Lib.X64WakeStartWfL
import Spike.Lib.X64WakeLoadT

namespace Spike.Lib.X64.WakeOD

open Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib (Arena PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}

/-- **main's `clone` call**: at `clonePc`, a system call decoding to a
`clone`.

The decode conjunct makes `OPrem.hClc` hold outright (`hClc_W`). In return,
the negative sites (`NodesA`'s rows, `AbortPathSC.sysC`, `AcSt.acSys`) need
every `inv1` state with `pc = clonePc ∧ atSys` to decode to a `clone`.
That is `h1`'s obligation. -/
def ClW (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (s : State) : Prop :=
  Scc.Sem.X64.pcOf s = Spike.Lib.X64.Flow.WakeWc.clonePc (RuntimeLayout.ofPlaceWX hp i) ∧
    Scc.Sem.X64.abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.clone st tl)

/-- **wake's arena**: the allocator's arena of the layout (`Rt.arOf`) with
box rows admitted (`Arena.newOk := True`) and the source's publication at a
fence admitted (`Arena.pub := True`). This is the truthful setting, not a
hypothesis: wake's `main` allocates a box (`let o = new z`), so its counter
add sits at a box allocation site (`AllocSite ar.newOk`), and it publishes
the box (`let c = publish o`) at `wc_main`'s `mfence`, inside `h1`'s
segment, so that fence's row is the source's publication step
(`FenceRun.pub`), which only a memory side with `pub` (`msOfA`'s, from the
arena) admits. `Arena.OK` reads neither flag. hello1's arenas, with no box
and no publication, keep the defaults `False`. -/
def arW (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : Arena :=
  { Spike.Lib.X64.Rt.arOf (RuntimeLayout.ofPlaceWX hp i).Λ with newOk := True, pub := True }

/-- `arW` admits box rows. -/
theorem arW_newOk (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : (arW hp i).newOk :=
  trivial

/-- `arW` admits the source's publication at a fence. -/
theorem arW_pub (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : (arW hp i).pub :=
  trivial

/-- **wake's pre-spawn instance data at entry `E`** (see the module doc),
the flag's word `cT`, the open fields as parameters. -/
def wakeD (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isa) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) : X64WakeO.OData where
  rd := fun _ => True
  G := X64WakeOG.gW hp i cT
  own := fun s _ => Spike.Lib.X64.WakePh.ownGXW (RuntimeLayout.ofPlaceWX hp i)
    (Spike.Lib.X64.Rt.Reserve.ntA (RuntimeLayout.ofPlaceWX hp i).lab) s
  ar := arW hp i
  Cl := ClW hp i
  Dt := Dt
  L0 := Spike.Lib.X64WakeLoadT.L0T (RuntimeLayout.ofPlaceWX hp i).Λ
  ls0 := Spike.Lib.X64WakeLoadT.ls0T ls0
  a := X64WakeOSide.aW hp i E
  W0 := W0
  inv0 := inv0
  W1 := W1
  inv1 := inv1
  r0 := X64WakeOSide.r0W hp i
  r1 := X64WakeOSide.r1W hp i

/-- **The root's write abort phase.** -/
def AbW (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : State → Prop :=
  Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceWX hp i).lab

/-- **The root's threads abort phase** (main's spawn failure). -/
def AcW (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) : State → Prop :=
  Spike.Lib.X64.ThreadsAb.Ac (RuntimeLayout.ofPlaceWX hp i).lab Spike.Lib.X64.WakePh.StartWf.pfxM

/-- **`OPrem.hok` at `wakeD`**: the arena's facts, given the counter's zeroed
item (`CtrZ`, a fact of the emitted sections); `Rt.arOf`'s, as `Arena.OK`
does not read `newOk`. -/
theorem hok_W (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isa) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (hc : Spike.Lib.X64.Rt.CtrZ o) : (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.OK :=
  let h := Spike.Lib.X64.Rt.ArenaW.arOf_ok (PlaceWX.link i hp) hc
  ⟨h.ctr_out, h.units, h.off, h.units_lt, h.cells_lt, h.ctr_lt⟩

/-- **`OPrem.hB` at `wakeD`**: a budget of `allocCells` cells. -/
theorem hB_W (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isa) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    B.cells = (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.cells := hB

/-- **`OPrem.hClc` at `wakeD`.** -/
theorem hClc_W (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isa) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) :
    ∀ s, (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).Cl s →
      ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.clone st tl) :=
  fun _ h => h.2.2

/-- **`OPrem.hrd` at `wakeD`**: every word is admitted. -/
theorem hrd_W (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry)
    (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isa) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (arch : WeakMem.Arch) :
    Spike.Lib.Consumer1.SrcRd (Spike.Lib.X64WakeT1.srcPo 2 arch Spike.Lib.X64WakeT1.wakeSrc)
      Spike.Lib.X64WakeT1.wakeSrc (wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).rd :=
  Spike.Lib.Consumer1.SrcRd.of_all fun _ => trivial

end Spike.Lib.X64.WakeOD

/-- info: 'Spike.Lib.X64.WakeOD.arW_newOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOD.arW_newOk

/-- info: 'Spike.Lib.X64.WakeOD.arW_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOD.arW_pub

/-- info: 'Spike.Lib.X64.WakeOD.hok_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOD.hok_W

/-- info: 'Spike.Lib.X64.WakeOD.hB_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOD.hB_W

/-- info: 'Spike.Lib.X64.WakeOD.hClc_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOD.hClc_W

/-- info: 'Spike.Lib.X64.WakeOD.hrd_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOD.hrd_W
