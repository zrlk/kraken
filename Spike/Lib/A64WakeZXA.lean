/-
**wake.w's worker fragment `wakeZX` at every node's states** (AArch64): `seg_childPreNNA`'s two premises at `Z := wakeZX Λ lbl cS
exe kp` (`Spike/Lib/A64WakeZX.lean`), its five conjuncts combined:
`wakeZE` (`EndOff.childThrZE`, `cZE`), `AbOffL` (`AbOffW.thrZ_ab`,
`cZ_ab`), the flag pointer (`CtlZ.childThrZ_flag`, `cZ_flag`), `Placed`
(`PlacedZ.thrZA_placed`, `cZA_placed`), `RelW1` (`RelZW.thrZA_rel`,
`cZA_rel`). The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `childThrZA_X`: `ThrZA (wakeZX …)` of the thread worker, the source at
  the worker's body.
- `cZA_X`: at the child's stub.
- `childThrZA_X'`, `cZA_X'`: at `seg_childPreNNA'`'s words (`ValRep` at
  `cA`, `meW`).
-/
import Spike.Lib.A64WakeZX
import Spike.Lib.A64WakeCtlZ
import Spike.Lib.A64WakePlacedZ

namespace Spike.Lib.A64.Flow.Worker.Wake.ZX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZA ThrZ.toA)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cN pfxM kidC)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerTy wc1)
open Spike.Lib.A64.Flow.Worker.Wake.PlacedZ (c2W c3W)
open Spike.Lib.A64.WakeLabels (wakeProg)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
  {T : Ty} {w1 w2 : TermRun.Word} {A B tp sp0 : BitVec 64}

/-- **`wakeZX` at every node's states of the thread worker's run**, the
source at the worker's body `kidC T w1 w2` (then `wc1`, past the store,
past the `unpark`), in a region covering its frames: `w1` the flag's
locative `cS` (`hw`), the words' values `A`, `B` (`hv1`, `hv2`). -/
theorem childThrZA_X (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) (hw : w1.val = .loc cS 0) (hv1 : ValRep lbl w1.val A.toNat)
    (hv2 : ValRep lbl w2.val B.toNat) :
    ThrZA (wakeZX Λ lbl cS exe kp) exe endPc R F ms (kidC T w1 w2) (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2)
      A B tp sp0 :=
  ThrZA.and (ThrZ.toA (EndOff.childThrZE hp T w1 w2 A B tp sp0))
    (ThrZA.and (ThrZ.toA (AbOffW.thrZ_ab hp))
      (ThrZA.and (ThrZ.toA (CtlZ.childThrZ_flag T w1 w2 hw A B tp sp0))
        (ThrZA.and (PlacedZ.thrZA_placed hlo hhi hv1 hv2) (RelZW.thrZA_rel hp hend hR hal hlo hhi))))

/-- **`wakeZX` at the child's stub.** -/
theorem cZA_X (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {R : Region}
    {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat) :
    ∀ i, NodeZA (wakeZX Λ lbl cS exe kp) exe endPc R F
      (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i) (Child.cBlk i) := fun i =>
  NodeZA.and (NodeZ.toAOf (EndOff.cZE hp T w1 w2 i) (by cases i <;> rfl))
    (NodeZA.and (NodeZ.toAOf (AbOffW.cZ_ab hp i) (by cases i <;> rfl))
      (NodeZA.and (NodeZ.toAOf (CtlZ.cZ_flag T w1 w2 i) (by cases i <;> rfl))
        (NodeZA.and (PlacedZ.cZA_placed hv1 hv2 i) (RelZW.cZA_rel hp hend hR hal hlo hhi i))))

/-- **`childThrZA_X` at `seg_childPreNNA'`'s words**: `A`, `B` the
registers' values `BitVec.ofNat 64 cA`, `BitVec.ofNat 64 meW`, the words'
`ValRep` at `cA`, `meW` (below `2 ^ 64`). -/
theorem childThrZA_X' (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {cA meW : Nat} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) (hcA : cA < 2 ^ 64) (hmW : meW < 2 ^ 64) (hw : w1.val = .loc cS 0)
    (hv1 : ValRep lbl w1.val cA) (hv2 : ValRep lbl w2.val meW) :
    ThrZA (wakeZX Λ lbl cS exe kp) exe endPc R F ms (kidC T w1 w2) (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2)
      (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0 :=
  childThrZA_X hp hend hR hal hlo hhi hw (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA])
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW])

/-- **`cZA_X` at `seg_childPreNNA'`'s words.** -/
theorem cZA_X' (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {R : Region}
    {F : MachineData → Prop} {cA meW : Nat} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128)
    (hhi : 0 ≤ R.hi) (hcA : cA < 2 ^ 64) (hmW : meW < 2 ^ 64) (hv1 : ValRep lbl w1.val cA)
    (hv2 : ValRep lbl w2.val meW) :
    ∀ i, NodeZA (wakeZX Λ lbl cS exe kp) exe endPc R F
      (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0 i)
      (Child.cBlk i) :=
  cZA_X hp hend hR hal hlo hhi (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA])
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW])

end Spike.Lib.A64.Flow.Worker.Wake.ZX
