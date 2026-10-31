/-
**wake.w's x86-64 worker fragment `wakeZX` at every node's states** (in the
manner of `Spike/Lib/A64WakeZXA.lean`): `seg_childPreNNA`'s two premises at
`Z := wakeZX Λ lbl cS tp exe kp` (`Spike/Lib/X64WakeZX.lean`). The worker's
own word is its thread pointer `tp`. The six conjuncts are combined from:
- `wakeZE`: `Pass.childThrZ`/`cZ_pass`, with the `EndOff` facts (`hE`,
  `hEc`);
- `AbOffL`: the facts `hAb`, `hAbc`;
- the flag pointer: `CtlZ.childThrZ_flag`, `cZ_flag`;
- `Placed`: `PlacedZ.thrZA_placed`, `cZA_placed`;
- `RelWS`: `RelZW.thrZA_rel`, `cZA_rel`;
- `OwnW tp`: `OwnW.thrZA_own`, `cZA_own`. Its `htp` (`tp + 24 ≠ tp`) is
  discharged here.

- `childThrZA_X`: `ThrZA (wakeZX …)` of the thread worker, the source at
  the worker's body (`hA : A ≠ tp`, `hB : B + 16 ≠ tp`).
- `cZA_X`: at the child's stub.
- `tcbOf_tcb2`: the worker's TCB (`tcb2Q`'s, `Tcb2Call.tcb2Q_tcbOf`) is
  `tcb2 L`.
- `childThrZA_X'`, `cZA_X'`: at `seg_childPreNNA'`'s words (`ValRep` at
  `cA`, `meW`). At `RuntimeLayout.ofPlaceWX` with `tp = tcb2`, `hA` and `hB`
  are discharged by `WakePh.flag_ne_tcb2_W` (the flag's cell `cA` in the
  heap) and `WakePh.unpark_ne_tcb2` (`meW` main's TCB `tcbM`).

**Unlike AArch64** (forced by the x64 shape):
- The fragment has the extra conjunct `OwnW tp`. Its premises are
  `A ≠ tp` and `B + 16 ≠ tp`, discharged at `ofPlaceWX` in the primed
  forms.
- The `EndOff` and `AbOffL` node facts are premises (`hE`, `hEc`, `hAb`,
  `hAbc`, in `ThrZ`/`NodeZ` form). AArch64 has them as `EndOff.childThrZE`
  and `AbOffW.thrZ_ab`; on x86-64 they are over the listing's byte runs and
  live with the x64 per-node lemmas.
- The region bounds are those of `thrZA_rel`/`thrZA_own`
  (`R.lo ≤ -120`, `8 ≤ R.hi`) and of `cZA_rel`/`cZA_own` (`R.lo ≤ -128`,
  `0 ≤ R.hi`). There is no alignment premise.
-/
import Spike.Lib.X64WakeZX
import Spike.Lib.X64WakeCtlZ
import Spike.Lib.X64WakePlacedZ
import Spike.Lib.X64WakeOwnWSep
import Spike.Lib.X64WakeTcb2Call

namespace Spike.Lib.X64.Flow.Worker.Wake.ZX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64.Flow.Worker (NodeZ NodeZA)
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZ ThrZA ThrZ.toA)
open Spike.Lib.X64.WakePh.Child (cN)
open Spike.Lib.X64.Flow.Worker.Wake.Child (kidC cBlk)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerTy wc1)
open Spike.Lib.X64.Flow.Worker.Wake.PlacedZ (c2W c3W)
open Spike.Lib.X64.Flow.Worker.Wake.EndOff (EndOff)
open Spike.Lib.X64AbOffL (AbOffL)
open Spike.Lib.X64.Rt (RuntimeLayout tcbOf)
open Spike.Lib.X64.WakePh (tcb2 tcbM)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
  {T : Ty} {w1 w2 : TermRun.Word} {A B tp sp0 : BitVec 64}

/-- **`wakeZX` at every node's states of the thread worker's run**, the
source at the worker's body `kidC T w1 w2` (then `wc1`, past the store,
past the `unpark`), in a region covering its frames: `w1` the flag's
locative `cS` (`hw`), the words' values `A`, `B` (`hv1`, `hv2`), neither
`A` nor the permit `B + 16` the worker's own word `tp` (`hA`, `hB`); off
the end and the abort stubs at the nodes (`hE`, `hAb`). -/
theorem childThrZA_X (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -120) (hhi : 8 ≤ R.hi)
    (hw : w1.val = .loc cS 0) (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat)
    (hA : A ≠ tp) (hB : B + 16#64 ≠ tp)
    (hE : ThrZ (EndOff exe kp) exe (kidC T w1 w2) (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2) A B tp sp0)
    (hAb : ThrZ (AbOffL (_root_.Executable.labels exe).label) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      (c2W w1 w2) (c3W w1 w2) A B tp sp0) :
    ThrZA (wakeZX Λ lbl cS tp exe kp) exe endPc R F ms (kidC T w1 w2) (wc1 workerTy w1 w2) (c2W w1 w2)
      (c3W w1 w2) A B tp sp0 :=
  ThrZA.and (ThrZ.toA (AbOffZ.thrZ_and (Pass.childThrZ hp T w1 w2 A B tp sp0) hE))
    (ThrZA.and (ThrZ.toA hAb)
      (ThrZA.and (ThrZ.toA (CtlZ.childThrZ_flag T w1 w2 hw A B tp sp0))
        (ThrZA.and (PlacedZ.thrZA_placed (by omega) (by omega) hv1 hv2)
          (ThrZA.and (RelZW.thrZA_rel hp hend hR hlo hhi)
            (OwnW.thrZA_own hp hend hR hlo hhi hA hB (by intro h; bv_omega))))))

/-- **`wakeZX` at the child's stub**: off the end and the abort stubs at
its nodes (`hEc`, `hAbc`). -/
theorem cZA_X (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hv1 : ValRep lbl w1.val A.toNat) (hv2 : ValRep lbl w2.val B.toNat)
    (hEc : ∀ i, NodeZ (EndOff exe kp) exe (cN (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i)
      (cBlk i))
    (hAbc : ∀ i, NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (cN (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i) (cBlk i)) :
    ∀ i, NodeZA (wakeZX Λ lbl cS tp exe kp) exe endPc R F
      (cN (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i) (cBlk i) := fun i =>
  NodeZA.and (NodeZ.toA (AbOffZ.nodeZ_and (Pass.cZ_pass hp (Pass.kidC_not T w1 w2) i) (hEc i)))
    (NodeZA.and (NodeZ.toA (hAbc i))
      (NodeZA.and (NodeZ.toA (CtlZ.cZ_flag T w1 w2 i))
        (NodeZA.and (PlacedZ.cZA_placed hv1 hv2 i)
          (NodeZA.and (RelZW.cZA_rel hp hend hR hlo hhi i) (OwnW.cZA_own hp hend hR hlo hhi i)))))

/-- **The worker's TCB is `tcb2`**: the second `scc_rt_alloc_tcb` call's
record `tcb2Q` has its TCB at `pinA + 104` (`Tcb2Call.tcb2Q_tcbOf`). -/
theorem tcbOf_tcb2 (L : RuntimeLayout) (g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G) (c0 : Ctl) :
    BitVec.ofNat 64 (tcbOf (_root_.Executable.labels L.exe).label (Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q g c0)).toNat =
      tcb2 L := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q_tcbOf, L.lab_pin]

section Placed

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (h : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX h i

/-- **`childThrZA_X` at `seg_childPreNNA'`'s words** at `ofPlaceWX`: `A`,
`B` the registers' values `BitVec.ofNat 64 cA`, `BitVec.ofNat 64 meW`, the
words' `ValRep` at `cA`, `meW` (below `2 ^ 64`), `tp` the worker's TCB
`tcb2` (`tcbOf_tcb2`); `hA` from the flag's cell in the heap (`hheap`),
`hB` from `meW` main's TCB (`hme`). -/
theorem childThrZA_X' (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {cA meW : Nat} (hR : R.OK) (hlo : R.lo ≤ -120)
    (hhi : 8 ≤ R.hi) (hcA : cA < 2 ^ 64) (hmW : meW < 2 ^ 64) (hw : w1.val = .loc cS 0)
    (hv1 : ValRep lbl w1.val cA) (hv2 : ValRep lbl w2.val meW) (hheap : (Ly).Λ.heap.contains cA)
    (hme : BitVec.ofNat 64 meW = tcbM (Ly)) (htp : tp = tcb2 (Ly))
    (hE : ThrZ (EndOff exe kp) exe (kidC T w1 w2) (wc1 workerTy w1 w2) (c2W w1 w2) (c3W w1 w2)
      (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0)
    (hAb : ThrZ (AbOffL (_root_.Executable.labels exe).label) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      (c2W w1 w2) (c3W w1 w2) (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0) :
    ThrZA (wakeZX Λ lbl cS tp exe kp) exe endPc R F ms (kidC T w1 w2) (wc1 workerTy w1 w2) (c2W w1 w2)
      (c3W w1 w2) (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0 :=
  childThrZA_X hp hend hR hlo hhi hw (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA])
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW])
    (htp ▸ Spike.Lib.X64.WakePh.flag_ne_tcb2_W h i hA13 hcA hheap)
    (htp ▸ Spike.Lib.X64.WakePh.unpark_ne_tcb2 hme) hE hAb

end Placed

/-- **`cZA_X` at `seg_childPreNNA'`'s words.** -/
theorem cZA_X' (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {R : Region} {F : MachineData → Prop} {cA meW : Nat} (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hcA : cA < 2 ^ 64) (hmW : meW < 2 ^ 64) (hv1 : ValRep lbl w1.val cA) (hv2 : ValRep lbl w2.val meW)
    (hEc : ∀ i, NodeZ (EndOff exe kp) exe
      (cN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0 i)
      (cBlk i))
    (hAbc : ∀ i, NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (cN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0 i)
      (cBlk i)) :
    ∀ i, NodeZA (wakeZX Λ lbl cS tp exe kp) exe endPc R F
      (cN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) tp sp0 i)
      (cBlk i) :=
  cZA_X hp hend hR hlo hhi (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA])
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW]) hEc hAbc

end Spike.Lib.X64.Flow.Worker.Wake.ZX

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.ZX.childThrZA_X'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.ZX.childThrZA_X'
