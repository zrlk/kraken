/-
**`scc_rt_main` after the setup block's return, at the switched stack**
(x86-64): `mainS0_segWSF` (`Spike/Lib/Rt/X64MainS0.lean`) at the switch
region `(swR v (-L) 0).callee (-8 - 0) (8 - L) 8` and its frame condition
`(Fw ∧ swFSL) ∧ CallerCells` (`mainS_segWSFB`'s, as `mainESF_segWSFB`
takes them, `Spike/Lib/Rt/X64MainSSBF.lean`): the region and frame facts
from the switch region's (`mainEF_ok`), the limit word from the start's
frame condition. The segment a setup bottom key's `h0` asks
(`Spike/Test/X64Hello1BotH.lean`).

- `mainS0_segSwF`: from `mainS0` at `[]` at the switch region, a segment
  to any `Q`.
-/
import Spike.Lib.Rt.X64MainS0
import Spike.Lib.Rt.X64MainSSBF

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf)

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}

/-- **`mainS0_segWSF` at the switch region**: at the switched stack's top
`v` (its region `OK`, `hv`) at depth `L`, the frame condition
`(Fw ∧ swFSL) ∧ CallerCells` (`FStable` in the switch region, `hFwS`), the
limit word's facts at any frame condition `F₀` the switch's implies
(`hlimU`; `swFSL` unloads the word), the ghost `⟨top - 8, tpOf tcb, c0⟩`:
the segment from `mainS0` at `[]` to any `Q`, given the user function's call
(`hU`), the exit (`hexit`), the marshalling block (`hsp0`) and the exit tail
(`hWx`) at that region. -/
theorem mainS0_segSwF {W : FragS isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64}
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop} {L : Int}
    (hL2 : 8 + 8 + sc.Z.toInt + 8 + D2 ≤ L) (hL8 : L % 8 = 0)
    (hK : (ms []).K = some Scc.Sem.X64.abi) {rS : Scc.Sem.Range} (tcb top v : BitVec 64) (c0 : Ctl) (x0 : BitVec 64)
    {Fw : _root_.Mem 64 → Prop} (hv : (swR v (-L) 0).OK)
    (hFwS : FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m))
    {F₀ : MachineData → Prop}
    (hlimU : LimOk (ms []) F₀ (limA (tpOf tcb)) (top - 8#64 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hU : MainCallWSF W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec (tpOf tcb))
    (hexit : ∀ s c fs (w : BitVec 64), Post c fs w →
      At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
        ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5, oU sc.Z,
          fun σ _ => σ.regs.rdi.toBitVec = w⟩ s c → MainExitFA p (ms []) s c fs w.toNat)
    (hsp0 : BlkW (nilW W) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (_root_.Executable.labels exe).label sc PostS ⟨top - 8#64, tpOf tcb, c0⟩ x0)
      (marshal sc.sw sc.fn))
    (hWx : ∀ fs, XExitW (fun s c => W s c fs) K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainSRR (_root_.Executable.labels exe).label sc (fun c w => Post c fs w)) (-8 - sc.Z.toInt) (-8) sc.k 4 4 5)
    {Q : FragS isa} :
    SegWS W K p lbl ms ((At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0 (_root_.Executable.labels exe).label sc PostS ⟨top - 8#64, tpOf tcb, c0⟩ x0)).at []) Q := by
  obtain ⟨hR, hF⟩ := mainEF_ok (rS := rS) (tcb := tcb) (top := top) (by omega) hL8 hv hFwS
  have hun : ∀ m, ((Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
      CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      Mem.loadInt m.dmem (limA (tpOf tcb)) 8 = none := fun _ h => h.1.2.1.2
  exact mainS0_segWSF hp hend hin hZ8 hsw hZw hk hD20 hD28 hK hF hR
    (show 8 - L ≤ -8 - sc.Z.toInt - 8 - D2 by omega) (show (0 : Int) ≤ 8 by decide)
    ⟨top - 8#64, tpOf tcb, c0⟩ x0 ⟨hlimU.rt, hlimU.mp, hun, hlimU.room⟩ hU hexit hsp0 hWx

end Proof

end Spike.Lib.X64.Rt

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.mainS0_segSwF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.mainS0_segSwF
