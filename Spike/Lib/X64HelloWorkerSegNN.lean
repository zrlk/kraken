/-
**hello.w on x86-64: `wc_worker`'s prologue off the transfer sites** (the twin of
`Spike/Lib/A64HelloWorkerSegNN.lean`): the stack-checked prologue (`Wk.wcPro`, frame 80,
`Spike/Lib/X64HelloWorker.lean`) as one segment over `SegTC (NNZ exe endPc Z)`, `Z` at the prologue's
states (`XProW`).

- `wc_prologue_segNN`: `prologue_seg_ofNNA` at `hello_wcPro`.

## Differences from the AArch64 version

- The obligation is `XProW` (the x64 prologue's five nodes: `push`/`mov`, `lea`, the `%fs` load, `cmp`/`jb`,
  the frame), the stack check through `%fs:8`; the frame is 80 below the saved `%rbp` (`oF 80`,
  `hlo : R.lo ≤ -88`), no alignment premise; `jb .stk` is the 6-byte form.
- A64's `SegTC.seq_or`, `Body.seg_wkBodyTH`, `Body.seg_wkTH`, `Wk.seg_wcWorkerHNN`, `Wk.seg_wcWorkerHANN`
  (dead) are not twinned.
-/
import Spike.Lib.X64HelloWorker
import Spike.Lib.X64WakeNN

namespace Spike.Lib.X64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Scc.Cert.Rt.X64 (Lays endOf)

section SegNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : Frag isa}

/-- **`wc_worker`'s prologue off the transfer sites** (`prologue_seg_ofNNA`), `Z` at the prologue's states
(`hz`, `XProW`). -/
theorem wc_prologue_segNN (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lwc_worker.entry")
    (ho : SO.le nb.o (oF 80) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 80 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs wcPs (xS1 σ).slot → nb.J σ' c)
    (hz : XProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker")
      80 8 ".Lwc_worker.stk" 5 9 3 6 4 wcPs J) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend hello_wcPro (by decide) hF hR
    (by have : (80 : Int64).toInt = 80 := by decide
        omega) hhi (by decide) hpc ho hedge hz

end SegNN

end Spike.Lib.X64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.wc_prologue_segNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.wc_prologue_segNN
