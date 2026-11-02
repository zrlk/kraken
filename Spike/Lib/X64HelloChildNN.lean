/-
**hello.w's worker-thread prologue and child stub off the transfer sites on x86-64** (the twin of
`Spike/Lib/A64HelloChildNN.lean`): `scc_rt_thr_worker`'s prologue (`HThrTail.thrPro`,
`Spike/Lib/X64HelloThr.lean`) as one segment over `SegTC (NNZ exe endPc Z)`, and the child stub's blocks
(`Spike/Lib/X64HelloChild.lean`), the `blk` of its nodes' `NodeZA`.

- `thr_prologue_segNN`: the prologue off the transfer sites (`prologue_seg_ofNNA` at `hello_thrPro`), `Z` at
  the prologue's states (`hz`, `XProW`).
- `Child.cBlk`: the stub's blocks, per node.

## Differences from the AArch64 version

- The prologue's obligation is `XProW` (the x64 prologue's five nodes: `push`/`mov`, `lea`, the `%fs` load,
  `cmp`/`jb`, the frame) and its stack check reads `%fs:8`; the frame is 64 below the saved `%rbp`
  (`oF 64`, `hlo : R.lo ≤ -72`), no alignment premise.
- `Child.cBlk` is over the four nodes of the x64 stub (`ts`, `je`, `xb`, `ch`) with sized cells; A64's
  `cLen`, `cLen_eq` have no twin (`NodeZA` is indexed by the block).
- A64's `HThrHead.seg_thrHeadH`, `Child.seg_thrWorkerH`, `Child.seg_childStubH` (dead) are not twinned.
-/
import Spike.Lib.X64HelloThrNN
import Spike.Lib.X64HelloChild

namespace Spike.Lib.X64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Scc.Cert.Rt.X64 (Lays endOf)

set_option linter.unusedSimpArgs false

section ProNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : Frag isa}

/-- **`scc_rt_thr_worker`'s prologue off the transfer sites** (`prologue_seg_ofNNA`), `Z` at the prologue's
states (`hz`, `XProW`). -/
theorem thr_prologue_segNN (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry")
    (ho : SO.le nb.o (oF 64) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 64 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs thrPs (xS1 σ).slot → nb.J σ' c)
    (hz : XProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker")
      64 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs J) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend hello_thrPro (by decide) hF hR
    (by have : (64 : Int64).toInt = 64 := by decide
        omega) hhi (by decide) hpc ho hedge hz

end ProNN

namespace Child

/-- The stub's blocks, the `blk` of its nodes' `NodeZA`. -/
def cBlk : CN → List (Directive × Nat)
  | .ts => tsB | .je => jeB | .xb => xbp | .ch => chB

end Child

end Spike.Lib.X64.Flow.Worker.Hello

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.thr_prologue_segNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.thr_prologue_segNN
