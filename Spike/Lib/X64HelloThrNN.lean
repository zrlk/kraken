/-
**hello.w's thread worker off the transfer sites on x86-64** (the twin of
`Spike/Lib/A64HelloThrNN.lean`): the tail of `scc_rt_thr_worker`
(`HThrTail`, `Spike/Lib/X64HelloThr.lean`) as one segment over
`SegTC (NNZ exe endPc Z)`, every state of its hidden invariants at a cell
other than a `nop`, each node keeping a fragment `Z` at its executing
offsets (`NodeZA`): wake.w's x86-64 `ThrTailW.seg_thrTailWNNA`
(`Spike/Lib/X64WakeWorkerNNA.lean`) at hello's labels and frame of 64.

- `HThrTail.blkN`, `HThrTail.NA`, `HThrTail.seg_thrTailNN`: the tail, to any
  fragment, from `.x13` (the thread pointer's load from the TCB's self word,
  the `exited` store, the `exit`).
- `HThrHead.blkN`: the head's blocks (`[]` at the call).

## Differences from the AArch64 version

- `NodeZA` is indexed by a node's block (`blkN`, sized cells): A64's
  `lenN`, `lenN_eq` have no twin; the obligations are at the executing
  offsets (`NA`: `.n1` at `oI`, `%rbp` claimed back from the invariant), as
  in `X64WakeWorkerNNA`; no alignment premise.
- The thread pointer is read through `%fs` (`ownFsld_ndNNA`, with `hT`,
  `hown`), the `exited` store is a plain `movq` (`rtst_ndNNA`), the exit a
  `syscall` (`texit_ndNNA`).
- A64's `HThrHead.lenN`, `lenN_eq`, `seg_thrHeadNN` (dead) are not twinned.
-/
import Spike.Lib.X64HelloThr
import Spike.Lib.X64WakeWorkerNNA

namespace Spike.Lib.X64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)

set_option linter.unusedSimpArgs false

namespace HThrTail

/-- Each node's block (the single instruction at the load, the store and
the `syscall`), the block of its `NodeZ` obligation. -/
def blkN : PN → List (Directive × Nat)
  | .x13 => [(fsDir .rax 0, 9)] | .n1 => b0 | .ex => [(stDir .rcx 24 .rax, 4)] | .n2 => b1
  | .sys => [(op64 .syscall, 2)]

/-- **The nodes at their executing offsets**: `N`, but `.n1` at the
frame's offsets with `%rbp` (`oI`, claimed back from the invariant:
`WaitLoop.At.rbpOf`), the node its block runs from. -/
def NA (lab : Label → Int64) (c0 : Ctl) (tp sp : BitVec 64) : PN → ND
  | .x13 => N lab c0 tp sp .x13
  | .n1 => ⟨(N lab c0 tp sp .n1).pc, oI, (N lab c0 tp sp .n1).J⟩
  | .ex => N lab c0 tp sp .ex
  | .n2 => N lab c0 tp sp .n2
  | .sys => N lab c0 tp sp .sys

section ProofNNA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}
  {Z : Frag isa}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "tnode " b:ident ok:ident f:ident i:term : tactic =>
  `(tactic| refine seg_ndNNA (blk := $b:ident) (by simp [$b:ident]) $ok (by decide) hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ $i))

/-- Hitting node `j`. -/
local macro "thit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, fsStep, Reg64s.set64, Reg64s.get64]))

/-- **`ThrTailW.seg_thrTailW`'s twin off the transfer sites.** -/
theorem seg_thrTailNN {Q : Frag isa} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13") tp tp)
    (hS : StOk ms F (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code c0 tp (R.addr 0) exe endPc)
    (hZ : ∀ i, NodeZA Z exe endPc R F (NA (_root_.Executable.labels exe).label c0 tp (R.addr 0) i) (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 tp (R.addr 0) .x13))
      Q := by
  refine (fn_segTS (N := N _ c0 tp (R.addr 0)) (E := (nofun : Empty → ND)) (fun i => ?_) PN.x13).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case x13 =>
    refine ownFsld_ndNNA (by decide) hF (fun s he hn => hcode.x13 s he hn) hown
      (fun m σ c _ hm hJ => ?_) (hZ .x13).toW
    obtain ⟨hc0, hfs, hbp⟩ := hJ
    have ha : σ.regs.fsBase.toBitVec + (0 : Int64).toBitVec = tp := by rw [hfs]; exact BitVec.add_zero tp
    refine ⟨ha, hT.rt, hT.mp, hT.unmapped m hm, c, .refl c, ?_⟩
    thit PN.n1
  case n1 =>
    refine (seg_ndNNA (n := ⟨(N (_root_.Executable.labels exe).label c0 tp (R.addr 0) .n1).pc, oI,
        (N (_root_.Executable.labels exe).label c0 tp (R.addr 0) .n1).J⟩) (blk := b0) (by simp [b0]) b0_ok
      (by decide) hF hR hlo hhi
      (fun s he hn => hcode.n1 s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ .n1)).mono_pre
      fun _ _ h => WaitLoop.At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2, WaitLoop.addr0_sub8]
    rw [b0_run]; thit PN.ex
  case ex =>
    refine rtst_ndNNA (fun s he hn => hcode.ex s he hn) (fun m σ c _ hm hJ => ?_) (hZ .ex).toW
    obtain ⟨rfl, hc, ha⟩ := hJ
    have hA : bAddr σ.regs .rcx 24 = tp + 24#64 := by rw [bAddr, hc]; rfl
    rw [hA, ha]
    exact ⟨hS.rt, hS.mp, hS.G, hS.unmapped m hm, c, .refl c, by thit PN.n2⟩
  case n2 => tnode b1 b1_ok n2 PN.n2; rw [N, b1_run]; thit PN.sys
  case sys =>
    refine texit_ndNNA hK (fun s he hn => hcode.sys s he hn)
      (fun σ c ⟨hc, h60⟩ => ⟨?_, a, by rw [hc]; exact ht⟩) (hZ .sys).toW
    have := congrArg BitVec.toNat h60; simpa [Reg64s.get64] using this

end ProofNNA

end HThrTail

namespace HThrHead

/-- Each node's block (`[]` at the call), the block of its `NodeZA`
obligation. -/
def blkN : TN → List (Directive × Nat)
  | .e => thE | .call => []

end HThrHead

end Spike.Lib.X64.Flow.Worker.Hello

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.HThrTail.seg_thrTailNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.HThrTail.seg_thrTailNN
