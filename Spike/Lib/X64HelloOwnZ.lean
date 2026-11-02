/-
**No write to the worker's own word at hello's worker nodes, x86-64** (in the manner of
`Spike/Lib/X64HelloRelZ.lean`, for x86-64 wake's own-word discipline `Spike/Lib/X64OwnWNodes.lean`): the fact
`OwnW W s c` (off a system call, every write of the instruction's event tree is to a location other than
`⟨W, 8⟩`) at every node's states of hello's worker segments, in the `NodeZA`/`XProW` form the segment lemmas take
(`X64HelloWkTailNN`, `X64HelloThrNN`, `X64HelloChildNN`, `X64HelloWorkerTCS`).

Every block is covered (it runs to `.done`: its stack accesses hit the private memory), the prologues' limit loads
and the thread tail's `movq %fs:0` are loads, the `syscall`s fault. The three shared writes are premises: the
store of the flag at `A` (`hA : A ≠ W`), `scc_rt_unpark`'s exchange on the permit at `B + 16` (`hB`), the thread
tail's store at `tp + 24` (`htp`).

- `unpk_ownH`, `tail_ownH`: `scc_rt_unpark`'s and `wc_worker`'s tail nodes.
- `thrTail_ownH`, `thrHead_ownH`, `child_ownH`: the thread worker's tail and head, the child's stub.
- `wcPro_ownH`, `thrPro_ownH`: the two stack-checked prologues.
- `wE_ownH`, `wCall_ownH`: `wc_worker`'s `.entry` nodes (the block before the multiply, the multiply, the block
  after it) and its call node (`scc_rt_print`'s first block, in the worker's region).

Unlike wake's (`X64OwnWNodes`), the tails' nodes are at their executing offsets (`NA`), `wc_worker`'s `.entry`
block is three nodes (`Body.wN`), and the flag's store is in `wc_worker`'s tail (`HelloTail`). `print`'s own nodes
and the write abort are not covered here.
-/
import Spike.Lib.X64HelloRelZ
import Spike.Lib.X64OwnWNodes

namespace Spike.Lib.X64.Flow.Worker.Hello.OwnZH

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker Spike.Lib.X64.Flow.Worker.Hello
open Spike.Lib.X64.Flow.Worker.Hello.Child (cN childIn CN jeB_ok chB_ok cBlk hello_childIn)
open Spike.Lib.X64.Flow.Worker.Wake.RelZW (blkZA_done nodeZA_cell)
open Spike.Lib.X64.Flow.Worker.Wake.OwnW (OwnW ownW_done ownW_movfs ownW_test ownW_fi ownW_syscall ownW_st
  ownW_xchg xProW_own eaddr_abs)

variable {W : BitVec 64} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

/-- Closes a covered block's obligation. -/
local macro "rb " ok:term:max code:term:max : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => ownW_done h) $ok (by assumption) (by omega) (by omega) $code)

/-- **`OwnW` at `scc_rt_unpark`'s nodes**, in its region: its exchange at `B + 16`. -/
theorem unpk_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {c1 c2 : Ctl} {B rbp1 ra1 tp : BitVec 64} (hB : B + 16#64 ≠ W) (i : Unpark.PN) :
    NodeZA (OwnW W) exe endPc R F (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i)
      (Unpark.blkN i) := by
  have hc := Labels.unpkCode hp hend (c0 := c1) (c1 := c2) (B := B) (rbp0 := rbp1) (ra := ra1) (tp := tp)
  cases i
  · rb Unpark.b0_ok hc.e
  · rb Unpark.b1_ok hc.n1
  · refine nodeZA_cell hc.xchg fun s σ c hc hd hAbs hJ => ownW_xchg hc hd ?_
    rw [eaddr_abs hAbs, hJ.2.1]
    exact hB
  · rb Unpark.b2_ok hc.n2
  · rb Unpark.b3_ok hc.n3
  · rb Unpark.b4_ok hc.wake
  · exact nodeZA_cell hc.sys fun _ _ _ hc _ _ _ => ownW_syscall hc
  · rb Unpark.b5_ok hc.n5
  · rb Unpark.b6_ok hc.done

/-- **`OwnW` at `wc_worker`'s tail nodes**, at their executing offsets, in its region: its store of the flag at
`A`. -/
theorem tail_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -96) (hhi : 8 ≤ R.hi)
    {c0 c1 c2 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (hA : A ≠ W) (i : HelloTail.PN) :
    NodeZA (OwnW W) exe endPc R F (HelloTail.NA (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp i)
      (HelloTail.blkN i) := by
  have hc := Labels.wkTailCode hp hend (c0 := c0) (c1 := c1) (c2 := c2) (A := A) (B := B) (rbp0 := rbp0) (ra := ra)
    (tp := tp) (sp := sp)
  cases i
  · rb HelloTail.b0_ok hc.e
  · refine nodeZA_cell hc.st fun s σ c hc hd hAbs hJ => ownW_st hc hd ?_
    rw [eaddr_abs hAbs, hJ.2.1]
    simpa using hA
  · rb HelloTail.b1_ok hc.n3
  · exact fun _ _ _ _ _ _ _ _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)
  · rb HelloTail.b2_ok hc.x18

/-- **`OwnW` at `scc_rt_thr_worker`'s tail**, at its executing offsets: its store at `tp + 24`. -/
theorem thrTail_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {c3 : Ctl} {tp sp0 : BitVec 64} (htp : tp + 24#64 ≠ W) (i : HThrTail.PN) :
    NodeZA (OwnW W) exe endPc R F (HThrTail.NA (_root_.Executable.labels exe).label c3 tp sp0 i) (HThrTail.blkN i) := by
  have hc := thrCode hp hend (c0 := c3) (tp := tp) (sp := sp0)
  cases i
  · exact nodeZA_cell hc.x13 fun _ _ _ hc _ _ _ => ownW_movfs hc
  · rb HThrTail.b0_ok hc.n1
  · refine nodeZA_cell hc.ex fun s σ c hc hd hAbs hJ => ownW_st hc hd ?_
    rw [eaddr_abs hAbs, hJ.2.1]
    exact htp
  · rb HThrTail.b1_ok hc.n2
  · exact nodeZA_cell hc.sys fun _ _ _ hc _ _ _ => ownW_syscall hc

/-- **`OwnW` at `scc_rt_thr_worker`'s head.** -/
theorem thrHead_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : HThrHead.TN) :
    NodeZA (OwnW W) exe endPc R F (HThrHead.tN (_root_.Executable.labels exe).label J L i) (HThrHead.blkN i) := by
  cases i
  · rb HThrHead.thE_ok (thECode hp hend)
  · exact fun _ _ _ _ _ _ _ _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)

/-- **`OwnW` at the child's stub**: it writes nothing shared. -/
theorem child_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {cW : Ctl} {w : Child.Words} {tp sp0 : BitVec 64} :
    ∀ i, NodeZA (OwnW W) exe endPc R F (cN (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i) := by
  have hin := hello_childIn
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt SccCode.helloCells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  intro i
  cases i
  · exact nodeZA_cell (fun s he hn => code bts s he hn) fun _ _ _ hc _ _ _ => ownW_test hc
  · rb jeB_ok (fun s he hn => code bje s he hn)
  · exact nodeZA_cell (fun s he hn => (by simpa using code bxb s he hn :
      CodeAt s ((_root_.Executable.labels exe).label Child.chL) Child.xbp)) fun _ _ _ hc _ _ _ => ownW_fi hc
  · rb chB_ok (fun s he hn => code bch s he hn)

/-- **`OwnW` at `wc_worker`'s prologue** (frame 80). -/
theorem wcPro_ownH {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -88)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    XProW (OwnW W) (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker")
      80 8 ".Lwc_worker.stk" 5 9 3 6 4 Wk.wcPs J :=
  xProW_own hp hend Wk.hello_wcPro hR
    (by have h80 : (80 : Int64).toInt = 80 := (by decide); omega) hhi (by decide) (by decide)

/-- **`OwnW` at `scc_rt_thr_worker`'s prologue** (frame 64). -/
theorem thrPro_ownH {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -72)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    XProW (OwnW W) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 64 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs J :=
  xProW_own hp hend hello_thrPro hR
    (by have h64 : (64 : Int64).toInt = 64 := (by decide); omega) hhi (by decide) (by decide)

/-- **`OwnW` at `wc_worker`'s `.entry` nodes**: the block up to the multiply, the multiply, the block after it. -/
theorem wE_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} :
    NodeZA (OwnW W) exe endPc R F (Body.wN (_root_.Executable.labels exe).label J Pr .e) Body.wkE1 ∧
      NodeZA (OwnW W) exe endPc R F (Body.wN (_root_.Executable.labels exe).label J Pr .mul)
        [(Body.wkMul.toDir, 4)] ∧
      NodeZA (OwnW W) exe endPc R F (Body.wN (_root_.Executable.labels exe).label J Pr .e2) Body.wkE2 := by
  refine ⟨?_, ?_, ?_⟩
  · rb Body.wkE1_ok (Wk.wkE1Code hp hend)
  · exact nodeZA_cell (Wk.wkMulCode hp hend) fun _ _ _ hc _ _ _ => ownW_fi hc
  · rb Body.wkE2_ok (Wk.wkE2Code hp hend)

/-- **`OwnW` at `wc_worker`'s call node** (`scc_rt_print`'s first block, `%rsp` at `-96`), in the worker's
region. -/
theorem wCall_ownH {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J Kc : AS → Ctl → Prop} :
    NodeZA (OwnW W) exe endPc R F (Body.wCall (_root_.Executable.labels exe).label J Kc) Spike.Lib.X64.Print.x0 := by
  rb RelZH.x0_okW (fun s he hn => (Wk.printCode hp hend (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := 0) (ra := 0)).e s he hn)

end Spike.Lib.X64.Flow.Worker.Hello.OwnZH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.unpk_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.unpk_ownH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.tail_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.tail_ownH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.thrTail_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.thrTail_ownH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.child_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.child_ownH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.OwnZH.wE_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.OwnZH.wE_ownH
