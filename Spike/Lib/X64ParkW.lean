/-
**`scc_rt_park` inside the abort-site predicate** (x64): the
x64 twin of `Spike/Lib/A64ParkW.lean`. `Park.seg_park`
(`Spike/Lib/X64Park.lean`) as a `SegW` segment inside any `W` that holds
every node's states (`ParkGW`, `seg_parkWG`), and inside `AbOffL`
(`Spike/Lib/X64AbOffLDef.lean`): every state of the routine is off the
`writeErr` and `threads` exit calls and the transfer sites, given that the
routine's pcs are (`RunsOff lab parkRuns`, byte runs, decided on the
listing).

- `parkRuns`: the routine's pcs as byte runs after its four labels.
- `ParkGW`, `seg_parkWG`: the routine inside any `W`, given every node's
  states in it (`BlkW` per block, `NodeW` per single instruction: the
  thread-pointer load, the two exchanges and the `syscall`).
- `parkGW_of_runs`: `AbOffL` holds them all, from `RunsOff`.
- `seg_parkW`: the routine as one segment inside `AbOffL`.
-/
import Spike.Lib.X64Park
import Spike.Lib.X64AbOffLDef

namespace Spike.Lib.X64.Flow.Park

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)
open Spike.Lib.X64AbOffL (PcOff AbOffL RunsOff pcOff_add pcOff_at)

/-- **`scc_rt_park`'s pcs**: the byte runs after its four labels (the
prologue's 8 bytes, `.entry`'s 50, `.wait`'s 92, `.done`'s 5). -/
def parkRuns : List (String × Nat × Nat) :=
  [("scc_rt_park", 0, 8), (".Lscc_rt_park.entry", 0, 50), (".Lscc_rt_park.wait", 0, 92),
    (".Lscc_rt_park.done", 0, 5)]

/-- **The routine's states inside `W`**, at one region `R` and frame
condition `F`: every block node's internal states (`BlkW`), the
thread-pointer load's, the two exchanges' and the futex wait's (`NodeW`). -/
structure ParkGW (W : Frag isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (c0 : Ctl) (rbp0 ra tp : BitVec 64) : Prop where
  e : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .e) b0
  fsl : NodeW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .fsl)
  n1 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n1) b1
  xchg1 : NodeW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .xchg1)
  n2 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n2) b2
  n3 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n3) b3
  wait : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .wait) b4
  sys : NodeW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .sys)
  n5 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n5) b5
  xchg2 : NodeW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .xchg2)
  n6 : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .n6) b6
  done : BlkW W (fun _ _ => False) exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .done) b7

section ProofW

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {rbp0 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node inside `W`: the block, its `okBlk`, its code and `ParkGW`
field; the edge is left. -/
macro "nodeGW " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) hW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_park` inside any `W`** (`seg_park` with every node's states
in `W`, `hW`). -/
theorem seg_parkWG {W : Frag isa} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -56) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hcode : Code c0 rbp0 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8)
    (hW : ParkGW W exe endPc R F c0 rbp0 ra tp) :
    SegW W (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c0 rbp0 ra tp x) s c) := by
  refine fn_segW (N := N _ c0 rbp0 ra tp) (E := E c0 rbp0 ra tp) (fun i => ?_) PN.e
  cases i
  case e => nodeGW b0 b0_ok e; rw [N, b0_run]; hit PN.fsl
  case fsl =>
    refine ownFsld_ndW (by decide) hF (fun s he hn => hcode.fsl s he hn) hown hW.fsl fun m σ c _ hm hJ => ?_
    obtain ⟨hc0, h8, h0, hfs⟩ := hJ
    have ha : σ.regs.fsBase.toBitVec + (0 : Int64).toBitVec = tp := by rw [hfs]; exact BitVec.add_zero tp
    refine ⟨ha, hT.rt, hT.mp, hT.unmapped m hm, c, .refl c, ?_⟩
    hit PN.n1
  case n1 => nodeGW b1 b1_ok n1; rw [N, b1_run]; hit PN.xchg1
  case xchg1 =>
    refine rtXchg_ndW (A := tp + 16#64) (by decide) hF (fun s he hn => hcode.xchg1 s he hn) hW.xchg1
      fun m σ c _ _ hJ => ?_
    obtain ⟨hT', hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; rfl, by rw [ha]; exact hS, fun v => ?_⟩
    hit PN.n2
  case n2 =>
    nodeGW b2 b2_ok n2; rw [N, b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => nodeGW b3 b3_ok n3; rw [N, b3_run]; hit PN.wait
  case wait =>
    nodeGW b4 b4_ok wait; rw [N, b4_run]
    have hc : (16#64 : BitVec 64) + tp = tp + 16#64 := BitVec.add_comm _ _
    hit PN.sys
  case sys =>
    have hcall : ∀ σ c, (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .sys).J σ c →
        syscallCall σ.regs = some .futexWait := by
      rintro σ c ⟨-, h0, h1, h3, h8⟩
      refine syscallCall_futexWait ?_ ?_ ?_ ?_
      · have := congrArg BitVec.toNat h8; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h1; simpa [Reg64s.get64] using this
      · have := congrArg BitVec.toNat h0; rw [← htp4, ← this]; simp [Reg64s.get64]
      · have := congrArg BitVec.toNat h3; simpa [Reg64s.get64] using this
    refine syscall_ndW hK hF (fun s he hn => hcode.sys s he hn) hW.sys (fun σ c hJ => ?_) ?_
    · refine ⟨.futexWait, hcall σ c hJ, nofun, fun v _ => ⟨c, .refl c, ?_⟩⟩
      obtain ⟨hT', -⟩ := hJ
      hit PN.n5
    · rintro s c σ call - hJ hc
      rw [hcall σ c hJ] at hc
      cases hc
      exact ⟨nofun, nofun, nofun, nofun⟩
  case n5 => nodeGW b5 b5_ok n5; rw [N, b5_run]; hit PN.xchg2
  case xchg2 =>
    refine rtXchg_ndW (A := tp + 16#64) (by decide) hF (fun s he hn => hcode.xchg2 s he hn) hW.xchg2
      fun m σ c _ _ hJ => ?_
    obtain ⟨hT', hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; rfl, by rw [ha]; exact hS, fun v => ?_⟩
    hit PN.n6
  case n6 => nodeGW b6 b6_ok n6; rw [N, b6_run]; exit PX.ret
  case done => nodeGW b7 b7_ok done; rw [N, b7_run]; exit PX.ret

set_option hygiene false in
/-- A block node's states inside `AbOffL`: the block, its run `(l, lo, hi)`
and offset `c` in it. -/
macro "blkW " b:ident l:term:max lo:term:max hi:term:max c:term:max : tactic =>
  `(tactic| exact fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ =>
    ⟨pcOff_add hW (l := $l) (lo := $lo) (hi := $hi) (c := $c) (by simp [parkRuns]) (by omega)
      ((show ∀ k < ($b).length, $c + cellOff $b k < $hi by decide) k hk)
      (by simp only [N, Int64.add_assoc]; first | rfl | simp), fun _ h => h⟩)

set_option hygiene false in
/-- A one-instruction node's states inside `AbOffL`. -/
macro "oneW " l:term:max lo:term:max hi:term:max c:term:max : tactic =>
  `(tactic| exact fun s _ ⟨_, _, _, hpc, _⟩ => ⟨by
    show PcOff _ s.st.2
    rw [hpc]
    exact pcOff_at hW (l := $l) (lo := $lo) (hi := $hi) (c := $c) (by simp [parkRuns]) (by omega) (by omega)
      (by simp only [N, pcSys, Int64.add_assoc]; first | rfl | simp), fun _ h => h⟩)

/-- **Every node's states are `AbOffL`**, given the routine's pcs are off
the exits and the transfer sites (`RunsOff`). -/
theorem parkGW_of_runs (hW : RunsOff (_root_.Executable.labels exe).label parkRuns) :
    ParkGW (AbOffL (_root_.Executable.labels exe).label) exe endPc R F c0 rbp0 ra tp where
  e := by blkW b0 "scc_rt_park" 0 8 0
  fsl := by oneW ".Lscc_rt_park.entry" 0 50 0
  n1 := by blkW b1 ".Lscc_rt_park.entry" 0 50 9
  xchg1 := by oneW ".Lscc_rt_park.entry" 0 50 24
  n2 := by blkW b2 ".Lscc_rt_park.entry" 0 50 28
  n3 := by blkW b3 ".Lscc_rt_park.entry" 0 50 48
  wait := by blkW b4 ".Lscc_rt_park.wait" 0 92 0
  sys := by oneW ".Lscc_rt_park.wait" 0 92 62
  n5 := by blkW b5 ".Lscc_rt_park.wait" 0 92 64
  xchg2 := by oneW ".Lscc_rt_park.wait" 0 92 79
  n6 := by blkW b6 ".Lscc_rt_park.wait" 0 92 83
  done := by blkW b7 ".Lscc_rt_park.done" 0 5 0

/-- **`scc_rt_park` inside `AbOffL`** (`seg_parkWG` with every state off
the `writeErr` and `threads` exit calls and the transfer sites, `hW`). -/
theorem seg_parkW (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -56) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hcode : Code c0 rbp0 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8)
    (hW : RunsOff (_root_.Executable.labels exe).label parkRuns) :
    SegW (AbOffL (_root_.Executable.labels exe).label) (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c0 rbp0 ra tp x) s c) :=
  seg_parkWG hF hR hlo hhi hK hT hown hS htp4 hcode hentry (parkGW_of_runs hW)

end ProofW

end Spike.Lib.X64.Flow.Park
