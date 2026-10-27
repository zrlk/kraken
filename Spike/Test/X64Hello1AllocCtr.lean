/-
**`scc_rt_alloc`'s counter write at `hello1.x`'s instance** (x86-64): the
allocator's node obligations (`AllocW`, `Spike/Lib/X64Alloc.lean`) inside
`W0`'s counter component (a write of the counter only in a context `Ctx`).
The twin of `Spike/Test/A64Hello1AllocCtr.lean`.

- `allocCtr`: every node of `scc_rt_alloc`, for a memory side with the
  arena's base: only the counter's add writes the counter (its
  states in `Ctx`, `hctx`), the header's store a word of the heap, every
  other step nothing.
- `blkW_pc`, `nodeW_pc`, `allocPc`, `abortW_of_pcOff`, `allocAbortW`: its
  states off the marks' sites, so `W0`'s abort sites' obligation vacuous.
-/
import Spike.Test.X64Hello1AllocArena

namespace Spike.Test.X64Hello1W0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide Frag)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND At bAddr cellOff)
open Spike.Lib.X64ConsumerA (WrAt)
open Spike.Test.X64ArenaHello1 (ar)
open Spike.Lib.X64.Flow.Hello1.Inst

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRet fnL entryL cntL slowL fullL okL bPro_ok bChk_ok bJ1_ok
  bC1_ok bC2_ok bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok
  bO9_ok)
open Spike.Test.X64Hello1RtW (hello1_instOk)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {q : Call} {Ctx : Frag isa}

set_option hygiene false in
/-- A block of `scc_rt_alloc`: it writes nothing. -/
local macro "nab " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.BlkW.imp (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩)) (l := $l) (off := $k)
    (by decide +kernel) (by first | rfl | exact Spike.Lib.X64.Flow.ofNat_zero' _) $ok hR (by omega) (by omega))
    Spike.Lib.X64.BlkW.triv (fun _ _ h _ hW => (h _ hW).elim))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "nsi " si:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.NodeW.imp (nodeW_noWr_si (hello1_instOk (rS := ⟨0, 0⟩)) (si := $si) (z := $z)
    (l := $l) (off := $k) (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl
    (by first | rfl | exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm))
    Spike.Lib.X64.NodeW.triv (fun _ _ h _ hW => (h _ hW).elim))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "nfi " fi:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.NodeW.imp (nodeW_noWr_fi (hello1_instOk (rS := ⟨0, 0⟩)) (fi := $fi) (z := $z)
    (l := $l) (off := $k) (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl rfl)
    Spike.Lib.X64.NodeW.triv (fun _ _ h _ hW => (h _ hW).elim))

/-- The counter lies below the heap. -/
theorem ctr_lt_heap : ar.ctr + 8 ≤ ar.heap := by decide

/-- **`scc_rt_alloc`'s states write the counter only in `Ctx`**, for a
memory side with the arena's base (`hheap`), the
counter add's states in `Ctx` (`hctx`), every header the code may store
unmapped in private memory (`hmem`, `hq`): the header's store writes a
word of the heap, every other step but the add nothing. -/
theorem allocCtr (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap)
    (hctx : ∀ s c, At hello1Exe hello1End R F (N (_root_.Executable.labels hello1Exe).label ms q .rmw) s c →
      Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun s c hA => ⟨fun _ => hctx s c hA, fun _ h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · nab fnL 0 bPro_ok
  · nab entryL 0 bChk_ok
  · nab entryL 16 bJ1_ok
  · nsi iCtr 7 cntL 0
  · nab cntL 7 bC1_ok
  · nab cntL 24 bC2_ok
  · nab cntL 59 bJ2_ok
  · nab slowL 0 bSlow_ok
  · nab slowL 16 bJ3_ok
  · nab fullL 0 bFull_ok
  · nab okL 0 bO0_ok
  · nfi (.shr_cl .rax) 3 okL 11
  · nab okL 14 bO1_ok
  · nfi (.and_rr .rax .rcx) 3 okL 29
  · nab okL 32 bO2_ok
  · nsi iHeap 7 okL 36
  · nab okL 43 bO3_ok
  · nfi (.shl_cl .rax) 3 okL 58
  · nab okL 61 bO4_ok
  · nfi (.imul_rr .rax .rcx) 4 okL 88
  · nab okL 92 bO5_ok
  · nfi (.shl_cl .rax) 3 okL 107
  · nab okL 110 bO6_ok
  · nfi (.shl_cl .rax) 3 okL 125
  · nab okL 128 bO7_ok
  · nfi (.or_rr .rax .rcx) 3 okL 140
  · nab okL 143 bO8_ok
  · refine Spike.Lib.X64.NodeW.imp (nodeW_wr_st (hello1_instOk (rS := ⟨0, 0⟩)) (b := .rcx) (k := 0) (r := .rax)
      (z := 3) (l := okL) (off := 170) (p := labT okL + Int64.ofNat 170) (by decide +kernel) rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
      have hq' := hq m hF
      rw [hello1_labT] at hq'
      exact hmem _ ⟨o.toNat, hle, hdr_addr hq' hle hn28 hcx⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, hcx⟩, hF, hL⟩ - hW
      have hq' := hq _ hF
      rw [hello1_labT] at hq'
      have ha := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only at ha
      rw [hdr_addr hq' hle hn28 hcx, Spike.Lib.X64.Alloc.Call.hdrAt, hheap] at ha
      have := ctr_lt_heap
      have : ar.ctrLoc.addr.toNat = ar.ctr := by decide
      omega
  · nab okL 173 bO9_ok
  · exact Spike.Lib.X64.NodeW.imp (BlkW.nodeW (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩))
      (l := okL) (off := 226) (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8) (by decide +kernel) rfl
      (show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide) hR
      (by omega) (by omega)) (List.cons_ne_nil _ _)) Spike.Lib.X64.NodeW.triv (fun _ _ h _ hW => (h _ hW).elim)

end Alloc

/-! ## Off the abort sites -/

section Pc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- A block node's states are at its pcs. -/
theorem blkW_pc {P : Nat → Prop} {n : ND} {blk : List (Directive × Nat)}
    (h : ∀ k < blk.length, P (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat) :
    BlkW (fun s _ => P (pcOf s)) (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ => ⟨h k hk, fun _ h => h⟩

/-- A node's states are at its pc. -/
theorem nodeW_pc {P : Nat → Prop} {n : ND} (h : P n.pc.toBitVec.toNat) :
    NodeW (fun s _ => P (pcOf s)) (fun _ _ => False) exe endPc R F n :=
  fun _ _ ⟨_, _, _, hpc, _⟩ =>
    ⟨(congrArg (fun p : Int64 => P p.toBitVec.toNat) hpc).mpr h, fun _ h => h⟩

/-- **The abort sites at a pair off them**: vacuous. -/
theorem abortW_of_pcOff {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame} (h : PcOff μ0 s) :
    AbortW μ0 s c fs :=
  fun k a ha hpc => (h.noAbort k a ha hpc).elim

end Pc

section AllocPc

open Spike.Lib.X64.Alloc (Call AllocW N)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

/-- **`scc_rt_alloc`'s states are off the marks' sites** (`okPc`). -/
theorem allocPc : AllocW ms q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  all_goals first
    | (refine blkW_pc (P := fun p => okPc p = true) ?_; dsimp only [N]; rw [labT_eq_labY]; decide +kernel)
    | (refine nodeW_pc (P := fun p => okPc p = true) ?_; dsimp only [N]; rw [labT_eq_labY]; decide +kernel)

/-- **`scc_rt_alloc`'s states meet the abort sites' obligation** (vacuously,
off them). -/
theorem allocAbortW : AllocW ms q (fun s c => ∀ fs, AbortW μ0 s c fs) (fun _ _ => False) hello1Exe hello1End R F :=
  Spike.Lib.X64.Alloc.AllocW.imp allocPc (Spike.Lib.X64.Alloc.AllocW.triv ms q) fun s _ h _ _ =>
    abortW_of_pcOff (pcOff_of_okPc (rS := ⟨0, 0⟩) s h).1

end AllocPc

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64Hello1W0.ctr_lt_heap' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms ctr_lt_heap

/--
info: 'Spike.Test.X64Hello1W0.allocCtr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocCtr

/--
info: 'Spike.Test.X64Hello1W0.allocPc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocPc

/--
info: 'Spike.Test.X64Hello1W0.allocAbortW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocAbortW

end Spike.Test.X64Hello1W0
