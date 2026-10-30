/-
**`scc_rt_alloc`'s counter write at `hello1.w`'s instance** (AArch64): the
allocator's node obligations (`AllocW`, `Spike/Lib/A64Alloc.lean`) inside
`W0`'s counter component (a write of the counter only in a context `Ctx`).

- `allocCtr`: every node of `scc_rt_alloc`, for a memory side with the
  arena's base: only the counter's add writes the counter (its
  states in `Ctx`, `hctx`), the header's store a word of the heap, every
  other step nothing.
- `blkW_pc`, `nodeW_pc`, `allocPc`, `abortW_of_pcOff`, `allocAbortW`: its
  states off the marks' sites, so `W0`'s abort sites' obligation vacuous.
-/
import Spike.Test.A64Hello1AllocArena

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide Frag)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64ConsumerA (WrAt)
open Spike.Test.A64ArenaHello1 (ar)
open Spike.Lib.A64.Flow.Hello1.Inst

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Spike.Test.A64Hello1RtW (hello1_instOk)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call} {Ctx : Frag isaLSE2}

set_option hygiene false in
/-- A block of `scc_rt_alloc`: it writes nothing. -/
local macro "nab " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact BlkW.imp (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩)) (l := $l) (k := $k) (by decide +kernel)
    (by dsimp only [N]; decide +kernel) $ok hR hal (by omega) (by omega)) Spike.Lib.A64.Flow.BlkW.triv
    (fun _ _ h _ hW => (h _ hW).elim))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "nsi " si:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_si (hello1_instOk (rS := ⟨0, 0⟩)) (si := $si) (l := $l) (k := $k)
    (p := labT $l + Int64.ofNat (4 * $k)) (by decide +kernel) rfl (by dsimp only [N]; decide +kernel))
    Spike.Lib.A64.Flow.NodeW.triv (fun _ _ h _ hW => (h _ hW).elim))

/-- The counter lies below the heap. -/
theorem ctr_lt_heap : ar.ctr + 8 ≤ ar.heap := by decide

/-- **`scc_rt_alloc`'s states write the counter only in `Ctx`**, for a
memory side with the arena's base (`hheap`), the
counter add's states in `Ctx` (`hctx`), every header the code may store
unmapped in private memory (`hmem`, `hq`): the header's store writes a
word of the heap, every other step but the add nothing. -/
theorem allocCtr (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap)
    (hctx : ∀ s c, At hello1Exe hello1End R F (N (_root_.Executable.labels hello1Exe).label ms q .rmw) s c →
      Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun s c hA => ⟨fun _ => hctx s c hA, fun _ h => h⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · nab "scc_rt_alloc" 0 b0_ok
  · nab ".L2_scc_rt_alloc.0_entry" 0 b1_ok
  · nab ".L2_scc_rt_alloc.0_entry" 4 b2_ok
  · nsi iAdrpC ".L2_scc_rt_alloc.1_cnt" 0
  · nsi iAddC ".L2_scc_rt_alloc.1_cnt" 1
  · nab ".L2_scc_rt_alloc.1_cnt" 2 b3_ok
  · nab ".L2_scc_rt_alloc.1_cnt" 6 b4_ok
  · nab ".L2_scc_rt_alloc.1_cnt" 15 b5_ok
  · nab ".L2_scc_rt_alloc.2_slow" 0 b6_ok
  · nab ".L2_scc_rt_alloc.2_slow" 4 b7_ok
  · nab ".L2_scc_rt_alloc.4_full" 0 b9_ok
  · nab ".L2_scc_rt_alloc.5_ok" 0 b11_ok
  · nsi iAdrpH ".L2_scc_rt_alloc.5_ok" 8
  · nsi iAddH ".L2_scc_rt_alloc.5_ok" 9
  · nab ".L2_scc_rt_alloc.5_ok" 10 b12_ok
  · refine NodeW.imp (nodeW_wr_st (hello1_instOk (rS := ⟨0, 0⟩)) (t := .X9) (b := .X10) (i := 0)
      (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (p := labT ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41))
      (by decide +kernel) rfl (by dsimp only [N]; decide +kernel) fun σ c m hJ hF => ?_)
      Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
      have hq' := hq m hF
      rw [hello1_labT] at hq'
      exact hmem _ ⟨o.toNat, hle, hdr_addr hq' hle hn28 h10⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -, -⟩, -, -, h10⟩, hF, hL⟩ - hW
      have hq' := hq _ hF
      rw [hello1_labT] at hq'
      have ha := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only at ha
      rw [hdr_addr hq' hle hn28 h10, Spike.Lib.A64.Alloc.Call.hdrAt, hheap] at ha
      have := ctr_lt_heap
      have : ar.ctrLoc.addr.toNat = ar.ctr := by decide
      omega
  · nab ".L2_scc_rt_alloc.5_ok" 42 b13_ok
  · exact NodeW.imp (Spike.Lib.LowerA64.BlkW.nodeW (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩))
      (l := ".L2_scc_rt_alloc.5_ok") (k := 54) (blk := [iRet.toDir]) (lo := -160) (hi := 0) (by decide +kernel)
      (by dsimp only [N]; decide +kernel) (by dsimp only [N]; decide) hR hal (by omega) (by omega))
      (List.cons_ne_nil _ _)) Spike.Lib.A64.Flow.NodeW.triv (fun _ _ h _ hW => (h _ hW).elim)

end Alloc

/-! ## Off the abort sites -/

section Pc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- A block node's states are at its pcs. -/
theorem blkW_pc {P : Nat → Prop} {n : ND} {blk : List Directive}
    (h : ∀ k < blk.length, P (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat) :
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

open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call}

/-- **`scc_rt_alloc`'s states are off the marks' sites** (`okPc`). -/
theorem allocPc : AllocW ms q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  all_goals first
    | (refine blkW_pc (P := fun p => okPc p = true) ?_; dsimp only [N]; rw [labT_eq_labY]; decide +kernel)
    | (refine nodeW_pc (P := fun p => okPc p = true) ?_; dsimp only [N]; rw [labT_eq_labY]; decide +kernel)

/-- **`scc_rt_alloc`'s states meet the abort sites' obligation** (vacuously,
off them). -/
theorem allocAbortW : AllocW ms q (fun s c => ∀ fs, AbortW μ0 s c fs) (fun _ _ => False) hello1Exe hello1End R F :=
  AllocW.imp allocPc (Spike.Lib.A64.Alloc.AllocW.triv ms q) fun s _ h _ _ =>
    abortW_of_pcOff (pcOff_of_okPc (rS := ⟨0, 0⟩) s h).1

end AllocPc

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.A64Hello1W0.ctr_lt_heap' depends on axioms: [propext] -/
#guard_msgs in #print axioms ctr_lt_heap

/-- info: 'Spike.Test.A64Hello1W0.allocCtr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtr

/-- info: 'Spike.Test.A64Hello1W0.allocPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocPc

/-- info: 'Spike.Test.A64Hello1W0.allocAbortW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbortW

end Spike.Test.A64Hello1W0
