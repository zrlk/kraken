/-
**Stage 4 (repeated acquisition): the static per-thread invariant of the
repeated-acquire ticket-lock worker** `tkLoopWorker`, on the semantic machine.

- `Static`: the worker keeps its program, addresses and private memory (as
  `TicketInv.Static`).
- `SInv`: `Static` and a pc in `tkLoopPcs`, kept by every instruction step
  with any promise set (`step_sinv`), hence along solo runs
  (`threadNP_sinv`); every worker drops at most one promise per instruction
  (`dropBounded_of_sinv`, with the generic `TicketDrop.spec_store_len` /
  `spec_rmw_len`).
- `trace_sinv`: `SInv` at every thread of every index of a semantic trace
  (`TraceSem`) from a start configuration (`TkLoopStart`), promise steps
  included; `weakFairInstrSem_loop`: semantic weak fairness gives weak
  fairness for instruction steps.
-/
import Kraken.Promising.LiveTicketLoopTrees
import Kraken.Promising.LiveTicketDrop
import Kraken.Promising.LiveSem

namespace Kraken.Promising.Live.TicketLoopStatic

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees
open Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.TicketTrees (w32)
open Kraken.Promising.Live.TicketDrop (spec_store_len spec_rmw_len)
open Kraken.Promising.SLR.A64Trees (At goto)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-- The static facts of a worker: program, no declarations, end address,
addresses in `X0`–`X2`, the three words outside its private memory. -/
structure Static (x o c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout tkLoopWorker
  decls : s.decls = {}
  endPc : s.endPc = pcA 17
  x0 : s.st.1.regs.X0.toBitVec = x
  x1 : s.st.1.regs.X1.toBitVec = o
  x2 : s.st.1.regs.X2.toBitVec = c
  dx : Mem.loadInt s.st.1.dmem x 4 = none
  dO : Mem.loadInt s.st.1.dmem o 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

omit hv in
theorem Static.goto {x o c : BitVec 64} {s : isa.State} (h : Static x o c s) (md : MachineData) (pc : Int64)
    (h0 : md.regs.X0 = s.st.1.regs.X0) (h1 : md.regs.X1 = s.st.1.regs.X1) (h2 : md.regs.X2 = s.st.1.regs.X2)
    (hd : md.dmem = s.st.1.dmem) : Static x o c (SLR.A64Trees.goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, h0 ▸ h.x0, h1 ▸ h.x1, h2 ▸ h.x2, hd ▸ h.dx, hd ▸ h.dO, hd ▸ h.dc⟩

theorem Static.at {x o c : BitVec 64} {s : isa.State} (h : Static x o c s) {i : Nat} (hi : i ∈ tkLoopPcs)
    (h17 : i ≠ 17) (hpc : s.st.2 = pcA i) : At tkLoopWorker s i :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h17 (addrOf_inj hi (by decide) e)⟩

omit hv in
/-- At the end address the worker has halted. -/
theorem stepOne_end {x o c : BitVec 64} {t : Thread isa} (h : Static x o c t.st) (hpc : t.st.st.2 = pcA 17)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A t tid mem = none := by
  have : isa.exec t.st = none := by
    show AArch64.exec t.st = none
    unfold AArch64.exec
    rw [hpc, h.endPc]
    simp
  simp [stepOne, this]

/-- **The promise-agnostic per-thread invariant**: `Static` and a pc in
`tkLoopPcs`. -/
structure SInv (x o c : BitVec 64) (s : isa.State) : Prop where
  st : Static x o c s
  pc : ∃ i ∈ tkLoopPcs, s.st.2 = pcA i

local macro "sinv" hS:ident hst:ident "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hS).goto _ _ rfl rfl rfl rfl, $j, by decide, by rw [$hst:ident] <;> rfl⟩)

/-- **One instruction step keeps `SInv` and drops at most one promise**, for
any promise set and memory. -/
theorem step_sinv {x o c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : SInv x o c t.st)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv x o c oc.thread.st ∧ t.prom.length ≤ oc.thread.prom.length + 1 := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_mov _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 3, by rw [hp]; omega⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_cbz _ (hS.at (by decide) (by decide) hpc)) hs ho
    refine ⟨?_, by rw [hp]; omega⟩
    by_cases hz : w32 t.st.st.1.regs.X7 = 0#32
    · rw [ite_eq_left hz] at hst; exact sinv hS hst, 17
    · rw [ite_eq_right hz] at hst; exact sinv hS hst, 4
  · obtain ⟨old, hst, hl⟩ := spec_rmw_len _ _ rfl (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    exact ⟨sinv hS hst, 6, hl⟩
  · obtain ⟨ts, v, hst, -, -, -, hp, -⟩ :=
      spec_load _ _ (exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    exact ⟨sinv hS hst, 7, by rw [hp]; omega⟩
  · obtain ⟨sf, hex, -⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
    obtain ⟨-, hst, hp, -⟩ := spec_done _ _ hex hs ho
    exact ⟨sinv hS hst, 8, by rw [hp]; omega⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hs ho
    refine ⟨?_, by rw [hp]; omega⟩
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst; exact sinv hS hst, 9
    · rw [ite_eq_right hz] at hst; exact sinv hS hst, 6
  · obtain ⟨ts, v, hst, -, -, -, hp, -⟩ :=
      spec_load _ _ (exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    exact ⟨sinv hS hst, 10, by rw [hp]; omega⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 11, by rw [hp]; omega⟩
  · obtain ⟨hst, hl⟩ := spec_store_len _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    exact ⟨sinv hS hst, 12, hl⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 13, by rw [hp]; omega⟩
  · obtain ⟨hst, hl⟩ := spec_store_len _ _ (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    exact ⟨sinv hS hst, 14, hl⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_sub _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 15, by rw [hp]; omega⟩
  · obtain ⟨-, hst, hp, -⟩ := spec_done _ _ (exec_b_round _ (hS.at (by decide) (by decide) hpc)) hs ho
    exact ⟨sinv hS hst, 3, by rw [hp]; omega⟩
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {x o c : BitVec 64} {tid : Nat} {p q : Thread isa × Memory}
    (h : ThreadNP Arch.armv8 tid p q) (hp : SInv x o c p.1.st) : SInv x o c q.1.st :=
  ThreadNP.stateInv (SInv x o c) (fun h hs ho => (step_sinv h hs ho).1) h hp

/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {x o c : BitVec 64} {tid : Nat} {t : Thread isa} (h : SInv x o c t.st) :
    DropBounded Arch.armv8 1 tid t :=
  dropBounded_of_stateInv (SInv x o c) (fun h hs ho => step_sinv h hs ho) h

/-- A start state satisfies `SInv` (at position 0, the address of 1). -/
theorem sinv_start {k : Nat} {x o c : BitVec 64} {s : isa.State} (h : LoopStartState k x o c s) : SInv x o c s :=
  ⟨⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.x2, h.dx, h.dO, h.dc⟩, 1, by decide, h.pc.trans addrOf_0⟩

omit layout hv in
/-- A semantic step: the thread's own instruction step, a promise step that
keeps the thread's state, or a step of another thread. -/
theorem stepSem_get {A : Arch} {fuel j tid : Nat} {c c' : Config isa} (h : StepSem A fuel j c c') {t' : Thread isa}
    (ht' : c'.threads[tid]? = some t') :
    (∃ t, c.threads[tid]? = some t ∧ t'.st = t.st) ∨
      ∃ t outs oc, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ .ok oc ∈ outs ∧ t' = oc.thread := by
  rcases h with ⟨u, outs, oc, hu, hso, ho, -, rfl⟩ | ⟨u, w, hu, -, -, rfl⟩
  · rcases SpinStep.wt_get hu ht' with ⟨rfl, rfl⟩ | ⟨-, ht⟩
    · exact .inr ⟨u, outs, oc, hu, hso, ho, rfl⟩
    · exact .inl ⟨t', ht, rfl⟩
  · rcases SpinStep.wt_get hu ht' with ⟨rfl, rfl⟩ | ⟨-, ht⟩
    · exact .inl ⟨u, hu, rfl⟩
    · exact .inl ⟨t', ht, rfl⟩

/-- **`SInv` at every thread of every index** of a semantic trace from a
start configuration, promise steps included. -/
theorem trace_sinv {fuel k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) :
    ∀ i (tid : Nat) t, (tr.cfg i).threads[tid]? = some t → SInv x o c t.st
  | 0, tid, t, ht => by
    rw [h0] at ht
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨s, hs', rfl⟩ := ht
    exact sinv_start (hs.hst s (List.mem_of_getElem? hs'))
  | i + 1, tid, t, ht => by
    have ih := trace_sinv hs tr h0 i
    rcases tr.step i with ⟨j, hst⟩ | ⟨-, he⟩
    · rcases stepSem_get hst ht with ⟨u, hu, e⟩ | ⟨u, outs, oc, hu, hso, ho, rfl⟩
      · have := ih tid u hu; rw [← e] at this; exact this
      · exact (step_sinv (ih tid u hu) hso ho).1
    · rw [he] at ht; exact ih tid t ht

/-- **Semantic weak fairness gives weak fairness for instruction steps** on
every trace from a start configuration (promises included). -/
theorem weakFairInstrSem_loop {fuel k N : Nat} {x o c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hf : WeakFairSem Arch.armv8 fuel tr.cfg) :
    WeakFairInstrSem Arch.armv8 fuel tr.cfg :=
  weakFairInstrSem_of_weakFairSem (B := 1) tr (fun i tid t ht => dropBounded_of_sinv (trace_sinv hs tr h0 i tid t ht)) hf

end Kraken.Promising.Live.TicketLoopStatic
