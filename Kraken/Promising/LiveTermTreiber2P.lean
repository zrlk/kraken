/-
**Stage 4: termination of `treiber2`-shaped workers on
the semantic machine, position-parametric** (`TermBoundSem`, no fairness).

`LiveTermTreiber2.lean` proves termination for `treiber2DWorker`, its rank
table indexed by that program's positions. This file restates the same
argument (the same rank `TermTreiber2.rk`, success count `sOf`, flag `fl`,
bound `cntBound`) for any program `W` whose cells are those of
`treiber2DWorker` at shifted positions: `σ i` is the position in `W` of the
cell at `treiber2DWorker` position `i`, and `pcS W σ i` its address. The
data flag `data` says whether `W` has the data store (`STR W9,[X1]`,
position `1`) and the data load (`LDR W11,[X2]`, position `18`); without
them a worker starts at `push` (position `3`) and `MOV X10,X2` (position
`17`) falls through to `B done` (position `19`).

The cells are the hypothesis `Cells W σ data` (one field per cell, the
statements of `LiveTermTreiber2Trees.lean` at `σ`, plus distinct addresses);
the instances are `LiveTermTreiber2Nodes.lean` (`treiber2_nodes.kl`) and,
`LiveTermTreiber2.lean` itself (`TermTreiber2.cells`, at
`σ = id`): the `treiber2` step lemmas and theorems are re-derived from this
file, statements unchanged. The rank table is in
`LiveTermTreiber2Rank.lean`. Everything here is on the semantic machine
(`StepSem`/`TraceSem` under `Arch.armv8`).
-/
import Kraken.Promising.LiveTermTreiber2Rank
import Kraken.Promising.LiveTermTreiber2Trees

namespace Kraken.Promising.Live.TermTreiber2P

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Term
open Kraken.Promising.Live.TermTreiber2 (topL fl rk sOf PcI cntBound)
open Kraken.Promising.SLR.A64Trees (At goto)
open Kraken.Promising.Live.TicketStep (spec_done spec_load)
open Kraken.Promising.Live.SemShape (spec_store_p)

/-! ## Rank lemmas (layout-free; `TermTreiber2`'s namesakes, which carry its
layout instance, are instances of these) -/

theorem sOf_le (p : Nat) (s : MachineData) : sOf p s ≤ 2 := by
  unfold sOf; split <;> (try split) <;> omega

theorem fl_le (s : MachineData) (c : Val) : fl s c ≤ 10 := by unfold fl; split <;> omega

/-- The rank inside a loop body, across a step that keeps `X2`. -/
theorem rank_body {N c0 c1 : Nat} {u0 u1 : Val} {s s' : MachineData} {a b : Nat} (hx : s'.regs.X2 = s.regs.X2)
    (hN : c1 ≤ N) (hc : c0 ≤ c1 ∧ (c0 < c1 ∨ (c0 = c1 ∧ u0 = u1))) (hab : a < b) :
    a + 10 * (N - c1) + fl s' u1 < b + 10 * (N - c0) + fl s u0 := by
  rcases hc with ⟨-, hlt | ⟨rfl, rfl⟩⟩
  · have := fl_le s' u1; omega
  · have : fl s' u0 = fl s u0 := by simp only [fl, hx]
    omega

/-- A step that changes neither memory nor the coherence view keeps `cnt`
and `cur`. -/
theorem cnt_done {t : BitVec 64} {u : Thread isa} {mem : Memory} {o : Outcome isa} (hm : o.mem = mem)
    (hc : o.thread.views.coh = u.views.coh) :
    o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) = mem.cntBelow (topL t) (u.views.getCoh (topL t)) ∧
      o.mem.curBelow (topL t) (o.thread.views.getCoh (topL t)) = mem.curBelow (topL t) (u.views.getCoh (topL t)) := by
  rw [hm, SpinSwpStep.getCoh_congr hc]; exact ⟨rfl, rfl⟩

variable [layout : _root_.Layout]

/-- The address of the cell at (`treiber2DWorker`) position `i` in `W`. -/
abbrev pcS (W : Program) (σ : Nat → Nat) (i : Nat) : Int64 := (layout W).addrOf (σ i)

/-! ## Positions and cells -/

/-- The positions shared by every worker shape (`21` is the end). -/
def cPcs : List Nat := [3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21]

/-- The positions of a worker shape: with the data cells `1` and `18` iff
`data`. -/
def pcsD (data : Bool) : List Nat := (if data then [1, 18] else []) ++ cPcs

theorem memC {data : Bool} {i : Nat} (h : i ∈ cPcs := by decide) : i ∈ pcsD data :=
  List.mem_append_right _ h

/-- **The cells of a `treiber2`-shaped worker `W`** at positions `σ`: the
statements of `LiveTermTreiber2Trees.lean` (the data cells only if `data`),
and distinct addresses for the positions. -/
structure Cells (W : Program) (σ : Nat → Nat) (data : Bool) : Prop where
  inj : ∀ {i j : Nat}, i ∈ pcsD data → j ∈ pcsD data → pcS W σ i = pcS W σ j → i = j
  str_d : data = true → ∀ (st : State), At W st (σ 1) → ∀ {n : BitVec 64}, st.st.1.regs.X1.toBitVec = n →
    Mem.loadInt st.st.1.dmem n 4 = none →
    isa.exec st = some (.store .plain false ⟨n, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X9.toBitVec))
      fun _ => .done (goto st st.st.1 (pcS W σ 3)))
  ldar : ∀ i, (i = 3 ∨ i = 10) → ∀ (st : State), At W st (σ i) → ∀ {t : BitVec 64},
    st.st.1.regs.X0.toBitVec = t → Mem.loadInt st.st.1.dmem t 8 = none →
    ∃ k : LoadKind, isa.exec st = some (.load k false ⟨t, 8⟩
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 v) }
        (pcS W σ (i + 1))))
  str_n : ∀ (st : State), At W st (σ 4) → ∀ {n : BitVec 64}, st.st.1.regs.X1.toBitVec = n →
    Mem.loadInt st.st.1.dmem (n + 8#64) 8 = none →
    isa.exec st = some (.store .plain false ⟨n + 8, 8⟩ (BitVec.setWidth 128 st.st.1.regs.X2.toBitVec)
      fun _ => .done (goto st st.st.1 (pcS W σ 5)))
  mov : ∀ i, (i = 5 ∨ i = 13) → ∀ (st : State), At W st (σ i) →
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 st.st.1.regs.X2.toBitVec } (pcS W σ (i + 1))))
  casal6 : ∀ (st : State), At W st (σ 6) → ∀ {t : BitVec 64}, st.st.1.regs.X0.toBitVec = t →
    Mem.loadInt st.st.1.dmem t 8 = none →
    ∃ k : RmwKind, isa.exec st = some (.rmw k false ⟨t, 8⟩
      (fun old => if BitVec.setWidth 64 old = st.st.1.regs.X3.toBitVec then
          some (BitVec.setWidth 128 st.st.1.regs.X1.toBitVec) else none)
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 v) }
        (pcS W σ 7)))
  cmp : ∀ i, (i = 7 ∨ i = 15) → ∀ (st : State), At W st (σ i) →
    ∃ s : StatusFlags, isa.exec st = some (.done (goto st { st.st.1 with status := s } (pcS W σ (i + 1))))
      ∧ (s.z = true ↔ st.st.1.regs.X3.toBitVec = st.st.1.regs.X2.toBitVec)
  bne8 : ∀ (st : State), At W st (σ 8) →
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.z = true then pcS W σ 10 else pcS W σ 3)))
  cbz11 : ∀ (st : State), At W st (σ 11) →
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.regs.X2.toBitVec = 0#64 then pcS W σ 21 else pcS W σ 12)))
  ldr12 : ∀ (st : State), At W st (σ 12) → ∀ {a : BitVec 64}, st.st.1.regs.X2.toBitVec = a →
    Mem.loadInt st.st.1.dmem (a + 8#64) 8 = none →
    isa.exec st = some (.load .plain false ⟨a + 8, 8⟩
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 v) }
        (pcS W σ 13)))
  casal14 : ∀ (st : State), At W st (σ 14) → ∀ {t : BitVec 64}, st.st.1.regs.X0.toBitVec = t →
    Mem.loadInt st.st.1.dmem t 8 = none →
    ∃ k : RmwKind, isa.exec st = some (.rmw k false ⟨t, 8⟩
      (fun old => if BitVec.setWidth 64 old = st.st.1.regs.X3.toBitVec then
          some (BitVec.setWidth 128 st.st.1.regs.X4.toBitVec) else none)
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 v) }
        (pcS W σ 15)))
  bne16 : ∀ (st : State), At W st (σ 16) →
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.z = true then pcS W σ 17 else pcS W σ 10)))
  mov17 : ∀ (st : State), At W st (σ 17) →
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X10 st.st.1.regs.X2.toBitVec }
      (pcS W σ (if data then 18 else 19))))
  ldr18 : data = true → ∀ (st : State), At W st (σ 18) → ∀ {a : BitVec 64}, st.st.1.regs.X2.toBitVec = a →
    Mem.loadInt st.st.1.dmem a 4 = none →
    isa.exec st = some (.load .plain false ⟨a, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X11 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        (pcS W σ 19)))
  b19 : ∀ (st : State), At W st (σ 19) → isa.exec st = some (.done (goto st st.st.1 (pcS W σ 21)))

/-- The position of an address (`0` off the positions). -/
def posOf (W : Program) (σ : Nat → Nat) (data : Bool) (pc : Int64) : Nat :=
  ((pcsD data).find? fun i => decide (pcS W σ i = pc)).getD 0

theorem posOf_pcS {W : Program} {σ : Nat → Nat} {data : Bool} (C : Cells W σ data) {i : Nat}
    (hi : i ∈ pcsD data) : posOf W σ data (pcS W σ i) = i := by
  unfold posOf
  cases h : (pcsD data).find? (fun j => decide (pcS W σ j = pcS W σ i)) with
  | none => exact absurd (by simpa using List.find?_eq_none.mp h i hi) (fun h' : ¬ pcS W σ i = pcS W σ i => h' rfl)
  | some j =>
    have := List.find?_some h
    simp only [decide_eq_true_eq] at this
    exact C.inj (List.mem_of_find?_eq_some h) hi this

/-! ## The per-thread state invariant, rank and count -/

/-- What a worker state never changes (`TermTreiber2.Static` at `σ`; the
4-byte private words only matter with the data cells). -/
structure Static (W : Program) (σ : Nat → Nat) (data : Bool) (t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout W
  decls : s.decls = {}
  endPc : s.endPc = pcS W σ 21
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec + 8#64 ≠ t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : data = true → ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- The worker sits at a position, with its register fact. -/
def PcOK (W : Program) (σ : Nat → Nat) (data : Bool) (s : isa.State) : Prop :=
  ∃ i ∈ pcsD data, s.st.2 = pcS W σ i ∧ PcI s.st.1 i

/-- A thread's rank in memory `mem` (`TermTreiber2.R` at `σ`). -/
def R (W : Program) (σ : Nat → Nat) (data : Bool) (N : Nat) (t : BitVec 64) (u : Thread isa) (mem : Memory) :
    Nat :=
  rk N (posOf W σ data u.st.st.2) u.st.st.1 (mem.cntBelow (topL t) (u.views.getCoh (topL t)))
    (mem.curBelow (topL t) (u.views.getCoh (topL t)))

/-- A thread's successful `CASAL`s. -/
def S (W : Program) (σ : Nat → Nat) (data : Bool) (u : Thread isa) : Nat :=
  sOf (posOf W σ data u.st.st.2) u.st.st.1

/-- **What one instruction step of a worker does** (`TermTreiber2.StepOK`
at `σ`). -/
structure StepOK (W : Program) (σ : Nat → Nat) (data : Bool) (t : BitVec 64) (N : Nat) (u : Thread isa)
    (mem : Memory) (o : Outcome isa) : Prop where
  st : Static W σ data t o.thread.st
  pc : PcOK W σ data o.thread.st
  eff : (o.mem = mem ∧ o.thread.prom = u.prom ∧ S W σ data u ≤ S W σ data o.thread) ∨
    (∃ w : Msg, WEff mem o.mem u.prom o.thread.prom w ∧
      S W σ data u + (if w.loc = topL t then 1 else 0) ≤ S W σ data o.thread)
  rank : Witness.FwdLeCoh u.views → u.views.getCoh (topL t) ≤ mem.last →
    o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ≤ N →
      R W σ data N t o.thread o.mem < R W σ data N t u mem

section Static

variable {W : Program} {σ : Nat → Nat} {data : Bool} (C : Cells W σ data)

theorem Static.goto {t : BitVec 64} {s : isa.State} (h : Static W σ data t s) (md : MachineData) (pc : Int64)
    (h0 : md.regs.X0 = s.st.1.regs.X0) (h1 : md.regs.X1 = s.st.1.regs.X1) (hd : md.dmem = s.st.1.dmem) :
    Static W σ data t (goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, h0 ▸ h.x0, h1 ▸ h.x1, hd ▸ h.d8, hd ▸ h.d4⟩

include C in
theorem Static.at {t : BitVec 64} {s : isa.State} (h : Static W σ data t s) {i : Nat} (hi : i ∈ pcsD data)
    (h21 : i ≠ 21) (hpc : s.st.2 = pcS W σ i) : At W s (σ i) :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h21 (C.inj hi memC e)⟩

/-- At the end address the worker has halted. -/
theorem stepOne_end {t : BitVec 64} {u : Thread isa} (h : Static W σ data t u.st) (hpc : u.st.st.2 = pcS W σ 21)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A u tid mem = none := by
  have : isa.exec u.st = none := by
    show AArch64.exec u.st = none
    unfold AArch64.exec
    rw [hpc, h.endPc]
    simp
  simp [stepOne, this]

end Static

/-! ## One step of a worker -/

section Steps

variable {W : Program} {σ : Nat → Nat} {data : Bool} (C : Cells W σ data)
  {t : BitVec 64} {N : Nat} {u : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {o : Outcome isa}
  (hS : Static W σ data t u.st) (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok o ∈ outs)

include C hS hs ho

omit C hS in
/-- The count across the step (`step_cnt`). -/
theorem cnt_step (hb : u.views.getCoh (topL t) ≤ mem.last) :
    mem.cntBelow (topL t) (u.views.getCoh (topL t)) ≤ o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ∧
      (mem.cntBelow (topL t) (u.views.getCoh (topL t)) < o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ∨
       (mem.cntBelow (topL t) (u.views.getCoh (topL t)) = o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ∧
        mem.curBelow (topL t) (u.views.getCoh (topL t)) = o.mem.curBelow (topL t) (o.thread.views.getCoh (topL t)))) :=
  step_cnt (stepOne_dord _ hs ho).2.2.1 hb ((stepOne_dord _ hs ho).2.1 _)

local macro "posn" i:term:max j:term:max : tactic => `(tactic|
  simp only [R, S, posOf_pcS C $i, posOf_pcS C $j])

theorem step1 (hd : data = true) (hpc : u.st.st.2 = pcS W σ 1) : StepOK W σ data t N u mem o := by
  subst hd
  obtain ⟨hst, h⟩ := spec_store_p _ _ (C.str_d rfl _ (hS.at C (by decide) (by decide) hpc) rfl (hS.d4 rfl _)) hs ho
  have hp3 : o.thread.st.st.2 = pcS W σ 3 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨3, memC, hp3, trivial⟩, .inr ⟨_, WEff.of_store h, ?_⟩,
    fun _ _ _ => ?_⟩
  · simp only [S, hp3, hpc, posOf_pcS C (show 1 ∈ pcsD true by decide), posOf_pcS C (memC (i := 3))]
    simp [sOf]
  · simp only [R, hp3, hpc, posOf_pcS C (show 1 ∈ pcsD true by decide), posOf_pcS C (memC (i := 3)), rk]
    omega

/-- The loads of `top` (positions `3` and `10`). -/
theorem stepLd {i : Nat} (hi : i = 3 ∨ i = 10) (hpc : u.st.st.2 = pcS W σ i) : StepOK W σ data t N u mem o := by
  have hm : i ∈ pcsD data ∧ i + 1 ∈ pcsD data ∧ i ≠ 21 := by
    rcases hi with rfl | rfl <;> exact ⟨memC, memC, by decide⟩
  obtain ⟨k, hex⟩ := C.ldar i hi _ (hS.at C hm.1 hm.2.2 hpc) hS.x0 (hS.d8 _)
  obtain ⟨ts, v, hst, -, -, hm', hp, -⟩ := spec_load _ _ hex hs ho
  have hpk : o.thread.st.st.2 = pcS W σ (i + 1) := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨i + 1, hm.2.1, hpk, by rcases hi with rfl | rfl <;> trivial⟩,
    .inl ⟨hm', hp, ?_⟩, fun hf hb hN => ?_⟩
  · rw [S, S, hpc, hpk]; posn hm.1 hm.2.1; rcases hi with rfl | rfl <;> simp [sOf]
  · obtain ⟨ts, v, hst, hmm, -, hr, h1, h2⟩ := load_window _ _ hf hex hs ho
    have hw := window_rank (Memory.Prefix.refl mem) hb hr h1 h2
    have hc := cnt_step hs ho hb
    rw [hmm] at hc hN ⊢
    rw [R, R, hpc, hst]
    simp only [posOf_pcS C hm.1, posOf_pcS C hm.2.1]
    generalize mem.cntBelow (topL t) (u.views.getCoh (topL t)) = c0 at *
    generalize mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) = c1 at *
    generalize mem.curBelow (topL t) (o.thread.views.getCoh (topL t)) = u1 at *
    rcases hi with rfl | rfl <;>
    · simp only [rk, fl]
      split
      · omega
      · have := hw.2 fun e => by simp_all
        omega

theorem step4 (hpc : u.st.st.2 = pcS W σ 4) : StepOK W σ data t N u mem o := by
  obtain ⟨hst, h⟩ := spec_store_p _ _ (C.str_n _ (hS.at C memC (by decide) hpc) rfl (hS.d8 _)) hs ho
  have hpk : o.thread.st.st.2 = pcS W σ 5 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨5, memC, hpk, trivial⟩, .inr ⟨_, WEff.of_store h, ?_⟩,
    fun hf hb hN => ?_⟩
  · rw [S, S, hpc, hpk]; posn (memC (i := 4)) (memC (i := 5))
    simp [sOf, topL, hS.x1]
  · rw [R, R, hpc, hst]; posn (memC (i := 4)) (memC (i := 5))
    exact rank_body rfl hN (cnt_step hs ho hb) (by omega)

/-- The `MOV X3,X2`s (positions `5` and `13`). -/
theorem stepMov {i : Nat} (hi : i = 5 ∨ i = 13) (hpc : u.st.st.2 = pcS W σ i) : StepOK W σ data t N u mem o := by
  have hm : i ∈ pcsD data ∧ i + 1 ∈ pcsD data ∧ i ≠ 21 := by
    rcases hi with rfl | rfl <;> exact ⟨memC, memC, by decide⟩
  obtain ⟨hm', hst, hp, hc⟩ := spec_done _ _ (C.mov i hi _ (hS.at C hm.1 hm.2.2 hpc)) hs ho
  have hpk : o.thread.st.st.2 = pcS W σ (i + 1) := by rw [hst]
  have hI : PcI o.thread.st.st.1 (i + 1) := by rcases hi with rfl | rfl <;> (rw [hst]; simp [PcI])
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨i + 1, hm.2.1, hpk, hI⟩,
    .inl ⟨hm', hp, by rw [S, S, hpc, hpk]; posn hm.1 hm.2.1; rcases hi with rfl | rfl <;> simp [sOf]⟩,
    fun hf hb hN => ?_⟩
  rw [R, R, hpc, hst]; posn hm.1 hm.2.1
  obtain ⟨e1, e2⟩ := cnt_done (t := t) hm' hc
  rw [e1, e2]
  rcases hi with rfl | rfl <;>
  · exact rank_body (by simp) (by rw [← e1]; exact hN) ⟨Nat.le_refl _, .inr ⟨rfl, rfl⟩⟩ (by omega)

/-- The `CASAL`s (positions `6` and `14`), given their cell. -/
theorem stepCas {i : Nat} (hi : i = 6 ∨ i = 14) (hpc : u.st.st.2 = pcS W σ i)
    (hI : u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec) {k : RmwKind} {nv : BitVec 128}
    (hex : isa.exec u.st = some (.rmw k false ⟨t, 8⟩
      (fun old => if BitVec.setWidth 64 old = u.st.st.1.regs.X3.toBitVec then some nv else none)
      fun v => .done (goto u.st { u.st.st.1 with regs := u.st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 v) }
        (pcS W σ (i + 1))))) :
    StepOK W σ data t N u mem o := by
  have hm : i ∈ pcsD data ∧ i + 1 ∈ pcsD data := by rcases hi with rfl | rfl <;> exact ⟨memC, memC⟩
  obtain ⟨tr, old, hst, -, -, hcase⟩ := SpinSemShape.spec_rmwo_p _ _ rfl hex hs ho
  have hpk : o.thread.st.st.2 = pcS W σ (i + 1) := by rw [hst]
  have hx2 : o.thread.st.st.1.regs.X2 = u.st.st.1.regs.X2 := by rw [hst]; simp
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨i + 1, hm.2, hpk, by rcases hi with rfl | rfl <;> trivial⟩,
    ?_, fun hf hb hN => ?_⟩
  · rcases hcase with ⟨-, hm', hp, -⟩ | ⟨new, hop, h⟩
    · refine .inl ⟨hm', hp, ?_⟩
      rw [S, S, hpc, hpk]; posn hm.1 hm.2
      rcases hi with rfl | rfl <;> simp only [sOf] <;> split <;> omega
    · refine .inr ⟨_, WEff.of_rmw h, ?_⟩
      have hc : BitVec.setWidth 64 old = u.st.st.1.regs.X3.toBitVec := by
        by_cases hne : BitVec.setWidth 64 old = u.st.st.1.regs.X3.toBitVec
        · exact hne
        · simp [hne] at hop
      have hx3 : o.thread.st.st.1.regs.X3.toBitVec = BitVec.setWidth 64 old := by rw [hst]; simp
      rw [S, S, hpc, hpk]; posn hm.1 hm.2
      rcases hi with rfl | rfl <;> simp [sOf, hx3, hx2, hc, hI]
  · obtain ⟨ts, v, hst', hr, h1, h2⟩ := rmw_window _ _ rfl hf hex hs ho
    have hw := window_rank (stepOne_dord _ hs ho).2.2.1 hb hr h1 h2
    have hc := cnt_step hs ho hb
    have hx3 : o.thread.st.st.1.regs.X3.toBitVec = BitVec.setWidth 64 v := by rw [hst']; simp
    rw [R, R, hpc, hpk]; posn hm.1 hm.2
    generalize mem.cntBelow (topL t) (u.views.getCoh (topL t)) = c0 at *
    generalize o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) = c1 at *
    generalize mem.curBelow (topL t) (u.views.getCoh (topL t)) = u0 at *
    rcases hi with rfl | rfl <;>
    · simp only [rk, fl, hx3, hx2]
      split
      · omega
      · rename_i hne
        split
        · rename_i he
          have := hw.1 fun e => hne (by rw [e, he])
          omega
        · omega

/-- The `CMP X3,X2`s (positions `7` and `15`). -/
theorem stepCmp {i : Nat} (hi : i = 7 ∨ i = 15) (hpc : u.st.st.2 = pcS W σ i) : StepOK W σ data t N u mem o := by
  have hm : i ∈ pcsD data ∧ i + 1 ∈ pcsD data ∧ i ≠ 21 := by
    rcases hi with rfl | rfl <;> exact ⟨memC, memC, by decide⟩
  obtain ⟨fs, hex, hz⟩ := C.cmp i hi _ (hS.at C hm.1 hm.2.2 hpc)
  obtain ⟨hm', hst, hp, hc⟩ := spec_done _ _ hex hs ho
  have hpk : o.thread.st.st.2 = pcS W σ (i + 1) := by rw [hst]
  have hz' : o.thread.st.st.1.status.z = true ↔ u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec := by
    rw [hst]; exact hz
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨i + 1, hm.2.1, hpk, by rcases hi with rfl | rfl <;> trivial⟩,
    .inl ⟨hm', hp, ?_⟩, fun hf hb hN => ?_⟩
  · rw [S, S, hpc, hpk]; posn hm.1 hm.2.1
    by_cases e : u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec
    · rcases hi with rfl | rfl <;> simp [sOf, e, hz'.mpr e]
    · have : ¬ o.thread.st.st.1.status.z = true := fun h => e (hz'.mp h)
      rcases hi with rfl | rfl <;> simp [sOf, e, this]
  · obtain ⟨e1, e2⟩ := cnt_done (t := t) hm' hc
    rw [R, R, hpc, hpk]; posn hm.1 hm.2.1
    rw [e1, e2]
    by_cases e : u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec
    · rcases hi with rfl | rfl <;> (simp only [rk, e, hz'.mpr e, ↓reduceIte]; omega)
    · have : ¬ o.thread.st.st.1.status.z = true := fun h => e (hz'.mp h)
      rcases hi with rfl | rfl <;> (simp only [rk, e, this, Bool.false_eq_true, ↓reduceIte]; omega)

theorem step8 (hpc : u.st.st.2 = pcS W σ 8) : StepOK W σ data t N u mem o := by
  obtain ⟨hm, hst, hp, hc⟩ := spec_done _ _ (C.bne8 _ (hS.at C memC (by decide) hpc)) hs ho
  have hSt : Static W σ data t o.thread.st := by rw [hst]; exact hS.goto _ _ rfl rfl rfl
  obtain ⟨e1, e2⟩ := cnt_done (t := t) hm hc
  by_cases hz : u.st.st.1.status.z = true
  · simp only [hz, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcS W σ 10 := by rw [hst]
    refine ⟨hSt, ⟨10, memC, hpk, trivial⟩, .inl ⟨hm, hp, ?_⟩, fun hf hb hN => ?_⟩
    · rw [S, S, hpc, hpk]; posn (memC (i := 8)) (memC (i := 10)); simp [sOf, hz]
    · rw [R, R, hpc, hpk]; posn (memC (i := 8)) (memC (i := 10))
      rw [e1]; simp only [rk, hz, ↓reduceIte]; omega
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcS W σ 3 := by rw [hst]
    refine ⟨hSt, ⟨3, memC, hpk, trivial⟩, .inl ⟨hm, hp, ?_⟩, fun hf hb hN => ?_⟩
    · rw [S, S, hpc, hpk]; posn (memC (i := 8)) (memC (i := 3)); simp [sOf, hz]
    · rw [R, R, hpc, hpk]; posn (memC (i := 8)) (memC (i := 3))
      rw [e1]; simp only [rk, hz, Bool.false_eq_true, ↓reduceIte]; omega

theorem step11 (hpc : u.st.st.2 = pcS W σ 11) : StepOK W σ data t N u mem o := by
  obtain ⟨hm, hst, hp, hc⟩ := spec_done _ _ (C.cbz11 _ (hS.at C memC (by decide) hpc)) hs ho
  have hSt : Static W σ data t o.thread.st := by rw [hst]; exact hS.goto _ _ rfl rfl rfl
  obtain ⟨e1, e2⟩ := cnt_done (t := t) hm hc
  by_cases hz : u.st.st.1.regs.X2.toBitVec = 0#64
  · simp only [hz, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcS W σ 21 := by rw [hst]
    refine ⟨hSt, ⟨21, memC, hpk, trivial⟩, .inl ⟨hm, hp, ?_⟩, fun hf hb hN => ?_⟩
    · rw [S, S, hpc, hpk]; posn (memC (i := 11)) (memC (i := 21)); simp [sOf]
    · rw [R, R, hpc, hpk]; posn (memC (i := 11)) (memC (i := 21))
      simp only [rk]; omega
  · simp only [hz, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcS W σ 12 := by rw [hst]
    refine ⟨hSt, ⟨12, memC, hpk, trivial⟩, .inl ⟨hm, hp, ?_⟩, fun hf hb hN => ?_⟩
    · rw [S, S, hpc, hpk]; posn (memC (i := 11)) (memC (i := 12)); simp [sOf]
    · rw [R, R, hpc, hpk]; posn (memC (i := 11)) (memC (i := 12))
      rw [e1, e2, hst]; simp only [rk]; omega

theorem step12 (hpc : u.st.st.2 = pcS W σ 12) : StepOK W σ data t N u mem o := by
  have hex := C.ldr12 _ (hS.at C memC (by decide) hpc) rfl (hS.d8 _)
  obtain ⟨ts, v, hst, -, -, hm, hp, -⟩ := spec_load _ _ hex hs ho
  have hpk : o.thread.st.st.2 = pcS W σ 13 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨13, memC, hpk, trivial⟩, .inl ⟨hm, hp, ?_⟩,
    fun hf hb hN => ?_⟩
  · rw [S, S, hpc, hpk]; posn (memC (i := 12)) (memC (i := 13)); simp [sOf]
  · rw [R, R, hpc, hst]; posn (memC (i := 12)) (memC (i := 13))
    exact rank_body (by simp) hN (cnt_step hs ho hb) (by omega)

theorem step16 (hpc : u.st.st.2 = pcS W σ 16) : StepOK W σ data t N u mem o := by
  obtain ⟨hm, hst, hp, hc⟩ := spec_done _ _ (C.bne16 _ (hS.at C memC (by decide) hpc)) hs ho
  have hSt : Static W σ data t o.thread.st := by rw [hst]; exact hS.goto _ _ rfl rfl rfl
  obtain ⟨e1, e2⟩ := cnt_done (t := t) hm hc
  by_cases hz : u.st.st.1.status.z = true
  · simp only [hz, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcS W σ 17 := by rw [hst]
    refine ⟨hSt, ⟨17, memC, hpk, trivial⟩, .inl ⟨hm, hp, ?_⟩, fun hf hb hN => ?_⟩
    · rw [S, S, hpc, hpk]; posn (memC (i := 16)) (memC (i := 17)); simp [sOf, hz]
    · rw [R, R, hpc, hpk]; posn (memC (i := 16)) (memC (i := 17))
      simp only [rk, hz, ↓reduceIte]; omega
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcS W σ 10 := by rw [hst]
    refine ⟨hSt, ⟨10, memC, hpk, trivial⟩, .inl ⟨hm, hp, ?_⟩, fun hf hb hN => ?_⟩
    · rw [S, S, hpc, hpk]; posn (memC (i := 16)) (memC (i := 10)); simp [sOf, hz]
    · rw [R, R, hpc, hpk]; posn (memC (i := 16)) (memC (i := 10))
      rw [e1]; simp only [rk, hz, Bool.false_eq_true, ↓reduceIte]; omega

/-- `MOV X10,X2` (position `17`), to the data load (`18`) or to `B done`
(`19`). -/
theorem step17 (hpc : u.st.st.2 = pcS W σ 17) : StepOK W σ data t N u mem o := by
  obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (C.mov17 _ (hS.at C memC (by decide) hpc)) hs ho
  have hj : (if data then 18 else 19) ∈ pcsD data := by cases data <;> decide
  have hpk : o.thread.st.st.2 = pcS W σ (if data then 18 else 19) := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨_, hj, hpk, by cases data <;> trivial⟩,
    .inl ⟨hm, hp, by rw [S, S, hpc, hpk]; posn (memC (i := 17)) hj; cases data <;> simp [sOf]⟩,
    fun _ _ _ => ?_⟩
  rw [R, R, hpc, hpk]; posn (memC (i := 17)) hj
  cases data <;> (simp only [Bool.false_eq_true, ↓reduceIte, rk]; omega)

theorem step18 (hd : data = true) (hpc : u.st.st.2 = pcS W σ 18) : StepOK W σ data t N u mem o := by
  have h18 : 18 ∈ pcsD data := by rw [hd]; decide
  obtain ⟨ts, v, hst, -, -, hm, hp, -⟩ :=
    spec_load _ _ (C.ldr18 hd _ (hS.at C h18 (by decide) hpc) rfl (hS.d4 hd _)) hs ho
  have hpk : o.thread.st.st.2 = pcS W σ 19 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨19, memC, hpk, trivial⟩,
    .inl ⟨hm, hp, by rw [S, S, hpc, hpk]; posn h18 (memC (i := 19)); simp [sOf]⟩,
    fun _ _ _ => ?_⟩
  rw [R, R, hpc, hpk]; posn h18 (memC (i := 19)); simp only [rk]; omega

theorem step19 (hpc : u.st.st.2 = pcS W σ 19) : StepOK W σ data t N u mem o := by
  obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (C.b19 _ (hS.at C memC (by decide) hpc)) hs ho
  have hpk : o.thread.st.st.2 = pcS W σ 21 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl, ⟨21, memC, hpk, trivial⟩,
    .inl ⟨hm, hp, by rw [S, S, hpc, hpk]; posn (memC (i := 19)) (memC (i := 21)); simp [sOf]⟩,
    fun _ _ _ => ?_⟩
  rw [R, R, hpc, hpk]; posn (memC (i := 19)) (memC (i := 21)); simp only [rk]; omega

/-- **One instruction step of a worker**, by position. -/
theorem thread_step (hpc : PcOK W σ data u.st) : StepOK W σ data t N u mem o := by
  obtain ⟨i, hi, hpc, hI⟩ := hpc
  have hd1 : i = 1 → data = true := fun h => by
    subst h; cases data
    · exact absurd hi (by decide)
    · rfl
  have hd18 : i = 18 → data = true := fun h => by
    subst h; cases data
    · exact absurd hi (by decide)
    · rfl
  have hi' : i = 1 ∨ i = 18 ∨ i ∈ cPcs := by
    unfold pcsD at hi
    rcases List.mem_append.mp hi with h | h
    · split at h <;> simp_all
    · exact .inr (.inr h)
  rcases hi' with rfl | rfl | hi'
  · exact step1 C hS hs ho (hd1 rfl) hpc
  · exact step18 C hS hs ho (hd18 rfl) hpc
  simp only [cPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stepLd C hS hs ho (.inl rfl) hpc
  · exact step4 C hS hs ho hpc
  · exact stepMov C hS hs ho (.inl rfl) hpc
  · obtain ⟨k, hex⟩ := C.casal6 _ (hS.at C memC (by decide) hpc) hS.x0 (hS.d8 _)
    exact stepCas C hS hs ho (.inl rfl) hpc hI hex
  · exact stepCmp C hS hs ho (.inl rfl) hpc
  · exact step8 C hS hs ho hpc
  · exact stepLd C hS hs ho (.inr rfl) hpc
  · exact step11 C hS hs ho hpc
  · exact step12 C hS hs ho hpc
  · exact stepMov C hS hs ho (.inr rfl) hpc
  · obtain ⟨k, hex⟩ := C.casal14 _ (hS.at C memC (by decide) hpc) hS.x0 (hS.d8 _)
    exact stepCas C hS hs ho (.inr rfl) hpc hI hex
  · exact stepCmp C hS hs ho (.inr rfl) hpc
  · exact step16 C hS hs ho hpc
  · exact step17 C hS hs ho hpc
  · exact step19 C hS hs ho hpc
  · rw [stepOne_end hS hpc] at hs; cases hs

end Steps

section Inv

variable {W : Program} {σ : Nat → Nat} {data : Bool} (C : Cells W σ data)
include C

/-- **Every instruction of a worker drops at most one promise**, on any run of
the worker alone. -/
theorem dropBounded {t : BitVec 64} {u : Thread isa} {tid : Nat} (hS : Static W σ data t u.st)
    (hP : PcOK W σ data u.st) : DropBounded Arch.armv8 1 tid u :=
  dropBounded_of_stateInv (fun s => Static W σ data t s ∧ PcOK W σ data s) (fun h hs ho => by
    have r := thread_step (N := 0) C h.1 hs ho h.2
    refine ⟨⟨r.st, r.pc⟩, ?_⟩
    rcases r.eff with ⟨-, hp, -⟩ | ⟨w, hw, -⟩
    · rw [hp]; omega
    · exact hw.len) ⟨hS, hP⟩

omit C

/-- **The per-thread invariant** (`TermTreiber2.TI` at `σ`). -/
structure TI (W : Program) (σ : Nat → Nat) (data : Bool) (fuel : Nat) (t : BitVec 64) (u : Thread isa)
    (mem : Memory) : Prop where
  st : Static W σ data t u.st
  pc : PcOK W σ data u.st
  fwd : Witness.FwdLeCoh u.views
  promLe : ∀ ts ∈ u.prom, ts ≤ mem.last
  plen : u.prom.length ≤ fuel

theorem TI.mono {fuel : Nat} {t : BitVec 64} {u : Thread isa} {mem mem' : Memory} (h : TI W σ data fuel t u mem)
    (hp : mem.Prefix mem') : TI W σ data fuel t u mem' :=
  ⟨h.st, h.pc, h.fwd, fun ts hts => Nat.le_trans (h.promLe ts hts) hp.last_le, h.plen⟩

/-- **The invariant** (`TermTreiber2.Inv` at `σ`). -/
structure Inv (W : Program) (σ : Nat → Nat) (data : Bool) (fuel n : Nat) (t : BitVec 64) (c : Config isa) :
    Prop where
  bnd : c.Bnd
  size : c.threads.size = n
  thr : ∀ (i : Nat) (u : Thread isa), c.threads[i]? = some u → TI W σ data fuel t u c.mem
  cnt : c.mem.cntBelow (topL t) c.mem.last ≤ tsum c fun _ u => S W σ data u + c.mem.promAt (topL t) u.prom

/-- **`cnt` is at most `N = n * (2 + fuel)`.** -/
theorem Inv.cnt_le {fuel n : Nat} {t : BitVec 64} {c : Config isa} (h : Inv W σ data fuel n t c) (b : Nat) :
    c.mem.cntBelow (topL t) b ≤ cntBound n fuel := by
  have h1 := cntBelow_le_last c.mem (topL t) b
  have h2 := tsum_le (c := c) (F := fun _ u => S W σ data u + c.mem.promAt (topL t) u.prom) (M := 2 + fuel)
    fun j v hv => by
      have := sOf_le (posOf W σ data v.st.st.2) v.st.st.1
      have := (promAt_le_length (m := c.mem) (l := topL t) (p := v.prom))
      have := (h.thr j v hv).plen
      simp only [S]; omega
  rw [h.size] at h2
  unfold cntBound
  have := h.cnt
  omega

variable {fuel n : Nat} {t : BitVec 64} {c : Config isa} {tid : Nat} {u : Thread isa}

/-- The invariant after a step of `tid`. -/
theorem Inv.build (h : Inv W σ data fuel n t c) (ht : c.threads[tid]? = some u) {u' : Thread isa}
    {mem' : Memory} (hpre : c.mem.Prefix mem') (hb : (c.withThread tid u' mem').Bnd)
    (hT : TI W σ data fuel t u' mem')
    (hcnt : mem'.cntBelow (topL t) mem'.last + (S W σ data u + c.mem.promAt (topL t) u.prom) ≤
      c.mem.cntBelow (topL t) c.mem.last + (S W σ data u' + mem'.promAt (topL t) u'.prom)) :
    Inv W σ data fuel n t (c.withThread tid u' mem') := by
  refine ⟨hb, by rw [withThread_size]; exact h.size, fun i v hv => ?_, ?_⟩
  · rcases SpinStep.wt_get ht hv with ⟨-, rfl⟩ | ⟨-, hv⟩
    · exact hT
    · exact (h.thr i v hv).mono hpre
  · have e := tsum_withThread_add (t' := u') (mem' := mem')
      (F := fun (_ : Nat) (v : Thread isa) => S W σ data v + c.mem.promAt (topL t) v.prom)
      (F' := fun (_ : Nat) (v : Thread isa) => S W σ data v + mem'.promAt (topL t) v.prom) ht fun i v _ hv => by
        simp only [promAt_prefix hpre (h.thr i v hv).promLe]
    have := h.cnt
    show mem'.cntBelow (topL t) mem'.last ≤
      tsum (c.withThread tid u' mem') fun _ v => S W σ data v + mem'.promAt (topL t) v.prom
    omega

include C in
/-- **A semantic step keeps the invariant.** -/
theorem Inv.step (h : Inv W σ data fuel n t c) (ht : c.threads[tid]? = some u) {c' : Config isa}
    (hst : StepSem Arch.armv8 fuel tid c c') : Inv W σ data fuel n t c' := by
  have hb := h.bnd.semStep hst
  have hT := h.thr tid u ht
  rcases hst with ⟨t1, outs, o, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, -, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    have r := thread_step (N := 0) C hT.st hs ho hT.pc
    have hpre : c.mem.Prefix o.mem := (stepOne_dord _ hs ho).2.2.1
    have hplen : o.thread.prom.length ≤ fuel := by
      have := prom_le_of_certOkN (dropBounded C r.st r.pc) hc; omega
    rcases r.eff with ⟨hm, hp, hS⟩ | ⟨w, hw, hS⟩
    · refine h.build ht hpre hb ⟨r.st, r.pc, Witness.stepOne_fwdLeCoh hs ho hT.fwd,
        by rw [hp, hm]; exact hT.promLe, hplen⟩ ?_
      rw [hm, hp]; omega
    · obtain ⟨e, hle⟩ := count_weff (l := topL t) hT.promLe hw
      refine h.build ht hpre hb ⟨r.st, r.pc, Witness.stepOne_fwdLeCoh hs ho hT.fwd, hle, hplen⟩ ?_
      by_cases hl : w.loc = topL t <;> simp only [hl, ↓reduceIte] at hS e <;> omega
  · rw [ht] at ht1; cases ht1
    have hpre : c.mem.Prefix (c.mem.append w).1 := Memory.Prefix.append _ _
    have hplen : (promThread u c.mem w).prom.length ≤ fuel := by
      have := prom_le_of_certOkN (dropBounded C (u := promThread u c.mem w) (tid := tid) hT.st hT.pc) hc
      omega
    have hlast : (c.mem.append w).1.last = c.mem.last + 1 := by simp [Memory.append, Memory.last]
    refine h.build ht hpre hb ⟨hT.st, hT.pc, hT.fwd, fun ts hts => ?_, hplen⟩ ?_
    · rw [hlast]
      rcases List.mem_append.mp hts with hts | hts
      · exact Nat.le_succ_of_le (hT.promLe ts hts)
      · rw [List.mem_singleton] at hts; rw [hts]; exact Nat.le_refl _
    · show _ + (S W σ data u + _) ≤
        _ + (S W σ data u + (c.mem.append w).1.promAt (topL t) (u.prom ++ [(c.mem.append w).2]))
      rw [cntBelow_append, promAt_promise w hT.promLe]
      omega

end Inv

/-! ## Termination -/

/-- The start position: the data store if there is one, else `push`. -/
abbrev startPos (data : Bool) : Nat := if data then 1 else 3

/-- **Termination of `treiber2`-shaped workers on the semantic machine, under
every schedule** (no fairness): for a worker `W` with the cells of
`treiber2DWorker` at positions `σ` (`Cells`), any number of threads running
`W`, sharing `top = t`, each at its start position with `Static` (its node's
link word not `top`, empty private memory, no declarations). At every fuel,
one bound `K` (depending on `fuel` and on the number of threads) on every
semantic trace. -/
theorem term_sem_genP {W : Program} {σ : Nat → Nat} {data : Bool} (C : Cells W σ data) {fuel : Nat}
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, Static W σ data t s ∧ s.st.2 = pcS W σ (startPos data)) :
    TermBoundSem Arch.armv8 fuel (Config.init states initMem : Config isa) := by
  let n := (Config.init states initMem : Config isa).threads.size
  have hinit : Inv W σ data fuel n t (Config.init states initMem) := by
    refine ⟨Config.init_bnd _ _, rfl, fun i u hu => ?_, ?_⟩
    · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
      obtain ⟨s, hm, rfl⟩ := hu
      obtain ⟨hS, hpc⟩ := hs s (List.mem_of_getElem? hm)
      exact ⟨hS, ⟨_, by cases data <;> decide, hpc, by cases data <;> trivial⟩, Witness.fwdLeCoh_of_nil rfl,
        fun ts h => by simp [Thread.init] at h, by simp [Thread.init]⟩
    · have : (Config.init states initMem : Config isa).mem.last = 0 := rfl
      rw [this]
      exact Nat.zero_le _
  refine termBoundSem_of_threadRank (B := 1) (Inv W σ data fuel n t) (R W σ data (cntBound n fuel) t) hinit
    (fun c c' tid h hst => ?_) (fun c h i u hu => ?_) (fun c h i u hu => ?_) (fun c h i u hu mem' hp => ?_)
    (fun _ _ _ => rfl) (fun c tid u outs o h hu hso ho h' => ?_)
  · obtain ⟨u, hu⟩ : ∃ u, c.threads[tid]? = some u := by
      rcases hst with ⟨u, -, -, hu, -⟩ | ⟨u, -, hu, -⟩ <;> exact ⟨u, hu⟩
    exact h.step C hu hst
  · rw [Nat.mul_one]; exact (h.thr i u hu).plen
  · exact dropBounded C (h.thr i u hu).st (h.thr i u hu).pc
  · have hb := (h.bnd i u hu).views.le.coh (topL t)
    unfold R
    rw [cntBelow_prefix hp hb, curBelow_prefix hp hb]
  · have hT := h.thr tid u hu
    exact (thread_step C hT.st hso ho hT.pc).rank hT.fwd ((h.bnd tid u hu).views.le.coh (topL t))
      (h'.cnt_le _)

end Kraken.Promising.Live.TermTreiber2P
