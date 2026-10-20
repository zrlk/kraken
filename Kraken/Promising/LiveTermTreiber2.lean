/-
**Stage 4: termination of the `treiber2.kl` workers on
the semantic machine, under every schedule** (`TermBoundSem`, no fairness),
any number of workers `treiber2DWorker` sharing `top` on a valid layout
(`LiveTermTreiber2Trees.lean` for the cells).

## The rank

`termBoundSem_of_threadRank` (`LiveTerm.lean`) with, per thread, a rank `R`
of its position, registers, and `cnt`/`cur`: the number of writes to `top`
at or below its coherence view of `top` and the value of the last one
(`Memory.cntBelow`, `Memory.curBelow`). With `V = 10 * (N - cnt)`:

- the push phase (positions 1–8 on a failed `CASAL`) lies above the pop
  phase (positions 7/8 after a successful `CASAL`, then 10–16 on a failed
  one), which lies above the exit (positions 15–21 after a successful pop or
  an empty stack);
- inside a retry loop the rank is `V` plus a position offset, plus `10` while
  `X2` (the value read at the top of the iteration) is not the current value
  `cur` (`fl`). A failed `CASAL` with `X2 = cur` read a value other than
  `cur`, so `cnt` strictly grew (`window_rank`); with `X2 ≠ cur` the flag pays.
  Every other step keeps `cnt` and `cur`, or grows `cnt` (`step_cnt`).

## The bound `N` on `cnt`

`cnt ≤ #(writes to top) ≤ Σ_threads (sOf + promAt)` (the invariant `Inv`,
field `cnt`): `sOf` counts the successful `CASAL`s a thread has executed
(at most `2`, read off its position and registers), `promAt` its outstanding
promises to `top` (at most `fuel`, by certification). A successful `CASAL`
appends (one more write) or fulfils (one promise fewer), and raises `sOf`; a
promise to `top` adds a write and a promise (`count_weff`). So
`N = size * (2 + fuel)`.

Promises are bounded by certification only (`prom_le_of_certOkN`, every
instruction drops at most one promise): the bound `K` depends on `fuel` and
on the number of threads.
The step lemmas, the invariant's preservation and the theorem
are instances of the position-parametric `LiveTermTreiber2P.lean` at
`σ = id` (`cells`: the cells of `LiveTermTreiber2Trees.lean`), through
`posOf_eq` and the `toP`/`ofP` conversions; every statement here is
unchanged. The rank table (`rk`, `sOf`, `fl`, `PcI`, `topL`, `cntBound`,
`isInstr`) is in `LiveTermTreiber2Rank.lean`.
-/
import Kraken.Promising.LiveTermTreiber2P
import Kraken.Promising.LiveTermTreiber2Trees
import Kraken.Promising.SLR.EnvG.Treiber2DataRelPure

namespace Kraken.Promising.Live.TermTreiber2

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Term Kraken.Promising.Live.TermTreiber2Trees
open Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker StartWD)
open Kraken.Promising.SLR.A64Trees (At goto)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiber2DWorker)]

set_option hygiene false in
local notation "pcT" => (layout treiber2DWorker).addrOf

/-! ## Positions -/

/-- The positions a worker's pc takes (each label at the address of the next
instruction; `21` is the end of the text). -/
def tPcs : List Nat := [1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21]

/-- The address-distinct representative of a position: the label before it. -/
def canon (i : Nat) : Nat :=
  if i = 3 then 2 else if i = 10 then 9 else if i = 21 then 20 else i

theorem addrOf_canon (i : Nat) : pcT (canon i) = pcT i := by
  unfold canon
  split
  · subst_vars; exact addrOf_2
  split
  · subst_vars; exact addrOf_9
  split
  · subst_vars; exact addrOf_20
  rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ tPcs) (hj : j ∈ tPcs) (h : pcT i = pcT j) : i = j :=
  SLR.A64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) tPcs canon (fun i _ => addrOf_canon i) (by decide) hi hj h

/-- The position of an address (`0` off the positions). -/
def posOf (pc : Int64) : Nat := (tPcs.find? fun i => decide (pcT i = pc)).getD 0

theorem posOf_pcT {i : Nat} (hi : i ∈ tPcs) : posOf (pcT i) = i := by
  unfold posOf
  cases h : tPcs.find? (fun j => decide (pcT j = pcT i)) with
  | none => exact absurd (by simpa using List.find?_eq_none.mp h i hi) (fun h' : ¬ pcT i = pcT i => h' rfl)
  | some j =>
    have := List.find?_some h
    simp only [decide_eq_true_eq] at this
    exact addrOf_inj (List.mem_of_find?_eq_some h) hi this

/-! ## The instance of `LiveTermTreiber2P.lean` -/

/-- The positions are those of `TermTreiber2P` with the data cells. -/
theorem mem_pcsD {i : Nat} : i ∈ tPcs ↔ i ∈ TermTreiber2P.pcsD true := by
  simp only [tPcs, TermTreiber2P.pcsD, TermTreiber2P.cPcs, ↓reduceIte, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **The cells of `treiber2DWorker`** (`LiveTermTreiber2Trees.lean`) as
`TermTreiber2P.Cells` at `σ = id`, with the data cells. -/
theorem cells : TermTreiber2P.Cells treiber2DWorker id true where
  inj hi hj h := addrOf_inj (mem_pcsD.mpr hi) (mem_pcsD.mpr hj) h
  str_d _ := exec_str_d
  ldar i hi st h := by
    rcases hi with rfl | rfl
    · exact exec_ldar3 st h
    · exact exec_ldar10 st h
  str_n := exec_str_n
  mov i hi st h := by
    rcases hi with rfl | rfl
    · exact exec_mov5 st h
    · exact exec_mov13 st h
  casal6 := exec_casal6
  cmp i hi st h := by
    rcases hi with rfl | rfl
    · exact exec_cmp7 st h
    · exact exec_cmp15 st h
  bne8 := exec_bne8
  cbz11 := exec_cbz11
  ldr12 := exec_ldr12
  casal14 := exec_casal14
  bne16 := exec_bne16
  mov17 := exec_mov17
  ldr18 _ := exec_ldr18
  b19 := exec_b19

/-- `posOf` is `TermTreiber2P.posOf` at `σ = id`. -/
theorem posOf_eq (pc : Int64) : posOf pc = TermTreiber2P.posOf treiber2DWorker id true pc := by
  by_cases h : ∃ i ∈ tPcs, pcT i = pc
  · obtain ⟨i, hi, rfl⟩ := h
    rw [posOf_pcT hi]
    exact (TermTreiber2P.posOf_pcS cells (mem_pcsD.mp hi)).symm
  · have e1 : tPcs.find? (fun i => decide (pcT i = pc)) = none :=
      List.find?_eq_none.mpr fun i hi e => h ⟨i, hi, of_decide_eq_true e⟩
    have e2 : (TermTreiber2P.pcsD true).find? (fun i => decide (TermTreiber2P.pcS treiber2DWorker id i = pc)) =
        none :=
      List.find?_eq_none.mpr fun i hi e => h ⟨i, mem_pcsD.mpr hi, of_decide_eq_true e⟩
    unfold posOf TermTreiber2P.posOf
    rw [e1, e2]

/-! ## The per-thread state invariant -/

/-- What a worker state never changes: its program, end address, `X0 = top`,
`X1` (its node, whose link word is not `top`) and the empty private memory. -/
structure Static (t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiber2DWorker
  decls : s.decls = {}
  endPc : s.endPc = pcT 21
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec + 8#64 ≠ t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

omit hv in
theorem Static.toP {t : BitVec 64} {s : isa.State} (h : Static t s) :
    TermTreiber2P.Static treiber2DWorker id true t s :=
  ⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.d8, fun _ => h.d4⟩

omit hv in
theorem Static.ofP {t : BitVec 64} {s : isa.State} (h : TermTreiber2P.Static treiber2DWorker id true t s) :
    Static t s :=
  ⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.d8, h.d4 rfl⟩

omit hv in
theorem Static.goto {t : BitVec 64} {s : isa.State} (h : Static t s) (md : MachineData) (pc : Int64)
    (h0 : md.regs.X0 = s.st.1.regs.X0) (h1 : md.regs.X1 = s.st.1.regs.X1) (hd : md.dmem = s.st.1.dmem) :
    Static t (goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, h0 ▸ h.x0, h1 ▸ h.x1, hd ▸ h.d8, hd ▸ h.d4⟩

theorem Static.at {t : BitVec 64} {s : isa.State} (h : Static t s) {i : Nat} (hi : i ∈ tPcs)
    (h21 : i ≠ 21) (hpc : s.st.2 = pcT i) : At treiber2DWorker s i :=
  h.toP.at cells (mem_pcsD.mp hi) h21 hpc

omit hv in
/-- At the end address the worker has halted. -/
theorem stepOne_end {t : BitVec 64} {u : Thread isa} (h : Static t u.st) (hpc : u.st.st.2 = pcT 21)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A u tid mem = none :=
  TermTreiber2P.stepOne_end h.toP hpc A tid mem

/-- The worker sits at a position, with its register fact. -/
def PcOK (s : isa.State) : Prop := ∃ i ∈ tPcs, s.st.2 = pcT i ∧ PcI s.st.1 i

theorem PcOK.toP {s : isa.State} (h : PcOK s) : TermTreiber2P.PcOK treiber2DWorker id true s :=
  let ⟨i, hi, hpc, hI⟩ := h
  ⟨i, mem_pcsD.mp hi, hpc, hI⟩

theorem PcOK.ofP {s : isa.State} (h : TermTreiber2P.PcOK treiber2DWorker id true s) : PcOK s :=
  let ⟨i, hi, hpc, hI⟩ := h
  ⟨i, mem_pcsD.mpr hi, hpc, hI⟩

/-! ## The rank and the successful-write count -/

theorem sOf_le (p : Nat) (s : MachineData) : sOf p s ≤ 2 := TermTreiber2P.sOf_le p s

/-- A thread's rank in memory `mem`. -/
def R (N : Nat) (t : BitVec 64) (u : Thread isa) (mem : Memory) : Nat :=
  rk N (posOf u.st.st.2) u.st.st.1 (mem.cntBelow (topL t) (u.views.getCoh (topL t)))
    (mem.curBelow (topL t) (u.views.getCoh (topL t)))

/-- A thread's successful `CASAL`s. -/
def S (u : Thread isa) : Nat := sOf (posOf u.st.st.2) u.st.st.1

theorem R_eq (N : Nat) (t : BitVec 64) (u : Thread isa) (mem : Memory) :
    R N t u mem = TermTreiber2P.R treiber2DWorker id true N t u mem := by
  unfold R TermTreiber2P.R
  rw [posOf_eq]
  all_goals (generalize TermTreiber2P.posOf treiber2DWorker id true u.st.st.2 = p; rfl)

theorem S_eq (u : Thread isa) : S u = TermTreiber2P.S treiber2DWorker id true u := by
  unfold S TermTreiber2P.S
  rw [posOf_eq]
  all_goals (generalize TermTreiber2P.posOf treiber2DWorker id true u.st.st.2 = p; rfl)

/-! ## One step of a worker -/

/-- **What one instruction step of a worker does**: it keeps `Static` and
`PcOK`; it changes neither memory nor promises (and does not lower `S`), or
performs one write (`WEff`), raising `S` if the write is to `top`; and, given
`FwdLeCoh`, `coh top ≤ |M|` and the bound `N` after the step, it lowers the
rank. -/
structure StepOK (t : BitVec 64) (N : Nat) (u : Thread isa) (mem : Memory) (o : Outcome isa) : Prop where
  st : Static t o.thread.st
  pc : PcOK o.thread.st
  eff : (o.mem = mem ∧ o.thread.prom = u.prom ∧ S u ≤ S o.thread) ∨
    (∃ w : Msg, WEff mem o.mem u.prom o.thread.prom w ∧ S u + (if w.loc = topL t then 1 else 0) ≤ S o.thread)
  rank : Witness.FwdLeCoh u.views → u.views.getCoh (topL t) ≤ mem.last →
    o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ≤ N → R N t o.thread o.mem < R N t u mem

theorem StepOK.ofP {t : BitVec 64} {N : Nat} {u : Thread isa} {mem : Memory} {o : Outcome isa}
    (h : TermTreiber2P.StepOK treiber2DWorker id true t N u mem o) : StepOK t N u mem o where
  st := Static.ofP h.st
  pc := PcOK.ofP h.pc
  eff := by simp only [S_eq]; exact h.eff
  rank hf hb hN := by rw [R_eq, R_eq]; exact h.rank hf hb hN

theorem fl_le (s : MachineData) (c : Val) : fl s c ≤ 10 := TermTreiber2P.fl_le s c

/-- The rank inside a loop body, across a step that keeps `X2`: `cnt` grows,
or `cnt`, `cur` and the flag stay. -/
theorem rank_body {N c0 c1 : Nat} {u0 u1 : Val} {s s' : MachineData} {a b : Nat} (hx : s'.regs.X2 = s.regs.X2)
    (hN : c1 ≤ N) (hc : c0 ≤ c1 ∧ (c0 < c1 ∨ (c0 = c1 ∧ u0 = u1))) (hab : a < b) :
    a + 10 * (N - c1) + fl s' u1 < b + 10 * (N - c0) + fl s u0 :=
  TermTreiber2P.rank_body hx hN hc hab

section Steps

variable {t : BitVec 64} {N : Nat} {u : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {o : Outcome isa}
  (hS : Static t u.st) (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok o ∈ outs)

include hS hs ho

/-- The count across the step (`step_cnt`). -/
theorem cnt_step (hb : u.views.getCoh (topL t) ≤ mem.last) :
    mem.cntBelow (topL t) (u.views.getCoh (topL t)) ≤ o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ∧
      (mem.cntBelow (topL t) (u.views.getCoh (topL t)) < o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ∨
       (mem.cntBelow (topL t) (u.views.getCoh (topL t)) = o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) ∧
        mem.curBelow (topL t) (u.views.getCoh (topL t)) = o.mem.curBelow (topL t) (o.thread.views.getCoh (topL t)))) :=
  TermTreiber2P.cnt_step hs ho hb

theorem step1 (hpc : u.st.st.2 = pcT 1) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step1 cells hS.toP hs ho rfl hpc)

omit hS hs ho in
/-- A step that changes neither memory nor the coherence view keeps `cnt`
and `cur`. -/
theorem cnt_done (hm : o.mem = mem) (hc : o.thread.views.coh = u.views.coh) :
    o.mem.cntBelow (topL t) (o.thread.views.getCoh (topL t)) = mem.cntBelow (topL t) (u.views.getCoh (topL t)) ∧
      o.mem.curBelow (topL t) (o.thread.views.getCoh (topL t)) = mem.curBelow (topL t) (u.views.getCoh (topL t)) :=
  TermTreiber2P.cnt_done hm hc

theorem step3 (hpc : u.st.st.2 = pcT 3) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.stepLd cells hS.toP hs ho (.inl rfl) hpc)

theorem step4 (hpc : u.st.st.2 = pcT 4) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step4 cells hS.toP hs ho hpc)

theorem step5 (hpc : u.st.st.2 = pcT 5) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.stepMov cells hS.toP hs ho (.inl rfl) hpc)

theorem step6 (hpc : u.st.st.2 = pcT 6) (hI : u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec) :
    StepOK t N u mem o := by
  obtain ⟨k, hex⟩ := exec_casal6 _ (hS.at (by decide) (by decide) hpc) hS.x0 (hS.d8 _)
  exact StepOK.ofP (TermTreiber2P.stepCas cells hS.toP hs ho (.inl rfl) hpc hI hex)

theorem step7 (hpc : u.st.st.2 = pcT 7) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.stepCmp cells hS.toP hs ho (.inl rfl) hpc)

theorem step8 (hpc : u.st.st.2 = pcT 8) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step8 cells hS.toP hs ho hpc)

theorem step10 (hpc : u.st.st.2 = pcT 10) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.stepLd cells hS.toP hs ho (.inr rfl) hpc)

theorem step11 (hpc : u.st.st.2 = pcT 11) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step11 cells hS.toP hs ho hpc)

theorem step12 (hpc : u.st.st.2 = pcT 12) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step12 cells hS.toP hs ho hpc)

theorem step13 (hpc : u.st.st.2 = pcT 13) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.stepMov cells hS.toP hs ho (.inr rfl) hpc)

theorem step14 (hpc : u.st.st.2 = pcT 14) (hI : u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec) :
    StepOK t N u mem o := by
  obtain ⟨k, hex⟩ := exec_casal14 _ (hS.at (by decide) (by decide) hpc) hS.x0 (hS.d8 _)
  exact StepOK.ofP (TermTreiber2P.stepCas cells hS.toP hs ho (.inr rfl) hpc hI hex)

theorem step15 (hpc : u.st.st.2 = pcT 15) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.stepCmp cells hS.toP hs ho (.inr rfl) hpc)

theorem step16 (hpc : u.st.st.2 = pcT 16) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step16 cells hS.toP hs ho hpc)

theorem step17 (hpc : u.st.st.2 = pcT 17) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step17 cells hS.toP hs ho hpc)

theorem step18 (hpc : u.st.st.2 = pcT 18) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step18 cells hS.toP hs ho rfl hpc)

theorem step19 (hpc : u.st.st.2 = pcT 19) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.step19 cells hS.toP hs ho hpc)

/-- **One instruction step of a worker**, by position. -/
theorem thread_step (hpc : PcOK u.st) : StepOK t N u mem o :=
  StepOK.ofP (TermTreiber2P.thread_step cells hS.toP hs ho hpc.toP)

end Steps

/-- **Every instruction of a worker drops at most one promise**, on any run of
the worker alone (`Static` and `PcOK` are kept). -/
theorem dropBounded {t : BitVec 64} {u : Thread isa} {tid : Nat} (hS : Static t u.st) (hP : PcOK u.st) :
    DropBounded Arch.armv8 1 tid u :=
  TermTreiber2P.dropBounded cells hS.toP hP.toP

/-! ## The invariant -/

/-- **The per-thread invariant**: `Static`, `PcOK`, forwarding below
coherence, promises in memory, and at most `fuel` of them. -/
structure TI (fuel : Nat) (t : BitVec 64) (u : Thread isa) (mem : Memory) : Prop where
  st : Static t u.st
  pc : PcOK u.st
  fwd : Witness.FwdLeCoh u.views
  promLe : ∀ ts ∈ u.prom, ts ≤ mem.last
  plen : u.prom.length ≤ fuel

theorem TI.mono {fuel : Nat} {t : BitVec 64} {u : Thread isa} {mem mem' : Memory} (h : TI fuel t u mem)
    (hp : mem.Prefix mem') : TI fuel t u mem' :=
  ⟨h.st, h.pc, h.fwd, fun ts hts => Nat.le_trans (h.promLe ts hts) hp.last_le, h.plen⟩

theorem TI.toP {fuel : Nat} {t : BitVec 64} {u : Thread isa} {mem : Memory} (h : TI fuel t u mem) :
    TermTreiber2P.TI treiber2DWorker id true fuel t u mem :=
  ⟨h.st.toP, h.pc.toP, h.fwd, h.promLe, h.plen⟩

theorem TI.ofP {fuel : Nat} {t : BitVec 64} {u : Thread isa} {mem : Memory}
    (h : TermTreiber2P.TI treiber2DWorker id true fuel t u mem) : TI fuel t u mem :=
  ⟨Static.ofP h.st, PcOK.ofP h.pc, h.fwd, h.promLe, h.plen⟩

/-- **The invariant**: bounded views, `n` threads, each satisfying `TI`, and
the writes to `top` bounded by the successful `CASAL`s and the outstanding
promises to `top`. -/
structure Inv (fuel n : Nat) (t : BitVec 64) (c : Config isa) : Prop where
  bnd : c.Bnd
  size : c.threads.size = n
  thr : ∀ (i : Nat) (u : Thread isa), c.threads[i]? = some u → TI fuel t u c.mem
  cnt : c.mem.cntBelow (topL t) c.mem.last ≤ tsum c fun _ u => S u + c.mem.promAt (topL t) u.prom

theorem Inv.toP {fuel n : Nat} {t : BitVec 64} {c : Config isa} (h : Inv fuel n t c) :
    TermTreiber2P.Inv treiber2DWorker id true fuel n t c :=
  ⟨h.bnd, h.size, fun i u hu => (h.thr i u hu).toP, by simpa only [S_eq] using h.cnt⟩

theorem Inv.ofP {fuel n : Nat} {t : BitVec 64} {c : Config isa}
    (h : TermTreiber2P.Inv treiber2DWorker id true fuel n t c) : Inv fuel n t c :=
  ⟨h.bnd, h.size, fun i u hu => TI.ofP (h.thr i u hu), by simpa only [S_eq] using h.cnt⟩

/-- **`cnt` is at most `N = n * (2 + fuel)`.** -/
theorem Inv.cnt_le {fuel n : Nat} {t : BitVec 64} {c : Config isa} (h : Inv fuel n t c) (b : Nat) :
    c.mem.cntBelow (topL t) b ≤ cntBound n fuel :=
  h.toP.cnt_le b

section Pres

variable {fuel n : Nat} {t : BitVec 64} {c : Config isa} {tid : Nat} {u : Thread isa}
  (h : Inv fuel n t c) (ht : c.threads[tid]? = some u)
include h ht

/-- The other threads' terms of the count invariant stay. -/
theorem others {mem' : Memory} (hpre : c.mem.Prefix mem') :
    ∀ (i : Nat) (v : Thread isa), i ≠ tid → c.threads[i]? = some v →
      (fun (_ : Nat) (v : Thread isa) => S v + mem'.promAt (topL t) v.prom) i v =
        (fun (_ : Nat) (v : Thread isa) => S v + c.mem.promAt (topL t) v.prom) i v := fun i v _ hv => by
  simp only [promAt_prefix hpre (h.thr i v hv).promLe]

/-- The invariant after a step of `tid`. -/
theorem build {u' : Thread isa} {mem' : Memory} (hpre : c.mem.Prefix mem') (hb : (c.withThread tid u' mem').Bnd)
    (hT : TI fuel t u' mem')
    (hcnt : mem'.cntBelow (topL t) mem'.last + (S u + c.mem.promAt (topL t) u.prom) ≤
      c.mem.cntBelow (topL t) c.mem.last + (S u' + mem'.promAt (topL t) u'.prom)) :
    Inv fuel n t (c.withThread tid u' mem') :=
  Inv.ofP (h.toP.build ht hpre hb hT.toP (by simpa only [S_eq] using hcnt))

/-- **A semantic step keeps the invariant.** -/
theorem inv_step {c' : Config isa} (hst : StepSem Arch.armv8 fuel tid c c') : Inv fuel n t c' :=
  Inv.ofP (h.toP.step cells ht hst)

set_option linter.unusedVariables false in
/-- **An instruction step keeps the invariant.** (`hb` is implied by the
step; `inv_step` does not need it.) -/
theorem inv_instr {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hs : stepOne Arch.armv8 u tid c.mem = some outs) (ho : .ok o ∈ outs)
    (hc : CertOkN Arch.armv8 tid o.thread o.mem fuel) (hb : (c.withThread tid o.thread o.mem).Bnd) :
    Inv fuel n t (c.withThread tid o.thread o.mem) :=
  inv_step h ht (.inl ⟨u, outs, o, ht, hs, ho, hc, rfl⟩)

/-- **A promise step keeps the invariant.** -/
theorem inv_prom {w : Msg} (hc : CertOkN Arch.armv8 tid (promThread u c.mem w) (c.mem.append w).1 fuel)
    (hb : (c.withThread tid (promThread u c.mem w) (c.mem.append w).1).Bnd) :
    Inv fuel n t (c.withThread tid (promThread u c.mem w) (c.mem.append w).1) := by
  have hT := h.thr tid u ht
  have hpre : c.mem.Prefix (c.mem.append w).1 := Memory.Prefix.append _ _
  have hplen : (promThread u c.mem w).prom.length ≤ fuel := by
    have := prom_le_of_certOkN (dropBounded (u := promThread u c.mem w) (tid := tid) hT.st hT.pc) hc; omega
  have hlast : (c.mem.append w).1.last = c.mem.last + 1 := by simp [Memory.append, Memory.last]
  refine build h ht hpre hb ⟨hT.st, hT.pc, hT.fwd, fun ts hts => ?_, hplen⟩ ?_
  · rw [hlast]
    rcases List.mem_append.mp hts with hts | hts
    · exact Nat.le_succ_of_le (hT.promLe ts hts)
    · rw [List.mem_singleton] at hts; rw [hts]; exact Nat.le_refl _
  · show _ + (S u + _) ≤ _ + (S u + (c.mem.append w).1.promAt (topL t) (u.prom ++ [(c.mem.append w).2]))
    rw [cntBelow_append, promAt_promise w hT.promLe]
    omega

end Pres

/-! ## Initially, and termination -/

/-- A worker's start: `StartWD` with its node's link word not `top`. -/
def Start (t : BitVec 64) (s : isa.State) : Prop := ∃ n d, StartWD t n d s ∧ t ≠ n + 8

theorem inv_init {fuel : Nat} {t : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, Start t s) :
    Inv fuel (Config.init states initMem : Config isa).threads.size t (Config.init states initMem) := by
  refine ⟨Config.init_bnd _ _, rfl, fun i u hu => ?_, ?_⟩
  · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
    obtain ⟨s, hm, rfl⟩ := hu
    obtain ⟨n, d, hW, hn⟩ := hs s (List.mem_of_getElem? hm)
    refine ⟨⟨hW.exe, hW.decls, hW.endPc, hW.x0, by show s.st.1.regs.X1.toBitVec + 8#64 ≠ t; rw [hW.x1]; exact fun e => hn e.symm, hW.d8, hW.d4⟩,
      ⟨1, by decide, hW.pc.trans addrOf_0, trivial⟩, Witness.fwdLeCoh_of_nil rfl,
      fun ts h => by simp [Thread.init] at h, by simp [Thread.init]⟩
  · have : (Config.init states initMem : Config isa).mem.last = 0 := rfl
    rw [this]
    exact Nat.zero_le _

/-- **Termination of the Treiber workers on the semantic machine, under
every schedule** (no fairness): any number of `treiber2DWorker` threads on a
valid layout, sharing `top`, each with its own node whose link word is not
`top`. At every fuel, one bound `K` (depending on `fuel` and on the number of
threads) on every semantic trace. -/
theorem treiber2_term_sem_gen {fuel : Nat} (t : BitVec 64) {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, Start t s) :
    TermBoundSem Arch.armv8 fuel (Config.init states initMem : Config isa) :=
  TermTreiber2P.term_sem_genP cells t fun s hm => by
    obtain ⟨n, d, hW, hn⟩ := hs s hm
    exact ⟨⟨hW.exe, hW.decls, hW.endPc, hW.x0,
      by show s.st.1.regs.X1.toBitVec + 8#64 ≠ t; rw [hW.x1]; exact fun e => hn e.symm, hW.d8, fun _ => hW.d4⟩,
      hW.pc.trans addrOf_0⟩

end Kraken.Promising.Live.TermTreiber2
