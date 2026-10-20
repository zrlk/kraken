/-
**Stage 4: termination of the x64 `treiber2.kl`
worker on the semantic machine, conditional on `NoEmptyRead`**
(`TermBoundSem` under `Arch.tso`, no fairness).

The A64 argument of `LiveTermTreiber2P.lean` on the x64 cells of
`LiveTermX64Treiber2Trees.lean`/`LiveTermX64Treiber2Step.lean`: a per-thread
rank `R` (the table `rkX`, keyed on `%rax`, the success count `sOfX`, the
retry count `cnt` of writes to `top` at or below the coherence view) lowered
by every instruction step, and `cnt` bounded by `n * (2 + fuel)` through the
count invariant (`Inv.cnt`), into `termBoundSem_of_threadRank` (`B = 1`).

The one difference with A64: x64 `treiber2.kl` has no `cbz` exit on an empty
stack. A pop that reads `top = 0` loops back (`testq; je pop`), which no rank
pays for. **`NoEmptyRead`** (below) says this never happens at a reachable
configuration; it is an explicit hypothesis here (`…_of_noEmptyRead`), not
proved. Its discharge is deferred (`KNOWN_GAPS.md`).

- `rmw_window_tso`: `Term.rmw_window` for a fencing RMW (`Arch.tso`).
- `StepOK`, `thread_step`: one instruction step by position.
- `Inv` (with reachability from the start, to consume `NoEmptyRead`),
  `Inv.step`.
- `x64_treiber2_termBoundSem_of_noEmptyRead`: any number of threads from
  `StartWV` states with nodes other than `top`.
-/
import Kraken.Promising.LiveTermX64Treiber2Step
import Kraken.Promising.LiveTerm

namespace Kraken.Promising.Live.TermX64Treiber2

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Term Kraken.Promising.Live.Bridge
open Kraken.Promising.Live.TermX64Treiber2Trees Kraken.Promising.Live.TermX64Treiber2Step
open Kraken.Promising.Live.TicketStep (spec_load)
open Kraken.Promising.X64.EnvG.Treiber2X (treiber2ImageV symT2 labT2 StartWV)

/-! ## The window of a fencing RMW -/

section Window

variable {I : ISA} (A : Arch) {tid : Nat} {t : Thread I} {mem : Memory}
  {outs : List (Except String (Outcome I))} {o : Outcome I}

/-- **The window of a fencing RMW** (`rmw_window` under `rmwFence = true`):
the leading and trailing `fence .sy` change neither memory nor coherence. -/
theorem rmw_window_tso (hA : A.rmwFence = true) (hfc : Witness.FwdLeCoh t.views) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧
      mem.lastWriteBelow l (t.views.getCoh l) ≤ ts ∧ ts ≤ o.mem.lastWriteBelow l (o.thread.views.getCoh l) := by
  obtain ⟨tree, c', hex', hr, -, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  simp only [runTree, hA, ↓reduceIte, List.mem_flatMap] at hr
  obtain ⟨⟨ts, old, c1⟩, hx, h⟩ := hr
  obtain ⟨e1, -, e2, e3, e4, -⟩ := read_window A (instrViews t (I.deps t.st))
    (c := fenceStep { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } .sy)
    hfc hx
  simp only [TsoRmw.fence_mem, TsoRmw.fence_getCoh] at e1 e2 e3 e4
  rw [coh_of_runK hv l, hm]
  cases hop : op old with
  | none =>
    simp only [hop] at h
    obtain ⟨hst, rfl⟩ := TicketStep.run_done A tid (instrViews t (I.deps t.st)) h
    refine ⟨ts, old, hst, e2, e3, ?_⟩
    rw [TsoRmw.fence_mem, TsoRmw.fence_getCoh, e1]; exact e4
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨hst, hc⟩ := TicketStep.run_done A tid (instrViews t (I.deps t.st)) h
    obtain ⟨q1, -, q3, -⟩ := TsoRmw.rmwPost_keeps (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    subst hc; rw [TsoRmw.fence_mem, TsoRmw.fence_getCoh]
    have hc2 := (Witness.cstep_writeSuccs (P := fun _ => False) A tid (instrViews t (I.deps t.st)) h2).coh l
    have hp2 : c1.mem.Prefix c2.mem := (writeSuccs_dord A tid (instrViews t (I.deps t.st)) h2).mem
    refine ⟨ts, old, hst, e2, e3, ?_⟩
    rw [q3 l, q1]
    rw [e1] at hp2
    exact Nat.le_trans e4 (Nat.le_trans (lastWriteBelow_prefix_le hp2 _) (lastWriteBelow_mono hc2))

end Window

/-! ## The rank table (layout-free) -/

/-- The flag term: `10` unless `%rax` holds the current value of `top`. -/
def flX (s : MachineData) (cur : Val) : Nat :=
  if s.regs.get64 .rax = BitVec.setWidth 64 cur then 0 else 10

/-- **The rank at position `p`** of the x64 worker (registers `s`, `cnt`
writes to `top` at or below the coherence view, current value `cur`); `N`
bounds `cnt`. Positions `2`–`5` are the push loop (A64 `3`–`8`, the compare
folded into the CAS), `7`–`12` the pop loop (A64 `10`–`16`); at `9` the
`ZF` (empty stack) branch is ranked above `7` only, which is why the step
`8 → 9` needs `%rax ≠ 0` (`NoEmptyRead`). -/
def rkX (N p : Nat) (s : MachineData) (cnt : Nat) (cur : Val) : Nat :=
  match p with
  | 2 => 32 + 10 * N + 10 * (N - cnt)
  | 3 => 31 + 10 * N + 10 * (N - cnt) + flX s cur
  | 4 => 30 + 10 * N + 10 * (N - cnt) + flX s cur
  | 5 => if s.status.zf = true then 25 + 10 * N else 34 + 10 * N + 10 * (N - cnt)
  | 7 => 12 + 10 * (N - cnt)
  | 8 => 11 + 10 * (N - cnt) + flX s cur
  | 9 => if s.status.zf = true then 13 + 10 * (N - cnt) else 10 + 10 * (N - cnt) + flX s cur
  | 10 => 9 + 10 * (N - cnt) + flX s cur
  | 11 => 8 + 10 * (N - cnt) + flX s cur
  | 12 => if s.status.zf = true then 4 else 13 + 10 * (N - cnt)
  | 13 => 3
  | 14 => 2
  | _ => 0

/-- The successful `lock cmpxchgq`s executed, read off position and flags. -/
def sOfX (p : Nat) (s : MachineData) : Nat :=
  match p with
  | 5 => if s.status.zf = true then 1 else 0
  | 7 | 8 | 9 | 10 | 11 => 1
  | 12 => if s.status.zf = true then 2 else 1
  | 13 | 14 | 16 => 2
  | _ => 0

theorem sOfX_le (p : Nat) (s : MachineData) : sOfX p s ≤ 2 := by
  unfold sOfX; split <;> (try split) <;> omega

theorem flX_le (s : MachineData) (c : Val) : flX s c ≤ 10 := by unfold flX; split <;> omega

/-- The rank inside a loop body, across a step that keeps `%rax`. -/
theorem rank_bodyX {N c0 c1 : Nat} {u0 u1 : Val} {s s' : MachineData} {a b : Nat}
    (hx : s'.regs.get64 .rax = s.regs.get64 .rax)
    (hN : c1 ≤ N) (hc : c0 ≤ c1 ∧ (c0 < c1 ∨ (c0 = c1 ∧ u0 = u1))) (hab : a < b) :
    a + 10 * (N - c1) + flX s' u1 < b + 10 * (N - c0) + flX s u0 := by
  rcases hc with ⟨-, hlt | ⟨rfl, rfl⟩⟩
  · have := flX_le s' u1; omega
  · have : flX s' u0 = flX s u0 := by simp only [flX, hx]
    omega

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiber2ImageV)]

/-- The register fact on the push loop (positions `2`–`5`): the thread's node
is not `top`, so its link store (position `3`) is not a write to `top`. -/
def PcI (s : MachineData) (i : Nat) : Prop := i ≤ 5 → s.regs.get64 .rbx ≠ symT2 "top"

theorem PcI.of_rbx {s s' : MachineData} {i j : Nat} (h : PcI s i) (hr : s'.regs.get64 .rbx = s.regs.get64 .rbx)
    (hj : j ≤ 5 → i ≤ 5) : PcI s' j := fun h' => hr ▸ h (hj h')

theorem PcI.big {s : MachineData} {j : Nat} (hj : 5 < j) : PcI s j := fun h => absurd h (by omega)

set_option hygiene false in
local notation "pcT" => (layout treiber2ImageV).addrOf

/-! ## Positions, rank and count -/

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

/-- The worker sits at a position, with its register fact. -/
def PcOK (s : isa.State) : Prop := ∃ i ∈ tPcs, s.st.2 = pcT i ∧ PcI s.st.1 i

/-- A thread's rank in memory `mem`. -/
def R (N : Nat) (u : Thread isa) (mem : Memory) : Nat :=
  rkX N (posOf u.st.st.2) u.st.st.1 (mem.cntBelow TopL (u.views.getCoh TopL))
    (mem.curBelow TopL (u.views.getCoh TopL))

/-- A thread's successful `lock cmpxchgq`s. -/
def S (u : Thread isa) : Nat := sOfX (posOf u.st.st.2) u.st.st.1

/-- **No empty read, for one thread state**: at `testq %rax,%rax`
(position `8`), the value just loaded from `top` by the pop is not `0`. -/
def NE (s : isa.State) : Prop := s.st.2 = pcT 8 → s.st.1.regs.get64 .rax ≠ 0#64

/-- **`NoEmptyRead`** (the hypothesis of this file): at every configuration
reachable from `c0` on the semantic machine (`Arch.tso`, certification fuel
`fuel`), every thread at position `8` (just after the pop's load of `top`)
holds a nonzero `%rax`: a pop never reads an empty stack.

It is not proved here. For `treiber2.kl` (two threads, distinct nonzero
nodes, `top` and the links initially `0`) the intended argument is:

1. Complete all certifications: at a reachable `c`, by the no-stuck proofs' TSO
   consistency every thread has a certification run without fresh writes
   (memory unchanged). These runs compose. The result is a configuration with
   **the same memory, built from the post-read configuration `c′`** (the
   configuration just after the load at position `7`), in which every
   message, the promised ones included, is fulfilled by an instruction step.
2. A ghost history invariant closed under every instruction and promise step
   gives, for fulfilled messages: every non-initial `top` message is a CAS;
   thread `x` writes `top` at most twice, `push(x)` (value its node) before
   `pop(x)`; a CAS's read is the immediate `top`-predecessor of its write;
   values of nodes first occur at their push.
3. A **stack count**: in timestamp order the pushes so far number `2` while the
   pops number `≤ 1`, the reader's own pop not being among them (a thread
   cannot read its own outstanding promise, and has not fulfilled it while at
   `pop`). So a `0`-valued `top` message at or above `push(w)`, the reader's
   coherence bound, with `pop(w)` not yet ordered at or below it, would make
   the stack empty after at least as many pops as pushes. That is impossible.

(The earlier variant, completing certifications from the pre-read `c`, is
wrong: the completed run may fulfil `w`'s own already-promised `pop(w)`.) -/
def NoEmptyRead (fuel : Nat) (c0 : Config isa) : Prop :=
  ∀ c, ReachableSem Arch.tso fuel c0 c → ∀ (i : Nat) (u : Thread isa), c.threads[i]? = some u → NE u.st

/-- **What one instruction step of a worker does**: the next state invariant,
the effect on memory, promises and the success count, and (given `NE` and
the window facts) the rank drop. -/
structure StepOK (N : Nat) (u : Thread isa) (mem : Memory) (o : Outcome isa) : Prop where
  st : Static o.thread.st
  pc : PcOK o.thread.st
  eff : (o.mem = mem ∧ o.thread.prom = u.prom ∧ S u ≤ S o.thread) ∨
    (∃ w : Msg, WEff mem o.mem u.prom o.thread.prom w ∧ S u + (if w.loc = TopL then 1 else 0) ≤ S o.thread)
  rank : NE u.st → Witness.FwdLeCoh u.views → u.views.getCoh TopL ≤ mem.last →
    o.mem.cntBelow TopL (o.thread.views.getCoh TopL) ≤ N → R N o.thread o.mem < R N u mem

omit layout hv in
theorem WriteP.weff {tid : Nat} {t : Thread isa} {mem : Memory} {oc : Outcome isa} {l : Loc} {v : Val}
    (h : WriteP tid t mem oc l v) : WEff mem oc.mem t.prom oc.thread.prom { loc := l, val := v, tid } := by
  rcases h with ⟨a, b, -⟩ | ⟨ts, hts, a, -, -, b, c, -⟩
  · exact .inl ⟨a, b⟩
  · exact .inr ⟨ts, hts, a, b, c⟩

/-! ## One step of a worker -/

section Steps

variable {N : Nat} {u : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {o : Outcome isa}
  (hS : Static u.st) (hs : stepOne Arch.tso u tid mem = some outs) (ho : .ok o ∈ outs)

include hS hs ho

omit hS in
/-- The count across the step (`step_cnt`). -/
theorem cnt_step (hb : u.views.getCoh TopL ≤ mem.last) :
    mem.cntBelow TopL (u.views.getCoh TopL) ≤ o.mem.cntBelow TopL (o.thread.views.getCoh TopL) ∧
      (mem.cntBelow TopL (u.views.getCoh TopL) < o.mem.cntBelow TopL (o.thread.views.getCoh TopL) ∨
       (mem.cntBelow TopL (u.views.getCoh TopL) = o.mem.cntBelow TopL (o.thread.views.getCoh TopL) ∧
        mem.curBelow TopL (u.views.getCoh TopL) = o.mem.curBelow TopL (o.thread.views.getCoh TopL))) :=
  step_cnt (stepOne_dord _ hs ho).2.2.1 hb ((stepOne_dord _ hs ho).2.1 _)

omit hS hs ho in
/-- A step that changes neither memory nor the coherence view keeps `cnt`
and `cur`. -/
theorem cnt_same (hm : o.mem = mem) (hc : o.thread.views.coh = u.views.coh) :
    o.mem.cntBelow TopL (o.thread.views.getCoh TopL) = mem.cntBelow TopL (u.views.getCoh TopL) ∧
      o.mem.curBelow TopL (o.thread.views.getCoh TopL) = mem.curBelow TopL (u.views.getCoh TopL) := by
  rw [hm, SpinSwpStep.getCoh_congr hc]; exact ⟨rfl, rfl⟩

local macro "posn" hpc:term:max hpk:term:max i:term:max j:term:max : tactic => `(tactic|
  simp only [R, S, $hpc:term, $hpk:term, posOf_pcT (i := $i) (by decide), posOf_pcT (i := $j) (by decide)])

/-- The loads of `top` (positions `2` and `7`). -/
theorem stepLd {i : Nat} (hi : i = 2 ∨ i = 7) (hpc : u.st.st.2 = pcT i) (hP : PcI u.st.st.1 i) :
    StepOK N u mem o := by
  have hm : i ∈ tPcs ∧ i + 1 ∈ tPcs ∧ i ≠ 16 := by rcases hi with rfl | rfl <;> decide
  obtain ⟨g, hg, hex⟩ := exec_ldtop _ hi (hS.at hm.1 hm.2.2 hpc) (hS.d8 _)
  obtain ⟨ts, v, hst, -, -, hmm, hp, -⟩ := spec_load _ _ hex hs ho
  have hpk : o.thread.st.st.2 = pcT (i + 1) := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ (hg v).1, ⟨i + 1, hm.2.1, hpk, by
      rw [hst]; exact hP.of_rbx (hg v).2.2 (by omega)⟩, .inl ⟨hmm, hp, ?_⟩, fun _ hf hb hN => ?_⟩
  · simp only [S, hpc, hpk, posOf_pcT hm.1, posOf_pcT hm.2.1]
    rcases hi with rfl | rfl <;> simp [sOfX]
  · obtain ⟨ts', v', hst', hmm', -, hr, h1, h2⟩ := load_window _ _ hf hex hs ho
    have hw := window_rank (Memory.Prefix.refl mem) hb hr h1 h2
    have hc := cnt_step hs ho hb
    have hx : o.thread.st.st.1.regs.get64 .rax = BitVec.setWidth 64 v' := by rw [hst']; exact (hg v').2.1
    rw [hmm'] at hc hN ⊢
    simp only [R, hpc, hpk, posOf_pcT hm.1, posOf_pcT hm.2.1]
    generalize mem.cntBelow TopL (u.views.getCoh TopL) = c0 at *
    generalize mem.cntBelow TopL (o.thread.views.getCoh TopL) = c1 at *
    generalize mem.curBelow TopL (o.thread.views.getCoh TopL) = u1 at *
    rcases hi with rfl | rfl <;>
    · simp only [rkX, flX]
      split
      · omega
      · rename_i hne
        have := hw.2 fun e => hne (by rw [hx, e])
        omega

/-- `movq %rax,(%rbx)` (position `3`): a write to the node's link, not `top`. -/
theorem step3 (hpc : u.st.st.2 = pcT 3) (hP : PcI u.st.st.1 3) : StepOK N u mem o := by
  obtain ⟨hst, hw⟩ := q3 hS hs ho hpc
  have hpk : o.thread.st.st.2 = pcT 4 := by rw [hst]
  have hl : LinkL (u.st.st.1.regs.get64 .rbx) ≠ TopL := fun e => hP (by omega) (congrArg Loc.addr e)
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨4, by decide, hpk, by rw [hst]; exact hP.of_rbx rfl (by omega)⟩,
    .inr ⟨_, WriteP.weff hw, ?_⟩, fun _ hf hb hN => ?_⟩
  · posn hpc hpk 3 4
    simpa [sOfX] using hP (by omega)
  · simp only [R, hpc, hpk, posOf_pcT (i := 3) (by decide), posOf_pcT (i := 4) (by decide), rkX]
    exact rank_bodyX (by rw [hst]) hN (cnt_step hs ho hb) (by omega)

/-- `lock cmpxchgq %R,(top)` (positions `4` with `%rbx`, `11` with `%rcx`). -/
theorem stepCas {i : Nat} {r : Reg64} (hi : (i = 4 ∧ r = .rbx) ∨ (i = 11 ∧ r = .rcx)) (hpc : u.st.st.2 = pcT i)
    (hP : PcI u.st.st.1 i) : StepOK N u mem o := by
  have hm : i ∈ tPcs ∧ i + 1 ∈ tPcs ∧ i ≠ 16 := by rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain ⟨tr, old, md, hd, hz, -, hbx, hst, -, -, hcas⟩ := qcas hS hs ho hi hpc
  have hpk : o.thread.st.st.2 = pcT (i + 1) := by rw [hst]
  have hzo : o.thread.st.st.1.status.zf = true ↔ BitVec.setWidth 64 old = u.st.st.1.regs.get64 .rax := by
    rw [hst]; exact hz
  refine ⟨by rw [hst]; exact hS.goto _ _ hd, ⟨i + 1, hm.2.1, hpk, by rw [hst]; exact hP.of_rbx hbx (by omega)⟩,
    ?_, fun _ hf hb hN => ?_⟩
  · rcases hcas with ⟨hne, hm', hp, -⟩ | ⟨he, hw, -⟩
    · refine .inl ⟨hm', hp, ?_⟩
      have h0 : o.thread.st.st.1.status.zf = false := by
        cases e : o.thread.st.st.1.status.zf
        · rfl
        · exact absurd (hzo.mp e) hne
      simp only [S, hpc, hpk, posOf_pcT hm.1, posOf_pcT hm.2.1]
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [sOfX, h0]
    · refine .inr ⟨_, WriteP.weff hw, ?_⟩
      have h1 : o.thread.st.st.1.status.zf = true := hzo.mpr he
      simp only [S, hpc, hpk, posOf_pcT hm.1, posOf_pcT hm.2.1]
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [sOfX, h1]
  · obtain ⟨g, hg, hex⟩ := exec_cas _ hi (hS.at hm.1 hm.2.2 hpc) (hS.d8 _)
    obtain ⟨ts, v, hst', hr, h1, h2⟩ := rmw_window_tso _ rfl hf hex hs ho
    have hw := window_rank (stepOne_dord _ hs ho).2.2.1 hb hr h1 h2
    have hc := cnt_step hs ho hb
    have hzv : o.thread.st.st.1.status.zf = true ↔ BitVec.setWidth 64 v = u.st.st.1.regs.get64 .rax := by
      rw [hst']; exact (hg v).2.1
    simp only [R, hpc, hpk, posOf_pcT hm.1, posOf_pcT hm.2.1]
    generalize mem.cntBelow TopL (u.views.getCoh TopL) = c0 at *
    generalize o.mem.cntBelow TopL (o.thread.views.getCoh TopL) = c1 at *
    generalize mem.curBelow TopL (u.views.getCoh TopL) = u0 at *
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    · simp only [rkX, flX]
      split
      · omega
      · rename_i hne
        split
        · rename_i he
          have := hw.1 fun e => hne (hzv.mpr (by rw [e, he]))
          omega
        · omega

/-- `jne push` (position `5`). -/
theorem step5 (hpc : u.st.st.2 = pcT 5) (hP : PcI u.st.st.1 5) : StepOK N u mem o := by
  obtain ⟨⟨hm, hp, -⟩, hst, hc⟩ := q5 hS hs ho hpc
  obtain ⟨e1, -⟩ := cnt_same hm hc
  by_cases hz : u.st.st.1.status.zf = true
  · simp only [hz, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcT 7 := by rw [hst]
    refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨7, by decide, hpk, PcI.big (by omega)⟩, .inl ⟨hm, hp, ?_⟩,
      fun _ _ _ _ => ?_⟩
    · posn hpc hpk 5 7; simp [sOfX, hz]
    · simp only [R, hpc, hpk, posOf_pcT (i := 5) (by decide), posOf_pcT (i := 7) (by decide), rkX, hz,
        ↓reduceIte]
      omega
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcT 2 := by rw [hst]
    refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨2, by decide, hpk, by rw [hst]; exact hP.of_rbx rfl (by omega)⟩,
      .inl ⟨hm, hp, ?_⟩, fun _ _ _ _ => ?_⟩
    · posn hpc hpk 5 2; simp [sOfX, hz]
    · simp only [R]; rw [e1]
      simp only [hpc, hpk, posOf_pcT (i := 5) (by decide), posOf_pcT (i := 2) (by decide), rkX, hz,
        Bool.false_eq_true, ↓reduceIte]
      omega

/-- `testq %rax,%rax` (position `8`): `ZF` clear, given `NE`. -/
theorem step8 (hpc : u.st.st.2 = pcT 8) : StepOK N u mem o := by
  obtain ⟨⟨hm, hp, -⟩, md, hd, hreg, hz, hst, hc⟩ := q8 hS hs ho hpc
  obtain ⟨e1, e2⟩ := cnt_same hm hc
  have hpk : o.thread.st.st.2 = pcT 9 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ hd, ⟨9, by decide, hpk, PcI.big (by omega)⟩, .inl ⟨hm, hp, ?_⟩,
    fun hne _ _ _ => ?_⟩
  · posn hpc hpk 8 9; simp [sOfX]
  · have hz0 : o.thread.st.st.1.status.zf = false := by
      rw [hst]
      cases e : md.status.zf
      · rfl
      · exact absurd (hz.mp e) (hne hpc)
    have hf : ∀ c, flX o.thread.st.st.1 c = flX u.st.st.1 c := fun c => by
      rw [hst]; show flX md c = _; simp only [flX, hreg]
    simp only [R]; rw [e1, e2]
    simp only [hpc, hpk, posOf_pcT (i := 8) (by decide), posOf_pcT (i := 9) (by decide), rkX, hz0,
      Bool.false_eq_true, ↓reduceIte, hf]
    omega

/-- `je pop` (position `9`). -/
theorem step9 (hpc : u.st.st.2 = pcT 9) : StepOK N u mem o := by
  obtain ⟨⟨hm, hp, -⟩, hst, hc⟩ := q9 hS hs ho hpc
  obtain ⟨e1, e2⟩ := cnt_same hm hc
  by_cases hz : u.st.st.1.status.zf = true
  · simp only [hz, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcT 7 := by rw [hst]
    refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨7, by decide, hpk, PcI.big (by omega)⟩, .inl ⟨hm, hp, ?_⟩,
      fun _ _ _ _ => ?_⟩
    · posn hpc hpk 9 7; simp [sOfX]
    · simp only [R]; rw [e1]
      simp only [hpc, hpk, posOf_pcT (i := 9) (by decide), posOf_pcT (i := 7) (by decide), rkX, hz, ↓reduceIte]
      omega
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcT 10 := by rw [hst]
    have h1 : o.thread.st.st.1 = u.st.st.1 := by rw [hst]
    refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨10, by decide, hpk, PcI.big (by omega)⟩, .inl ⟨hm, hp, ?_⟩,
      fun _ _ _ _ => ?_⟩
    · posn hpc hpk 9 10; simp [sOfX]
    · simp only [R]; rw [e1, e2, h1]
      simp only [hpc, hpk, posOf_pcT (i := 9) (by decide), posOf_pcT (i := 10) (by decide), rkX, hz,
        Bool.false_eq_true, ↓reduceIte]
      omega

/-- `movq (%rax),%rcx` (position `10`). -/
theorem step10 (hpc : u.st.st.2 = pcT 10) : StepOK N u mem o := by
  obtain ⟨⟨hm, hp, -⟩, md, hd, hax, -, ts, v, -, hst, -⟩ := q10 hS hs ho hpc
  have hpk : o.thread.st.st.2 = pcT 11 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ hd, ⟨11, by decide, hpk, PcI.big (by omega)⟩, .inl ⟨hm, hp, ?_⟩,
    fun _ hf hb hN => ?_⟩
  · posn hpc hpk 10 11; simp [sOfX]
  · simp only [R, hpc, hpk, posOf_pcT (i := 10) (by decide), posOf_pcT (i := 11) (by decide), rkX]
    exact rank_bodyX (by rw [hst]; exact hax) hN (cnt_step hs ho hb) (by omega)

/-- `jne pop` (position `12`). -/
theorem step12 (hpc : u.st.st.2 = pcT 12) : StepOK N u mem o := by
  obtain ⟨⟨hm, hp, -⟩, hst, hc⟩ := q12 hS hs ho hpc
  obtain ⟨e1, -⟩ := cnt_same hm hc
  by_cases hz : u.st.st.1.status.zf = true
  · simp only [hz, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcT 13 := by rw [hst]
    refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨13, by decide, hpk, PcI.big (by omega)⟩, .inl ⟨hm, hp, ?_⟩,
      fun _ _ _ _ => ?_⟩
    · posn hpc hpk 12 13; simp [sOfX, hz]
    · simp only [R, hpc, hpk, posOf_pcT (i := 12) (by decide), posOf_pcT (i := 13) (by decide), rkX, hz,
        ↓reduceIte]
      omega
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
    have hpk : o.thread.st.st.2 = pcT 7 := by rw [hst]
    refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨7, by decide, hpk, PcI.big (by omega)⟩, .inl ⟨hm, hp, ?_⟩,
      fun _ _ _ _ => ?_⟩
    · posn hpc hpk 12 7; simp [sOfX, hz]
    · simp only [R]; rw [e1]
      simp only [hpc, hpk, posOf_pcT (i := 12) (by decide), posOf_pcT (i := 7) (by decide), rkX, hz,
        Bool.false_eq_true, ↓reduceIte]
      omega

/-- `movq %rax,%r12` (position `13`). -/
theorem step13 (hpc : u.st.st.2 = pcT 13) : StepOK N u mem o := by
  obtain ⟨⟨hm, hp, -⟩, md, hd, -, hst, -⟩ := q13 hS hs ho hpc
  have hpk : o.thread.st.st.2 = pcT 14 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ hd, ⟨14, by decide, hpk, PcI.big (by omega)⟩,
    .inl ⟨hm, hp, by posn hpc hpk 13 14; simp [sOfX]⟩, fun _ _ _ _ => ?_⟩
  simp only [R, hpc, hpk, posOf_pcT (i := 13) (by decide), posOf_pcT (i := 14) (by decide), rkX]; omega

/-- `jmp done` (position `14`). -/
theorem step14 (hpc : u.st.st.2 = pcT 14) : StepOK N u mem o := by
  obtain ⟨⟨hm, hp, -⟩, hst, -⟩ := q14 hS hs ho hpc
  have hpk : o.thread.st.st.2 = pcT 16 := by rw [hst]
  refine ⟨by rw [hst]; exact hS.goto _ _ rfl, ⟨16, by decide, hpk, PcI.big (by omega)⟩,
    .inl ⟨hm, hp, by posn hpc hpk 14 16; simp [sOfX]⟩, fun _ _ _ _ => ?_⟩
  simp only [R, hpc, hpk, posOf_pcT (i := 14) (by decide), posOf_pcT (i := 16) (by decide), rkX]; omega

/-- **One instruction step of a worker**, by position. -/
theorem thread_step (hpc : PcOK u.st) : StepOK N u mem o := by
  obtain ⟨i, hi, hpc, hI⟩ := hpc
  simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stepLd hS hs ho (.inl rfl) hpc hI
  · exact step3 hS hs ho hpc hI
  · exact stepCas hS hs ho (.inl ⟨rfl, rfl⟩) hpc hI
  · exact step5 hS hs ho hpc hI
  · exact stepLd hS hs ho (.inr rfl) hpc hI
  · exact step8 hS hs ho hpc
  · exact step9 hS hs ho hpc
  · exact step10 hS hs ho hpc
  · exact stepCas hS hs ho (.inr ⟨rfl, rfl⟩) hpc hI
  · exact step12 hS hs ho hpc
  · exact step13 hS hs ho hpc
  · exact step14 hS hs ho hpc
  · rw [stepOne_end hS hpc] at hs; cases hs

end Steps

/-! ## The invariant -/

section Inv

/-- `PcOK` gives `SInv`. -/
theorem sinv_of {s : isa.State} (hS : Static s) (hP : PcOK s) : SInv s :=
  ⟨hS, let ⟨i, hi, hp, _⟩ := hP; ⟨i, hi, hp⟩⟩

/-- **The per-thread invariant.** -/
structure TI (fuel : Nat) (u : Thread isa) (mem : Memory) : Prop where
  st : Static u.st
  pc : PcOK u.st
  fwd : Witness.FwdLeCoh u.views
  promLe : ∀ ts ∈ u.prom, ts ≤ mem.last
  plen : u.prom.length ≤ fuel

theorem TI.mono {fuel : Nat} {u : Thread isa} {mem mem' : Memory} (h : TI fuel u mem) (hp : mem.Prefix mem') :
    TI fuel u mem' :=
  ⟨h.st, h.pc, h.fwd, fun ts hts => Nat.le_trans (h.promLe ts hts) hp.last_le, h.plen⟩

/-- **The invariant**: reachable from `c0` (for `NoEmptyRead`), every thread
a worker, and the count of writes to `top` at most the successes plus the
promises to `top`. -/
structure Inv (fuel n : Nat) (c0 c : Config isa) : Prop where
  reach : ReachableSem Arch.tso fuel c0 c
  bnd : c.Bnd
  size : c.threads.size = n
  thr : ∀ (i : Nat) (u : Thread isa), c.threads[i]? = some u → TI fuel u c.mem
  cnt : c.mem.cntBelow TopL c.mem.last ≤ tsum c fun _ u => S u + c.mem.promAt TopL u.prom

/-- **`cnt` is at most `n * (2 + fuel)`.** -/
theorem Inv.cnt_le {fuel n : Nat} {c0 c : Config isa} (h : Inv fuel n c0 c) (b : Nat) :
    c.mem.cntBelow TopL b ≤ n * (2 + fuel) := by
  have h1 := cntBelow_le_last c.mem TopL b
  have h2 := tsum_le (c := c) (F := fun _ u => S u + c.mem.promAt TopL u.prom) (M := 2 + fuel)
    fun j v hv => by
      have := sOfX_le (posOf v.st.st.2) v.st.st.1
      have := (promAt_le_length (m := c.mem) (l := TopL) (p := v.prom))
      have := (h.thr j v hv).plen
      simp only [S]; omega
  rw [h.size] at h2
  have := h.cnt
  omega

variable {fuel n : Nat} {c0 c : Config isa} {tid : Nat} {u : Thread isa}

/-- The invariant after a step of `tid`. -/
theorem Inv.build (h : Inv fuel n c0 c) (ht : c.threads[tid]? = some u) {u' : Thread isa}
    {mem' : Memory} (hr : ReachableSem Arch.tso fuel c0 (c.withThread tid u' mem')) (hpre : c.mem.Prefix mem')
    (hb : (c.withThread tid u' mem').Bnd) (hT : TI fuel u' mem')
    (hcnt : mem'.cntBelow TopL mem'.last + (S u + c.mem.promAt TopL u.prom) ≤
      c.mem.cntBelow TopL c.mem.last + (S u' + mem'.promAt TopL u'.prom)) :
    Inv fuel n c0 (c.withThread tid u' mem') := by
  refine ⟨hr, hb, by rw [withThread_size]; exact h.size, fun i v hv => ?_, ?_⟩
  · rcases SpinStep.wt_get ht hv with ⟨-, rfl⟩ | ⟨-, hv⟩
    · exact hT
    · exact (h.thr i v hv).mono hpre
  · have e := tsum_withThread_add (t' := u') (mem' := mem')
      (F := fun (_ : Nat) (v : Thread isa) => S v + c.mem.promAt TopL v.prom)
      (F' := fun (_ : Nat) (v : Thread isa) => S v + mem'.promAt TopL v.prom) ht fun i v _ hv => by
        simp only [promAt_prefix hpre (h.thr i v hv).promLe]
    have := h.cnt
    show mem'.cntBelow TopL mem'.last ≤ tsum (c.withThread tid u' mem') fun _ v => S v + mem'.promAt TopL v.prom
    omega

/-- **A semantic step keeps the invariant.** -/
theorem Inv.step (h : Inv fuel n c0 c) (ht : c.threads[tid]? = some u) {c' : Config isa}
    (hst : StepSem Arch.tso fuel tid c c') : Inv fuel n c0 c' := by
  have hb := h.bnd.semStep hst
  have hr := NoStuck.reachableSem_snoc h.reach hst
  have hT := h.thr tid u ht
  rcases hst with ⟨t1, outs, o, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, -, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    have r := thread_step (N := 0) hT.st hs ho hT.pc
    have hpre : c.mem.Prefix o.mem := (stepOne_dord _ hs ho).2.2.1
    have hplen : o.thread.prom.length ≤ fuel := by
      have := prom_le_of_certOkN (dropBounded_of_sinv (sinv_of r.st r.pc)) hc; omega
    rcases r.eff with ⟨hm, hp, hS⟩ | ⟨w, hw, hS⟩
    · refine h.build ht hr hpre hb ⟨r.st, r.pc, Witness.stepOne_fwdLeCoh hs ho hT.fwd,
        by rw [hp, hm]; exact hT.promLe, hplen⟩ ?_
      rw [hm, hp]; omega
    · obtain ⟨e, hle⟩ := count_weff (l := TopL) hT.promLe hw
      refine h.build ht hr hpre hb ⟨r.st, r.pc, Witness.stepOne_fwdLeCoh hs ho hT.fwd, hle, hplen⟩ ?_
      by_cases hl : w.loc = TopL <;> simp only [hl, ↓reduceIte] at hS e <;> omega
  · rw [ht] at ht1; cases ht1
    have hpre : c.mem.Prefix (c.mem.append w).1 := Memory.Prefix.append _ _
    have hplen : (promThread u c.mem w).prom.length ≤ fuel := by
      have := prom_le_of_certOkN (dropBounded_of_sinv (t := promThread u c.mem w) (tid := tid)
        (sinv_of hT.st hT.pc)) hc
      omega
    have hlast : (c.mem.append w).1.last = c.mem.last + 1 := by simp [Memory.append, Memory.last]
    refine h.build ht hr hpre hb ⟨hT.st, hT.pc, hT.fwd, fun ts hts => ?_, hplen⟩ ?_
    · rw [hlast]
      rcases List.mem_append.mp hts with hts | hts
      · exact Nat.le_succ_of_le (hT.promLe ts hts)
      · rw [List.mem_singleton] at hts; rw [hts]; exact Nat.le_refl _
    · show _ + (S u + _) ≤ _ + (S u + (c.mem.append w).1.promAt TopL (u.prom ++ [(c.mem.append w).2]))
      rw [cntBelow_append, promAt_promise w hT.promLe]
      omega

end Inv

/-! ## Termination, given `NoEmptyRead` -/

/-- **Termination of the x64 `treiber2.kl` worker on the semantic machine,
under every schedule, given `NoEmptyRead`**: any number of threads, each a
`StartWV` state (`treiber2ImageV`, at `worker`, no declarations, empty private
memory) whose node `%rbx` is not `top`. At every fuel at which `NoEmptyRead`
holds from the start, one bound on every semantic trace (`TermBoundSem`). -/
theorem x64_treiber2_termBoundSem_of_noEmptyRead {fuel : Nat} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, ∃ n, StartWV n s ∧ n ≠ symT2 "top")
    (hne : NoEmptyRead fuel (Config.init states initMem)) :
    TermBoundSem Arch.tso fuel (Config.init states initMem : Config isa) := by
  let c0 : Config isa := Config.init states initMem
  let n := c0.threads.size
  have hinit : Inv fuel n c0 c0 := by
    refine ⟨.refl _, Config.init_bnd _ _, rfl, fun i u hu => ?_, ?_⟩
    · simp only [c0, Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
      obtain ⟨s, hm, rfl⟩ := hu
      obtain ⟨nd, hS, hn⟩ := hs s (List.mem_of_getElem? hm)
      exact ⟨⟨hS.exe, hS.decls, hS.endPc.trans label_done, hS.d8⟩,
        ⟨2, by decide, hS.pc.trans label_worker, fun _ h => hn (hS.rbx.symm.trans h)⟩,
        Witness.fwdLeCoh_of_nil rfl, fun ts h => by simp [Thread.init] at h, by simp [Thread.init]⟩
    · have : c0.mem.last = 0 := rfl
      rw [this]
      exact Nat.zero_le _
  refine termBoundSem_of_threadRank (B := 1) (Inv fuel n c0) (R (n * (2 + fuel))) hinit
    (fun c c' tid h hst => ?_) (fun c h i u hu => ?_) (fun c h i u hu => ?_) (fun c h i u hu mem' hp => ?_)
    (fun _ _ _ => rfl) (fun c tid u outs o h hu hso ho h' => ?_)
  · obtain ⟨u, hu⟩ : ∃ u, c.threads[tid]? = some u := by
      rcases hst with ⟨u, -, -, hu, -⟩ | ⟨u, -, hu, -⟩ <;> exact ⟨u, hu⟩
    exact h.step hu hst
  · rw [Nat.mul_one]; exact (h.thr i u hu).plen
  · exact dropBounded_of_sinv (sinv_of (h.thr i u hu).st (h.thr i u hu).pc)
  · have hb := (h.bnd i u hu).views.le.coh TopL
    unfold R
    rw [cntBelow_prefix hp hb, curBelow_prefix hp hb]
  · have hT := h.thr tid u hu
    exact (thread_step hT.st hso ho hT.pc).rank (hne c h.reach tid u hu) hT.fwd
      ((h.bnd tid u hu).views.le.coh TopL) (h'.cnt_le _)

end Kraken.Promising.Live.TermX64Treiber2
