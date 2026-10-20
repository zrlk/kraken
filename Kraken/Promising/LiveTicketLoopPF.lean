/-
**Stage 4 (repeated acquisition): repeated-acquire ticket-lock liveness,
promise-free fragment, on the semantic machine** (`ticket_loop_live_pf`), on a
valid layout of `tkLoopWorker`.

On a semantic trace (`TraceSem`) from a start configuration with no promise
step (`PromiseFreeSem`), every step is an instruction step of a promise-free
thread, so `LiveTicketLoopInv.InvL` holds at every index (`inv_at`). Write `m`
for the value of `owner` (`Mo`); it never decreases (`M_mono`), and while it
stays, so does its last write (`M_step`).

- **Starvation-freedom per round** (`ticket_loop_starve_pf`). Thread `T`
  waits in round `r` and never acquires in round `r`: it stays in its spin
  loop with its ticket `K` and its round (`stay`), so `m ≤ K` forever and `m`
  is eventually constant. The holder `H` of `m` exists (`tkSurj`, `m ≤ K <
  xc`) and keeps holding `m` (`holder_persist`: its `STLR` would raise `m`).
  It is always instruction-enabled (`henH`), never gets through its critical
  section (`cs_false`), so it reads `owner` infinitely often (`reads_inf`);
  memory fairness brings its view of `owner` up to the fixed last write, and
  its next `LDAR` reads `m` and it enters the critical section (`at_false`):
  contradiction (`holder_false`). The argument is `LiveTicketPF`'s, on the
  loop worker's positions (6–13 instead of 4–11) and on the semantic
  machine.
- **Every thread completes all its rounds** (`ticket_loop_finish_pf`). A
  thread never at the end is always instruction-enabled. Its rank `20 · X7 +
  rk pc` (`rk`: steps to the end of the round) never grows along its steps,
  and drops at each step outside the spin loop (`rk_lt`, `pos_step`); in the
  spin loop of round `r` starvation-freedom gets it out with a smaller rank.
  Well-founded induction on the rank.

The concrete instance `ticket_loop_live_pf_concrete` fixes the layout
`tkLoopLayout` (text at `0x100000`).
-/
import Kraken.Promising.LiveTicketLoopInv
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Promising.LiveTkHolderP

namespace Kraken.Promising.Live.TicketLoopPF

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketLoopInv
open Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SpinSwpStep (getCoh_congr)
open Kraken.Promising.Live.TicketInv (wn L4 w32_eq_iff)
open Kraken.Promising.Live.TicketTrees (w32)
open Kraken.Promising.SLR.A64Trees (At goto)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-! ## The position after a step -/

/-- The position after the instruction at position `p` (`z`: the `Z` flag;
`w`: no round left, `X7 = 0`). -/
def nextPc (z w : Bool) : Nat → Nat
  | 1 => 3 | 3 => if w then 17 else 4 | 4 => 6 | 6 => 7 | 7 => 8 | 8 => if z then 9 else 6
  | 9 => 10 | 10 => 11 | 11 => 12 | 12 => 13 | 13 => 14 | 14 => 15 | 15 => 3 | _ => 17

/-- Steps to the end of the round (the spin loop counts once). -/
def rk : Nat → Nat
  | 1 => 16 | 15 => 14 | 3 => 13 | 4 => 12 | 6 | 7 | 8 => 11 | 9 => 10 | 10 => 9 | 11 => 8 | 12 => 7
  | 13 => 6 | 14 => 5 | _ => 0

theorem nextPc_mem : ∀ z w : Bool, ∀ p ∈ tkLoopPcs, nextPc z w p ∈ tkLoopPcs := by decide

theorem rk_le : ∀ p ∈ tkLoopPcs, rk p ≤ 16 := by decide

/-- Outside the spin loop and the `SUB`, a step lowers `rk`. -/
theorem rk_lt : ∀ z w : Bool, ∀ p ∈ tkLoopPcs, p ∉ [6, 7, 8] → p ≠ 14 → p ≠ 17 → rk (nextPc z w p) < rk p := by
  decide

/-- The spin loop: `LDAR` to `CMP`, `CMP` to `B.NE`, `B.NE` back or out. -/
theorem spin_facts : ∀ p ∈ [6, 7, 8], p ∈ tkLoopPcs ∧ p ≠ 4 ∧ p ≠ 14 ∧ p ∈ tkHeld ∧ rk p = 11 := by decide

theorem held_ne17 : ∀ p ∈ tkHeld, p ≠ 17 := by decide

theorem cs_facts : ∀ q ∈ [9, 10, 11, 12, 13, 14], q ∈ tkLoopPcs ∧ rk q ≤ 10 := by decide

theorem next_spin : ∀ z w : Bool, ∀ p ∈ [6, 7, 8], nextPc z w p ∈ [6, 7, 8] ∨ nextPc z w p = 9 := by decide

local macro "pos" hst:ident : tactic =>
  `(tactic| exact ⟨by rw [$hst:ident] <;> rfl, fun _ => by rw [$hst:ident] <;> rfl,
    fun _ => by rw [$hst:ident] <;> rfl, fun e => absurd e (by decide)⟩)

/-- **The position and registers after a step, with any promise set**, from
`Static` and `X7 ≠ 0` at the `SUB` (shared by `pos_step` and
`TicketLoopSem.pos_step'`): the next position, `X3` kept except at the
`LDADDA`, `X7` kept except at the `SUB`, which lowers it by one. -/
theorem pos_step_st {x o c : BitVec 64} {u : Thread isa} {A : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : Static x o c u.st) {p : Nat}
    (hp : p ∈ tkLoopPcs) (hpc : u.st.st.2 = pcA p) (h7 : p = 14 → wn u.st.st.1.regs.X7 ≠ 0)
    (hs : stepOne Arch.armv8 u A mem = some outs) (ho : .ok oc ∈ outs) :
    oc.thread.st.st.2 = pcA (nextPc u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) p) ∧
      (p ≠ 4 → oc.thread.st.st.1.regs.X3 = u.st.st.1.regs.X3) ∧
      (p ≠ 14 → oc.thread.st.st.1.regs.X7 = u.st.st.1.regs.X7) ∧
      (p = 14 → wn oc.thread.st.st.1.regs.X7 + 1 = wn u.st.st.1.regs.X7) := by
  have hi := hp
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, -⟩ := s1 hS hs ho hpc; pos hst
  · obtain ⟨-, hst, -⟩ := s3 hS hs ho hpc
    by_cases hz : w32 u.st.st.1.regs.X7 = 0#32
    · rw [ite_eq_left hz] at hst
      have : nextPc u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) 3 = 17 := by
        simp [nextPc, (w32_zero_iff _).mp hz]
      rw [this]; pos hst
    · rw [ite_eq_right hz] at hst
      have : nextPc u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) 3 = 4 := by
        have hz' : wn u.st.st.1.regs.X7 ≠ 0 := fun e => hz ((w32_zero_iff _).mpr e)
        simp [nextPc, hz']
      rw [this]; pos hst
  · obtain ⟨tr, old, hst, -⟩ := SpinSemShape.spec_rmwo_p _ _ rfl
      (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    exact ⟨by rw [hst] <;> rfl, fun e => absurd rfl e, fun _ => by rw [hst] <;> rfl, fun e => absurd e (by decide)⟩
  · obtain ⟨ts, v, hst, -⟩ := s6 hS hs ho hpc; pos hst
  · obtain ⟨sf, hst, -⟩ := s7 hS hs ho hpc; pos hst
  · obtain ⟨-, hst, -⟩ := s8 hS hs ho hpc
    by_cases hz : u.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      have : nextPc u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) 8 = 9 := by simp [nextPc, hz]
      rw [this]; pos hst
    · rw [ite_eq_right hz] at hst
      have : nextPc u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) 8 = 6 := by simp [nextPc, hz]
      rw [this]; pos hst
  · obtain ⟨v, hst, -⟩ := s9 hS hs ho hpc; pos hst
  · obtain ⟨-, hst, -⟩ := s10 hS hs ho hpc; pos hst
  · obtain ⟨hst, -⟩ := SemShape.spec_store_p _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    pos hst
  · obtain ⟨-, hst, -⟩ := s12 hS hs ho hpc; pos hst
  · obtain ⟨hst, -⟩ := SemShape.spec_store_p _ _ (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    pos hst
  · obtain ⟨-, hst, -⟩ := s14 hS hs ho hpc
    have h7 : wn u.st.st.1.regs.X7 ≠ 0 := h7 rfl
    refine ⟨by rw [hst] <;> rfl, fun _ => by rw [hst] <;> rfl, fun e => absurd rfl e, fun _ => ?_⟩
    have := wn_sub1 _ h7
    rw [hst]; show (BitVec.setWidth 64 (u.st.st.1.regs.X7.toBitVec.take 32 - 1#32)).toNat % 2 ^ 32 + 1 = _
    omega
  · obtain ⟨-, hst, -⟩ := s15 hS hs ho hpc; pos hst
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- **The position and registers after a step**: the next position, `X3`
kept except at the `LDADDA`, `X7` kept except at the `SUB`, which lowers it
by one. -/
theorem pos_step {k : Nat} {x o c : BitVec 64} {m : Nat} {u : Thread isa} {A : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv k x o c m u) {p : Nat}
    (hp : p ∈ tkLoopPcs) (hpc : u.st.st.2 = pcA p) (hs : stepOne Arch.armv8 u A mem = some outs)
    (ho : .ok oc ∈ outs) :
    oc.thread.st.st.2 = pcA (nextPc u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) p) ∧
      (p ≠ 4 → oc.thread.st.st.1.regs.X3 = u.st.st.1.regs.X3) ∧
      (p ≠ 14 → oc.thread.st.st.1.regs.X7 = u.st.st.1.regs.X7) ∧
      (p = 14 → wn oc.thread.st.st.1.regs.X7 + 1 = wn u.st.st.1.regs.X7) :=
  pos_step_st h.st hp hpc (fun e => by subst e; exact h.pcinv (by decide) hpc) hs ho

/-- **A worker with no promise, not at its end, can take an instruction step
that leaves no promise** (moved from `LiveTicketLoopSem`, same full
name; `en_tinv` is an instance). -/
theorem _root_.Kraken.Promising.Live.TicketLoopSem.en_nil {x o c : BitVec 64} {u : Thread isa} {A : Nat} {mem : Memory} (h : SInv x o c u.st)
    (hp0 : u.prom = []) (hb : u.Bnd mem.last) (hne : u.st.st.2 ≠ pcA 17) :
    ∃ outs oc, stepOne Arch.armv8 u A mem = some outs ∧ .ok oc ∈ outs ∧ oc.thread.prom = [] := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  have hA : i ≠ 17 → At tkLoopWorker u.st i := fun h17 => hS.at hi h17 hpc
  have hd : ∀ {s : isa.State}, isa.exec u.st = some (.done s) →
      ∃ outs oc, stepOne Arch.armv8 u A mem = some outs ∧ .ok oc ∈ outs ∧ oc.thread.prom = [] :=
    fun hex => let ⟨outs, oc, h1, h2, h3⟩ := en_done Arch.armv8 A hex (mem := mem); ⟨outs, oc, h1, h2, h3.trans hp0⟩
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hd (exec_mov _ (hA (by decide)))
  · exact hd (exec_cbz _ (hA (by decide)))
  · exact en_rmw Arch.armv8 A rfl hp0 hb (exec_ldadda _ (hA (by decide)) hS.x0 hS.dx)
  · exact en_load Arch.armv8 A hp0 (exec_ldar _ (hA (by decide)) hS.x1 hS.dO)
  · exact hd (exec_cmp _ (hA (by decide))).choose_spec.1
  · exact hd (exec_bne _ (hA (by decide)))
  · exact en_load Arch.armv8 A hp0 (exec_ldr_c _ (hA (by decide)) hS.x2 hS.dc)
  · exact hd (exec_add5 _ (hA (by decide)))
  · exact en_store Arch.armv8 A hp0 hb (exec_str_c _ (hA (by decide)) hS.x2 hS.dc)
  · exact hd (exec_add4 _ (hA (by decide)))
  · exact en_store Arch.armv8 A hp0 hb (exec_stlr _ (hA (by decide)) hS.x1 hS.dO)
  · exact hd (exec_sub _ (hA (by decide)))
  · exact hd (exec_b_round _ (hA (by decide)))
  · exact absurd hpc hne

/-- **A promise-free worker not at the end can take an instruction step.** -/
theorem en_tinv {k : Nat} {x o c : BitVec 64} {m : Nat} {u : Thread isa} {A : Nat} {mem : Memory}
    (h : TInv k x o c m u) (hb : u.Bnd mem.last) (hne : u.st.st.2 ≠ pcA 17) :
    ∃ outs oc, stepOne Arch.armv8 u A mem = some outs ∧ .ok oc ∈ outs ∧ oc.thread.prom = [] := by
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  exact TicketLoopSem.en_nil ⟨h.st, i, hi, hpc⟩ h.prom hb hne

/-! ## Along a promise-free semantic trace -/

/-- The value of `owner` at index `i`. -/
abbrev Mo {fuel : Nat} (tr : TraceSem Arch.armv8 fuel isa) (o : BitVec 64) (i : Nat) : Nat :=
  ((tr.cfg i).mem.finalVal (L4 o)).toNat

section Trace

variable {fuel k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.armv8 fuel isa}

omit hv in
/-- Without promise steps, a step of the trace is a final stutter or an
instruction step. -/
theorem step_or (hpf : PromiseFreeSem Arch.armv8 fuel tr.cfg) (i : Nat) : tr.cfg (i + 1) = tr.cfg i ∨
    ∃ tid, InstrBy Arch.armv8 tid (tr.cfg i) (tr.cfg (i + 1)) ∧ StepSem Arch.armv8 fuel tid (tr.cfg i) (tr.cfg (i + 1)) := by
  rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
  · refine .inr ⟨tid, ?_, hst⟩
    rcases hst with ⟨t, outs, oc, ht, hso, ho, -, he⟩ | hp
    · exact ⟨t, outs, oc, ht, hso, ho, he⟩
    · exact absurd hp (hpf i tid)
  · exact .inl he

variable (hs : TkLoopStart k N x o c states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
  (hpf : PromiseFreeSem Arch.armv8 fuel tr.cfg)

include hs h0 hpf

/-- **The invariant along a promise-free semantic trace.** -/
theorem trace_inv (i : Nat) : ∃ xc m, InvL k N x o c xc m (tr.cfg i) := by
  induction i with
  | zero => exact ⟨0, 0, h0 ▸ inv_init hs⟩
  | succ i ih =>
    obtain ⟨xc, m, h⟩ := ih
    rcases step_or hpf i with he | ⟨tid, hi, hst⟩
    · rw [he]; exact ⟨xc, m, h⟩
    · rcases step_inv h (h.bnd.semStep hst) hi with ⟨xc', h', -⟩ | h'
      · exact ⟨xc', m, h'⟩
      · exact ⟨xc, m + 1, h'⟩

theorem inv_at (i : Nat) : ∃ xc, InvL k N x o c xc (Mo tr o i) (tr.cfg i) := by
  obtain ⟨xc, m, h⟩ := trace_inv hs h0 hpf i
  have := h.fo; subst this; exact ⟨xc, h⟩

theorem M_step (i : Nat) : (Mo tr o (i + 1) = Mo tr o i ∧
    (tr.cfg (i + 1)).mem.lastWrite (L4 o) = (tr.cfg i).mem.lastWrite (L4 o)) ∨ Mo tr o (i + 1) = Mo tr o i + 1 := by
  rcases step_or hpf i with he | ⟨tid, hi, hst⟩
  · simp only [Mo]; rw [he]; exact .inl ⟨rfl, rfl⟩
  obtain ⟨xc, h⟩ := inv_at hs h0 hpf i
  rcases step_inv h (h.bnd.semStep hst) hi with ⟨xc', h', hl⟩ | h'
  · exact .inl ⟨h'.fo, hl⟩
  · exact .inr h'.fo

theorem M_mono (i j : Nat) (hij : i ≤ j) : Mo tr o i ≤ Mo tr o j := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step k _ ih => show _ ≤ Mo tr o (k + 1); rcases M_step hs h0 hpf k with ⟨e, -⟩ | e <;> omega

/-- A thread not at the end is instruction-enabled. -/
theorem en_at {T j : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[T]? = some u) (hne : u.st.st.2 ≠ pcA 17) :
    InstrEnabledSem Arch.armv8 fuel T (tr.cfg j) := by
  obtain ⟨xc, I⟩ := inv_at hs h0 hpf j
  obtain ⟨outs, oc, h1, h2, h3⟩ := en_tinv (A := T) (I.thr T u hu) (I.bnd T u hu) hne
  exact instrEnabledSem_of_step hu h1 h2 h3

/-- The per-thread invariant of a thread at index `j`. -/
theorem tinv_at {T j : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[T]? = some u) :
    TInv k x o c (Mo tr o j) u :=
  let ⟨_, I⟩ := inv_at hs h0 hpf j; I.thr T u hu

/-- **A holder of a constant `owner` keeps its ticket**: its only way to give
it up, the `STLR`, raises `owner`. -/
theorem holder_persist {n m H : Nat} (hM : ∀ j, n ≤ j → Mo tr o j = m) {u : Thread isa}
    (hu : (tr.cfg n).threads[H]? = some u) (hk : Ticketed u) (htk : tk u = m) :
    ∀ j, n ≤ j → ∃ u, (tr.cfg j).threads[H]? = some u ∧ Ticketed u ∧ tk u = m := by
  intro j hj
  induction hj with
  | refl => exact ⟨u, hu, hk, htk⟩
  | @step j hnj ih =>
    obtain ⟨u, hu, hk, htk⟩ := ih
    rcases tr.same_or_instr j H hu with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
    · exact ⟨u', hu', by unfold Ticketed; rw [e1]; exact hk, by unfold tk; rw [e1]; exact htk⟩
    · obtain ⟨xc, I⟩ := inv_at hs h0 hpf j
      have hxc : xc + 1 < 2 ^ 32 := by have := I.xcle; have := I.Nk32; omega
      cases thread_step (I.thr H u hu) hxc I.mxc I.fx (I.own H u hu) I.ov hso ho with
      | same _ _ htk' hk' => exact ⟨oc.thread, tr.wt_self hu he, htk'.mpr hk, (hk' hk).trans htk⟩
      | tkt _ _ _ _ h0' => exact absurd hk h0'
      | rel v hv hm =>
        have e1 := hM (j + 1) (Nat.le_succ_of_le hnj)
        have e2 := hM j hnj
        simp only [Mo, he, Config.withThread, hm, finalVal_append, ite_true] at e1 e2
        omega

/-! ## The holder of a constant `owner` -/

section Holder

variable {n m H : Nat} (hwfi : WeakFairInstrSem Arch.armv8 fuel tr.cfg)
  (hM : ∀ j, n ≤ j → Mo tr o j = m)
  (hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 o) = (tr.cfg n).mem.lastWrite (L4 o))
  (hH : ∀ j, n ≤ j → ∃ u, (tr.cfg j).threads[H]? = some u ∧ Ticketed u ∧ tk u = m)

include hwfi hM hL hH

theorem hold (j : Nat) (hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) :
    TInv k x o c m u ∧ tk u = m ∧ ∃ p ∈ tkHeld, u.st.st.2 = pcA p := by
  obtain ⟨u', hu', hk, htk⟩ := hH j hj
  rw [hu] at hu'; cases hu'
  have hT := tinv_at hs h0 hpf hu
  rw [hM j hj] at hT
  exact ⟨hT, htk, hk⟩

theorem henH {j : Nat} (hj : n ≤ j) : InstrEnabledSem Arch.armv8 fuel H (tr.cfg j) := by
  obtain ⟨u, hu, -⟩ := hH j hj
  obtain ⟨-, -, p, hp, hpc⟩ := hold hs h0 hpf hwfi hM hL hH _ hj _ hu
  exact en_at hs h0 hpf hu fun e => held_ne17 p hp (addrOf_inj (held_sub p hp) (by decide) (hpc.symm.trans e))

theorem advH (j : Nat) (_hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) :
    ∃ k, j ≤ k ∧ ∃ u', (tr.cfg k).threads[H]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∃ outs oc, stepOne Arch.armv8 u' H (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
        tr.cfg (k + 1) = (tr.cfg k).withThread H oc.thread oc.mem :=
  tr.adv (hwfi H ⟨n, fun _ hj => henH hs h0 hpf hwfi hM hL hH hj⟩) hu

/-- `H` never gets through its critical section: its `STLR` would raise `m`. -/
theorem cs_false : ∀ d p j, p + d = 13 → 9 ≤ p → n ≤ j → ∀ u, (tr.cfg j).threads[H]? = some u →
    u.st.st.2 = pcA p → False := by
  intro d
  induction d with
  | zero =>
    intro p j hp _ hj u hu hpc
    obtain rfl : p = 13 := by omega
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := advH hs h0 hpf hwfi hM hL hH _ hj _ hu
    obtain ⟨hT, -, -⟩ := hold hs h0 hpf hwfi hM hL hH _ (Nat.le_trans hj hk) _ hu'
    have hpc' : u'.st.st.2 = pcA 13 := by rw [e1]; exact hpc
    obtain ⟨hm, -, -⟩ := s13 hT.st hT.prom hso ho hpc'
    have h4 := (hT.pcinv (by decide) hpc').2.2
    have e := hM (k + 1) (by omega)
    simp only [Mo, he, Config.withThread, hm, finalVal_append, ite_true] at e
    simp [BitVec.toNat_setWidth, wn] at h4 e; omega
  | succ d ih =>
    intro p j hp h9 hj u hu hpc
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := advH hs h0 hpf hwfi hM hL hH _ hj _ hu
    obtain ⟨hT, -, -⟩ := hold hs h0 hpf hwfi hM hL hH _ (Nat.le_trans hj hk) _ hu'
    have hp' : p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 := by omega
    have hpt : p ∈ tkLoopPcs := by rcases hp' with rfl | rfl | rfl | rfl <;> decide
    have hn := (pos_step hT hpt (by rw [e1]; exact hpc) hso ho).1
    have e : nextPc u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) p = p + 1 := by
      rcases hp' with rfl | rfl | rfl | rfl <;> rfl
    rw [e] at hn
    exact ih (p + 1) (k + 1) (by omega) (by omega) (by omega) _ (tr.wt_self hu' he) hn

theorem cs_false' (j : Nat) (hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) {p : Nat}
    (hp : p ∈ [9, 10, 11, 12, 13]) (hpc : u.st.st.2 = pcA p) : False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  exact cs_false hs h0 hpf hwfi hM hL hH (13 - p) p j (by omega) (by omega) hj u hu hpc

/-- `H` spins: positions 6–8. -/
theorem posH (j : Nat) (hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) :
    ∃ p ∈ [6, 7, 8], u.st.st.2 = pcA p := by
  obtain ⟨-, -, p, hp, hpc⟩ := hold hs h0 hpf hwfi hM hL hH _ hj _ hu
  simp only [tkHeld, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨_, by decide, hpc⟩
    | exact (cs_false' hs h0 hpf hwfi hM hL hH _ hj _ hu (by decide) hpc).elim

/-- `H`'s spin cells (`LDAR`, `CMP`, `B.NE`, critical section from 9) as
`TkHolderP.SpinCells`. -/
private theorem cells : TkHolderP.SpinCells Arch.armv8 tr.cfg (L4 o) H n m (fun s => s.st.2 = pcA 6)
    (fun s => s.st.2 = pcA 7) (fun s => s.st.2 = pcA 8) (fun s => s.st.2 = pcA 9)
    (fun s => wn s.st.1.regs.X3) (fun s => wn s.st.1.regs.X4) (fun s => s.st.1.status.z) where
  adv j hj u hu := advH hs h0 hpf hwfi hM hL hH j hj u hu
  tk j hj u hu _ := (hold hs h0 hpf hwfi hM hL hH j hj u hu).2.1
  lw := hL
  fval := hM
  cs j hj u hu hpc := cs_false' hs h0 hpf hwfi hM hL hH j hj u hu (p := 9) (by decide) hpc
  ld k' hk u outs oc hu hso ho hpc := by
    obtain ⟨hT, -⟩ := hold hs h0 hpf hwfi hM hL hH k' hk u hu
    obtain ⟨ts, v, hst, -, hv, -, -, ⟨ν, hlog⟩, -⟩ := s6 hT.st hso ho hpc
    refine ⟨by rw [hst], fun hc => ?_, ts, v, ν, hlog⟩
    obtain ⟨xc, hI⟩ := inv_at hs h0 hpf k'
    have := hI.Nk32; have := hI.xcle
    have hmx : ((tr.cfg k').mem.finalVal (L4 o)).toNat ≤ xc := hI.mxc
    rw [hst]; show (BitVec.setWidth 64 (BitVec.setWidth 32 v)).toNat % 2 ^ 32 = _
    rw [hv hc]; simp [BitVec.toNat_setWidth]
    omega
  cmp k' hk u outs oc hu hso ho hpc := by
    obtain ⟨hT, -⟩ := hold hs h0 hpf hwfi hM hL hH k' hk u hu
    obtain ⟨sf, hst, hz, -, -, hcoh⟩ := s7 hT.st hso ho hpc
    exact ⟨by rw [hst], by rw [hst]; exact hz, hcoh⟩
  bne k' hk u outs oc hu hso ho hpc := by
    obtain ⟨hT, -⟩ := hold hs h0 hpf hwfi hM hL hH k' hk u hu
    obtain ⟨-, hst, -, hcoh⟩ := s8 hT.st hso ho hpc
    refine ⟨?_, hcoh⟩
    rw [hst]; by_cases hz : u.st.st.1.status.z = true <;> simp [hz]

/-- `H` spins (`posH`), as a disjunction. -/
private theorem spinPos (j : Nat) (hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) :
    u.st.st.2 = pcA 6 ∨ u.st.st.2 = pcA 7 ∨ u.st.st.2 = pcA 8 := by
  obtain ⟨p, hp, hpc⟩ := posH hs h0 hpf hwfi hM hL hH j hj u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .inl hpc
  · exact .inr (.inl hpc)
  · exact .inr (.inr hpc)

/-- In the spin loop with an up-to-date view of `owner`, `H` enters the
critical section: contradiction (`TkHolderP.SpinCells.spin_false`). -/
theorem at_false {j : Nat} (hj : n ≤ j) {u : Thread isa} (hu : (tr.cfg j).threads[H]? = some u)
    (hc : (tr.cfg n).mem.lastWrite (L4 o) ≤ u.views.getCoh (L4 o)) : False :=
  (cells hs h0 hpf hwfi hM hL hH).spin_false hj hu (spinPos hs h0 hpf hwfi hM hL hH j hj u hu) hc

/-- `H` reads `owner` infinitely often (`TkHolderP.SpinCells.reads_inf`). -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg H (L4 o) ts i) :=
  (cells hs h0 hpf hwfi hM hL hH).reads_inf (spinPos hs h0 hpf hwfi hM hL hH)
    fun j hj => let ⟨u, hu, _⟩ := hH j hj; ⟨u, hu⟩

/-- **The holder of a constant `owner` cannot exist** (memory fairness). -/
theorem holder_false (hmf : MemFair Arch.armv8 tr.cfg) : False := by
  obtain ⟨u, hu, -⟩ := hH n (Nat.le_refl _)
  exact memFair_lastWrite_false hmf (reads_inf hs h0 hpf hwfi hM hL hH) hu fun _ hj _ ht' hc =>
    at_false hs h0 hpf hwfi hM hL hH hj ht' hc

end Holder

end Trace

/-! ## The theorems -/

/-- **Starvation-freedom per round, promise-free fragment** (semantic machine):
on a valid layout of `tkLoopWorker`, for every `fuel`, on every semantic trace
with no promise step from a start configuration under weak and memory
fairness, a thread waiting in round `r` eventually acquires in round `r`. -/
theorem ticket_loop_starve_pf (fuel : Nat) : TicketLoopStarvePFSem fuel := by
  intro k N x o c states initMem hs r tr h0 ⟨⟨hwf, hmf⟩, hpf⟩ T i ⟨t, ht, hsp, hr⟩
  apply Classical.byContradiction
  intro hnd
  have hwfi := weakFairInstrSem_loop hs tr h0 hwf
  have hsp' : ∃ p ∈ [6, 7, 8], t.st.st.2 = pcA p := by
    simp only [tkLoopSpinPcs, List.mem_map] at hsp
    obtain ⟨p, hp, e⟩ := hsp; exact ⟨p, hp, e.symm⟩
  -- `T` stays in its spin loop, with its ticket and its round
  have stay : ∀ j, i ≤ j → ∃ u, (tr.cfg j).threads[T]? = some u ∧ (∃ p ∈ [6, 7, 8], u.st.st.2 = pcA p) ∧
      u.st.st.1.regs.X3 = t.st.st.1.regs.X3 ∧ u.st.st.1.regs.X7 = t.st.st.1.regs.X7 := by
    intro j hj
    induction hj with
    | refl => exact ⟨t, ht, hsp', rfl, rfl⟩
    | @step j hij ih =>
      obtain ⟨u, hu, ⟨p, hp, hpc⟩, h3, h7⟩ := ih
      rcases tr.same_or_instr j T hu with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', ⟨p, hp, by rw [e1]; exact hpc⟩, by rw [e1]; exact h3, by rw [e1]; exact h7⟩
      · obtain ⟨hpt, hp4, hp14, -⟩ := spin_facts p hp
        obtain ⟨hn, h3', h7', -⟩ := pos_step (tinv_at hs h0 hpf hu) hpt hpc hso ho
        have hu' := tr.wt_self hu he
        have h3'' := (h3' hp4).trans h3
        have h7'' := (h7' hp14).trans h7
        rcases next_spin u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) p hp with hq | hq
        · exact ⟨oc.thread, hu', ⟨_, hq, hn⟩, h3'', h7''⟩
        · refine absurd ⟨j + 1, Nat.le_succ_of_le hij, oc.thread, hu', .inl ⟨?_, by rw [h7'']; exact hr⟩⟩ hnd
          rw [hn, hq]; exact List.mem_map_of_mem (by decide)
  -- `owner ≤ K` from `i` on
  have hb : ∀ j, i ≤ j → Mo tr o j ≤ wn t.st.st.1.regs.X3 := by
    intro j hj
    obtain ⟨u, hu, ⟨p, hp, hpc⟩, h3, -⟩ := stay j hj
    have hT := tinv_at hs h0 hpf hu
    rw [← h3]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact (hT.pcinv (by decide) hpc).2
    · exact (hT.pcinv (by decide) hpc).2.1
    · exact (hT.pcinv (by decide) hpc).2.1
  obtain ⟨n, hin, hc⟩ := SpinCommon.evconst (Mo tr o) (M_mono hs h0 hpf) _ i hb
  -- `owner` is constant from `n` on, and so is its last write
  have hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 o) = (tr.cfg n).mem.lastWrite (L4 o) := by
    intro j hj
    induction hj with
    | refl => rfl
    | @step k hle ih =>
      rcases M_step hs h0 hpf k with ⟨-, e⟩ | e
      · exact e.trans ih
      · have h1 : Mo tr o (k + 1) = Mo tr o n := hc (k + 1) (Nat.le_succ_of_le hle)
        have h2 := hc k hle; omega
  -- the holder of `owner`
  obtain ⟨xc, hI⟩ := inv_at hs h0 hpf n
  obtain ⟨un, hun, ⟨p, hp, hpc⟩, h3, -⟩ := stay n hin
  have hkn : Ticketed un := (ticketed_iff (spin_facts p hp).1 hpc).mpr (spin_facts p hp).2.2.2.1
  have hlt := hI.tkLt T un hun hkn
  have hbn := hb n hin
  unfold tk at hlt; rw [h3] at hlt
  obtain ⟨H, u, hu, hku, hkm⟩ := hI.tkSurj (Mo tr o n) (Nat.le_refl _) (by omega)
  exact holder_false hs h0 hpf hwfi (fun j hj => hc j hj) hL (holder_persist hs h0 hpf (fun j hj => hc j hj) hu hku hkm)
    hmf

/-- **Every thread completes all its rounds, promise-free fragment** (semantic
machine): on a valid layout of `tkLoopWorker`, for every `fuel`. -/
theorem ticket_loop_finish_pf (fuel : Nat) : TicketLoopFinishPFSem fuel := by
  intro k N x o c states initMem hs tr h0 hF T i ⟨t, ht⟩
  obtain ⟨⟨hwf, hmf⟩, hpf⟩ := hF
  apply Classical.byContradiction
  intro hnf
  have hwfi := weakFairInstrSem_loop hs tr h0 hwf
  have hst := ticket_loop_starve_pf fuel k N x o c states initMem hs
  have hen : ∀ j, i ≤ j → InstrEnabledSem Arch.armv8 fuel T (tr.cfg j) := fun j hj => by
    obtain ⟨u, hu⟩ := tr.get_persist ht j hj
    exact en_at hs h0 hpf hu fun e => hnf ⟨j, hj, u, hu, e⟩
  suffices H : ∀ v j, i ≤ j → ∀ u p, (tr.cfg j).threads[T]? = some u → p ∈ tkLoopPcs → u.st.st.2 = pcA p →
      20 * wn u.st.st.1.regs.X7 + rk p ≤ v → False by
    obtain ⟨-, -, -, -, p, hp, hpc, -⟩ := tinv_at hs h0 hpf ht
    exact H _ i (Nat.le_refl _) t p ht hp hpc (Nat.le_refl _)
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
  intro j hj u p hu hp hpc hv
  have hT := tinv_at hs h0 hpf hu
  by_cases h17 : p = 17
  · subst h17; exact hnf ⟨j, hj, u, hu, hpc⟩
  by_cases hsp : p ∈ [6, 7, 8]
  · -- waiting in round `k - X7`: starvation-freedom gets it out
    have hk7 := hT.k7
    obtain ⟨j', hj', u', hu', hd⟩ := hst (k - wn u.st.st.1.regs.X7) tr h0 ⟨⟨hwf, hmf⟩, hpf⟩ T j
      ⟨u, hu, by rw [hpc]; exact List.mem_map_of_mem hsp, by omega⟩
    obtain ⟨-, -, hk7', -, q, hq, hqc, -⟩ := tinv_at hs h0 hpf hu'
    refine ih _ ?_ j' (by omega) u' q hu' hq hqc (Nat.le_refl _)
    have hrq := rk_le q hq
    rcases hd with ⟨hcs, h7⟩ | h7
    · simp only [tkLoopCsPcs, List.mem_map] at hcs
      obtain ⟨q', hq', e⟩ := hcs
      obtain rfl := addrOf_inj hq (cs_facts q' hq').1 (hqc.symm.trans e.symm)
      have := (cs_facts q hq').2
      have := (spin_facts p hsp).2.2.2.2
      omega
    · have := (spin_facts p hsp).2.2.2.2
      omega
  · -- any other position: its next step lowers the rank
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv (hwfi T ⟨i, hen⟩) hu
    have hpc' : u'.st.st.2 = pcA p := by rw [e1]; exact hpc
    obtain ⟨hn, -, h7, h14⟩ := pos_step (tinv_at hs h0 hpf hu') hp hpc' hso ho
    have hq := nextPc_mem u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) p hp
    refine ih _ ?_ (k' + 1) (by omega) _ _ (tr.wt_self hu' he) hq hn (Nat.le_refl _)
    have e7 : u'.st.st.1.regs.X7 = u.st.st.1.regs.X7 := by rw [e1]
    by_cases h14' : p = 14
    · subst h14'
      have := h14 rfl
      have : nextPc u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) 14 = 15 := rfl
      rw [this]; simp only [rk] at hv ⊢; rw [e7] at *; omega
    · have := rk_lt u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) p hp hsp h14' h17
      have e7' : wn u'.st.st.1.regs.X7 = wn u.st.st.1.regs.X7 := by rw [e7]
      rw [h7 h14']; omega

/-- **Repeated-acquire ticket-lock liveness, promise-free fragment** (semantic
machine): starvation-freedom per round and completion of all rounds. -/
theorem ticket_loop_live_pf (fuel : Nat) : TicketLoopLivePFSem fuel :=
  ⟨ticket_loop_starve_pf fuel, ticket_loop_finish_pf fuel⟩

/-! ## A concrete instance -/

/-- A concrete layout of `tkLoopWorker`: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def tkLoopLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize tkLoopWorker

instance tkLoopValid : Executable.ValidLayout (tkLoopLayout tkLoopWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- `ticket_loop_live_pf` at the concrete layout `tkLoopLayout`: no
hypothesis left. -/
theorem ticket_loop_live_pf_concrete (fuel : Nat) : @TicketLoopLivePFSem tkLoopLayout fuel :=
  @ticket_loop_live_pf tkLoopLayout tkLoopValid fuel

end Kraken.Promising.Live.TicketLoopPF

#print axioms Kraken.Promising.Live.TicketLoopPF.ticket_loop_live_pf_concrete
