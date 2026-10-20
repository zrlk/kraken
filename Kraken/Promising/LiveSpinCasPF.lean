/-
**Stage 3: promise-free deadlock-freedom of the
AArch64 CAS spinlock under weak fairness and memory fairness**
(`spin_cas_live_pf`), on a valid layout of `casTtasWorker`; and per-thread
liveness of its one-shot workers (`spin_cas_live_oneShot_pf`).

On a promise-free stuttering trace from a start configuration,
`SpinCasInv.trace_inv` gives `InvC` at every index. A finished thread stays
finished (`done_mono`). The core lemma `stuck_false`: if from index `n` on
no thread newly finishes, then every thread is finished at `n`. Suppose `T`
is not.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n`. A holder
  stays a holder until its `STLR`, so it is always instruction-enabled, and
  weak fairness drives it through positions 5, 11–14 to its `STLR`, after
  which it is finished: a new finished thread.
- (b) Hence the lock is `0` (`lock_zero`, from `InvC.held`) and its last
  write is constant (`lw_const`) from `n` on.
- (c) `T` sits in its try/spin loop forever (`tpos`), always enabled, and
  reads the lock at its `LDR` infinitely often (`reads_inf`). Memory fairness
  brings its coherence view of the lock up to the last write, and the view
  never drops again; its next `LDR` reads `0`, `B try`, and its `CASA` reads
  `0 = W2` and writes: `T` holds the lock (`at_false`), against (a).

Deadlock-freedom is the core lemma at the waiting index. For the one-shot
workers, the set of finished threads is monotone and bounded, so it is
eventually constant; the core lemma there gives per-thread liveness. This is
a property of the one-shot programs, not starvation-freedom of the lock.

**Invalid layouts.** As for the ticket lock (`LiveTicketPF.lean`), the
theorem assumes `ValidLayout (layout casTtasWorker)`.
-/
import Kraken.Promising.LiveSpinCasInv
import Kraken.Promising.LiveSpinCommon
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.Live.SpinCasPF

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SpinCasInv Kraken.Promising.Live.SpinCommon
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

/-! ## Positions -/

/-- The position in `spPcs` at the address of position `k`. -/
def rep (k : Nat) : Nat := if k = 0 then 1 else if k = 2 then 3 else if k = 6 then 7 else if k = 10 then 11 else k

theorem addrOf_rep (k : Nat) : pcA (rep k) = pcA k := by
  unfold rep
  split
  · subst_vars; exact addrOf_0.symm
  split
  · subst_vars; exact addrOf_2.symm
  split
  · subst_vars; exact addrOf_6.symm
  split
  · subst_vars; exact addrOf_10.symm
  rfl

/-- A position of `spPcs` is up to the release iff it is below 15. -/
theorem pre_iff {i : Nat} (hi : i ∈ spPcs) : pcA i ∈ Spin.casPrePcs ↔ i < 15 := by
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := List.mem_map.mp h
    have hk := List.mem_range.mp hk
    have hr : rep k ∈ spPcs ∧ rep k < 15 := by
      have : ∀ k < 15, rep k ∈ spPcs ∧ rep k < 15 := by decide
      exact this k hk
    rw [← addrOf_rep] at e
    rw [← addrOf_inj hr.1 hi e]; exact hr.2
  · intro h; exact List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩

theorem getCoh_eq {t t' : Thread isa} (h : t'.views.coh = t.views.coh) (l : Loc) :
    t'.views.getCoh l = t.views.getCoh l :=
  SpinSwpStep.getCoh_congr h l

/-- **Enabledness**: a thread of an `InvC` configuration at a position other
than the end can take an instruction step. -/
theorem en_at {fuel : Nat} {l c : BitVec 64} {cfg : Config isa} (h : InvC l c cfg) {U : Nat} {t : Thread isa}
    (ht : cfg.threads[U]? = some t) {p : Nat} (hp : p ∈ [1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15])
    (hpc : t.st.st.2 = pcA p) : InstrEnabled Arch.armv8 fuel U cfg := by
  have hT := h.thr U t ht
  have hS := hT.st
  have hb' := h.bnd U t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (exec_mov3 _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (exec_mov2 _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_rmwo Arch.armv8 U rfl hT.prom hb'
      (exec_casa _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (exec_cbz _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 U hT.prom
      (exec_ldr_l _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl) (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (exec_cbnz _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (exec_b_try _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 U hT.prom
      (exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dc) (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (exec_add5 _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 U hT.prom hb'
      (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dc)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 U hT.prom hb'
      (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (exec_b_done _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)

section Trace

variable {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceS Arch.armv8 fuel isa}
  (hs : Spin.CasStart l c states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
  (hpf : PromiseFree Arch.armv8 tr.cfg)

include hs h0 hpf

theorem inv_at (i : Nat) : InvC l c (tr.cfg i) := trace_inv hs tr h0 hpf i

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : Spin.CasDone U (tr.cfg j)) : Spin.CasDone U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases step_or hpf j with he | ⟨tid, ⟨u, outs, oc, hu, hso, ho, he⟩, -⟩
  · rw [he]; exact ⟨t, ht, hpc⟩
  rw [he]
  by_cases e : U = tid
  · subst e; rw [ht] at hu; cases hu
    have hT := (inv_at hs h0 hpf j).thr U t ht
    obtain ⟨i, hi, hpi, -⟩ := hT.pc
    have h15 : ¬ i < 15 := fun h => hpc (hpi ▸ (pre_iff hi).mpr h)
    have : i = 15 ∨ i = 17 := by
      simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    rcases this with rfl | rfl
    · obtain ⟨-, hst, -⟩ := s15 hT.st hso ho hpi
      refine ⟨_, wt_tid ht, ?_⟩
      rw [hst, pre_iff (by decide)]; omega
    · rw [stepOne_end hT.st hpi] at hso; cases hso
  · exact ⟨t, by rw [wt_ne hu e]; exact ht, hpc⟩

theorem done_mono {j U : Nat} (hd : Spin.CasDone U (tr.cfg j)) : ∀ k, j ≤ k → Spin.CasDone U (tr.cfg k) := by
  intro k hk
  induction hk with
  | refl => exact hd
  | @step k _ ih => exact done_step hs h0 hpf k U ih

/-! ## The core lemma -/

section Stuck

variable {n : Nat} (hnd : ∀ j, n ≤ j → ∀ U, Spin.CasDone U (tr.cfg j) → Spin.CasDone U (tr.cfg n))
  (hwf : WeakFairInstr Arch.armv8 fuel tr.cfg)

include hnd hwf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ Spin.CasDone U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ Spin.CasDone U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hs h0 hpf (hnd k (by omega) U hd) j hj)

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder t) : False := by
  have hnot : ∀ k, j ≤ k → ¬ Spin.CasDone H (tr.cfg k) := by
    refine not_done hs h0 hpf hnd hwf hj fun ⟨t', ht', hpc⟩ => ?_
    rw [ht] at ht'; cases ht'
    obtain ⟨p, hp, hpc'⟩ := hh.pos
    refine hpc (hpc' ▸ (pre_iff ?_).mpr ?_) <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  have hold : ∀ k, j ≤ k → ∃ u, (tr.cfg k).threads[H]? = some u ∧ Holder u := by
    intro k hk
    induction hk with
    | refl => exact ⟨t, ht, hh⟩
    | @step k hjk ih =>
      obtain ⟨u, hu, hhu⟩ := ih
      rcases step_or hpf k with he | ⟨tid, ⟨u', outs, oc, hu', hso, ho, he⟩, -⟩
      · rw [he]; exact ⟨u, hu, hhu⟩
      by_cases e : H = tid
      · subst e; rw [hu] at hu'; cases hu'
        have hT := (inv_at hs h0 hpf k).thr H u hu
        cases thread_step hT hso ho with
        | quiet _ _ hh' => exact ⟨_, wt_self hu he, hh' hhu⟩
        | acq _ _ _ hh' => exact ⟨_, wt_self hu he, hh'⟩
        | rel _ _ _ hpc =>
          refine absurd ⟨_, wt_self hu he, ?_⟩ (hnot (k + 1) (Nat.le_succ_of_le hjk))
          rw [hpc, pre_iff (by decide)]; omega
      · exact ⟨u, by rw [he, wt_ne hu' e]; exact hu, hhu⟩
  have hen : ∀ k, j ≤ k → InstrEnabled Arch.armv8 fuel H (tr.cfg k) := fun k hk => by
    obtain ⟨u, hu, hhu⟩ := hold k hk
    obtain ⟨p, hp, hpc⟩ := hhu.pos
    exact en_at (inv_at hs h0 hpf k) hu (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc
  have nxt := adv hpf hwf hen
  have c14 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 14 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s14 hT.st hT.prom hso ho hpc
    refine hnot (k' + 1) (by omega) ⟨_, wt_self hu' he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  have c13 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 13 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s13 hT.st hT.prom hso ho hpc
    exact c14 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c12 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 12 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s12 hT.st hso ho hpc
    exact c13 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c11 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 11 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨ts, v, hst, -⟩ := s11 hT.st hso ho hpc
    exact c12 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  rcases hh with ⟨hpc, hz⟩ | hpc
  · obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt j (Nat.le_refl _) ht
    have hT := (inv_at hs h0 hpf k').thr H t hu'
    obtain ⟨-, hst, -⟩ := s5 hT.st hso ho hpc
    rw [ite_eq_left hz] at hst
    exact c11 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c11 j (Nat.le_refl _) t ht hpc
    · exact c12 j (Nat.le_refl _) t ht hpc
    · exact c13 j (Nat.le_refl _) t ht hpc
    · exact c14 j (Nat.le_refl _) t ht hpc

/-- **(b) The lock is `0` from `n` on.** -/
theorem lock_zero (j : Nat) (hj : n ≤ j) : (tr.cfg j).mem.finalVal (L4 l) = 0 :=
  Classical.byContradiction fun hne =>
    let ⟨_, _, hu, hh⟩ := (inv_at hs h0 hpf j).held hne
    holder_false hs h0 hpf hnd hwf hj hu hh

/-- **(b) The lock's last write is constant from `n` on.** -/
theorem lw_const : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 l) = (tr.cfg n).mem.lastWrite (L4 l) := by
  intro j hj
  induction hj with
  | refl => rfl
  | @step k hk ih =>
    rcases step_or hpf k with he | ⟨tid, hi, hm⟩
    · rw [he]; exact ih
    obtain ⟨-, h | ⟨_, hu, hh⟩ | ⟨_, hu, hh⟩⟩ := step_inv (inv_at hs h0 hpf k) ((inv_at hs h0 hpf k).bnd.succ hm) hi
    · exact h.trans ih
    · exact (holder_false hs h0 hpf hnd hwf (Nat.le_succ_of_le hk) hu hh).elim
    · exact (holder_false hs h0 hpf hnd hwf hk hu hh).elim

/-! ### (c) A thread that is not finished -/

section Waiter

variable {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
  (hT1 : ¬ Spin.CasDone T (tr.cfg n))

include hT0 hT1

/-- `T` stays in its try/spin loop, and at the `CBZ` it has `W2 ≠ 0`. -/
theorem tpos (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t) :
    ∃ p ∈ [1, 3, 4, 5, 7, 8, 9], t.st.st.2 = pcA p ∧ (p = 5 → w32 t.st.st.1.regs.X2 ≠ 0#32) := by
  obtain ⟨i, hi, hpc, -⟩ := ((inv_at hs h0 hpf j).thr T t ht).pc
  have hnd' := not_done hs h0 hpf hnd hwf (Nat.le_refl n) hT1 j hj
  have hlt : i < 15 := Classical.byContradiction fun h =>
    hnd' ⟨t, ht, fun hm => h ((pre_iff hi).mp (hpc ▸ hm))⟩
  have hnh : ¬ Holder t := fun hh => holder_false hs h0 hpf hnd hwf hj ht hh
  have hi' := hi
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  any_goals (exfalso; omega)
  any_goals (exfalso; exact hnh (holder_of_pc (of_decide_eq_true rfl) hpc))
  all_goals refine ⟨_, by decide, hpc, fun e => ?_⟩
  all_goals first | (cases e; done) | exact fun hz => hnh (.inl ⟨hpc, hz⟩)

theorem henT : ∀ j, n ≤ j → InstrEnabled Arch.armv8 fuel T (tr.cfg j) := fun j hj => by
  obtain ⟨t, ht⟩ := get_persist hpf hT0 j hj
  obtain ⟨p, hp, hpc, -⟩ := tpos hs h0 hpf hnd hwf hT0 hT1 _ hj ht
  exact en_at (inv_at hs h0 hpf j) ht (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc

/-- `T` reads the lock infinitely often. -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg T (L4 l) ts i) := by
  have nxt := adv hpf hwf (henT hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos hs h0 hpf hnd hwf hT0 hT1
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.armv8 tr.cfg T (L4 l) ts k
  have r7 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 7 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨ts, v, -, -, -, -, -, ⟨ν, hlog⟩, -⟩ := s7 hT.st hso ho hpc
    exact ⟨k, hk, ts, t, outs, oc, htk, hso, ho, he, v, ν, hlog⟩
  have r5 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 5 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨p, hp, hpc', hz⟩ := tp _ (Nat.le_trans hj hk) htk
    obtain rfl := addrOf_inj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by decide) (hpc'.symm.trans hpc)
    obtain ⟨-, hst, -⟩ := s5 hT.st hso ho hpc
    rw [ite_eq_right (hz rfl)] at hst
    obtain ⟨k', hk', h⟩ := r7 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r4 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨tr', old, hst, -⟩ := s4 hT.st hT.prom hso ho hpc
    obtain ⟨k', hk', h⟩ := r5 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r3 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s3 hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r4 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r9 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 9 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s9 hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r1 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s1 hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r8 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 8 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s8 hT.st hso ho hpc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      obtain ⟨k', hk', h⟩ := r9 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
      exact ⟨k', by omega, h⟩
    · rw [ite_eq_right hz] at hst
      obtain ⟨k', hk', h⟩ := r7 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
      exact ⟨k', by omega, h⟩
  intro m
  obtain ⟨t, ht⟩ := get_persist hpf hT0 (max n m) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left n m
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  have hR : R (max n m) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r1 _ hj t ht hpc
    · exact r3 _ hj t ht hpc
    · exact r4 _ hj t ht hpc
    · exact r5 _ hj t ht hpc
    · exact r7 _ hj t ht hpc
    · exact r8 _ hj t ht hpc
    · exact r9 _ hj t ht hpc
  obtain ⟨k, hk, h⟩ := hR
  exact ⟨k, by omega, h⟩

/-- **(c) With an up-to-date view of the lock, `T` acquires it**: contradiction. -/
theorem at_false {j : Nat} (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t)
    (hc : (tr.cfg n).mem.lastWrite (L4 l) ≤ t.views.getCoh (L4 l)) : False := by
  have nxt := adv hpf hwf (henT hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos hs h0 hpf hnd hwf hT0 hT1
  have lw := lw_const hs h0 hpf hnd hwf
  have lz := lock_zero hs h0 hpf hnd hwf
  let LW := (tr.cfg n).mem.lastWrite (L4 l)
  let Q (p : Nat) : Prop := ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA p →
    LW ≤ t.views.getCoh (L4 l) → False
  have p4 : Q 4 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    have hz : w32 t.st.st.1.regs.X2 = 0#32 := hT.pcinv (by decide) hpc
    obtain ⟨tr', old, hst, -, hold, -, hcase⟩ := s4 hT.st hT.prom hso ho hpc
    have hold := hold (by rw [lw k (by omega)]; exact hc)
    rw [lz _ (by omega)] at hold
    subst hold
    rcases hcase with ⟨hne, -⟩ | ⟨-, -⟩
    · exact hne (by rw [hz]; rfl)
    · refine holder_false hs h0 hpf hnd hwf (j := k + 1) (by omega) (wt_self htk he) (.inl ⟨by rw [hst], ?_⟩)
      rw [hst]; rfl
  have p3 : Q 3 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s3 hT.st hso ho hpc
    exact p4 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  have p9 : Q 9 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s9 hT.st hso ho hpc
    exact p3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  have p1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s1 hT.st hso ho hpc
    exact p3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  have p8z : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 8 →
      w32 t.st.st.1.regs.X2 = 0#32 → LW ≤ t.views.getCoh (L4 l) → False := by
    intro j hj t ht hpc hz hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s8 hT.st hso ho hpc
    rw [ite_eq_left hz] at hst
    exact p9 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  have p7 : Q 7 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨ts, v, hst, -, hv, -, -, -, hmono⟩ := s7 hT.st hso ho hpc
    have hv := hv (by rw [lw k (by omega)]; exact hc)
    rw [lz _ (by omega)] at hv
    subst hv
    exact p8z (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [hst]; rfl)
      (Nat.le_trans hc (hmono _))
  have p5 : Q 5 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨p, hp, hpc', hz⟩ := tp _ (Nat.le_trans hj hk) htk
    obtain rfl := addrOf_inj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by decide) (hpc'.symm.trans hpc)
    obtain ⟨-, hst, -, hcoh⟩ := s5 hT.st hso ho hpc
    rw [ite_eq_right (hz rfl)] at hst
    exact p7 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  have p8 : Q 8 := by
    intro j hj t ht hpc hc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · exact p8z j hj t ht hpc hz hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s8 hT.st hso ho hpc
    rw [ite_eq_right hz] at hst
    exact p7 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p1 j hj t ht hpc hc
  · exact p3 j hj t ht hpc hc
  · exact p4 j hj t ht hpc hc
  · exact p5 j hj t ht hpc hc
  · exact p7 j hj t ht hpc hc
  · exact p8 j hj t ht hpc hc
  · exact p9 j hj t ht hpc hc

end Waiter

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. -/
theorem stuck_false (hmf : MemFair Arch.armv8 tr.cfg) {T : Nat} {tT : Thread isa}
    (hT0 : (tr.cfg n).threads[T]? = some tT) (hT1 : ¬ Spin.CasDone T (tr.cfg n)) : False := by
  exact memFair_lastWrite_false hmf (reads_inf hs h0 hpf hnd hwf hT0 hT1) hT0 fun _ hj _ ht' hc =>
    at_false hs h0 hpf hnd hwf hT0 hT1 hj ht' hc

end Stuck

omit hs h0 hpf in
/-- `SpinCommon.size_eq`. -/
theorem size_eq (hpf : PromiseFree Arch.armv8 tr.cfg) :
    ∀ j, (tr.cfg j).threads.size = (tr.cfg 0).threads.size :=
  SpinCommon.size_eq hpf

end Trace

/-! ## The theorems -/

theorem wait_not_done {tid : Nat} {cfg : Config isa} (hw : Spin.CasWaiting tid cfg) : ¬ Spin.CasDone tid cfg := by
  obtain ⟨t, ht, hpc⟩ := hw
  rintro ⟨t', ht', hpc'⟩
  rw [ht] at ht'; cases ht'
  apply hpc'
  obtain ⟨k, hk, e⟩ := List.mem_map.mp hpc
  rw [← e]
  refine List.mem_map.mpr ⟨k, List.mem_range.mpr ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega

/-- **Promise-free deadlock-freedom of the CAS spinlock** (Stage 3,
promise-free fragment): on a valid layout of `casTtasWorker`, on every
promise-free stuttering trace from a start configuration under weak fairness
and memory fairness, if a thread waits in its try/spin loop, then some thread
not yet past its release later is. -/
theorem spin_cas_live_pf (fuel : Nat) : Spin.CasSpinLivePF fuel := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, Spin.CasDone U (tr.cfg j) → Spin.CasDone U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hs h0 hpf hnd (weakFairInstr_of_promiseFree hpf hwf) hmf ht (wait_not_done hw)

/-- **Per-thread liveness of the one-shot CAS workers** (promise-free
fragment): every waiting thread eventually gets past its release. A property
of these one-shot programs (from `stuck_false` and the finite number of
threads), not starvation-freedom of the lock. -/
theorem spin_cas_live_oneShot_pf (fuel : Nat) : Spin.CasSpinLiveOneShotPF fuel := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ Spin.CasDone tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := stable_of_mono (fun k j => Spin.CasDone k (tr.cfg j)) (tr.cfg 0).threads.size
    (fun k j ⟨_, ht, _⟩ => size_eq hpf j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hs h0 hpf hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist hpf ht n hin
  exact stuck_false hs h0 hpf (fun j hj U hd => hst j hj U hd) (weakFairInstr_of_promiseFree hpf hwf) hmf hu
    (hnd' n hin)

/-! ## A concrete instance -/

/-- A concrete layout of `casTtasWorker`: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def casLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize casTtasWorker

instance casValid : Executable.ValidLayout (casLayout casTtasWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- `spin_cas_live_pf` at the concrete layout `casLayout`: no hypothesis left. -/
theorem spin_cas_live_pf_concrete (fuel : Nat) : @Spin.CasSpinLivePF casLayout fuel :=
  @spin_cas_live_pf casLayout casValid fuel

/-- `spin_cas_live_oneShot_pf` at the concrete layout `casLayout`. -/
theorem spin_cas_live_oneShot_pf_concrete (fuel : Nat) : @Spin.CasSpinLiveOneShotPF casLayout fuel :=
  @spin_cas_live_oneShot_pf casLayout casValid fuel

end Kraken.Promising.Live.SpinCasPF
