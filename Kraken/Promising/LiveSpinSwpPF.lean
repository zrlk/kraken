/-
**Stage 3: promise-free deadlock-freedom of the
AArch64 SWP spinlocks under weak fairness and memory fairness**, for any
program with `SwpCode P` on a valid layout (`swp_live_pf_gen`,
`swp_live_oneShot_pf_gen`), instantiated to `spinlock_swp2/3`
(`spin_swp_live_pf`, `SWPA`/`STLR`) and `spinlock_swpl2/3`
(`spin_swpl_live_pf`, `SWPA`/`SWPL`), with one-shot corollaries and concrete
layouts.

The proof follows `LiveSpinCasPF.lean`. On a promise-free stuttering trace
from a start configuration, `SpinSwpInv.trace_inv` gives `InvS` at every
index; a finished thread stays finished (`done_mono`). The core lemma
`stuck_false`: if from index `n` on no thread newly finishes, every thread
is finished at `n`. Suppose `T` is not.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n`. A holder stays
  a holder until its release and is always enabled; weak fairness drives it
  through positions 4, 10–13 past its release: a new finished thread.
- (b) Hence the lock is `0` (`lock_zero`, from `InvS.held`) and its last
  write is constant (`lw_const`) from `n` on.
- (c) `T` sits in its try/spin loop forever (`tpos`), always enabled, and
  reads the lock at its `LDR` infinitely often (`reads_inf`). Memory fairness
  brings its coherence view of the lock up to the last write; the view never
  drops. Its next `LDR` reads `0`, `B try`, and its `SWPA` reads the final
  value `0` (every swap reads the last write, `InvS.own`): `T` holds the
  lock (`at_false`), against (a).

The one-shot corollary: the set of finished threads is monotone and bounded,
hence eventually constant; the core lemma there. A property of these
one-shot programs, not starvation-freedom of the lock.

**Invalid layouts.** As for the ticket and CAS locks, the theorems assume
`ValidLayout` of the worker's layout.
-/
import Kraken.Promising.LiveSpinSwpInv
import Kraken.Promising.LiveSpinCommon
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.Live.SpinSwpPF

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SpinSwpStep Kraken.Promising.Live.SpinSwpInv Kraken.Promising.Live.SpinCommon
open Kraken.Promising.Live.SpinSwp
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] {P : Program} [hv : Executable.ValidLayout (layout P)] (hC : SwpCode P)

set_option hygiene false in
local notation "pcA" => (layout P).addrOf

/-! ## Positions -/

/-- The position in `swPcs` at the address of position `k`. -/
def rep (k : Nat) : Nat := if k = 0 then 1 else if k = 2 then 3 else if k = 5 then 6 else if k = 9 then 10 else k

include hC in
theorem addrOf_rep (k : Nat) : pcA (rep k) = pcA k := by
  unfold rep
  split
  · subst_vars; exact hC.a0.symm
  split
  · subst_vars; exact hC.a2.symm
  split
  · subst_vars; exact hC.a5.symm
  split
  · subst_vars; exact hC.a9.symm
  rfl

include hC in
/-- A position of `swPcs` is up to the release iff it is below 14. -/
theorem pre_iff {i : Nat} (hi : i ∈ swPcs) : pcA i ∈ swpPrePcs P ↔ i < 14 := by
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := List.mem_map.mp h
    have hk := List.mem_range.mp hk
    have hr : rep k ∈ swPcs ∧ rep k < 14 := by
      have : ∀ k < 14, rep k ∈ swPcs ∧ rep k < 14 := by decide
      exact this k hk
    rw [← addrOf_rep hC] at e
    rw [← hC.inj hr.1 hi e]; exact hr.2
  · intro h; exact List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩

include hC in
/-- **Enabledness**: a thread of an `InvS` configuration at a position other
than the end can take an instruction step. -/
theorem en_at {fuel : Nat} {l c : BitVec 64} {cfg : Config isa} (h : InvS P l c cfg) {U : Nat} {t : Thread isa}
    (ht : cfg.threads[U]? = some t) {p : Nat} (hp : p ∈ [1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14])
    (hpc : t.st.st.2 = pcA p) : InstrEnabled Arch.armv8 fuel U cfg := by
  have hT := h.thr U t ht
  have hS := hT.st
  have hb' := h.bnd U t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (hC.mov _ (hS.at hC (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_rmw Arch.armv8 U rfl hT.prom hb'
      (hC.swpa _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (hC.cbz _ (hS.at hC (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 U hT.prom
      (hC.ldr _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl) (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (hC.cbnz _ (hS.at hC (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (hC.btry _ (hS.at hC (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 U hT.prom
      (hC.ldrc _ c (hS.at hC (by decide) (by decide) hpc) hS.x1 hS.dc) (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (hC.add _ (hS.at hC (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 U hT.prom hb'
      (hC.strc _ c (hS.at hC (by decide) (by decide) hpc) hS.x1 hS.dc)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · rcases hC.rel _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl with hex | ⟨k, hex⟩
    · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 U hT.prom hb' hex
      exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
    · obtain ⟨_, _, h1, h2, h3⟩ := en_rmw Arch.armv8 U (g := fun _ => 0#128) rfl hT.prom hb' hex
      exact instrEnabled_of Arch.armv8 U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 U (hC.bdone _ (hS.at hC (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.armv8 U ht h1 h2 (h3.trans hT.prom)

section Trace

variable {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceS Arch.armv8 fuel isa}
  (hs : SwpStartG (StartG P) l c states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
  (hpf : PromiseFree Arch.armv8 tr.cfg)

include hC hs h0 hpf

theorem inv_at (i : Nat) : InvS P l c (tr.cfg i) := trace_inv hC hs tr h0 hpf i

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : SwpDoneG P U (tr.cfg j)) : SwpDoneG P U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases step_or hpf j with he | ⟨tid, ⟨u, outs, oc, hu, hso, ho, he⟩, -⟩
  · rw [he]; exact ⟨t, ht, hpc⟩
  rw [he]
  by_cases e : U = tid
  · subst e; rw [ht] at hu; cases hu
    have hT := (inv_at hC hs h0 hpf j).thr U t ht
    obtain ⟨i, hi, hpi⟩ := hT.pc
    have h14 : ¬ i < 14 := fun h => hpc (hpi ▸ (pre_iff hC hi).mpr h)
    have : i = 14 ∨ i = 16 := by
      simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    rcases this with rfl | rfl
    · obtain ⟨-, hst, -⟩ := s14 hC hT.st hso ho hpi
      refine ⟨_, wt_tid ht, ?_⟩
      rw [hst, pre_iff hC (by decide)]; omega
    · rw [stepOne_end hT.st hpi] at hso; cases hso
  · exact ⟨t, by rw [wt_ne hu e]; exact ht, hpc⟩

theorem done_mono {j U : Nat} (hd : SwpDoneG P U (tr.cfg j)) : ∀ k, j ≤ k → SwpDoneG P U (tr.cfg k) := by
  intro k hk
  induction hk with
  | refl => exact hd
  | @step k _ ih => exact done_step hC hs h0 hpf k U ih

/-! ## The core lemma -/

section Stuck

variable {n : Nat} (hnd : ∀ j, n ≤ j → ∀ U, SwpDoneG P U (tr.cfg j) → SwpDoneG P U (tr.cfg n))
  (hwf : WeakFairInstr Arch.armv8 fuel tr.cfg)

include hnd hwf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ SwpDoneG P U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ SwpDoneG P U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hC hs h0 hpf (hnd k (by omega) U hd) j hj)

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder P t) : False := by
  have hnot : ∀ k, j ≤ k → ¬ SwpDoneG P H (tr.cfg k) := by
    refine not_done hC hs h0 hpf hnd hwf hj fun ⟨t', ht', hpc⟩ => ?_
    rw [ht] at ht'; cases ht'
    obtain ⟨p, hp, hpc'⟩ := hh.pos hC
    refine hpc (hpc' ▸ (pre_iff hC ?_).mpr ?_) <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  have hold : ∀ k, j ≤ k → ∃ u, (tr.cfg k).threads[H]? = some u ∧ Holder P u := by
    intro k hk
    induction hk with
    | refl => exact ⟨t, ht, hh⟩
    | @step k hjk ih =>
      obtain ⟨u, hu, hhu⟩ := ih
      rcases step_or hpf k with he | ⟨tid, ⟨u', outs, oc, hu', hso, ho, he⟩, -⟩
      · rw [he]; exact ⟨u, hu, hhu⟩
      by_cases e : H = tid
      · subst e; rw [hu] at hu'; cases hu'
        have hI := inv_at hC hs h0 hpf k
        cases thread_step hC (hI.thr H u hu) (hI.own H u hu) hso ho with
        | quiet _ _ hh' _ => exact ⟨_, wt_self hu he, hh' hhu⟩
        | write _ _ _ _ _ hcase =>
          rcases hcase with ⟨hh', -⟩ | ⟨-, hnh⟩ | ⟨-, -, hpc⟩
          · exact ⟨_, wt_self hu he, hh'⟩
          · exact absurd hhu hnh
          · refine absurd ⟨_, wt_self hu he, ?_⟩ (hnot (k + 1) (Nat.le_succ_of_le hjk))
            rw [hpc, pre_iff hC (by decide)]; omega
      · exact ⟨u, by rw [he, wt_ne hu' e]; exact hu, hhu⟩
  have hen : ∀ k, j ≤ k → InstrEnabled Arch.armv8 fuel H (tr.cfg k) := fun k hk => by
    obtain ⟨u, hu, hhu⟩ := hold k hk
    obtain ⟨p, hp, hpc⟩ := hhu.pos hC
    exact en_at hC (inv_at hC hs h0 hpf k) hu
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc
  have nxt := adv hpf hwf hen
  have c13 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 13 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hI := inv_at hC hs h0 hpf k'
    have hT := hI.thr H u hu'
    obtain ⟨-, ⟨md, hst, -⟩, -⟩ := s13 hC hT.st hT.prom hso ho hpc (hI.own H u hu')
    refine hnot (k' + 1) (by omega) ⟨_, wt_self hu' he, ?_⟩
    rw [hst, pre_iff hC (by decide)]; omega
  have c12 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 12 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hC hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s12 hC hT.st hT.prom hso ho hpc
    exact c13 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c11 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 11 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hC hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s11 hC hT.st hso ho hpc
    exact c12 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c10 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 10 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hC hs h0 hpf k').thr H u hu'
    obtain ⟨v, hst, -⟩ := s10 hC hT.st hso ho hpc
    exact c11 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  rcases hh with ⟨hpc, hz⟩ | hpc
  · obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt j (Nat.le_refl _) ht
    have hT := (inv_at hC hs h0 hpf k').thr H t hu'
    obtain ⟨-, hst, -⟩ := s4 hC hT.st hso ho hpc
    rw [ite_eq_left hz] at hst
    exact c10 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c10 j (Nat.le_refl _) t ht hpc
    · exact c11 j (Nat.le_refl _) t ht hpc
    · exact c12 j (Nat.le_refl _) t ht hpc
    · exact c13 j (Nat.le_refl _) t ht hpc

/-- **(b) The lock is `0` from `n` on.** -/
theorem lock_zero (j : Nat) (hj : n ≤ j) : (tr.cfg j).mem.finalVal (L4 l) = 0 :=
  Classical.byContradiction fun hne =>
    let ⟨_, _, hu, hh⟩ := (inv_at hC hs h0 hpf j).held hne
    holder_false hC hs h0 hpf hnd hwf hj hu hh

/-- **(b) The lock's last write is constant from `n` on.** -/
theorem lw_const : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 l) = (tr.cfg n).mem.lastWrite (L4 l) := by
  intro j hj
  induction hj with
  | refl => rfl
  | @step k hk ih =>
    rcases step_or hpf k with he | ⟨tid, hi, hm⟩
    · rw [he]; exact ih
    obtain ⟨-, h | ⟨_, hu, hh⟩ | ⟨_, _, hu, hh⟩⟩ :=
      step_inv hC (inv_at hC hs h0 hpf k) ((inv_at hC hs h0 hpf k).bnd.succ hm) hi
    · exact h.trans ih
    · exact (holder_false hC hs h0 hpf hnd hwf (Nat.le_succ_of_le hk) hu hh).elim
    · exact (holder_false hC hs h0 hpf hnd hwf hk hu hh).elim

/-! ### (c) A thread that is not finished -/

section Waiter

variable {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
  (hT1 : ¬ SwpDoneG P T (tr.cfg n))

include hT0 hT1

/-- `T` stays in its try/spin loop, and at the `CBZ` it has `W2 ≠ 0`. -/
theorem tpos (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t) :
    ∃ p ∈ [1, 3, 4, 6, 7, 8], t.st.st.2 = pcA p ∧ (p = 4 → w32 t.st.st.1.regs.X2 ≠ 0#32) := by
  obtain ⟨i, hi, hpc⟩ := ((inv_at hC hs h0 hpf j).thr T t ht).pc
  have hnd' := not_done hC hs h0 hpf hnd hwf (Nat.le_refl n) hT1 j hj
  have hlt : i < 14 := Classical.byContradiction fun h =>
    hnd' ⟨t, ht, fun hm => h ((pre_iff hC hi).mp (hpc ▸ hm))⟩
  have hnh : ¬ Holder P t := fun hh => holder_false hC hs h0 hpf hnd hwf hj ht hh
  have hi' := hi
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  any_goals (exfalso; omega)
  any_goals (exfalso; exact hnh (holder_of_pc (of_decide_eq_true rfl) hpc))
  all_goals refine ⟨_, by decide, hpc, fun e => ?_⟩
  all_goals first | (cases e; done) | exact fun hz => hnh (.inl ⟨hpc, hz⟩)

theorem henT : ∀ j, n ≤ j → InstrEnabled Arch.armv8 fuel T (tr.cfg j) := fun j hj => by
  obtain ⟨t, ht⟩ := get_persist hpf hT0 j hj
  obtain ⟨p, hp, hpc, -⟩ := tpos hC hs h0 hpf hnd hwf hT0 hT1 _ hj ht
  exact en_at hC (inv_at hC hs h0 hpf j) ht
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc

/-- At position 4 from `n` on, `T` goes to position 6. -/
theorem at4 {k : Nat} (hk : n ≤ k) {t : Thread isa} (htk : (tr.cfg k).threads[T]? = some t)
    (hpc : t.st.st.2 = pcA 4) {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hso : stepOne Arch.armv8 t T (tr.cfg k).mem = some outs) (ho : .ok oc ∈ outs) :
    oc.thread.st.st.2 = pcA 6 ∧ oc.thread.views.coh = t.views.coh := by
  have hT := (inv_at hC hs h0 hpf k).thr T t htk
  obtain ⟨p, hp, hpc', hz⟩ := tpos hC hs h0 hpf hnd hwf hT0 hT1 _ hk htk
  have hp' : p ∈ swPcs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
  obtain rfl := hC.inj hp' (by decide) (hpc'.symm.trans hpc)
  obtain ⟨-, hst, -, hcoh⟩ := s4 hC hT.st hso ho hpc
  rw [ite_eq_right (hz rfl)] at hst
  exact ⟨by rw [hst], hcoh⟩

/-- `T` reads the lock infinitely often. -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg T (L4 l) ts i) := by
  have nxt := adv hpf hwf (henT hC hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos hC hs h0 hpf hnd hwf hT0 hT1
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.armv8 tr.cfg T (L4 l) ts k
  have r6 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 6 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨ts, v, -, -, -, -, ⟨ν, hlog⟩, -⟩ := s6 hC hT.st hso ho hpc
    exact ⟨k, hk, ts, t, outs, oc, htk, hso, ho, he, v, ν, hlog⟩
  have r4 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    obtain ⟨h6, -⟩ := at4 hC hs h0 hpf hnd hwf hT0 hT1 (Nat.le_trans hj hk) htk hpc hso ho
    obtain ⟨k', hk', h⟩ := r6 (k + 1) (by omega) _ (wt_self htk he) h6
    exact ⟨k', by omega, h⟩
  have r3 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hI := inv_at hC hs h0 hpf k
    have hT := hI.thr T t htk
    obtain ⟨hst, -⟩ := s3 hC hT.st hT.prom hso ho hpc (hI.own T t htk)
    obtain ⟨k', hk', h⟩ := r4 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r8 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 8 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s8 hC hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r1 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s1 hC hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r7 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 7 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s7 hC hT.st hso ho hpc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      obtain ⟨k', hk', h⟩ := r8 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
      exact ⟨k', by omega, h⟩
    · rw [ite_eq_right hz] at hst
      obtain ⟨k', hk', h⟩ := r6 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
      exact ⟨k', by omega, h⟩
  intro m
  obtain ⟨t, ht⟩ := get_persist hpf hT0 (max n m) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left n m
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  have hR : R (max n m) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact r1 _ hj t ht hpc
    · exact r3 _ hj t ht hpc
    · exact r4 _ hj t ht hpc
    · exact r6 _ hj t ht hpc
    · exact r7 _ hj t ht hpc
    · exact r8 _ hj t ht hpc
  obtain ⟨k, hk, h⟩ := hR
  exact ⟨k, by omega, h⟩

/-- **(c) With an up-to-date view of the lock, `T` acquires it**: contradiction. -/
theorem at_false {j : Nat} (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t)
    (hc : (tr.cfg n).mem.lastWrite (L4 l) ≤ t.views.getCoh (L4 l)) : False := by
  have nxt := adv hpf hwf (henT hC hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos hC hs h0 hpf hnd hwf hT0 hT1
  have lw := lw_const hC hs h0 hpf hnd hwf
  have lz := lock_zero hC hs h0 hpf hnd hwf
  let LW := (tr.cfg n).mem.lastWrite (L4 l)
  let Q (p : Nat) : Prop := ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA p →
    LW ≤ t.views.getCoh (L4 l) → False
  -- the `SWPA` reads the final value `0`, whatever the view
  have p3 : Q 3 := by
    intro j hj t ht hpc _
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hI := inv_at hC hs h0 hpf k
    have hT := hI.thr T t htk
    obtain ⟨hst, -⟩ := s3 hC hT.st hT.prom hso ho hpc (hI.own T t htk)
    refine holder_false hC hs h0 hpf hnd hwf (j := k + 1) (by omega) (wt_self htk he) (.inl ⟨by rw [hst], ?_⟩)
    rw [hst, lz k (by omega)]; rfl
  have p8 : Q 8 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s8 hC hT.st hso ho hpc
    exact p3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_congr hcoh]; exact hc)
  have p1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s1 hC hT.st hso ho hpc
    exact p3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_congr hcoh]; exact hc)
  have p7z : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 7 →
      w32 t.st.st.1.regs.X2 = 0#32 → LW ≤ t.views.getCoh (L4 l) → False := by
    intro j hj t ht hpc hz hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s7 hC hT.st hso ho hpc
    rw [ite_eq_left hz] at hst
    exact p8 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_congr hcoh]; exact hc)
  have p6 : Q 6 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨ts, v, hst, hv, -, -, -, hmono⟩ := s6 hC hT.st hso ho hpc
    have hv := hv (by rw [lw k (by omega)]; exact hc)
    rw [lz _ (by omega)] at hv
    subst hv
    exact p7z (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [hst]; rfl)
      (Nat.le_trans hc (hmono _))
  have p4 : Q 4 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    obtain ⟨h6, hcoh⟩ := at4 hC hs h0 hpf hnd hwf hT0 hT1 (Nat.le_trans hj hk) htk hpc hso ho
    exact p6 (k + 1) (by omega) _ (wt_self htk he) h6 (by rw [getCoh_congr hcoh]; exact hc)
  have p7 : Q 7 := by
    intro j hj t ht hpc hc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · exact p7z j hj t ht hpc hz hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hC hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s7 hC hT.st hso ho hpc
    rw [ite_eq_right hz] at hst
    exact p6 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_congr hcoh]; exact hc)
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p1 j hj t ht hpc hc
  · exact p3 j hj t ht hpc hc
  · exact p4 j hj t ht hpc hc
  · exact p6 j hj t ht hpc hc
  · exact p7 j hj t ht hpc hc
  · exact p8 j hj t ht hpc hc

end Waiter

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. -/
theorem stuck_false (hmf : MemFair Arch.armv8 tr.cfg) {T : Nat} {tT : Thread isa}
    (hT0 : (tr.cfg n).threads[T]? = some tT) (hT1 : ¬ SwpDoneG P T (tr.cfg n)) : False := by
  exact memFair_lastWrite_false hmf (reads_inf hC hs h0 hpf hnd hwf hT0 hT1) hT0 fun _ hj _ ht' hc =>
    at_false hC hs h0 hpf hnd hwf hT0 hT1 hj ht' hc

end Stuck

omit hC hs h0 hpf in
/-- `SpinCommon.size_eq`. -/
theorem size_eq (hpf : PromiseFree Arch.armv8 tr.cfg) :
    ∀ j, (tr.cfg j).threads.size = (tr.cfg 0).threads.size :=
  SpinCommon.size_eq hpf

end Trace

/-! ## The generic theorems -/

include hC in
theorem wait_not_done {tid : Nat} {cfg : Config isa} (hw : SwpWaitingG P tid cfg) : ¬ SwpDoneG P tid cfg := by
  obtain ⟨t, ht, hpc⟩ := hw
  rintro ⟨t', ht', hpc'⟩
  rw [ht] at ht'; cases ht'
  apply hpc'
  obtain ⟨k, hk, e⟩ := List.mem_map.mp hpc
  rw [← e]
  refine List.mem_map.mpr ⟨k, List.mem_range.mpr ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega

include hC in
/-- **Promise-free deadlock-freedom of an SWP-shaped spinlock** (Stage 3,
promise-free fragment), for any program with `SwpCode P` on a valid layout. -/
theorem swp_live_pf_gen (fuel : Nat) : SwpLiveUnderG P (StartG P) fuel (FairPF fuel) := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, SwpDoneG P U (tr.cfg j) → SwpDoneG P U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hC hs h0 hpf hnd (weakFairInstr_of_promiseFree hpf hwf) hmf ht (wait_not_done hC hw)

include hC in
/-- **Per-thread liveness of one-shot SWP-shaped workers** (promise-free
fragment): from `stuck_false` and the finite number of threads. A property
of these one-shot programs, not starvation-freedom of the lock. -/
theorem swp_live_oneShot_pf_gen (fuel : Nat) : SwpOneShotUnderG P (StartG P) fuel (FairPF fuel) := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ SwpDoneG P tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := stable_of_mono (fun k j => SwpDoneG P k (tr.cfg j)) (tr.cfg 0).threads.size
    (fun k j ⟨_, ht, _⟩ => size_eq hpf j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hC hs h0 hpf hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist hpf ht n hin
  exact stuck_false hC hs h0 hpf (fun j hj U hd => hst j hj U hd) (weakFairInstr_of_promiseFree hpf hwf) hmf hu
    (hnd' n hin)

end Kraken.Promising.Live.SpinSwpPF
