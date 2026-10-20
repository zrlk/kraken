/-
**Stage 3: promise-free deadlock-freedom of the x64
`lock cmpxchg` spinlock under weak fairness and memory fairness**
(`spin_cmpx_live_pf`), for the verbatim workers of `spinlock_cmpxchg2/3.kl`
on any valid layout of their image (declarations `{}`, the form of
`CmpxAbs.x64_cmpx_counter_envG_verbatim`); and per-thread liveness of the
one-shot workers (`spin_cmpx_live_oneShot_pf`). The x64 twin of
`LiveSpinCasPF.lean`, with the same proof:

On a promise-free stuttering `Arch.tso` trace from a start configuration,
`SpinX64CmpxInv.trace_inv` gives `InvX` at every index. The core lemma
`stuck_false`: if from index `n` on no thread newly finishes, then every
thread is finished at `n`. Suppose `T` is not.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n`: a holder is
  always instruction-enabled, and weak fairness drives it through positions
  4–8 to its release store, after which it is finished.
- (b) Hence the lock is `0` (`lock_zero`) and its last write is constant
  (`lw_const`) from `n` on.
- (c) `T` sits in its `xorl`/`movl`/`lock cmpxchg`/`jne` loop forever
  (`tpos`), always enabled, and reads the lock at its `lock cmpxchg`
  infinitely often (`reads_inf`; the locked RMW's read is logged). Memory
  fairness brings its coherence view of the lock up to the last write, and the
  view never drops again (the failing `cmpxchg`'s fences change no coherence
  view); its next `lock cmpxchg` reads `0 = %eax` and writes: `T` holds the
  lock (`at_false`), against (a).

On TSO the RMW's fences do not remove the need for `MemFair`: the waiter's
coherence view of the lock is what bounds its RMW's read from below.

**Invalid layouts.** As for the AArch64 locks, the theorem assumes
`ValidLayout (layout cmpxImageV)`; `spin_cmpx_live_pf_runnerN` discharges it
at the `.kl` runner's layout.
-/
import Kraken.Promising.LiveSpinX64CmpxInv
import Kraken.Promising.LiveSpinCommon
import Kraken.Promising.SLR.EnvG.X64CmpxAbsConcrete

namespace Kraken.Promising.Live.SpinX64CmpxPF

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SpinX64CmpxInv Kraken.Promising.Live.SpinCommon Kraken.Promising.Live.SpinX64Step
open Kraken.Promising.Live.TsoRmw
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC)

set_option linter.unusedSectionVars false

section Gen

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

/-! ## Positions -/

/-- The position in `spPcs` at the address of position `k`. -/
def rep (k : Nat) : Nat := if k = 0 then 1 else k

theorem addrOf_rep (k : Nat) : pcA (rep k) = pcA k := by
  unfold rep
  split
  · subst_vars; exact addrOf_0.symm
  · rfl

/-- A position of `spPcs` is up to the release iff it is below 9. -/
theorem pre_iff {i : Nat} (hi : i ∈ spPcs) : pcA i ∈ SpinX64.cmpxPrePcs ↔ i < 9 := by
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := List.mem_map.mp h
    have hk := List.mem_range.mp hk
    have hr : rep k ∈ spPcs ∧ rep k < 9 := by
      have : ∀ k < 9, rep k ∈ spPcs ∧ rep k < 9 := by decide
      exact this k hk
    rw [← addrOf_rep] at e
    rw [← addrOf_inj hr.1 hi e]; exact hr.2
  · intro h; exact List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩

theorem getCoh_eq {t t' : Thread isa} (h : t'.views.coh = t.views.coh) (l : Loc) :
    t'.views.getCoh l = t.views.getCoh l :=
  SpinSwpStep.getCoh_congr h l

/-- **Enabledness**: a thread of an `InvX` configuration at a position other
than the end can take an instruction step. -/
theorem en_at {fuel : Nat} {cfg : Config isa} (h : InvX cfg) {U : Nat} {t : Thread isa}
    (ht : cfg.threads[U]? = some t) {p : Nat} (hp : p ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9])
    (hpc : t.st.st.2 = pcA p) : InstrEnabled Arch.tso fuel U cfg := by
  have hT := h.thr U t ht
  have hS := hT.st
  have hb' := h.bnd U t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, h1, h2, h3⟩ := en_choose Arch.tso U (by decide)
      (exec_xor _ (hS.at (by decide) (by decide) hpc)) (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U (exec_movc _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨g, -, hex⟩ := exec_cmpxchg _ (hS.at (by decide) (by decide) hpc) hS.dl
    obtain ⟨_, _, h1, h2, h3⟩ := en_rmwo_tso Arch.tso U rfl hT.prom hb' hex
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U (exec_jne _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨g, -, hex⟩ := exec_ldc _ (hS.at (by decide) (by decide) hpc) hS.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso U hT.prom hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨md, -, hex⟩ := exec_add _ (hS.at (by decide) (by decide) hpc)
    obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨v, md, -, hex⟩ := exec_stc _ (hS.at (by decide) (by decide) hpc) hS.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso U hT.prom hb' hex
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso U hT.prom hb'
      (exec_unlock _ (hS.at (by decide) (by decide) hpc) hS.dl)
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U (exec_jmp _ (hS.at (by decide) (by decide) hpc))
      (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)

section Trace

variable {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceS Arch.tso fuel isa}
  (hs : SpinX64.CmpxStart states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
  (hpf : PromiseFree Arch.tso tr.cfg)

include hs h0 hpf

theorem inv_at (i : Nat) : InvX (tr.cfg i) := trace_inv hs tr h0 hpf i

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : SpinX64.CmpxDone U (tr.cfg j)) : SpinX64.CmpxDone U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases step_or hpf j with he | ⟨tid, ⟨u, outs, oc, hu, hso, ho, he⟩, -⟩
  · rw [he]; exact ⟨t, ht, hpc⟩
  rw [he]
  by_cases e : U = tid
  · subst e; rw [ht] at hu; cases hu
    have hT := (inv_at hs h0 hpf j).thr U t ht
    obtain ⟨i, hi, hpi, -⟩ := hT.pc
    have h9 : ¬ i < 9 := fun h => hpc (hpi ▸ (pre_iff hi).mpr h)
    have : i = 9 ∨ i = 10 := by
      simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    rcases this with rfl | rfl
    · obtain ⟨-, hst, -⟩ := s9 hT.st hso ho hpi
      refine ⟨_, wt_tid ht, ?_⟩
      rw [hst, pre_iff (by decide)]; omega
    · rw [stepOne_end hT.st hpi] at hso; cases hso
  · exact ⟨t, by rw [wt_ne hu e]; exact ht, hpc⟩

theorem done_mono {j U : Nat} (hd : SpinX64.CmpxDone U (tr.cfg j)) :
    ∀ k, j ≤ k → SpinX64.CmpxDone U (tr.cfg k) := by
  intro k hk
  induction hk with
  | refl => exact hd
  | @step k _ ih => exact done_step hs h0 hpf k U ih

/-! ## The core lemma -/

section Stuck

variable {n : Nat} (hnd : ∀ j, n ≤ j → ∀ U, SpinX64.CmpxDone U (tr.cfg j) → SpinX64.CmpxDone U (tr.cfg n))
  (hwf : WeakFairInstr Arch.tso fuel tr.cfg)

include hnd hwf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ SpinX64.CmpxDone U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ SpinX64.CmpxDone U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hs h0 hpf (hnd k (by omega) U hd) j hj)

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder t) : False := by
  have hnot : ∀ k, j ≤ k → ¬ SpinX64.CmpxDone H (tr.cfg k) := by
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
  have hen : ∀ k, j ≤ k → InstrEnabled Arch.tso fuel H (tr.cfg k) := fun k hk => by
    obtain ⟨u, hu, hhu⟩ := hold k hk
    obtain ⟨p, hp, hpc⟩ := hhu.pos
    exact en_at (inv_at hs h0 hpf k) hu (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc
  have nxt := adv hpf hwf hen
  have c8 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 8 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s8 hT.st hT.prom hso ho hpc
    refine hnot (k' + 1) (by omega) ⟨_, wt_self hu' he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  have c7 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 7 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨md, -, hst, -⟩ := s7 hT.st hT.prom hso ho hpc
    exact c8 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c6 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 6 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨md, -, hst, -⟩ := s6 hT.st hso ho hpc
    exact c7 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c5 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 5 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨md, -, hst, -⟩ := s5 hT.st hso ho hpc
    exact c6 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  rcases hh with ⟨hpc, hz⟩ | hpc
  · obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt j (Nat.le_refl _) ht
    have hT := (inv_at hs h0 hpf k').thr H t hu'
    obtain ⟨-, hst, -⟩ := s4 hT.st hso ho hpc
    rw [ite_eq_left hz] at hst
    exact c5 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c5 j (Nat.le_refl _) t ht hpc
    · exact c6 j (Nat.le_refl _) t ht hpc
    · exact c7 j (Nat.le_refl _) t ht hpc
    · exact c8 j (Nat.le_refl _) t ht hpc

/-- **(b) The lock is `0` from `n` on.** -/
theorem lock_zero (j : Nat) (hj : n ≤ j) : (tr.cfg j).mem.finalVal LkL = 0 :=
  Classical.byContradiction fun hne =>
    let ⟨_, _, hu, hh⟩ := (inv_at hs h0 hpf j).held hne
    holder_false hs h0 hpf hnd hwf hj hu hh

/-- **(b) The lock's last write is constant from `n` on.** -/
theorem lw_const : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite LkL = (tr.cfg n).mem.lastWrite LkL := by
  intro j hj
  induction hj with
  | refl => rfl
  | @step k hk ih =>
    rcases step_or hpf k with he | ⟨tid, hi, hm⟩
    · rw [he]; exact ih
    obtain ⟨-, h | ⟨_, hu, hh⟩ | ⟨_, hu, hh⟩⟩ :=
      step_inv (inv_at hs h0 hpf k) ((inv_at hs h0 hpf k).bnd.succ hm) hi
    · exact h.trans ih
    · exact (holder_false hs h0 hpf hnd hwf (Nat.le_succ_of_le hk) hu hh).elim
    · exact (holder_false hs h0 hpf hnd hwf hk hu hh).elim

/-! ### (c) A thread that is not finished -/

section Waiter

variable {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
  (hT1 : ¬ SpinX64.CmpxDone T (tr.cfg n))

include hT0 hT1

/-- `T` stays in its acquire loop, and at the `jne` it has `ZF` clear. -/
theorem tpos (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t) :
    ∃ p ∈ [1, 2, 3, 4], t.st.st.2 = pcA p ∧ (p = 4 → t.st.st.1.status.zf = false) := by
  obtain ⟨i, hi, hpc, -⟩ := ((inv_at hs h0 hpf j).thr T t ht).pc
  have hnd' := not_done hs h0 hpf hnd hwf (Nat.le_refl n) hT1 j hj
  have hlt : i < 9 := Classical.byContradiction fun h =>
    hnd' ⟨t, ht, fun hm => h ((pre_iff hi).mp (hpc ▸ hm))⟩
  have hnh : ¬ Holder t := fun hh => holder_false hs h0 hpf hnd hwf hj ht hh
  have hi' := hi
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  any_goals (exfalso; omega)
  any_goals (exfalso; exact hnh (holder_of_pc (of_decide_eq_true rfl) hpc))
  all_goals refine ⟨_, by decide, hpc, fun e => ?_⟩
  all_goals first | (cases e; done) | exact Bool.eq_false_iff.mpr fun hz => hnh (.inl ⟨hpc, hz⟩)

theorem henT : ∀ j, n ≤ j → InstrEnabled Arch.tso fuel T (tr.cfg j) := fun j hj => by
  obtain ⟨t, ht⟩ := get_persist hpf hT0 j hj
  obtain ⟨p, hp, hpc, -⟩ := tpos hs h0 hpf hnd hwf hT0 hT1 _ hj ht
  exact en_at (inv_at hs h0 hpf j) ht (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc

/-- `T` reads the lock infinitely often (at its `lock cmpxchg`). -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.tso tr.cfg T LkL ts i) := by
  have nxt := adv hpf hwf (henT hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos hs h0 hpf hnd hwf hT0 hT1
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.tso tr.cfg T LkL ts k
  have r3 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, ts, v, -, -, -, -, ⟨ν, hlog⟩, -⟩ := s3 hT.st hT.prom hso ho hpc
    exact ⟨k, hk, ts, t, outs, oc, htk, hso, ho, he, v, ν, hlog⟩
  have r2 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 2 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s2 hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r1 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, ⟨md, -, -, hst⟩, -⟩ := s1 hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r2 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r4 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨p, hp, hpc', hz⟩ := tp _ (Nat.le_trans hj hk) htk
    obtain rfl := addrOf_inj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                                 simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by decide) (hpc'.symm.trans hpc)
    obtain ⟨-, hst, -⟩ := s4 hT.st hso ho hpc
    rw [hz rfl] at hst
    obtain ⟨k', hk', h⟩ := r1 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]; rfl)
    exact ⟨k', by omega, h⟩
  intro m
  obtain ⟨t, ht⟩ := get_persist hpf hT0 (max n m) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left n m
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  have hR : R (max n m) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact r1 _ hj t ht hpc
    · exact r2 _ hj t ht hpc
    · exact r3 _ hj t ht hpc
    · exact r4 _ hj t ht hpc
  obtain ⟨k, hk, h⟩ := hR
  exact ⟨k, by omega, h⟩

/-- **(c) With an up-to-date view of the lock, `T` acquires it**: contradiction. -/
theorem at_false {j : Nat} (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t)
    (hc : (tr.cfg n).mem.lastWrite LkL ≤ t.views.getCoh LkL) : False := by
  have nxt := adv hpf hwf (henT hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos hs h0 hpf hnd hwf hT0 hT1
  have lw := lw_const hs h0 hpf hnd hwf
  have lz := lock_zero hs h0 hpf hnd hwf
  let LW := (tr.cfg n).mem.lastWrite LkL
  let Q (p : Nat) : Prop := ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA p →
    LW ≤ t.views.getCoh LkL → False
  have p3 : Q 3 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    have hz : eax t.st.st.1 = 0#32 := hT.pcinv (by decide) hpc
    obtain ⟨md, -, tr', old, hst, -, hold, -, -, -, hcase⟩ := s3 hT.st hT.prom hso ho hpc
    have hold := hold (by rw [lw k (by omega)]; exact hc)
    rw [lz _ (by omega)] at hold
    subst hold
    rcases hcase with ⟨hne, -⟩ | ⟨-, hzf, -⟩
    · exact hne (by rw [hz]; rfl)
    · exact holder_false hs h0 hpf hnd hwf (j := k + 1) (by omega) (wt_self htk he)
        (.inl ⟨by rw [hst], by rw [hst]; exact hzf⟩)
  have p2 : Q 2 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s2 hT.st hso ho hpc
    exact p3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  have p1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, ⟨md, -, -, hst⟩, -, hcoh⟩ := s1 hT.st hso ho hpc
    exact p2 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [getCoh_eq hcoh]; exact hc)
  have p4 : Q 4 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨p, hp, hpc', hz⟩ := tp _ (Nat.le_trans hj hk) htk
    obtain rfl := addrOf_inj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                                 simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by decide) (hpc'.symm.trans hpc)
    obtain ⟨-, hst, -, hcoh⟩ := s4 hT.st hso ho hpc
    rw [hz rfl] at hst
    exact p1 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]; rfl) (by rw [getCoh_eq hcoh]; exact hc)
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact p1 j hj t ht hpc hc
  · exact p2 j hj t ht hpc hc
  · exact p3 j hj t ht hpc hc
  · exact p4 j hj t ht hpc hc

end Waiter

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. -/
theorem stuck_false (hmf : MemFair Arch.tso tr.cfg) {T : Nat} {tT : Thread isa}
    (hT0 : (tr.cfg n).threads[T]? = some tT) (hT1 : ¬ SpinX64.CmpxDone T (tr.cfg n)) : False := by
  exact memFair_lastWrite_false hmf (reads_inf hs h0 hpf hnd hwf hT0 hT1) hT0 fun _ hj _ ht' hc =>
    at_false hs h0 hpf hnd hwf hT0 hT1 hj ht' hc

end Stuck

omit hs h0 hpf in
/-- `SpinCommon.size_eq`. -/
theorem size_eq (hpf : PromiseFree Arch.tso tr.cfg) :
    ∀ j, (tr.cfg j).threads.size = (tr.cfg 0).threads.size :=
  SpinCommon.size_eq hpf

end Trace

/-! ## The theorems -/

theorem wait_not_done {tid : Nat} {cfg : Config isa} (hw : SpinX64.CmpxWaiting tid cfg) :
    ¬ SpinX64.CmpxDone tid cfg := by
  obtain ⟨t, ht, hpc⟩ := hw
  rintro ⟨t', ht', hpc'⟩
  rw [ht] at ht'; cases ht'
  apply hpc'
  obtain ⟨k, hk, e⟩ := List.mem_map.mp hpc
  rw [← e]
  refine List.mem_map.mpr ⟨k, List.mem_range.mpr ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega

/-- **Promise-free deadlock-freedom of the x64 `lock cmpxchg` spinlock**
(Stage 3, promise-free fragment): on a valid layout of the verbatim image
`cmpxImageV`, on every promise-free stuttering `Arch.tso` trace from a start
configuration under weak fairness and memory fairness, if a thread waits in
its acquire loop, then some thread not yet past its release later is. -/
theorem spin_cmpx_live_pf (fuel : Nat) : SpinX64.CmpxSpinLivePF fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, SpinX64.CmpxDone U (tr.cfg j) → SpinX64.CmpxDone U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hs h0 hpf hnd (weakFairInstr_of_promiseFree hpf hwf) hmf ht (wait_not_done hw)

/-- **Per-thread liveness of the one-shot x64 `lock cmpxchg` workers**
(promise-free fragment): every waiting thread eventually gets past its
release. A property of these one-shot programs (from `stuck_false` and the
finite number of threads), not starvation-freedom of the lock. -/
theorem spin_cmpx_live_oneShot_pf (fuel : Nat) : SpinX64.CmpxSpinLiveOneShotPF fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ SpinX64.CmpxDone tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := stable_of_mono (fun k j => SpinX64.CmpxDone k (tr.cfg j)) (tr.cfg 0).threads.size
    (fun k j ⟨_, ht, _⟩ => size_eq hpf j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hs h0 hpf hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist hpf ht n hin
  exact stuck_false hs h0 hpf (fun j hj U hd => hst j hj U hd) (weakFairInstr_of_promiseFree hpf hwf) hmf hu
    (hnd' n hin)

end Gen

/-! ## Concrete instances: the `.kl` runner's executable -/

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete in
/-- `spin_cmpx_live_pf` at the `.kl` runner's layout `cmpxLayoutV`: no
hypothesis left. -/
theorem spin_cmpx_live_pf_concrete (fuel : Nat) : @SpinX64.CmpxSpinLivePF cmpxLayoutV fuel :=
  @spin_cmpx_live_pf cmpxLayoutV cmpxValidV fuel

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete in
/-- `spin_cmpx_live_oneShot_pf` at the runner's layout. -/
theorem spin_cmpx_live_oneShot_pf_concrete (fuel : Nat) : @SpinX64.CmpxSpinLiveOneShotPF cmpxLayoutV fuel :=
  @spin_cmpx_live_oneShot_pf cmpxLayoutV cmpxValidV fuel

section
open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete
attribute [local instance] cmpxLayoutV

/-- **The runner's start, `N` workers** (`spinlock_cmpxchg2.kl` for `N = 2`,
`spinlock_cmpxchg3.kl` for `N = 3`): `N` copies of the runner's prepared
worker `cmpxWorkerV0`, the runner's initial memory, at its layout. No
configuration is evaluated. -/
theorem cmpxStart_runnerN (N : Nat) :
    @SpinX64.CmpxStart cmpxLayoutV (List.replicate N cmpxWorkerV0) cmpxInitMemV :=
  ⟨by rw [symC_lock, symC_counter]; decide,
   fun s hs => (List.eq_of_mem_replicate hs) ▸ cmpxWorkerV0_start,
   by rw [symC_lock]; simp only [Config.init_mem]; decide⟩

end

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete in
/-- **Promise-free deadlock-freedom for `N` runner workers**: from the
runner's configuration of `N` workers, under `WeakFair ∧ MemFair ∧
PromiseFree`. -/
theorem spin_cmpx_live_pf_runnerN (fuel N : Nat) :
    ProgressFromN Arch.tso fuel (Config.init (List.replicate N cmpxWorkerV0) cmpxInitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      (@SpinX64.CmpxWaiting cmpxLayoutV) (@SpinX64.CmpxDone cmpxLayoutV) :=
  spin_cmpx_live_pf_concrete fuel _ _ (cmpxStart_runnerN N)

end Kraken.Promising.Live.SpinX64CmpxPF
