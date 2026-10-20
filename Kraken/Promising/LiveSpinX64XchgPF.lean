/-
**Stage 3: promise-free deadlock-freedom of the x64
`xchg` spinlock under weak fairness and memory fairness**
(`spin_xchg_live_pf`), for the verbatim workers of `spinlock2/3.kl` on any
valid layout of their image (declarations `{}`, the form of
`SpinAbs.x64_spin_counter_envG_verbatim`); and per-thread liveness of the
one-shot workers (`spin_xchg_live_oneShot_pf`). The twin of
`LiveSpinX64CmpxPF.lean`, with the same proof:

On a promise-free stuttering `Arch.tso` trace from a start configuration,
`SpinX64XchgInv.trace_inv` gives `InvX` at every index. The core lemma
`stuck_false`: if from index `n` on no thread newly finishes, then every
thread is finished at `n`. Suppose `T` is not.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n`: a holder is
  always instruction-enabled, and weak fairness drives it through positions
  6–11 to its release store, after which it is finished.
- (b) Hence the lock is `0` (`lock_zero`) and its last write is constant
  (`lw_const`: every write to the lock is an `xchgl`, which then makes a
  holder or needs one, or a holder's release) from `n` on.
- (c) `T` sits in its test-and-test-and-set loop forever (`tpos`), always
  enabled, and reads the lock at its `movl (lock),%eax` infinitely often
  (`reads_inf`). Memory fairness brings its coherence view of the lock up to
  the last write, and the view never drops again; its next plain load reads
  `0`, it passes both tests to the `xchgl`, which reads the final value `0`
  (`own`: the swap always reads the last write) and makes `T` a holder
  (`at_false`), against (a).

**Invalid layouts.** As for the other spinlocks, the theorem assumes
`ValidLayout (layout spinImageV)`; `spin_xchg_live_pf_runnerN` discharges it
at the `.kl` runner's layout.
-/
import Kraken.Promising.LiveSpinX64XchgInv
import Kraken.Promising.LiveSpinSwpStep
import Kraken.Promising.LiveSpinCommon
import Kraken.Promising.SLR.EnvG.X64SpinAbsConcrete

namespace Kraken.Promising.Live.SpinX64XchgPF

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64XchgTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SpinX64XchgInv Kraken.Promising.Live.SpinCommon Kraken.Promising.Live.SpinX64Step
open Kraken.Promising.Live.TsoRmw
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV symV)

set_option linter.unusedSectionVars false

section Gen

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

set_option hygiene false in
local notation "pcA" => (layout spinImageV).addrOf

/-! ## Positions -/

/-- The position in `spPcs` at the address of position `k`. -/
def rep (k : Nat) : Nat := if k = 0 then 1 else k

theorem addrOf_rep (k : Nat) : pcA (rep k) = pcA k := by
  unfold rep
  split
  · subst_vars; exact addrOf_0.symm
  · rfl

/-- A position of `spPcs` is up to the release iff it is below 12. -/
theorem pre_iff {i : Nat} (hi : i ∈ spPcs) : pcA i ∈ SpinX64Xchg.xchgPrePcs ↔ i < 12 := by
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := List.mem_map.mp h
    have hk := List.mem_range.mp hk
    have hr : rep k ∈ spPcs ∧ rep k < 12 := by
      have : ∀ k < 12, rep k ∈ spPcs ∧ rep k < 12 := by decide
      exact this k hk
    rw [← addrOf_rep] at e
    rw [← addrOf_inj hr.1 hi e]; exact hr.2
  · intro h; exact List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩

local macro "mems" h:ident : tactic =>
  `(tactic| simp only [List.mem_cons, List.not_mem_nil, or_false] at $h:ident)

/-- **Enabledness**: a thread of an `InvX` configuration at a position other
than the end can take an instruction step. -/
theorem en_at {fuel : Nat} {cfg : Config isa} (h : InvX cfg) {U : Nat} {t : Thread isa}
    (ht : cfg.threads[U]? = some t) {p : Nat} (hp : p ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
    (hpc : t.st.st.2 = pcA p) : InstrEnabled Arch.tso fuel U cfg := by
  have hT := h.thr U t ht
  have hS := hT.st
  have hb' := h.bnd U t ht
  have hp' : p ∈ spPcs := by mems hp; simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
  have hat := hS.at hp' (by mems hp; omega) hpc
  mems hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g, -, hex⟩ := exec_ldl _ hat hS.dl
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso U hT.prom hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨g, -, hex⟩ := exec_test _ (.inl rfl) hat
    obtain ⟨_, _, h1, h2, h3⟩ := en_choose Arch.tso U (by decide) hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U (exec_jne _ (.inl rfl) hat) (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨md, -, hex⟩ := exec_mov1 _ hat
    obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨g, -, hex⟩ := exec_xchg _ hat hS.dl
    obtain ⟨_, _, h1, h2, h3⟩ := en_rmwo_tso Arch.tso U rfl hT.prom hb' hex
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨g, -, hex⟩ := exec_test _ (.inr rfl) hat
    obtain ⟨_, _, h1, h2, h3⟩ := en_choose Arch.tso U (by decide) hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U (exec_jne _ (.inr rfl) hat) (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨g, -, hex⟩ := exec_ldc _ hat hS.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso U hT.prom hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨md, -, hex⟩ := exec_add _ hat
    obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U hex (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)
  · obtain ⟨v, md, -, hex⟩ := exec_stc _ hat hS.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso U hT.prom hb' hex
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso U hT.prom hb' (exec_unlock _ hat hS.dl)
    exact instrEnabled_of Arch.tso U ht h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso U (exec_jmp _ hat) (mem := cfg.mem)
    exact instrEnabled_of Arch.tso U ht h1 h2 (h3.trans hT.prom)

section Trace

variable {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceS Arch.tso fuel isa}
  (hs : SpinX64Xchg.XchgStart states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
  (hpf : PromiseFree Arch.tso tr.cfg)

include hs h0 hpf

theorem inv_at (i : Nat) : InvX (tr.cfg i) := trace_inv hs tr h0 hpf i

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : SpinX64Xchg.XchgDone U (tr.cfg j)) :
    SpinX64Xchg.XchgDone U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases step_or hpf j with he | ⟨tid, ⟨u, outs, oc, hu, hso, ho, he⟩, -⟩
  · rw [he]; exact ⟨t, ht, hpc⟩
  rw [he]
  by_cases e : U = tid
  · subst e; rw [ht] at hu; cases hu
    have hT := (inv_at hs h0 hpf j).thr U t ht
    obtain ⟨i, hi, hpi⟩ := hT.pc
    have h12 : ¬ i < 12 := fun h => hpc (hpi ▸ (pre_iff hi).mpr h)
    have : i = 12 ∨ i = 13 := by
      simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    rcases this with rfl | rfl
    · obtain ⟨-, hst, -⟩ := s12 hT.st hso ho hpi
      refine ⟨_, wt_tid ht, ?_⟩
      rw [hst, pre_iff (by decide)]; omega
    · rw [stepOne_end hT.st hpi] at hso; cases hso
  · exact ⟨t, by rw [wt_ne hu e]; exact ht, hpc⟩

theorem done_mono {j U : Nat} (hd : SpinX64Xchg.XchgDone U (tr.cfg j)) :
    ∀ k, j ≤ k → SpinX64Xchg.XchgDone U (tr.cfg k) := by
  intro k hk
  induction hk with
  | refl => exact hd
  | @step k _ ih => exact done_step hs h0 hpf k U ih

/-! ## The core lemma -/

section Stuck

variable {n : Nat}
  (hnd : ∀ j, n ≤ j → ∀ U, SpinX64Xchg.XchgDone U (tr.cfg j) → SpinX64Xchg.XchgDone U (tr.cfg n))
  (hwf : WeakFairInstr Arch.tso fuel tr.cfg)

include hnd hwf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ SpinX64Xchg.XchgDone U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ SpinX64Xchg.XchgDone U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hs h0 hpf (hnd k (by omega) U hd) j hj)

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder t) : False := by
  have hnot : ∀ k, j ≤ k → ¬ SpinX64Xchg.XchgDone H (tr.cfg k) := by
    refine not_done hs h0 hpf hnd hwf hj fun ⟨t', ht', hpc⟩ => ?_
    rw [ht] at ht'; cases ht'
    obtain ⟨p, hp, hpc'⟩ := hh.pos
    refine hpc (hpc' ▸ (pre_iff ?_).mpr ?_) <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
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
        have hI := inv_at hs h0 hpf k
        cases thread_step (hI.thr H u hu) (hI.own H u hu) hso ho with
        | quiet _ _ hh' _ => exact ⟨_, wt_self hu he, hh' hhu⟩
        | write _ _ _ _ _ hcase =>
          rcases hcase with ⟨hh', -⟩ | ⟨-, hn⟩ | ⟨-, -, hpc⟩
          · exact ⟨_, wt_self hu he, hh'⟩
          · exact absurd hhu hn
          · refine absurd ⟨_, wt_self hu he, ?_⟩ (hnot (k + 1) (Nat.le_succ_of_le hjk))
            rw [hpc, pre_iff (by decide)]; omega
      · exact ⟨u, by rw [he, wt_ne hu' e]; exact hu, hhu⟩
  have hen : ∀ k, j ≤ k → InstrEnabled Arch.tso fuel H (tr.cfg k) := fun k hk => by
    obtain ⟨u, hu, hhu⟩ := hold k hk
    obtain ⟨p, hp, hpc⟩ := hhu.pos
    exact en_at (inv_at hs h0 hpf k) hu (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc
  have nxt := adv hpf hwf hen
  have c11 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 11 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s11 hT.st hT.prom hso ho hpc
    refine hnot (k' + 1) (by omega) ⟨_, wt_self hu' he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  have c10 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 10 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨md, -, hst, -⟩ := s10 hT.st hT.prom hso ho hpc
    exact c11 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c9 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 9 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨md, -, hst, -⟩ := s9 hT.st hso ho hpc
    exact c10 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c8 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 8 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨md, -, hst, -⟩ := s8 hT.st hso ho hpc
    exact c9 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c7 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 7 →
      u.st.st.1.status.zf = true → False := by
    intro k hk u hu hpc hz
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨-, hst, -⟩ := s_jne hT.st hso ho (.inr rfl) hpc
    rw [ite_eq_left hz] at hst
    exact c8 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c6 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 6 →
      eax u.st.st.1 = 0#32 → False := by
    intro k hk u hu hpc hz
    obtain ⟨k', hk', hu', outs, oc, hso, ho, he⟩ := nxt k hk hu
    have hT := (inv_at hs h0 hpf k').thr H u hu'
    obtain ⟨md, -, hzf, hst, -⟩ := s_test hT.st hso ho (.inr rfl) hpc
    exact c7 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst]) (by rw [hst]; exact hzf.mpr hz)
  rcases hh with ⟨hpc, hz⟩ | ⟨hpc, hz⟩ | hpc
  · exact c6 j (Nat.le_refl _) t ht hpc hz
  · exact c7 j (Nat.le_refl _) t ht hpc hz
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c8 j (Nat.le_refl _) t ht hpc
    · exact c9 j (Nat.le_refl _) t ht hpc
    · exact c10 j (Nat.le_refl _) t ht hpc
    · exact c11 j (Nat.le_refl _) t ht hpc

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
    obtain ⟨-, h | ⟨_, hu, hh⟩ | ⟨_, _, hu, hh⟩⟩ :=
      step_inv (inv_at hs h0 hpf k) ((inv_at hs h0 hpf k).bnd.succ hm) hi
    · exact h.trans ih
    · exact (holder_false hs h0 hpf hnd hwf (Nat.le_succ_of_le hk) hu hh).elim
    · exact (holder_false hs h0 hpf hnd hwf hk hu hh).elim

/-! ### (c) A thread that is not finished -/

section Waiter

variable {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
  (hT1 : ¬ SpinX64Xchg.XchgDone T (tr.cfg n))

include hT0 hT1

/-- `T` stays in its acquire loop, not holding the lock. -/
theorem tpos (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t) :
    ∃ p ∈ [1, 2, 3, 4, 5, 6, 7], t.st.st.2 = pcA p ∧ (p = 6 → eax t.st.st.1 ≠ 0#32) ∧
      (p = 7 → t.st.st.1.status.zf = false) := by
  obtain ⟨i, hi, hpc⟩ := ((inv_at hs h0 hpf j).thr T t ht).pc
  have hnd' := not_done hs h0 hpf hnd hwf (Nat.le_refl n) hT1 j hj
  have hlt : i < 12 := Classical.byContradiction fun h =>
    hnd' ⟨t, ht, fun hm => h ((pre_iff hi).mp (hpc ▸ hm))⟩
  have hnh : ¬ Holder t := fun hh => holder_false hs h0 hpf hnd hwf hj ht hh
  have h8 : i ∉ [8, 9, 10, 11] := fun h8 => hnh (holder_of_pc h8 hpc)
  have hi7 : i ∈ [1, 2, 3, 4, 5, 6, 7] := by
    simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi h8 ⊢; omega
  refine ⟨i, hi7, hpc, fun e hz => hnh (.inl ⟨e ▸ hpc, hz⟩), fun e => ?_⟩
  exact Bool.eq_false_iff.mpr fun hz => hnh (.inr (.inl ⟨e ▸ hpc, hz⟩))

theorem henT : ∀ j, n ≤ j → InstrEnabled Arch.tso fuel T (tr.cfg j) := fun j hj => by
  obtain ⟨t, ht⟩ := get_persist hpf hT0 j hj
  obtain ⟨p, hp, hpc, -⟩ := tpos hs h0 hpf hnd hwf hT0 hT1 _ hj ht
  exact en_at (inv_at hs h0 hpf j) ht (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) hpc

/-- `T`'s positions from `n` on are positions of the loop: pin down `p`. -/
theorem tpos_at (j : Nat) (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t) {q : Nat}
    (hq : q ∈ [1, 2, 3, 4, 5, 6, 7]) (hpc : t.st.st.2 = pcA q) :
    (q = 6 → eax t.st.st.1 ≠ 0#32) ∧ (q = 7 → t.st.st.1.status.zf = false) := by
  obtain ⟨p, hp, hpc', h6, h7⟩ := tpos hs h0 hpf hnd hwf hT0 hT1 j hj ht
  obtain rfl := addrOf_inj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                               simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega) (hpc'.symm.trans hpc)
  exact ⟨h6, h7⟩

/-- `T` reads the lock infinitely often (at its `movl (lock),%eax`). -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.tso tr.cfg T LkL ts i) := by
  have nxt := adv hpf hwf (henT hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos_at hs h0 hpf hnd hwf hT0 hT1
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.tso tr.cfg T LkL ts k
  have r1 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨ts, v, -, -, -, -, -, -, -, ⟨ν, hlog⟩, -⟩ := s1 hT.st hso ho hpc
    exact ⟨k, hk, ts, t, outs, oc, htk, hso, ho, he, v, ν, hlog⟩
  have r7 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 7 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s_jne hT.st hso ho (.inr rfl) hpc
    rw [(tp _ (Nat.le_trans hj hk) htk (by decide) hpc).2 rfl] at hst
    obtain ⟨k', hk', h⟩ := r1 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]; rfl)
    exact ⟨k', by omega, h⟩
  have r6 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 6 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, -, hst, -⟩ := s_test hT.st hso ho (.inr rfl) hpc
    obtain ⟨k', hk', h⟩ := r7 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r5 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 5 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hI := inv_at hs h0 hpf k
    have hT := hI.thr T t htk
    obtain ⟨md, -, -, hst, -⟩ := s5 hT.st hT.prom hso ho hpc (hI.own T t htk)
    obtain ⟨k', hk', h⟩ := r6 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r4 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, hst, -⟩ := s4 hT.st hso ho hpc
    obtain ⟨k', hk', h⟩ := r5 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r3 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s_jne hT.st hso ho (.inl rfl) hpc
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      obtain ⟨k', hk', h⟩ := r4 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
      exact ⟨k', by omega, h⟩
    · rw [ite_eq_right hz] at hst
      obtain ⟨k', hk', h⟩ := r1 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
      exact ⟨k', by omega, h⟩
  have r2 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 2 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, -, hst, -⟩ := s_test hT.st hso ho (.inl rfl) hpc
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  intro m
  obtain ⟨t, ht⟩ := get_persist hpf hT0 (max n m) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left n m
  obtain ⟨p, hp, hpc, -⟩ := tpos hs h0 hpf hnd hwf hT0 hT1 _ hj ht
  have hR : R (max n m) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r1 _ hj t ht hpc
    · exact r2 _ hj t ht hpc
    · exact r3 _ hj t ht hpc
    · exact r4 _ hj t ht hpc
    · exact r5 _ hj t ht hpc
    · exact r6 _ hj t ht hpc
    · exact r7 _ hj t ht hpc
  obtain ⟨k, hk, h⟩ := hR
  exact ⟨k, by omega, h⟩

/-- **(c) With an up-to-date view of the lock, `T` acquires it**: contradiction. -/
theorem at_false {j : Nat} (hj : n ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[T]? = some t)
    (hc : (tr.cfg n).mem.lastWrite LkL ≤ t.views.getCoh LkL) : False := by
  have nxt := adv hpf hwf (henT hs h0 hpf hnd hwf hT0 hT1)
  have tp := tpos_at hs h0 hpf hnd hwf hT0 hT1
  have lw := lw_const hs h0 hpf hnd hwf
  have lz := lock_zero hs h0 hpf hnd hwf
  let LW := (tr.cfg n).mem.lastWrite LkL
  -- the `xchgl` reads the final value `0`: `T` holds
  have a5 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 5 → False := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hI := inv_at hs h0 hpf k
    have hT := hI.thr T t htk
    obtain ⟨md, -, hz, hst, -⟩ := s5 hT.st hT.prom hso ho hpc (hI.own T t htk)
    rw [lz k (by omega)] at hz
    exact holder_false hs h0 hpf hnd hwf (j := k + 1) (by omega) (wt_self htk he)
      (.inl ⟨by rw [hst], by rw [hst]; exact hz⟩)
  have a4 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 4 → False := by
    intro j hj t ht hpc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, hst, -⟩ := s4 hT.st hso ho hpc
    exact a5 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
  have a3 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 3 →
      t.st.st.1.status.zf = true → False := by
    intro j hj t ht hpc hz
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -⟩ := s_jne hT.st hso ho (.inl rfl) hpc
    rw [ite_eq_left hz] at hst
    exact a4 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst])
  have a2 : ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA 2 →
      eax t.st.st.1 = 0#32 → False := by
    intro j hj t ht hpc hz
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, hzf, hst, -⟩ := s_test hT.st hso ho (.inl rfl) hpc
    exact a3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [hst]; exact hzf.mpr hz)
  -- with the coherence view at the last write
  let Q (p : Nat) : Prop := ∀ j, n ≤ j → ∀ t, (tr.cfg j).threads[T]? = some t → t.st.st.2 = pcA p →
    LW ≤ t.views.getCoh LkL → False
  have q1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨ts, v, md, -, hz, hst, hv, -⟩ := s1 hT.st hso ho hpc
    have hv := hv (by rw [lw k (by omega)]; exact hc)
    rw [lz k (by omega)] at hv
    subst hv
    exact a2 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [hst]; exact hz)
  have q3 : Q 3 := by
    intro j hj t ht hpc hc
    by_cases hz : t.st.st.1.status.zf
    · exact a3 j hj t ht hpc hz
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s_jne hT.st hso ho (.inl rfl) hpc
    rw [ite_eq_right hz] at hst
    exact q1 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [SpinSwpStep.getCoh_congr hcoh]; exact hc)
  have q2 : Q 2 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, -, hst, -, -, hcoh⟩ := s_test hT.st hso ho (.inl rfl) hpc
    exact q3 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [SpinSwpStep.getCoh_congr hcoh]; exact hc)
  have q7 : Q 7 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨-, hst, -, hcoh⟩ := s_jne hT.st hso ho (.inr rfl) hpc
    rw [(tp _ (Nat.le_trans hj hk) htk (by decide) hpc).2 rfl] at hst
    exact q1 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]; rfl) (by rw [SpinSwpStep.getCoh_congr hcoh]; exact hc)
  have q6 : Q 6 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, htk, outs, oc, hso, ho, he⟩ := nxt j hj ht
    have hT := (inv_at hs h0 hpf k).thr T t htk
    obtain ⟨md, -, -, hst, -, -, hcoh⟩ := s_test hT.st hso ho (.inr rfl) hpc
    exact q7 (k + 1) (by omega) _ (wt_self htk he) (by rw [hst]) (by rw [SpinSwpStep.getCoh_congr hcoh]; exact hc)
  obtain ⟨p, hp, hpc, -⟩ := tpos hs h0 hpf hnd hwf hT0 hT1 _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q1 j hj t ht hpc hc
  · exact q2 j hj t ht hpc hc
  · exact q3 j hj t ht hpc hc
  · exact a4 j hj t ht hpc
  · exact a5 j hj t ht hpc
  · exact q6 j hj t ht hpc hc
  · exact q7 j hj t ht hpc hc

end Waiter

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. -/
theorem stuck_false (hmf : MemFair Arch.tso tr.cfg) {T : Nat} {tT : Thread isa}
    (hT0 : (tr.cfg n).threads[T]? = some tT) (hT1 : ¬ SpinX64Xchg.XchgDone T (tr.cfg n)) : False := by
  exact memFair_lastWrite_false hmf (reads_inf hs h0 hpf hnd hwf hT0 hT1) hT0 fun _ hj _ ht' hc =>
    at_false hs h0 hpf hnd hwf hT0 hT1 hj ht' hc

end Stuck

omit hs h0 hpf in
/-- The number of threads is constant (formerly a local copy of
`SpinX64CmpxPF.size_eq`, whose statement carries that file's layout instance;
`SpinCommon.size_eq`). -/
theorem size_eq (hpf : PromiseFree Arch.tso tr.cfg) :
    ∀ j, (tr.cfg j).threads.size = (tr.cfg 0).threads.size :=
  SpinCommon.size_eq hpf

end Trace

/-! ## The theorems -/

theorem wait_not_done {tid : Nat} {cfg : Config isa} (hw : SpinX64Xchg.XchgWaiting tid cfg) :
    ¬ SpinX64Xchg.XchgDone tid cfg := by
  obtain ⟨t, ht, hpc⟩ := hw
  rintro ⟨t', ht', hpc'⟩
  rw [ht] at ht'; cases ht'
  apply hpc'
  obtain ⟨k, hk, e⟩ := List.mem_map.mp hpc
  rw [← e]
  refine List.mem_map.mpr ⟨k, List.mem_range.mpr ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega

/-- **Promise-free deadlock-freedom of the x64 `xchg` spinlock** (Stage 3,
promise-free fragment): on a valid layout of the verbatim image
`spinImageV`, on every promise-free stuttering `Arch.tso` trace from a start
configuration under weak fairness and memory fairness, if a thread waits in
its acquire loop, then some thread not yet past its release later is. -/
theorem spin_xchg_live_pf (fuel : Nat) : SpinX64Xchg.XchgSpinLivePF fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, SpinX64Xchg.XchgDone U (tr.cfg j) → SpinX64Xchg.XchgDone U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hs h0 hpf hnd (weakFairInstr_of_promiseFree hpf hwf) hmf ht (wait_not_done hw)

/-- **Per-thread liveness of the one-shot x64 `xchg` workers** (promise-free
fragment): every waiting thread eventually gets past its release. A property
of these one-shot programs (from `stuck_false` and the finite number of
threads), not starvation-freedom of the lock. -/
theorem spin_xchg_live_oneShot_pf (fuel : Nat) : SpinX64Xchg.XchgSpinLiveOneShotPF fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ SpinX64Xchg.XchgDone tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := stable_of_mono (fun k j => SpinX64Xchg.XchgDone k (tr.cfg j)) (tr.cfg 0).threads.size
    (fun k j ⟨_, ht, _⟩ => size_eq hpf j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hs h0 hpf hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist hpf ht n hin
  exact stuck_false hs h0 hpf (fun j hj U hd => hst j hj U hd) (weakFairInstr_of_promiseFree hpf hwf) hmf hu
    (hnd' n hin)

end Gen

/-! ## Concrete instances: the `.kl` runner's executable -/

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete in
/-- `spin_xchg_live_pf` at the `.kl` runner's layout `spinLayoutV`: no
hypothesis left. -/
theorem spin_xchg_live_pf_concrete (fuel : Nat) : @SpinX64Xchg.XchgSpinLivePF spinLayoutV fuel :=
  @spin_xchg_live_pf spinLayoutV spinValidV fuel

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete in
/-- `spin_xchg_live_oneShot_pf` at the runner's layout. -/
theorem spin_xchg_live_oneShot_pf_concrete (fuel : Nat) :
    @SpinX64Xchg.XchgSpinLiveOneShotPF spinLayoutV fuel :=
  @spin_xchg_live_oneShot_pf spinLayoutV spinValidV fuel

section
open Kraken.Promising.X64.EnvG.SpinAbs.Concrete
attribute [local instance] spinLayoutV

/-- **The runner's start, `N` workers** (`spinlock2.kl` for `N = 2`,
`spinlock3.kl` for `N = 3`): `N` copies of the runner's prepared worker
`spinWorkerV0`, the runner's initial memory, at its layout. No configuration
is evaluated. -/
theorem xchgStart_runnerN (N : Nat) :
    @SpinX64Xchg.XchgStart spinLayoutV (List.replicate N spinWorkerV0) spinInitMemV :=
  ⟨by rw [symV_lock, symV_counter]; decide,
   fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorkerV0_start,
   by rw [symV_lock]; simp only [Config.init_mem]; decide⟩

end

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete in
/-- **Promise-free deadlock-freedom for `N` runner workers**: from the
runner's configuration of `N` workers, under `WeakFair ∧ MemFair ∧
PromiseFree`. -/
theorem spin_xchg_live_pf_runnerN (fuel N : Nat) :
    ProgressFromN Arch.tso fuel (Config.init (List.replicate N spinWorkerV0) spinInitMemV)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      (@SpinX64Xchg.XchgWaiting spinLayoutV) (@SpinX64Xchg.XchgDone spinLayoutV) :=
  spin_xchg_live_pf_concrete fuel _ _ (xchgStart_runnerN N)

end Kraken.Promising.Live.SpinX64XchgPF
