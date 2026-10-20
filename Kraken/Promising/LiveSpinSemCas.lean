/-
**Stage 3: deadlock-freedom of the AArch64 CAS
spinlock with promises, on the machine with semantic certification**
(`spin_cas_live_sem : Spin.CasSpinLiveSem fuel`, any `fuel`), on a valid
layout of `casTtasWorker`; and per-thread liveness of its one-shot workers
(`spin_cas_live_oneShot_sem`).

On a semantic trace from a start configuration, `SpinSemInv.trace_invS`
gives `InvS` at every index. The core lemma `stuck_false`: if from index `n`
on no thread newly finishes, then every thread is finished at `n`.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n`. A holder is
  not pre-acquire, so it certifies without fresh writes and is always
  instruction-enabled; weak fairness (`WeakFairInstrSem`, from `WeakFairSem`
  and the drop bound) drives it to its `STLR`, after which it is finished.
- (a') `acq_false`: no thread holds an acquire promise at any `j ≥ n`. It
  never fulfils it (it would hold the lock), so it stays pre-acquire and
  instruction-enabled, reads the lock infinitely often (`reads_inf`), and
  memory fairness brings its coherence view past its own promise, which a
  certifiable thread keeps above it (`InvS`).
- (b) The lock is `0` (`lock_zero`, from `Held`) and its last write constant
  (`lw_const`) from `n` on: no new lock message, fulfilled or promised.
- (c) A thread `T` is not finished at `n`, so no configuration from `n` on is
  final and some thread steps at every index; one, `S`, steps infinitely
  often (`inf_pigeon`), and, its promises being bounded, takes infinitely
  many instruction steps (`instr_inf`). Promise-blocked threads (a
  pre-acquire thread with a counter promise may be unable to certify) need
  never step. `S` is not finished (a finished thread has no instruction
  step left after `B done`), so it spins; with an up-to-date view of the
  lock its `LDR` reads `0` and its `CASA` writes (`at_false`), against (a).
-/
import Kraken.Promising.LiveSpinSemInv
import Kraken.Promising.LiveSpinSem
import Kraken.Promising.LiveSpinCasPF

namespace Kraken.Promising.Live.SpinSemCas

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinSemSolo Kraken.Promising.Live.SpinSemInv
open Kraken.Promising.Live.SpinSem (CasSpinLiveSem CasSpinLiveOneShotSem)
open Kraken.Promising.Live.SpinCasInv (Static Holder Holder.pos holder_of_pc stepOne_end s3 s5 s7 s8 s9 s1 s11 s12 s15)
open Kraken.Promising.Live.SpinCasPF (pre_iff getCoh_eq wait_not_done casLayout casValid)
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

/-! ## Generic trace facts (instances of `LiveSem`'s generic forms) -/

/-- An infinite pigeonhole: if at every index from `n` on some `k < M`
has `P k`, then some `k < M` has it infinitely often (`Sem.infOften_pigeon`). -/
theorem inf_pigeon (P : Nat → Nat → Prop) : ∀ M n, (∀ j, n ≤ j → ∃ k < M, P k j) →
    ∃ k < M, InfOften (P k) :=
  infOften_pigeon P

/-- A semantic step keeps the number of threads. -/
theorem size_stepSem {fuel tid : Nat} {c c' : Config isa} (h : StepSem Arch.armv8 fuel tid c c') :
    c'.threads.size = c.threads.size :=
  stepSem_size h

section Trace

variable {fuel : Nat} {tr : TraceSem Arch.armv8 fuel isa}

theorem size_eq : ∀ j, (tr.cfg j).threads.size = (tr.cfg 0).threads.size := tr.size_eq

theorem step_prefix (i : Nat) : (tr.cfg i).mem.Prefix (tr.cfg (i + 1)).mem := tr.step_prefix i

theorem get_le {i j : Nat} (hij : i ≤ j) {ts : Time} {w : Msg} (hw : (tr.cfg i).mem.get? ts = some w) :
    (tr.cfg j).mem.get? ts = some w := tr.get_le hij hw

theorem wt_self {k U : Nat} {t : Thread isa} {oc : Outcome isa} (ht : (tr.cfg k).threads[U]? = some t)
    (he : tr.cfg (k + 1) = (tr.cfg k).withThread U oc.thread oc.mem) :
    (tr.cfg (k + 1)).threads[U]? = some oc.thread := tr.wt_self ht he

/-- A step leaves thread `A`'s state and views alone and keeps its promises,
or is an instruction step of `A`. -/
theorem same_or_instr (j A : Nat) {u : Thread isa} (hu : (tr.cfg j).threads[A]? = some u) :
    (∃ u', (tr.cfg (j + 1)).threads[A]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∀ ts ∈ u.prom, ts ∈ u'.prom) ∨
    ∃ outs oc, stepOne Arch.armv8 u A (tr.cfg j).mem = some outs ∧ .ok oc ∈ outs ∧
      tr.cfg (j + 1) = (tr.cfg j).withThread A oc.thread oc.mem :=
  tr.same_or_instr j A hu

theorem get_persist {U j : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[U]? = some t) :
    ∀ k, j ≤ k → ∃ t', (tr.cfg k).threads[U]? = some t' := tr.get_persist ht

/-- **`A`'s next instruction step**, when it takes infinitely many: from `j`,
`A`'s state and views are unchanged until some `k` where it takes one. -/
theorem adv {A : Nat} (hinf : InfOften fun k => InstrSem Arch.armv8 fuel A (tr.cfg k) (tr.cfg (k + 1))) {j : Nat}
    {u : Thread isa} (hu : (tr.cfg j).threads[A]? = some u) :
    ∃ k, j ≤ k ∧ ∃ u', (tr.cfg k).threads[A]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∃ outs oc, stepOne Arch.armv8 u' A (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
        tr.cfg (k + 1) = (tr.cfg k).withThread A oc.thread oc.mem :=
  tr.adv hinf hu

/-- (`weakFairInstrSem_of_weakFairSem` for one thread that steps
infinitely often, enabled or not): on a trace that never stutters from `n`
on, whose threads drop at most one promise per instruction, a thread taking
infinitely many steps takes infinitely many instruction steps (`TraceSem.instr_inf` at `B = 1`). -/
theorem instr_inf {S n : Nat} (hd : ∀ i tid t, (tr.cfg i).threads[tid]? = some t → DropBounded Arch.armv8 1 tid t)
    (hstepj : ∀ j, n ≤ j → ∃ k, StepSem Arch.armv8 fuel k (tr.cfg j) (tr.cfg (j + 1)))
    (hinf : InfOften fun j => StepSem Arch.armv8 fuel S (tr.cfg j) (tr.cfg (j + 1))) :
    InfOften fun j => InstrSem Arch.armv8 fuel S (tr.cfg j) (tr.cfg (j + 1)) :=
  tr.instr_inf hd hstepj hinf

end Trace

/-! ## Positions -/

theorem pci_at {l c : BitVec 64} {s : isa.State} (h : SInv l c s) {i : Nat} (hi : i ∈ spPcs)
    (hpc : s.st.2 = pcA i) : PcI s.st.1 i := by
  obtain ⟨-, j, hj, hpc', hI⟩ := h
  rw [addrOf_inj hi hj (hpc.symm.trans hpc')]; exact hI

/-- A holder's step: still a holder, or at `B done` (position 15). -/
theorem holder_step {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv l c t.st) (hh : Holder t)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    Holder oc.thread ∨ oc.thread.st.st.2 = pcA 15 := by
  obtain ⟨p, hp, hpc⟩ := hh.pos
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, -⟩ := s5 hS.st hs ho hpc
    obtain ⟨-, hz⟩ | h' := (holder_iff (by decide) hpc).mp hh
    · rw [ite_eq_left hz] at hst; exact .inl (holder_of_pc (p := 11) (by decide) (by rw [hst]))
    · exact absurd h' (by decide)
  · obtain ⟨ts, v, hst, -⟩ := s11 hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 12) (by decide) (by rw [hst]))
  · obtain ⟨-, hst, -⟩ := s12 hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 13) (by decide) (by rw [hst]))
  · obtain ⟨hst, -⟩ := s13p hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 14) (by decide) (by rw [hst]))
  · obtain ⟨hst, -⟩ := s14p hS.st hs ho hpc
    exact .inr (by rw [hst])

/-- A worker before its end is not halted. -/
theorem not_halted {l c : BitVec 64} {t : Thread isa} (hS : Static l c t.st) {p : Nat} (hp : p ∈ spPcs)
    (hpc : t.st.st.2 = pcA p) (h17 : p ≠ 17) : t.halted ≠ true := by
  simp only [Thread.halted]
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_mov3 _ (hS.at (by decide) (by decide) hpc)]; simp
  · rw [exec_mov2 _ (hS.at (by decide) (by decide) hpc)]; simp
  · rw [exec_casa _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl]; simp
  · rw [exec_cbz _ (hS.at (by decide) (by decide) hpc)]; simp
  · rw [exec_ldr_l _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl]; simp
  · rw [exec_cbnz _ (hS.at (by decide) (by decide) hpc)]; simp
  · rw [exec_b_try _ (hS.at (by decide) (by decide) hpc)]; simp
  · rw [exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dc]; simp
  · rw [exec_add5 _ (hS.at (by decide) (by decide) hpc)]; simp
  · rw [exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dc]; simp
  · rw [exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl]; simp
  · rw [exec_b_done _ (hS.at (by decide) (by decide) hpc)]; simp
  · exact absurd rfl h17

/-! ## Along a trace from a start configuration -/

section Start

variable {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.armv8 fuel isa}
  (hs : Spin.CasStart l c states initMem) (h0 : tr.cfg 0 = Config.init states initMem)

include hs h0

theorem inv_at (i : Nat) : InvS fuel l c (tr.cfg i) := trace_invS hs tr h0 i

theorem wfi (hwf : WeakFairSem Arch.armv8 fuel tr.cfg) : WeakFairInstrSem Arch.armv8 fuel tr.cfg :=
  weakFairInstrSem_of_weakFairSem tr (fun i tid t ht => dropBounded_of_sinv ((inv_at hs h0 i).thr tid t ht).sinv) hwf

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : Spin.CasDone U (tr.cfg j)) : Spin.CasDone U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases same_or_instr j U ht with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
  · exact ⟨u', hu', by rw [e1]; exact hpc⟩
  obtain ⟨hSt, i, hi, hpi, -⟩ := ((inv_at hs h0 j).thr U t ht).sinv
  have h15 : ¬ i < 15 := fun h => hpc (hpi ▸ (pre_iff hi).mpr h)
  have : i = 15 ∨ i = 17 := by
    simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  rcases this with rfl | rfl
  · obtain ⟨-, hst, -⟩ := s15 hSt hso ho hpi
    refine ⟨_, wt_self ht he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  · rw [stepOne_end hSt hpi] at hso; cases hso

theorem done_mono {j U : Nat} (hd : Spin.CasDone U (tr.cfg j)) : ∀ k, j ≤ k → Spin.CasDone U (tr.cfg k) := by
  intro k hk
  induction hk with
  | refl => exact hd
  | @step k _ ih => exact done_step hs h0 k U ih

/-! ### A spinning thread -/

section Spinner

variable {S m : Nat} {uS : Thread isa} (hS0 : (tr.cfg m).threads[S]? = some uS)
  (hinf : InfOften fun k => InstrSem Arch.armv8 fuel S (tr.cfg k) (tr.cfg (k + 1)))
  (hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq u)

include hS0 hinf hpre

/-- A pre-acquire thread is in its try/spin loop, with `W2 ≠ 0` at the `CBZ`. -/
theorem tpos (j : Nat) (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t) :
    ∃ p ∈ [1, 3, 4, 5, 7, 8, 9], t.st.st.2 = pcA p ∧ (p = 5 → w32 t.st.st.1.regs.X2 ≠ 0#32) := by
  obtain ⟨-, i, hi, hpc, -⟩ := ((inv_at hs h0 j).thr S t ht).sinv
  have h := (preAcq_iff hi hpc).mp (hpre j hj t ht)
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd h.1 (by decide)
    | exact ⟨_, by decide, hpc, fun _ hz => h.2 ⟨rfl, hz⟩⟩
    | exact ⟨_, by decide, hpc, fun e => absurd e (by decide)⟩

/-- **A spinning thread reads the lock infinitely often.** -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg S (L4 l) ts i) := by
  have tp := tpos hs h0 hS0 hinf hpre
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.armv8 tr.cfg S (L4 l) ts k
  have r7 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 7 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hT := ((inv_at hs h0 k).thr S u hu).sinv
    obtain ⟨ts, v, -, -, -, -, -, ⟨ν, hlog⟩, -⟩ := s7 hT.st hso ho (by rw [e1]; exact hpc)
    exact ⟨k, hk, ts, u, outs, oc, hu, hso, ho, he, v, ν, hlog⟩
  have r5 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 5 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hT := ((inv_at hs h0 k).thr S u hu).sinv
    have hpc' : u.st.st.2 = pcA 5 := by rw [e1]; exact hpc
    obtain ⟨p, hp, hpp, hz⟩ := tp _ (Nat.le_trans hj hk) hu
    have hp' : p ∈ spPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    obtain rfl := addrOf_inj hp' (by decide) (hpp.symm.trans hpc')
    obtain ⟨-, hst, -⟩ := s5 hT.st hso ho hpc'
    rw [ite_eq_right (hz rfl)] at hst
    obtain ⟨k', hk', h⟩ := r7 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r4 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨tr', old, hst, -⟩ := s4p ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r5 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r3 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s3 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r4 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r9 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 9 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s9 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r1 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s1 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r8 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 8 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s8 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    by_cases hz : w32 u.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      obtain ⟨k', hk', h⟩ := r9 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      exact ⟨k', by omega, h⟩
    · rw [ite_eq_right hz] at hst
      obtain ⟨k', hk', h⟩ := r7 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      exact ⟨k', by omega, h⟩
  intro j0
  obtain ⟨t, ht⟩ := get_persist hS0 (max m j0) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left m j0
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  have hR : R (max m j0) := by
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

end Spinner

/-! ### The core lemma -/

section Stuck

variable {n : Nat} (hnd : ∀ j, n ≤ j → ∀ U, Spin.CasDone U (tr.cfg j) → Spin.CasDone U (tr.cfg n))
  (hwf : WeakFairSem Arch.armv8 fuel tr.cfg) (hmf : MemFair Arch.armv8 tr.cfg)

include hnd hwf hmf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ Spin.CasDone U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ Spin.CasDone U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hs h0 (hnd k (by omega) U hd) j hj)

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder t) : False := by
  have hnot : ∀ k, j ≤ k → ¬ Spin.CasDone H (tr.cfg k) := by
    refine not_done hs h0 hnd hwf hmf hj fun ⟨t', ht', hpc⟩ => ?_
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
      rcases same_or_instr k H hu with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', by unfold Holder; rw [e1]; exact hhu⟩
      · rcases holder_step ((inv_at hs h0 k).thr H u hu).sinv hhu hso ho with h' | hpc
        · exact ⟨_, wt_self hu he, h'⟩
        · refine absurd ⟨_, wt_self hu he, ?_⟩ (hnot (k + 1) (Nat.le_succ_of_le hjk))
          rw [hpc, pre_iff (by decide)]; omega
  have hen : ∀ k, j ≤ k → InstrEnabledSem Arch.armv8 fuel H (tr.cfg k) := fun k hk => by
    obtain ⟨u, hu, hhu⟩ := hold k hk
    have hT := (inv_at hs h0 k).thr H u hu
    obtain ⟨p, hp, hpc⟩ := hhu.pos
    refine instrEnabledSem_of hu hT.sinv (fun e => ?_) ((inv_at hs h0 k).bnd H u hu)
      (.inr (hT.nac (.inl fun hpa => hpa.2 hhu)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hp' : p ∈ spPcs := by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    have := addrOf_inj hp' (by decide) (hpc.symm.trans e)
    omega
  have hinfH := wfi hs h0 hwf H ⟨j, hen⟩
  have c14 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 14 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨hst, -⟩ := s14p ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    refine hnot (k' + 1) (by omega) ⟨_, wt_self hu' he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  have c13 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 13 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨hst, -⟩ := s13p ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c14 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c12 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 12 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨-, hst, -⟩ := s12 ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c13 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c11 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 11 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨ts, v, hst, -⟩ := s11 ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c12 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  rcases hh with ⟨hpc, hz⟩ | hpc
  · obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH ht
    obtain ⟨-, hst, -⟩ := s5 ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    rw [ite_eq_left (by rw [e1]; exact hz)] at hst
    exact c11 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c11 j (Nat.le_refl _) t ht hpc
    · exact c12 j (Nat.le_refl _) t ht hpc
    · exact c13 j (Nat.le_refl _) t ht hpc
    · exact c14 j (Nat.le_refl _) t ht hpc

/-- **(a') No thread holds an acquire promise from `n` on.** -/
theorem acq_false {j : Nat} (hj : n ≤ j) {U : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[U]? = some u)
    (ha : HasAcq l u (tr.cfg j).mem) : False := by
  obtain ⟨ts, hts, w, hw, hl, hv⟩ := ha
  have keep : ∀ k, j ≤ k → ∃ u', (tr.cfg k).threads[U]? = some u' ∧ ts ∈ u'.prom := by
    intro k hk
    induction hk with
    | refl => exact ⟨u, hu, hts⟩
    | @step k hjk ih =>
      obtain ⟨u1, hu1, hts1⟩ := ih
      have hjk : j ≤ k := hjk
      rcases same_or_instr k U hu1 with ⟨u', hu', -, -, hp⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', hp ts hts1⟩
      have hT := (inv_at hs h0 k).thr U u1 hu1
      have hf := holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu1 he)
      have hf' := holder_false hs h0 hnd hwf hmf (j := k) (by omega) hu1
      cases (step_solo (inv_at hs h0 k).hlc hT.sinv hT.promIn hso ho).eff with
      | quiet _ hkeep _ => exact ⟨_, wt_self hu1 he, hkeep ts hts1 w (get_le hjk hw) hl⟩
      | acqFresh _ _ _ hh _ => exact (hf hh).elim
      | acqFul _ _ _ _ _ _ _ _ hh _ _ => exact (hf hh).elim
      | relFresh _ hh => exact (hf' hh).elim
      | relFul _ _ _ _ _ _ hh => exact (hf' hh).elim
  have hpa : ∀ k, j ≤ k → ∀ u', (tr.cfg k).threads[U]? = some u' → PreAcq u' := fun k hk u' hu' => by
    obtain ⟨u2, hu2, hts2⟩ := keep k hk
    rw [hu'] at hu2; cases hu2
    rcases ((inv_at hs h0 k).thr U u' hu').good.loc ts hts2 w (get_le hk hw) with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd (hl.symm.trans h) (inv_at hs h0 k).hlc
    · exact absurd h hv
  have hen : ∀ k, j ≤ k → InstrEnabledSem Arch.armv8 fuel U (tr.cfg k) := fun k hk => by
    obtain ⟨u2, hu2, hts2⟩ := keep k hk
    have hT := (inv_at hs h0 k).thr U u2 hu2
    refine instrEnabledSem_of hu2 hT.sinv
      (fun e => absurd ((rkLe_iff (p := 17) (by decide) e 1).mp (hpa k hk u2 hu2).1) (by decide))
      ((inv_at hs h0 k).bnd U u2 hu2) (.inr (hT.nac (.inr ⟨ts, hts2, w, get_le hk hw, hl, hv⟩)))
  obtain ⟨k, hk, u', hu', hc⟩ := memFair_catchup hmf (reads_inf hs h0 hu (wfi hs h0 hwf U ⟨j, hen⟩) hpa) hw hl
  obtain ⟨u2, hu2, hts2⟩ := keep k hk
  rw [hu'] at hu2; cases hu2
  have := ((inv_at hs h0 k).thr U u' hu').coh ts hts2 w (get_le hk hw)
  rw [hl] at this
  exact absurd hc (Nat.not_le_of_lt this)

/-- No promise to the lock from `n` on: an acquire promise is (a'); a
release promise is held by a holder (a) or with an acquire promise (a'). -/
theorem no_lock_prom {j : Nat} (hj : n ≤ j) {U : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[U]? = some u)
    {ts : Time} (hts : ts ∈ u.prom) {w : Msg} (hw : (tr.cfg j).mem.get? ts = some w) : w.loc ≠ L4 l := by
  intro hl
  have hT := (inv_at hs h0 j).thr U u hu
  rcases hT.good.loc ts hts w hw with ⟨-, hv, -⟩ | ⟨h, -⟩ | ⟨-, -, h5, -, hacq⟩
  · exact acq_false hs h0 hnd hwf hmf hj hu ⟨ts, hts, w, hw, hl, hv⟩
  · exact (inv_at hs h0 j).hlc (hl.symm.trans h)
  by_cases hpa : PreAcq u
  · exact acq_false hs h0 hnd hwf hmf hj hu (hacq hpa)
  by_cases hh : Holder u
  · exact holder_false hs h0 hnd hwf hmf hj hu hh
  obtain ⟨-, p, hp, hpc, -⟩ := hT.sinv
  apply hpa
  rw [preAcq_iff hp hpc]
  refine ⟨?_, fun h => hh ((holder_iff hp hpc).mpr (.inl h))⟩
  have h11 : p ∉ [11, 12, 13, 14] := fun h => hh ((holder_iff hp hpc).mpr (.inr h))
  have h5' := (rkLe_iff hp hpc 5).mp h5
  revert h11 h5'
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **(b) The lock is `0` from `n` on.** -/
theorem lock_zero (j : Nat) (hj : n ≤ j) : (tr.cfg j).mem.finalVal (L4 l) = 0 :=
  Classical.byContradiction fun hne =>
    let ⟨_, _, hw, hl, _, hu, ho⟩ := (inv_at hs h0 j).held hne
    ho.elim (fun hp => no_lock_prom hs h0 hnd hwf hmf hj hu hp hw hl)
      (fun ⟨hh, _⟩ => holder_false hs h0 hnd hwf hmf hj hu hh)

/-- **(b) The lock's last write is constant from `n` on.** -/
theorem lw_const : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 l) = (tr.cfg n).mem.lastWrite (L4 l) := by
  intro j hj
  induction hj with
  | refl => rfl
  | @step k hk ih =>
    have hk : n ≤ k := hk
    rcases tr.step k with ⟨tid, ⟨t, outs, oc, ht, hso, ho, -, he⟩ | ⟨t, w, ht, -, -, he⟩⟩ | ⟨-, he⟩
    · have hT := (inv_at hs h0 k).thr tid t ht
      have hf := holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self ht he)
      have hf' := holder_false hs h0 hnd hwf hmf (j := k) hk ht
      rw [he]; show oc.mem.lastWrite (L4 l) = _
      cases (step_solo (inv_at hs h0 k).hlc hT.sinv hT.promIn hso ho).eff with
      | quiet hm _ _ =>
        rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
        · exact ih
        · exact ((mem_frame _ { loc := L4 c, val := v, tid } (Ne.symm (inv_at hs h0 k).hlc)).2.1).trans ih
      | acqFresh _ _ _ hh _ => exact (hf hh).elim
      | acqFul _ _ _ _ _ _ _ _ hh _ _ => exact (hf hh).elim
      | relFresh _ hh => exact (hf' hh).elim
      | relFul _ _ _ _ _ _ hh => exact (hf' hh).elim
    · by_cases hl : w.loc = L4 l
      · refine (no_lock_prom hs h0 hnd hwf hmf (j := k + 1) (by omega) (by rw [he]; exact withThread_get_self ht)
          (ts := (tr.cfg k).mem.last + 1) (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (w := w) ?_ hl).elim
        rw [he]; exact Memory.get?_append_last _ _
      · rw [he]; exact (mem_frame _ w hl).2.1.trans ih
    · rw [he]; exact ih

/-- **(c) With an up-to-date view of the lock, a spinning thread acquires
it**: contradiction. -/
theorem at_false {S m : Nat} {uS : Thread isa} (hm : n ≤ m) (hS0 : (tr.cfg m).threads[S]? = some uS)
    (hinf : InfOften fun k => InstrSem Arch.armv8 fuel S (tr.cfg k) (tr.cfg (k + 1)))
    (hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq u)
    {j : Nat} (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t)
    (hc : (tr.cfg n).mem.lastWrite (L4 l) ≤ t.views.getCoh (L4 l)) : False := by
  have tp := tpos hs h0 hS0 hinf hpre
  have lw := lw_const hs h0 hnd hwf hmf
  have lz := lock_zero hs h0 hnd hwf hmf
  let LW := (tr.cfg n).mem.lastWrite (L4 l)
  let Q (p : Nat) : Prop := ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA p →
    LW ≤ t.views.getCoh (L4 l) → False
  have p4 : Q 4 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hpc' : u.st.st.2 = pcA 4 := by rw [e1]; exact hpc
    have hT := ((inv_at hs h0 k).thr S u hu).sinv
    have hz : w32 u.st.st.1.regs.X2 = 0#32 := (pci_at hT (by decide) hpc').2 rfl
    obtain ⟨tr', old, hst, -, hold, hcase⟩ := s4p hT.st hso ho hpc'
    have hold := hold (by rw [lw k (by omega), e2]; exact hc)
    rw [lz _ (by omega)] at hold
    subst hold
    rcases hcase with ⟨hne, -⟩ | ⟨-, -⟩
    · exact hne (by rw [hz]; rfl)
    · refine holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu he) (.inl ⟨by rw [hst], ?_⟩)
      rw [hst]; rfl
  have p3 : Q 3 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -, hcoh⟩ := s3 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p4 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [getCoh_eq hcoh, e2]; exact hc)
  have p9 : Q 9 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -, hcoh⟩ := s9 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [getCoh_eq hcoh, e2]; exact hc)
  have p1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -, hcoh⟩ := s1 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [getCoh_eq hcoh, e2]; exact hc)
  have p8z : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 8 →
      w32 t.st.st.1.regs.X2 = 0#32 → LW ≤ t.views.getCoh (L4 l) → False := by
    intro j hj t ht hpc hz hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -, hcoh⟩ := s8 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    rw [ite_eq_left (by rw [e1]; exact hz)] at hst
    exact p9 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [getCoh_eq hcoh, e2]; exact hc)
  have p7 : Q 7 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨ts, v, hst, -, hv, -, -, -, hmono⟩ :=
      s7 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    have hv := hv (by rw [lw k (by omega), e2]; exact hc)
    rw [lz _ (by omega)] at hv
    subst hv
    exact p8z (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [hst]; rfl)
      (Nat.le_trans (show LW ≤ u.views.getCoh (L4 l) by rw [e2]; exact hc) (hmono _))
  have p5 : Q 5 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hpc' : u.st.st.2 = pcA 5 := by rw [e1]; exact hpc
    obtain ⟨p, hp, hpp, hz⟩ := tp _ (Nat.le_trans hj hk) hu
    have hp' : p ∈ spPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    obtain rfl := addrOf_inj hp' (by decide) (hpp.symm.trans hpc')
    obtain ⟨-, hst, -, hcoh⟩ := s5 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho hpc'
    rw [ite_eq_right (hz rfl)] at hst
    exact p7 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [getCoh_eq hcoh, e2]; exact hc)
  have p8 : Q 8 := by
    intro j hj t ht hpc hc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · exact p8z j hj t ht hpc hz hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -, hcoh⟩ := s8 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    rw [ite_eq_right (by rw [e1]; exact hz)] at hst
    exact p7 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [getCoh_eq hcoh, e2]; exact hc)
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

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. -/
theorem stuck_false {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
    (hT1 : ¬ Spin.CasDone T (tr.cfg n)) : False := by
  have pos : ∀ j U u, (tr.cfg j).threads[U]? = some u → ¬ Spin.CasDone U (tr.cfg j) →
      ∃ p ∈ spPcs, u.st.st.2 = pcA p ∧ p < 15 := fun j U u hu hnd' => by
    obtain ⟨-, p, hp, hpc, -⟩ := ((inv_at hs h0 j).thr U u hu).sinv
    exact ⟨p, hp, hpc, Classical.byContradiction fun h => hnd' ⟨u, hu, fun hm => h ((pre_iff hp).mp (hpc ▸ hm))⟩⟩
  -- no configuration from `n` on is final
  have hstep : ∀ j, n ≤ j → ∃ k, StepSem Arch.armv8 fuel k (tr.cfg j) (tr.cfg (j + 1)) := by
    intro j hj
    rcases tr.step j with h | ⟨hf, -⟩
    · exact h
    exfalso
    obtain ⟨t, ht⟩ := get_persist hT0 j hj
    obtain ⟨p, hp, hpc, hlt⟩ := pos j T t ht (not_done hs h0 hnd hwf hmf (Nat.le_refl _) hT1 j hj)
    have hSt := ((inv_at hs h0 j).thr T t ht).sinv.st
    obtain ⟨hlt', rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    have := (Array.all_eq_true.mp hf) T hlt'
    simp only [Bool.and_eq_true] at this
    exact not_halted hSt hp hpc (by omega) this.1
  -- a thread `S` taking infinitely many instruction steps
  obtain ⟨S, -, hSinf⟩ := inf_pigeon (fun k j => StepSem Arch.armv8 fuel k (tr.cfg j) (tr.cfg (j + 1)))
    (tr.cfg 0).threads.size n fun j hj => by
      obtain ⟨k, hk⟩ := hstep j hj
      refine ⟨k, ?_, hk⟩
      rw [← size_eq j]
      rcases hk with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact lt_size_of_get? ht
  have hSi := instr_inf (fun i tid t ht => dropBounded_of_sinv ((inv_at hs h0 i).thr tid t ht).sinv) hstep hSinf
  obtain ⟨m, hm, uS, -, -, hS0, -⟩ := hSi n
  -- `S` is not finished at `m`: a finished thread has no two instruction steps left
  have hSnd : ¬ Spin.CasDone S (tr.cfg m) := by
    rintro ⟨u, hu, hpc⟩
    obtain ⟨k, -, u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hSi hu
    obtain ⟨hSt, p, hp, hpc', -⟩ := ((inv_at hs h0 k).thr S u' hu').sinv
    have h15 : ¬ p < 15 := fun h => hpc (by rw [← e1, hpc']; exact (pre_iff hp).mpr h)
    have : p = 15 ∨ p = 17 := by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp; omega
    rcases this with rfl | rfl
    · obtain ⟨-, hst, -⟩ := s15 hSt hso ho hpc'
      obtain ⟨k2, -, u2, hu2, e3, -, outs2, oc2, hso2, -⟩ := adv hSi (wt_self hu' he)
      rw [stepOne_end ((inv_at hs h0 k2).thr S u2 hu2).sinv.st (by rw [e3, hst])] at hso2; cases hso2
    · rw [stepOne_end hSt hpc'] at hso; cases hso
  -- so `S` spins from `m` on
  have hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq u := by
    intro j hj u hu
    obtain ⟨p, hp, hpc, hlt⟩ := pos j S u hu (not_done hs h0 hnd hwf hmf hm hSnd j hj)
    have hnh : ¬ Holder u := fun hh => holder_false hs h0 hnd hwf hmf (by omega) hu hh
    rw [preAcq_iff hp hpc]
    refine ⟨?_, fun h => hnh ((holder_iff hp hpc).mpr (.inl h))⟩
    have h11 : p ∉ [11, 12, 13, 14] := fun h => hnh ((holder_iff hp hpc).mpr (.inr h))
    revert hlt h11
    simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- memory fairness brings `S` up to date with the lock
  by_cases h0w : (tr.cfg n).mem.lastWrite (L4 l) = 0
  · exact at_false hs h0 hnd hwf hmf hm hS0 hSi hpre (Nat.le_refl _) hS0 (by rw [h0w]; exact Nat.zero_le _)
  obtain ⟨w, hw, hl⟩ := Memory.get?_lastWriteBelow _ _ _ h0w
  obtain ⟨j, hj, t', ht', hc⟩ := memFair_catchup hmf (reads_inf hs h0 hS0 hSi hpre) (get_le hm hw) hl
  exact at_false hs h0 hnd hwf hmf hm hS0 hSi hpre hj ht' hc

end Stuck

end Start

/-! ## The theorems -/

/-- **Deadlock-freedom of the CAS spinlock with promises** (Stage 3, on the
machine with semantic certification): on a valid layout of `casTtasWorker`,
for every `fuel`, on every semantic trace from a start configuration under
`WeakFairSem ∧ MemFair`, if a thread waits in its try/spin loop, then some
thread not yet past its release later is. -/
theorem spin_cas_live_sem (fuel : Nat) : CasSpinLiveSem fuel := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, Spin.CasDone U (tr.cfg j) → Spin.CasDone U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hs h0 hnd hwf hmf ht (wait_not_done hw)

/-- **Per-thread liveness of the one-shot CAS workers with promises**
(semantic machine): every waiting thread eventually gets past its release (from
`stuck_false` and the finite number of threads). A property of these
one-shot programs, not starvation-freedom of the lock. -/
theorem spin_cas_live_oneShot_sem (fuel : Nat) : CasSpinLiveOneShotSem fuel := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ Spin.CasDone tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := SpinCommon.stable_of_mono (fun k j => Spin.CasDone k (tr.cfg j))
    (tr.cfg 0).threads.size (fun k j ⟨_, ht, _⟩ => size_eq j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hs h0 hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist ht n hin
  exact stuck_false hs h0 (fun j hj U hd => hst j hj U hd) hwf hmf hu (hnd' n hin)

/-! ## A concrete instance -/

/-- `spin_cas_live_sem` at the concrete layout `SpinCasPF.casLayout`: no
hypothesis left. -/
theorem spin_cas_live_sem_concrete (fuel : Nat) : @CasSpinLiveSem casLayout fuel :=
  @spin_cas_live_sem casLayout casValid fuel

/-- `spin_cas_live_oneShot_sem` at the concrete layout `SpinCasPF.casLayout`. -/
theorem spin_cas_live_oneShot_sem_concrete (fuel : Nat) : @CasSpinLiveOneShotSem casLayout fuel :=
  @spin_cas_live_oneShot_sem casLayout casValid fuel

end Kraken.Promising.Live.SpinSemCas
