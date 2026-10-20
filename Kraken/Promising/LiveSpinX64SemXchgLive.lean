/-
**Stage 3: deadlock-freedom of the x64 `xchg`
spinlock with promises, on the machine with semantic certification**
(`spin_xchg_live_sem : SpinX64Sem.XchgSpinLiveSem fuel`, any `fuel`), on
valid layouts of the verbatim image `SpinAbs.spinImageV`; per-thread
liveness of its one-shot workers (`spin_xchg_live_oneShot_sem`); and the
instances at the `.kl` runner's layout `spinLayoutV` with no hypothesis
left. The port of `LiveSpinSemSwpLive` to `Arch.tso`.

On a semantic trace from a start configuration, `SpinX64SemXchgInv.trace_invS`
gives `InvS` at every index. The core lemma `stuck_false`: if from index `n`
on no thread newly finishes, then every thread is finished at `n`.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n` (it certifies
  without fresh writes, so weak fairness drives it past its release).
- (a') `acq_false`: no thread holds a pinned acquire-kind promise (`AcqAt`) at
  any `j ≥ n`: it stays pre-acquire and enabled, reads the lock infinitely
  often, and memory fairness brings its coherence view past its own promise.
- (b) `no_above`, `above_zero`: from `n` on, every lock message above the top
  zero `Z` at `n` has value `0`.
- (c) Some thread `S` takes infinitely many instruction steps and spins;
  memory fairness brings its view of the lock to `Z`, after which its
  `movl (lock),%eax` reads `0` and its `xchgl` reads `0` (`read_zero`): it
  holds the lock, against (a) (`at_false`).

`MemFair` on x86 is a modelling assumption (store buffers drain in finite
time, as in x86-TSO); see its docstring in `LiveTrace.lean`. The existing
`SpinX64Xchg.XchgSpinLive fuel`, over `succs`, stays open.
-/
import Kraken.Promising.LiveSpinX64SemXchgInv
import Kraken.Promising.LiveSpinX64Sem
import Kraken.Promising.LiveSpinX64XchgPF

namespace Kraken.Promising.Live.SpinX64SemXchgLive

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64XchgTrees Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinX64SemXchgSolo Kraken.Promising.Live.SpinX64SemXchgInv
open Kraken.Promising.Live.SpinX64XchgInv (Static Holder Holder.pos holder_of_pc stepOne_end LkL CtL s1 s_test
  s_jne s4 s8 s9 s12)
open Kraken.Promising.Live.SpinX64Xchg (XchgStart XchgWaiting XchgDone xchgPrePcs)
open Kraken.Promising.Live.SpinX64XchgPF (pre_iff wait_not_done)
open Kraken.Promising.Live.SpinSemSwpSolo (ZeroAt ZNot Gap TopZ read_zero spec_load_w)
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV)

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

local macro "mems" h:ident : tactic =>
  `(tactic| simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at $h:ident)

/-! ## Generic facts -/

local notation "adv" => TraceSem.adv _
local notation "same_or_instr" => TraceSem.same_or_instr _
local notation "get_persist" => TraceSem.get_persist _
local notation "wt_self" => TraceSem.wt_self _
local notation "get_le" => TraceSem.get_le _
local notation "step_prefix" => TraceSem.step_prefix _
local notation "size_eq" => TraceSem.size_eq _
local notation "instr_inf" => TraceSem.instr_inf _

/-- A least witness, without `Nat.find` (`SpinSemSwpLive.exists_least`). -/
theorem exists_least {p : Nat → Prop} : ∀ N n, n ≤ N → p n → ∃ m, p m ∧ ∀ k, k < m → ¬ p k :=
  SpinSemSwpLive.exists_least

/-- A greatest witness up to a bound, without `Nat.findGreatest`
(`SpinSemSwpLive.exists_greatest`). -/
theorem exists_greatest {p : Nat → Prop} (h0 : p 0) : ∀ N, ∃ m, m ≤ N ∧ p m ∧ ∀ k, m < k → k ≤ N → ¬ p k :=
  SpinSemSwpLive.exists_greatest h0

section Gen

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

set_option hygiene false in
local notation "pcA" => (layout spinImageV).addrOf

/-! ## Positions -/

/-- A holder's step: still a holder, or at the `jmp` (position 12). -/
theorem holder_step {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv t.st) (hh : Holder t)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) :
    Holder oc.thread ∨ oc.thread.st.st.2 = pcA 12 := by
  obtain ⟨p, hp, hpc⟩ := hh.pos
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨md, -, hzf, hst, -⟩ := s_test hS.st hs ho (.inr rfl) hpc
    obtain ⟨-, hz⟩ | ⟨h', -⟩ | h' := (holder_iff (by decide) hpc).mp hh
    · exact .inl (.inr (.inl ⟨by rw [hst], by rw [hst]; exact hzf.mpr hz⟩))
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · obtain ⟨-, hst, -⟩ := s_jne hS.st hs ho (.inr rfl) hpc
    obtain ⟨h', -⟩ | ⟨-, hz⟩ | h' := (holder_iff (by decide) hpc).mp hh
    · exact absurd h' (by decide)
    · simp only [hz, ↓reduceIte] at hst; exact .inl (holder_of_pc (p := 8) (by decide) (by rw [hst]))
    · exact absurd h' (by decide)
  · obtain ⟨md, -, hst, -⟩ := s8 hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 9) (by decide) (by rw [hst]))
  · obtain ⟨md, -, hst, -⟩ := s9 hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 10) (by decide) (by rw [hst]))
  · obtain ⟨md, -, hst, -⟩ := s10p hS hs ho hpc
    exact .inl (holder_of_pc (p := 11) (by decide) (by rw [hst]))
  · obtain ⟨hst, -⟩ := s11p hS hs ho hpc
    exact .inr (by rw [hst])

/-- A worker before its end is not halted. -/
theorem not_halted {t : Thread isa} (hS : SInv t.st) (h13 : t.st.st.2 ≠ pcA 13) : t.halted ≠ true := by
  have hSt := hS.st
  obtain ⟨p, hp, hpc⟩ := hS.pc
  simp only [Thread.halted]
  mems hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g, -, hex⟩ := exec_ldl _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    rw [hex]; simp
  · obtain ⟨g, -, hex⟩ := exec_test _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)
    rw [hex]; simp
  · rw [exec_jne _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)]; simp
  · obtain ⟨md, -, hex⟩ := exec_mov1 _ (hSt.at (by decide) (by decide) hpc)
    rw [hex]; simp
  · obtain ⟨g, -, hex⟩ := exec_xchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    rw [hex]; simp
  · obtain ⟨g, -, hex⟩ := exec_test _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)
    rw [hex]; simp
  · rw [exec_jne _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)]; simp
  · obtain ⟨g, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [hex]; simp
  · obtain ⟨md, -, hex⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    rw [hex]; simp
  · obtain ⟨v, md, -, hex⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [hex]; simp
  · rw [exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl]; simp
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)]; simp
  · exact absurd hpc h13

/-! ## Along a trace from a start configuration -/

section Start

variable {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.tso fuel isa}
  (hs : XchgStart states initMem) (h0 : tr.cfg 0 = Config.init states initMem)

include hs h0

theorem inv_at (i : Nat) : InvS fuel (tr.cfg i) := trace_invS hs tr h0 i

theorem wfi (hwf : WeakFairSem Arch.tso fuel tr.cfg) : WeakFairInstrSem Arch.tso fuel tr.cfg :=
  weakFairInstrSem_of_weakFairSem tr
    (fun i tid t ht => dropBounded_of_sinv ((inv_at hs h0 i).thr tid t ht).sinv) hwf

/-- A step appends at most one message. -/
theorem last_step (k : Nat) : (tr.cfg (k + 1)).mem.last ≤ (tr.cfg k).mem.last + 1 := by
  rcases tr.step k with ⟨tid, ⟨t, outs, oc, ht, hso, ho, -, he⟩ | ⟨t, w, ht, -, -, he⟩⟩ | ⟨-, he⟩
  · rw [he]; show oc.mem.last ≤ _
    have hT := (inv_at hs h0 k).thr tid t ht
    cases (step_solo (inv_at hs h0 k).hlc hT.sinv hT.promIn hso ho).eff with
    | quiet hm =>
      rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
      · exact Nat.le_succ _
      · exact Nat.le_of_eq (Memory.last_append _ _)
    | swpFresh hm => rw [hm]; exact Nat.le_of_eq (Memory.last_append _ _)
    | swpFul _ _ _ hm => rw [hm]; exact Nat.le_succ _
    | relFresh hm => rw [hm]; exact Nat.le_of_eq (Memory.last_append _ _)
    | relFul _ _ _ _ hm => rw [hm]; exact Nat.le_succ _
  · rw [he]; exact Nat.le_of_eq (Memory.last_append _ _)
  · rw [he]; exact Nat.le_succ _

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : XchgDone U (tr.cfg j)) : XchgDone U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases same_or_instr j U ht with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
  · exact ⟨u', hu', by rw [e1]; exact hpc⟩
  obtain ⟨hSt, ⟨i, hi, hpi⟩, -⟩ := ((inv_at hs h0 j).thr U t ht).sinv
  have h12 : ¬ i < 12 := fun h => hpc (hpi ▸ (pre_iff hi).mpr h)
  have : i = 12 ∨ i = 13 := by mems hi; omega
  rcases this with rfl | rfl
  · obtain ⟨-, hst, -⟩ := s12 hSt hso ho hpi
    refine ⟨_, wt_self ht he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  · rw [stepOne_end hSt hpi] at hso; cases hso

theorem done_mono {j U : Nat} (hd : XchgDone U (tr.cfg j)) : ∀ k, j ≤ k → XchgDone U (tr.cfg k) := by
  intro k hk
  induction hk with
  | refl => exact hd
  | @step k _ ih => exact done_step hs h0 k U ih

/-! ### A spinning thread -/

section Spinner

variable {S m : Nat} {uS : Thread isa} (hS0 : (tr.cfg m).threads[S]? = some uS)
  (hinf : InfOften fun k => InstrSem Arch.tso fuel S (tr.cfg k) (tr.cfg (k + 1)))
  (hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq u)

include hS0 hinf hpre

/-- A pre-acquire thread is in its test-and-test-and-set loop, with `%eax ≠ 0`
at the second `testl` and `ZF` clear at the second `jne`. -/
theorem tpos (j : Nat) (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t) :
    ∃ p ∈ [1, 2, 3, 4, 5, 6, 7], t.st.st.2 = pcA p ∧ (p = 6 → eax t.st.st.1 ≠ 0#32) ∧
      (p = 7 → t.st.st.1.status.zf = false) := by
  obtain ⟨-, ⟨i, hi, hpc⟩, -⟩ := ((inv_at hs h0 j).thr S t ht).sinv
  have h := (preAcq_iff hi hpc).mp (hpre j hj t ht)
  refine ⟨i, ?_, hpc, fun e hz => h.2.1 ⟨e, hz⟩, fun e => Bool.eq_false_iff.mpr fun hz => h.2.2 ⟨e, hz⟩⟩
  have := h.1
  mems hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- `tpos` at a known position. -/
theorem tpos_at (j : Nat) (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t) {q : Nat}
    (hq : q ∈ spPcs) (hpc : t.st.st.2 = pcA q) :
    (q = 6 → eax t.st.st.1 ≠ 0#32) ∧ (q = 7 → t.st.st.1.status.zf = false) := by
  obtain ⟨p, hp, hpc', h6, h7⟩ := tpos hs h0 hS0 hinf hpre j hj ht
  have hp' : p ∈ spPcs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
  obtain rfl := addrOf_inj hp' hq (hpc'.symm.trans hpc)
  exact ⟨h6, h7⟩

/-- **A spinning thread reads the lock infinitely often** (at its
`movl (lock),%eax`). -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.tso tr.cfg S LkL ts i) := by
  have tp := tpos hs h0 hS0 hinf hpre
  have ta := tpos_at hs h0 hS0 hinf hpre
  have inv := inv_at hs h0
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.tso tr.cfg S LkL ts k
  have r1 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨ts, v, -, -, -, -, -, -, -, ⟨ν, hlog⟩, -⟩ :=
      s1 ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact ⟨k, hk, ts, u, outs, oc, hu, hso, ho, he, v, ν, hlog⟩
  have r7 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 7 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hpc' : u.st.st.2 = pcA 7 := by rw [e1]; exact hpc
    have hz := (ta k (by omega) hu (by decide) hpc').2 rfl
    obtain ⟨-, hst, -⟩ := s_jne ((inv k).thr S u hu).sinv.st hso ho (.inr rfl) hpc'
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
    obtain ⟨k', hk', h⟩ := r1 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r6 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 6 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨md, -, -, hst, -⟩ := s_test ((inv k).thr S u hu).sinv.st hso ho (.inr rfl) (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r7 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r5 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 5 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨tr', old, md, -, -, hst, -⟩ := s5p ((inv k).thr S u hu).sinv hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r6 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r4 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨md, -, hst, -⟩ := s4 ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r5 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r3 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s_jne ((inv k).thr S u hu).sinv.st hso ho (.inl rfl) (by rw [e1]; exact hpc)
    by_cases hz : u.st.st.1.status.zf = true
    · simp only [hz, ↓reduceIte] at hst
      obtain ⟨k', hk', h⟩ := r4 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      exact ⟨k', by omega, h⟩
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
      obtain ⟨k', hk', h⟩ := r1 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      exact ⟨k', by omega, h⟩
  have r2 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 2 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨md, -, -, hst, -⟩ := s_test ((inv k).thr S u hu).sinv.st hso ho (.inl rfl) (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  intro j0
  obtain ⟨t, ht⟩ := get_persist hS0 (max m j0) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left m j0
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  have hR' : R (max m j0) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r1 _ hj t ht hpc
    · exact r2 _ hj t ht hpc
    · exact r3 _ hj t ht hpc
    · exact r4 _ hj t ht hpc
    · exact r5 _ hj t ht hpc
    · exact r6 _ hj t ht hpc
    · exact r7 _ hj t ht hpc
  obtain ⟨k, hk, h⟩ := hR'
  exact ⟨k, by omega, h⟩

end Spinner

/-! ### The core lemma -/

section Stuck

variable {n : Nat} (hnd : ∀ j, n ≤ j → ∀ U, XchgDone U (tr.cfg j) → XchgDone U (tr.cfg n))
  (hwf : WeakFairSem Arch.tso fuel tr.cfg) (hmf : MemFair Arch.tso tr.cfg)

include hnd hwf hmf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ XchgDone U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ XchgDone U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hs h0 (hnd k (by omega) U hd) j hj)

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder t) : False := by
  have inv := inv_at hs h0
  have hnot : ∀ k, j ≤ k → ¬ XchgDone H (tr.cfg k) := by
    refine not_done hs h0 hnd hwf hmf hj fun ⟨t', ht', hpc⟩ => ?_
    rw [ht] at ht'; cases ht'
    obtain ⟨p, hp, hpc'⟩ := hh.pos
    have hp' : p ∈ spPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    refine hpc (hpc' ▸ (pre_iff hp').mpr ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; omega
  have done12 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 12 → False :=
    fun k hk u hu hpc => hnot k hk ⟨u, hu, by rw [hpc, pre_iff (by decide)]; omega⟩
  have hold : ∀ k, j ≤ k → ∃ u, (tr.cfg k).threads[H]? = some u ∧ Holder u := by
    intro k hk
    induction hk with
    | refl => exact ⟨t, ht, hh⟩
    | @step k hjk ih =>
      obtain ⟨u, hu, hhu⟩ := ih
      rcases same_or_instr k H hu with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', by unfold Holder; rw [e1]; exact hhu⟩
      · rcases holder_step ((inv k).thr H u hu).sinv hhu hso ho with h' | hpc
        · exact ⟨_, wt_self hu he, h'⟩
        · exact (done12 (k + 1) (Nat.le_succ_of_le hjk) _ (wt_self hu he) hpc).elim
  have hen : ∀ k, j ≤ k → InstrEnabledSem Arch.tso fuel H (tr.cfg k) := fun k hk => by
    obtain ⟨u, hu, hhu⟩ := hold k hk
    have hT := (inv k).thr H u hu
    obtain ⟨p, hp, hpc⟩ := hhu.pos
    refine instrEnabledSem_of hu hT.sinv (fun e => ?_) ((inv k).bnd H u hu) (.inr hT.nac)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hp' : p ∈ spPcs := by simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    have := addrOf_inj hp' (by decide) (hpc.symm.trans e)
    omega
  have hinfH := wfi hs h0 hwf H ⟨j, hen⟩
  have c11 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 11 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨hst, -⟩ := s11p ((inv k').thr H u' hu').sinv hso ho (by rw [e1]; exact hpc)
    exact done12 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c10 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 10 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨md, -, hst, -⟩ := s10p ((inv k').thr H u' hu').sinv hso ho (by rw [e1]; exact hpc)
    exact c11 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c9 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 9 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨md, -, hst, -⟩ := s9 ((inv k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c10 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c8 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 8 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨md, -, hst, -⟩ := s8 ((inv k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c9 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c7 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 7 →
      u.st.st.1.status.zf = true → False := by
    intro k hk u hu hpc hz
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨-, hst, -⟩ := s_jne ((inv k').thr H u' hu').sinv.st hso ho (.inr rfl) (by rw [e1]; exact hpc)
    have hz' : u'.st.st.1.status.zf = true := by rw [e1]; exact hz
    simp only [hz', ↓reduceIte] at hst
    exact c8 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  rcases hh with ⟨hpc, hz⟩ | ⟨hpc, hz⟩ | hpc
  · obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH ht
    obtain ⟨md, -, hzf, hst, -⟩ := s_test ((inv k').thr H u' hu').sinv.st hso ho (.inr rfl) (by rw [e1]; exact hpc)
    exact c7 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
      (by rw [hst]; exact hzf.mpr (by rw [e1]; exact hz))
  · exact c7 j (Nat.le_refl _) t ht hpc hz
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c8 j (Nat.le_refl _) t ht hpc
    · exact c9 j (Nat.le_refl _) t ht hpc
    · exact c10 j (Nat.le_refl _) t ht hpc
    · exact c11 j (Nat.le_refl _) t ht hpc

/-- **(a') No thread holds a pinned acquire-kind promise from `n` on.** -/
theorem acq_false {j : Nat} (hj : n ≤ j) {U : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[U]? = some u)
    {mz z : Time} (ha : AcqAt U u (tr.cfg j).mem mz z) : False := by
  have inv := inv_at hs h0
  have keep : ∀ k, j ≤ k → ∃ u', (tr.cfg k).threads[U]? = some u' ∧ AcqAt U u' (tr.cfg k).mem mz z := by
    intro k hk
    induction hk with
    | refl => exact ⟨u, hu, ha⟩
    | @step k hjk ih =>
      obtain ⟨u1, hu1, ha1⟩ := ih
      have hjk : j ≤ k := hjk
      rcases same_or_instr k U hu1 with ⟨u', hu', -, -, hp⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', (ha1.of_prom (hp _ ha1.prom)).mono (step_prefix k)⟩
      have hT := (inv k).thr U u1 hu1
      have hf := holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu1 he)
      have hf' := holder_false hs h0 hnd hwf hmf (j := k) (by omega) hu1
      obtain ⟨w, hw, hl, -⟩ := ha1.msg
      refine ⟨_, wt_self hu1 he, AcqAt.mono (step_prefix k) (AcqAt.of_prom ha1 ?_)⟩
      cases (step_solo (inv k).hlc hT.sinv hT.promIn hso ho).eff with
      | quiet _ hkeep _ => exact hkeep mz ha1.prom w hw hl
      | swpFresh _ hpr => rw [hpr]; exact ha1.prom
      | swpFul ts _ _ _ hpr _ _ hz =>
        by_cases e : mz = ts
        · subst e; exact (hf (hz z ha1.zero ha1.znot ha1.lt ha1.gap)).elim
        · rw [hpr]; exact (List.mem_erase_of_ne e).mpr ha1.prom
      | relFresh _ hh => exact (hf' hh).elim
      | relFul _ _ _ _ _ _ hh => exact (hf' hh).elim
  have hpa : ∀ k, j ≤ k → ∀ u', (tr.cfg k).threads[U]? = some u' → PreAcq u' := fun k hk u' hu' => by
    obtain ⟨u2, hu2, ha2⟩ := keep k hk
    rw [hu'] at hu2; cases hu2
    obtain ⟨w, hw, hl, hv⟩ := ha2.msg
    exact ((inv k).thr U u' hu').good.acq mz ha2.prom w hw hl hv
  have hen : ∀ k, j ≤ k → InstrEnabledSem Arch.tso fuel U (tr.cfg k) := fun k hk => by
    obtain ⟨u2, hu2, ha2⟩ := keep k hk
    have hT := (inv k).thr U u2 hu2
    refine instrEnabledSem_of hu2 hT.sinv
      (fun e => absurd ((hpa k hk u2 hu2).1 13 (by decide) e) (by decide))
      ((inv k).bnd U u2 hu2) (.inr hT.nac)
  obtain ⟨w, hw, hl, -⟩ := ha.msg
  obtain ⟨k, hk, u', hu', hc⟩ := memFair_catchup hmf
    (reads_inf hs h0 hu (wfi hs h0 hwf U ⟨j, hen⟩) hpa) hw hl
  obtain ⟨u2, hu2, ha2⟩ := keep k hk
  rw [hu'] at hu2; cases hu2
  have := ((inv k).thr U u' hu').coh mz ha2.prom w (get_le hk hw)
  rw [hl] at this
  exact absurd hc (Nat.not_le_of_lt this)

/-- **(b) From `n` on, every lock message is at or below a zero of the
lock.** -/
theorem no_above {j : Nat} (hj : n ≤ j) {ts : Time} {w : Msg} (hw : (tr.cfg j).mem.get? ts = some w)
    (hl : w.loc = LkL) : ∃ z, ZeroAt LkL (tr.cfg j).mem z ∧ ts ≤ z := by
  have I := inv_at hs h0 j
  let mem := (tr.cfg j).mem
  obtain ⟨Z, hZl, hZ, hZtop⟩ := exists_greatest (p := ZeroAt LkL mem) (.inl ⟨rfl, I.init0⟩) mem.last
  refine Classical.byContradiction fun hno => ?_
  have hlt : Z < ts := Nat.lt_of_not_le fun h => hno ⟨Z, hZ, h⟩
  have htop : TopZ LkL mem Z := fun ts' w' h1 hw' hl' hv' =>
    hZtop ts' h1 (mem.last_le_of_get?_eq_some hw') (.inr ⟨w', hw', hl', hv'⟩)
  obtain ⟨m, ⟨hzm, w', hw', hl'⟩, hmin⟩ := exists_least (p := fun m => Z < m ∧ ∃ w', mem.get? m = some w' ∧
    w'.loc = LkL) ts ts (Nat.le_refl _) ⟨hlt, w, hw, hl⟩
  have hgap : Gap LkL mem Z m := fun k wk h1 h2 hwk hlk => hmin k h2 ⟨h1, wk, hwk, hlk⟩
  obtain ⟨u, hu, ⟨hmu, hzn⟩ | ⟨hh, -⟩⟩ := I.held Z m w' hZ htop hzm hgap hw' hl'
  · exact acq_false hs h0 hnd hwf hmf hj hu
      ⟨hmu, ⟨w', hw', hl', htop m w' hzm hw' hl'⟩, hzm, hZ, hzn, hgap⟩
  · exact holder_false hs h0 hnd hwf hmf hj hu hh

/-- **(b) From `n` on, every lock message above the top zero at `n` has value
`0`.** -/
theorem above_zero {Z : Time}
    (hZtop : ∀ k, Z < k → k ≤ (tr.cfg n).mem.last → ¬ ZeroAt LkL (tr.cfg n).mem k) :
    ∀ j, n ≤ j → ∀ ts w, Z < ts → (tr.cfg j).mem.get? ts = some w → w.loc = LkL → w.val = 0 := by
  intro j hj
  induction hj with
  | refl =>
    intro ts w h1 hw hl
    obtain ⟨z, hz, hle⟩ := no_above hs h0 hnd hwf hmf (Nat.le_refl _) hw hl
    have hzl : z ≤ (tr.cfg n).mem.last := by
      rcases hz with ⟨rfl, -⟩ | ⟨wz, hwz, -⟩
      · exact Nat.zero_le _
      · exact (tr.cfg n).mem.last_le_of_get?_eq_some hwz
    exact (hZtop z (by omega_t) hzl hz).elim
  | @step k hk ih =>
    intro ts w h1 hw hl
    by_cases hle : ts ≤ (tr.cfg k).mem.last
    · exact ih ts w h1 (by rw [← (step_prefix k).get? hle]; exact hw) hl
    · obtain ⟨z, hz, hz'⟩ := no_above hs h0 hnd hwf hmf (Nat.le_succ_of_le hk) hw hl
      have hlast := last_step hs h0 k
      have hts := (tr.cfg (k + 1)).mem.last_le_of_get?_eq_some hw
      rcases hz with ⟨rfl, -⟩ | ⟨wz, hwz, -, hvz⟩
      · omega_t
      · have := (tr.cfg (k + 1)).mem.last_le_of_get?_eq_some hwz
        obtain rfl : z = ts := by omega_t
        rw [hw] at hwz; cases hwz; exact hvz

/-- **(c) With a view of the lock at or past `Z`, a spinning thread acquires
it**: contradiction. -/
theorem at_false {Z : Time} (hZ : ZeroAt LkL (tr.cfg n).mem Z)
    (habove : ∀ j, n ≤ j → ∀ ts w, Z < ts → (tr.cfg j).mem.get? ts = some w → w.loc = LkL → w.val = 0)
    {S m : Nat} {uS : Thread isa} (hm : n ≤ m) (hS0 : (tr.cfg m).threads[S]? = some uS)
    (hinf : InfOften fun k => InstrSem Arch.tso fuel S (tr.cfg k) (tr.cfg (k + 1)))
    (hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq u)
    {j : Nat} (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t)
    (hc : Z ≤ t.views.getCoh LkL) : False := by
  have tp := tpos hs h0 hS0 hinf hpre
  have ta := tpos_at hs h0 hS0 hinf hpre
  have inv := inv_at hs h0
  have hzk : ∀ k, n ≤ k → ZeroAt LkL (tr.cfg k).mem Z := fun k hk => by
    have hp : (tr.cfg n).mem.Prefix (tr.cfg k).mem := by
      induction hk with
      | refl => exact Memory.Prefix.refl _
      | @step k _ ih => exact ih.trans (step_prefix k)
    exact hZ.mono hp
  let Q (p : Nat) : Prop := ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA p →
    Z ≤ t.views.getCoh LkL → False
  have p5 : Q 5 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hSt := ((inv k).thr S u hu).sinv.st
    have hpc' : u.st.st.2 = pcA 5 := by rw [e1]; exact hpc
    obtain ⟨g, hg, hex⟩ := exec_xchg _ (hSt.at (by decide) (by decide) hpc') hSt.dl
    obtain ⟨tr', old, hst, hrd, hw⟩ := spec_rmw_w_tso _ _ rfl hex hso ho
    have h0' : old = 0 := read_zero hrd hw (hzk k (by omega)) (by rw [e2]; exact hc) (habove k (by omega))
    refine holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu he) (.inl ⟨by rw [hst], ?_⟩)
    rw [hst]; show eax (g old) = 0#32
    rw [(hg old).2, h0']; rfl
  have p4 : Q 4 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨md, -, hst, -⟩ := s4 ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p5 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p3z : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 3 →
      t.st.st.1.status.zf = true → Z ≤ t.views.getCoh LkL → False := by
    intro j hj t ht hpc hz hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s_jne ((inv k).thr S u hu).sinv.st hso ho (.inl rfl) (by rw [e1]; exact hpc)
    have hz' : u.st.st.1.status.zf = true := by rw [e1]; exact hz
    simp only [hz', ↓reduceIte] at hst
    exact p4 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p2z : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 2 →
      eax t.st.st.1 = 0#32 → Z ≤ t.views.getCoh LkL → False := by
    intro j hj t ht hpc hz hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨md, -, hzf, hst, -⟩ := s_test ((inv k).thr S u hu).sinv.st hso ho (.inl rfl) (by rw [e1]; exact hpc)
    exact p3z (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [hst]; exact hzf.mpr (by rw [e1]; exact hz))
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hSt := ((inv k).thr S u hu).sinv.st
    have hpc' : u.st.st.2 = pcA 1 := by rw [e1]; exact hpc
    obtain ⟨g, hg, hex⟩ := exec_ldl _ (hSt.at (by decide) (by decide) hpc') hSt.dl
    obtain ⟨ts, v, hst, hrd, hw⟩ := spec_load_w _ _ hex hso ho
    have hv : v = 0 := read_zero hrd hw (hzk k (by omega)) (by rw [e2]; exact hc) (habove k (by omega))
    exact p2z (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (by rw [hst]; show eax (g v) = 0#32; rw [(hg v).2, hv]; rfl)
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p3 : Q 3 := by
    intro j hj t ht hpc hc
    by_cases hz : t.st.st.1.status.zf = true
    · exact p3z j hj t ht hpc hz hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s_jne ((inv k).thr S u hu).sinv.st hso ho (.inl rfl) (by rw [e1]; exact hpc)
    have hz' : ¬ u.st.st.1.status.zf = true := by rw [e1]; exact hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte] at hst
    exact p1 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p2 : Q 2 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨md, -, -, hst, -⟩ := s_test ((inv k).thr S u hu).sinv.st hso ho (.inl rfl) (by rw [e1]; exact hpc)
    exact p3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p7 : Q 7 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hpc' : u.st.st.2 = pcA 7 := by rw [e1]; exact hpc
    have hz := (ta k (by omega) hu (by decide) hpc').2 rfl
    obtain ⟨-, hst, -⟩ := s_jne ((inv k).thr S u hu).sinv.st hso ho (.inr rfl) hpc'
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hst
    exact p1 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p6 : Q 6 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨md, -, -, hst, -⟩ := s_test ((inv k).thr S u hu).sinv.st hso ho (.inr rfl) (by rw [e1]; exact hpc)
    exact p7 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p1 j hj t ht hpc hc
  · exact p2 j hj t ht hpc hc
  · exact p3 j hj t ht hpc hc
  · exact p4 j hj t ht hpc hc
  · exact p5 j hj t ht hpc hc
  · exact p6 j hj t ht hpc hc
  · exact p7 j hj t ht hpc hc

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. -/
theorem stuck_false {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
    (hT1 : ¬ XchgDone T (tr.cfg n)) : False := by
  have inv := inv_at hs h0
  have pos : ∀ j U u, (tr.cfg j).threads[U]? = some u → ¬ XchgDone U (tr.cfg j) →
      ∃ p ∈ spPcs, u.st.st.2 = pcA p ∧ p < 12 := fun j U u hu hnd' => by
    obtain ⟨-, ⟨p, hp, hpc⟩, -⟩ := ((inv j).thr U u hu).sinv
    exact ⟨p, hp, hpc, Classical.byContradiction fun h => hnd' ⟨u, hu, fun hm => h ((pre_iff hp).mp (hpc ▸ hm))⟩⟩
  -- no configuration from `n` on is final
  have hstep : ∀ j, n ≤ j → ∃ k, StepSem Arch.tso fuel k (tr.cfg j) (tr.cfg (j + 1)) := by
    intro j hj
    rcases tr.step j with h | ⟨hf, -⟩
    · exact h
    exfalso
    obtain ⟨t, ht⟩ := get_persist hT0 j hj
    obtain ⟨p, hp, hpc, hlt⟩ := pos j T t ht (not_done hs h0 hnd hwf hmf (Nat.le_refl _) hT1 j hj)
    have hSi := ((inv j).thr T t ht).sinv
    obtain ⟨hlt', rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    have := (Array.all_eq_true.mp hf) T hlt'
    simp only [Bool.and_eq_true] at this
    exact not_halted hSi (fun e => absurd (addrOf_inj hp (by decide) (hpc.symm.trans e)) (by omega)) this.1
  -- a thread `S` taking infinitely many instruction steps
  obtain ⟨S, -, hSinf⟩ := infOften_pigeon (fun k j => StepSem Arch.tso fuel k (tr.cfg j) (tr.cfg (j + 1)))
    (tr.cfg 0).threads.size n fun j hj => by
      obtain ⟨k, hk⟩ := hstep j hj
      refine ⟨k, ?_, hk⟩
      rw [← size_eq j]
      rcases hk with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact lt_size_of_get? ht
  have hSi := instr_inf (fun i tid t ht => dropBounded_of_sinv ((inv i).thr tid t ht).sinv) hstep hSinf
  obtain ⟨m, hm, uS, -, -, hS0, -⟩ := hSi n
  -- `S` is not finished at `m`: a finished thread has no two instruction steps left
  have hSnd : ¬ XchgDone S (tr.cfg m) := by
    rintro ⟨u, hu, hpc⟩
    obtain ⟨k, -, u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hSi hu
    obtain ⟨hSt, ⟨p, hp, hpc'⟩, -⟩ := ((inv k).thr S u' hu').sinv
    have h12 : ¬ p < 12 := fun h => hpc (by rw [← e1, hpc']; exact (pre_iff hp).mpr h)
    have : p = 12 ∨ p = 13 := by mems hp; omega
    rcases this with rfl | rfl
    · obtain ⟨-, hst, -⟩ := s12 hSt hso ho hpc'
      obtain ⟨k2, -, u2, hu2, e3, -, outs2, oc2, hso2, -⟩ := adv hSi (wt_self hu' he)
      rw [stepOne_end ((inv k2).thr S u2 hu2).sinv.st (by rw [e3, hst])] at hso2; cases hso2
    · rw [stepOne_end hSt hpc'] at hso; cases hso
  -- so `S` spins from `m` on
  have hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq u := by
    intro j hj u hu
    obtain ⟨p, hp, hpc, hlt⟩ := pos j S u hu (not_done hs h0 hnd hwf hmf hm hSnd j hj)
    have hnh : ¬ Holder u := fun hh => holder_false hs h0 hnd hwf hmf (by omega) hu hh
    rw [preAcq_iff hp hpc]
    refine ⟨?_, fun ⟨e, hz⟩ => hnh (.inl ⟨e ▸ hpc, hz⟩), fun ⟨e, hz⟩ => hnh (.inr (.inl ⟨e ▸ hpc, hz⟩))⟩
    have h8 : p ∉ [8, 9, 10, 11] := fun h => hnh (holder_of_pc h hpc)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h8
    mems hp
    omega
  -- the top zero of the lock at `n`; memory fairness brings `S` up to it
  obtain ⟨Z, -, hZ, hZtop⟩ := exists_greatest (p := ZeroAt LkL (tr.cfg n).mem)
    (.inl ⟨rfl, (inv n).init0⟩) (tr.cfg n).mem.last
  have habove := above_zero hs h0 hnd hwf hmf hZtop
  rcases hZ with ⟨rfl, h00⟩ | ⟨w, hw, hl, hv⟩
  · exact at_false hs h0 hnd hwf hmf (.inl ⟨rfl, h00⟩) habove hm hS0 hSi hpre (Nat.le_refl _) hS0
      (Nat.zero_le _)
  obtain ⟨j, hj, t', ht', hc⟩ := memFair_catchup hmf (reads_inf hs h0 hS0 hSi hpre) (get_le hm hw) hl
  exact at_false hs h0 hnd hwf hmf (.inr ⟨w, hw, hl, hv⟩) habove hm hS0 hSi hpre hj ht' hc

end Stuck

end Start

/-! ## The theorems -/

/-- **x64 `xchg`-spinlock deadlock-freedom with promises** (Stage 3, on the
machine with semantic certification): on a valid layout of the verbatim image
`spinImageV`, for every `fuel`, on every semantic `Arch.tso` trace from a
start configuration under `WeakFairSem ∧ MemFair`, if a thread waits in its
acquire loop, then some thread not yet past its release later is.

`MemFair` on x86 is a modelling assumption (store buffers drain in finite
time, as in x86-TSO). This is *not* the existing `SpinX64Xchg.XchgSpinLive
fuel`, stated over `succs` (incomplete certification search), which stays
open. -/
theorem spin_xchg_live_sem (fuel : Nat) : SpinX64Sem.XchgSpinLiveSem fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, XchgDone U (tr.cfg j) → XchgDone U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hs h0 hnd hwf hmf ht (wait_not_done hw)

/-- **Per-thread liveness of the one-shot x64 `xchg` workers with promises**
(semantic machine): every waiting thread eventually gets past its release. A
property of these one-shot programs, not starvation-freedom of the lock.
`MemFair` on x86 is a modelling assumption. -/
theorem spin_xchg_live_oneShot_sem (fuel : Nat) : SpinX64Sem.XchgSpinLiveOneShotSem fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ XchgDone tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := SpinCommon.stable_of_mono (fun k j => XchgDone k (tr.cfg j))
    (tr.cfg 0).threads.size (fun k j ⟨_, ht, _⟩ => size_eq j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hs h0 hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist ht n hin
  exact stuck_false hs h0 (fun j hj U hd => hst j hj U hd) hwf hmf hu (hnd' n hin)

end Gen

/-! ## Concrete instances: the `.kl` runner's executable -/

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete in
/-- `spin_xchg_live_sem` at the `.kl` runner's layout `spinLayoutV`: no
hypothesis left. -/
theorem spin_xchg_live_sem_concrete (fuel : Nat) : @SpinX64Sem.XchgSpinLiveSem spinLayoutV fuel :=
  @spin_xchg_live_sem spinLayoutV spinValidV fuel

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete in
/-- `spin_xchg_live_oneShot_sem` at the runner's layout. -/
theorem spin_xchg_live_oneShot_sem_concrete (fuel : Nat) :
    @SpinX64Sem.XchgSpinLiveOneShotSem spinLayoutV fuel :=
  @spin_xchg_live_oneShot_sem spinLayoutV spinValidV fuel

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete in
/-- **Deadlock-freedom with promises for `N` runner workers** (`spinlock2.kl`
for `N = 2`, `spinlock3.kl` for `N = 3`; semantic machine): from the
runner's configuration of `N` workers, under `WeakFairSem ∧ MemFair`. -/
theorem spin_xchg_live_sem_runnerN (fuel N : Nat) :
    SpinSem.ProgressFromSem Arch.tso fuel (Config.init (List.replicate N spinWorkerV0) spinInitMemV)
      (SpinX64Sem.FairX fuel) (@XchgWaiting spinLayoutV) (@XchgDone spinLayoutV) :=
  spin_xchg_live_sem_concrete fuel _ _ (SpinX64XchgPF.xchgStart_runnerN N)

end Kraken.Promising.Live.SpinX64SemXchgLive
