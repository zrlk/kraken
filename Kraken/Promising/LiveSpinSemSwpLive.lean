/-
**Stage 3: deadlock-freedom of the AArch64 SWP
spinlocks with promises, on the machine with semantic certification**
(`spin_swp_live_sem : SwpSpinLiveSem fuel`, `spin_swpl_live_sem :
SwplSpinLiveSem fuel`, any `fuel`), on valid layouts of `swpWorker` /
`swplWorker`; per-thread liveness of their one-shot workers; and the
concrete-layout instances with no hypothesis left.

One generic proof (`swp_live_sem_gen`, `swp_live_oneShot_sem_gen`) for any
program with `SwpCode P` and `RelR P` (the release is a release write; a
release by a plain RMW would not order the critical section's counter store
before the lock's `0`, so its promise could be certified ahead of the
store). Both hypotheses are discharged for the two programs (`relR_swp`:
`STLR`; `relR_swpl`: `SWPL`), so the instances carry only `[ValidLayout]`.

On a semantic trace from a start configuration, `SpinSemSwpInv.trace_invS`
gives `InvS` at every index. The core lemma `stuck_false`: if from index `n`
on no thread newly finishes, then every thread is finished at `n`.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n` (it certifies
  without fresh writes, so weak fairness drives it past its release).
- (a') `acq_false`: no thread holds a pinned acquire-kind promise (`AcqAt`) at
  any `j ≥ n`: fulfilling it would acquire, so it stays pre-acquire and
  enabled, reads the lock infinitely often, and memory fairness brings its
  coherence view past its own promise.
- (b) `no_above`: from `n` on, every lock message is at or below a zero of
  the lock (the first message above the top zero would be (a) or (a'), by
  `Held`); so (`above_zero`) every lock message above the top zero `Z` at `n`
  has value `0` at every later index.
- (c) As for the CAS lock, some thread `S` takes infinitely many instruction
  steps and spins; memory fairness brings its view of the lock to `Z`, after
  which its `LDR` reads `0` and its `SWPA` reads `0` (`read_zero`): it holds
  the lock, against (a) (`at_false`).
-/
import Kraken.Promising.LiveSpinSemSwpInv
import Kraken.Promising.LiveSpinSemSwp
import Kraken.Promising.LiveSpinSemCas
import Kraken.Promising.LiveSpinSwpFam

namespace Kraken.Promising.Live.SpinSemSwpLive

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinSemSwpSolo Kraken.Promising.Live.SpinSemSwpInv
open Kraken.Promising.Live.SpinSemSwp
open Kraken.Promising.Live.SpinSwp (SwpWaitingG SwpDoneG SwpStartG StartG swpPrePcs)
open Kraken.Promising.Live.SpinSwpInv (Static Holder Holder.pos holder_of_pc stepOne_end s1 s4 s6 s7 s8 s10 s11 s14
  w32)
open Kraken.Promising.SLR.SwpTrees (goto)
open Kraken.Promising.Live.SpinSwpPF (pre_iff wait_not_done)
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Generic facts

The trace lemmas are the layout-free `TraceSem.*` of `LiveSem` (`SpinSemCas`'s
carry an unused layout instance of `casTtasWorker`). -/

local notation "adv" => TraceSem.adv _
local notation "same_or_instr" => TraceSem.same_or_instr _
local notation "get_persist" => TraceSem.get_persist _
local notation "wt_self" => TraceSem.wt_self _
local notation "get_le" => TraceSem.get_le _
local notation "step_prefix" => TraceSem.step_prefix _
local notation "size_eq" => TraceSem.size_eq _
local notation "inf_pigeon" => infOften_pigeon
local notation "instr_inf" => TraceSem.instr_inf _

/-! `exists_least`/`exists_greatest` moved to `LiveSemShape` (same full names). -/

variable [layout : _root_.Layout] {P : Program} [hv : Executable.ValidLayout (layout P)]
  (hC : SwpCode P) (hR : RelR P)

set_option hygiene false in
local notation "pcA" => (layout P).addrOf

/-! ## Positions -/

include hC in
/-- The lock `LDR` (position 6) with its read. -/
theorem s6r {l c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : Static P l c t.st)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) (hpc : t.st.st.2 = pcA 6) :
    ∃ ts v, oc.thread.st = goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 7) ∧
      mem.read? (L4 l) ts = some v ∧ mem.writeIn (L4 l) ts (t.views.getCoh (L4 l)) = false :=
  let ⟨ts, v, hst, hrd, hw⟩ := spec_load_w _ _ (hC.ldr _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl) hs ho
  ⟨ts, v, hst, hrd, hw⟩

include hC hR in
/-- A holder's step: still a holder, or at `B done` (position 14). -/
theorem holder_step {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv P l c t.st) (hh : Holder P t)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    Holder P oc.thread ∨ oc.thread.st.st.2 = pcA 14 := by
  obtain ⟨p, hp, hpc⟩ := hh.pos hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, -⟩ := s4 hC hS.st hs ho hpc
    obtain ⟨-, hz⟩ | h' := (holder_iff hC (by decide) hpc).mp hh
    · simp only [hz, ↓reduceIte] at hst; exact .inl (holder_of_pc (p := 10) (by decide) (by rw [hst]))
    · exact absurd h' (by decide)
  · obtain ⟨v, hst, -⟩ := s10 hC hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 11) (by decide) (by rw [hst]))
  · obtain ⟨-, hst, -⟩ := s11 hC hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 12) (by decide) (by rw [hst]))
  · obtain ⟨hst, -⟩ := s12p hC hS.st hs ho hpc
    exact .inl (holder_of_pc (p := 13) (by decide) (by rw [hst]))
  · obtain ⟨⟨md, hst, -⟩, -⟩ := s13p hC hR hS.st hs ho hpc
    exact .inr (by rw [hst])

include hC hR in
/-- A worker before its end is not halted. -/
theorem not_halted {l c : BitVec 64} {t : Thread isa} (hS : Static P l c t.st) {p : Nat} (hp : p ∈ swPcs)
    (hpc : t.st.st.2 = pcA p) (h16 : p ≠ 16) : t.halted ≠ true := by
  simp only [Thread.halted]
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hC.mov _ (hS.at hC (by decide) (by decide) hpc)]; simp
  · rw [hC.swpa _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl]; simp
  · rw [hC.cbz _ (hS.at hC (by decide) (by decide) hpc)]; simp
  · rw [hC.ldr _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl]; simp
  · rw [hC.cbnz _ (hS.at hC (by decide) (by decide) hpc)]; simp
  · rw [hC.btry _ (hS.at hC (by decide) (by decide) hpc)]; simp
  · rw [hC.ldrc _ c (hS.at hC (by decide) (by decide) hpc) hS.x1 hS.dc]; simp
  · rw [hC.add _ (hS.at hC (by decide) (by decide) hpc)]; simp
  · rw [hC.strc _ c (hS.at hC (by decide) (by decide) hpc) hS.x1 hS.dc]; simp
  · rcases hR _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl with hex | hex <;> rw [hex] <;> simp
  · rw [hC.bdone _ (hS.at hC (by decide) (by decide) hpc)]; simp
  · exact absurd rfl h16

/-! ## Along a trace from a start configuration -/

section Start

variable {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.armv8 fuel isa}
  (hs : SwpStartG (StartG P) l c states initMem) (h0 : tr.cfg 0 = Config.init states initMem)

include hC hR hs h0

theorem inv_at (i : Nat) : InvS fuel P l c (tr.cfg i) := trace_invS hC hR hs tr h0 i

theorem wfi (hwf : WeakFairSem Arch.armv8 fuel tr.cfg) : WeakFairInstrSem Arch.armv8 fuel tr.cfg :=
  weakFairInstrSem_of_weakFairSem tr
    (fun i tid t ht => dropBounded_of_sinv hC hR ((inv_at hC hR hs h0 i).thr tid t ht).sinv) hwf

/-- A step appends at most one message. -/
theorem last_step (k : Nat) : (tr.cfg (k + 1)).mem.last ≤ (tr.cfg k).mem.last + 1 := by
  rcases tr.step k with ⟨tid, ⟨t, outs, oc, ht, hso, ho, -, he⟩ | ⟨t, w, ht, -, -, he⟩⟩ | ⟨-, he⟩
  · rw [he]; show oc.mem.last ≤ _
    have hT := (inv_at hC hR hs h0 k).thr tid t ht
    cases (step_solo hC hR (inv_at hC hR hs h0 k).hlc hT.sinv hT.promIn hso ho).eff with
    | quiet hm => rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]; exact Nat.le_succ _; exact Nat.le_of_eq (Memory.last_append _ _)
    | swpFresh _ _ hm => rw [hm]; exact Nat.le_of_eq (Memory.last_append _ _)
    | swpFul _ _ _ _ _ _ hm => rw [hm]; exact Nat.le_succ _
    | relFresh hm => rw [hm]; exact Nat.le_of_eq (Memory.last_append _ _)
    | relFul _ _ _ _ hm => rw [hm]; exact Nat.le_succ _
  · rw [he]; exact Nat.le_of_eq (Memory.last_append _ _)
  · rw [he]; exact Nat.le_succ _

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : SwpDoneG P U (tr.cfg j)) : SwpDoneG P U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases same_or_instr j U ht with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
  · exact ⟨u', hu', by rw [e1]; exact hpc⟩
  obtain ⟨hSt, i, hi, hpi, -⟩ := ((inv_at hC hR hs h0 j).thr U t ht).sinv
  have h14 : ¬ i < 14 := fun h => hpc (hpi ▸ (pre_iff hC hi).mpr h)
  have : i = 14 ∨ i = 16 := by
    simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  rcases this with rfl | rfl
  · obtain ⟨-, hst, -⟩ := s14 hC hSt hso ho hpi
    refine ⟨_, wt_self ht he, ?_⟩
    rw [hst, pre_iff hC (by decide)]; omega
  · rw [stepOne_end hSt hpi] at hso; cases hso

theorem done_mono {j U : Nat} (hd : SwpDoneG P U (tr.cfg j)) : ∀ k, j ≤ k → SwpDoneG P U (tr.cfg k) := by
  intro k hk
  induction hk with
  | refl => exact hd
  | @step k _ ih => exact done_step hC hR hs h0 k U ih

/-! ### A spinning thread -/

section Spinner

variable {S m : Nat} {uS : Thread isa} (hS0 : (tr.cfg m).threads[S]? = some uS)
  (hinf : InfOften fun k => InstrSem Arch.armv8 fuel S (tr.cfg k) (tr.cfg (k + 1)))
  (hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq P u)

include hS0 hinf hpre

/-- A pre-acquire thread is in its try/spin loop, with `W2 ≠ 0` at the `CBZ`. -/
theorem tpos (j : Nat) (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t) :
    ∃ p ∈ [1, 3, 4, 6, 7, 8], t.st.st.2 = pcA p ∧ (p = 4 → w32 t.st.st.1.regs.X2 ≠ 0#32) := by
  obtain ⟨-, i, hi, hpc, -⟩ := ((inv_at hC hR hs h0 j).thr S t ht).sinv
  have h := (preAcq_iff hC hi hpc).mp (hpre j hj t ht)
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd h.1 (by decide)
    | exact ⟨_, by decide, hpc, fun _ hz => h.2 ⟨rfl, hz⟩⟩
    | exact ⟨_, by decide, hpc, fun e => absurd e (by decide)⟩

/-- **A spinning thread reads the lock infinitely often.** -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg S (L4 l) ts i) := by
  have tp := tpos hC hR hs h0 hS0 hinf hpre
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.armv8 tr.cfg S (L4 l) ts k
  have r6 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 6 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hT := ((inv_at hC hR hs h0 k).thr S u hu).sinv
    obtain ⟨ts, v, -, -, -, -, ⟨ν, hlog⟩, -⟩ := s6 hC hT.st hso ho (by rw [e1]; exact hpc)
    exact ⟨k, hk, ts, u, outs, oc, hu, hso, ho, he, v, ν, hlog⟩
  have r4 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hpc' : u.st.st.2 = pcA 4 := by rw [e1]; exact hpc
    obtain ⟨p, hp, hpp, hz⟩ := tp _ (Nat.le_trans hj hk) hu
    have hp' : p ∈ swPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    obtain rfl := hC.inj hp' (by decide) (hpp.symm.trans hpc')
    obtain ⟨-, hst, -⟩ := s4 hC ((inv_at hC hR hs h0 k).thr S u hu).sinv.st hso ho hpc'
    simp only [hz rfl, ↓reduceIte] at hst
    obtain ⟨k', hk', h⟩ := r6 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r3 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨tr', old, hst, -⟩ := s3p hC ((inv_at hC hR hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r4 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r8 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 8 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s8 hC ((inv_at hC hR hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r1 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s1 hC ((inv_at hC hR hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r7 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 7 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s7 hC ((inv_at hC hR hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    by_cases hz : w32 u.st.st.1.regs.X2 = 0#32
    · simp only [hz, ↓reduceIte] at hst
      obtain ⟨k', hk', h⟩ := r8 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      exact ⟨k', by omega, h⟩
    · simp only [hz, ↓reduceIte] at hst
      obtain ⟨k', hk', h⟩ := r6 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      exact ⟨k', by omega, h⟩
  intro j0
  obtain ⟨t, ht⟩ := get_persist hS0 (max m j0) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left m j0
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  have hR' : R (max m j0) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact r1 _ hj t ht hpc
    · exact r3 _ hj t ht hpc
    · exact r4 _ hj t ht hpc
    · exact r6 _ hj t ht hpc
    · exact r7 _ hj t ht hpc
    · exact r8 _ hj t ht hpc
  obtain ⟨k, hk, h⟩ := hR'
  exact ⟨k, by omega, h⟩

end Spinner

/-! ### The core lemma -/

section Stuck

variable {n : Nat} (hnd : ∀ j, n ≤ j → ∀ U, SwpDoneG P U (tr.cfg j) → SwpDoneG P U (tr.cfg n))
  (hwf : WeakFairSem Arch.armv8 fuel tr.cfg) (hmf : MemFair Arch.armv8 tr.cfg)

include hnd hwf hmf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ SwpDoneG P U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ SwpDoneG P U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hC hR hs h0 (hnd k (by omega) U hd) j hj)

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder P t) : False := by
  have inv := inv_at hC hR hs h0
  have hnot : ∀ k, j ≤ k → ¬ SwpDoneG P H (tr.cfg k) := by
    refine not_done hC hR hs h0 hnd hwf hmf hj fun ⟨t', ht', hpc⟩ => ?_
    rw [ht] at ht'; cases ht'
    obtain ⟨p, hp, hpc'⟩ := hh.pos hC
    have hp' : p ∈ swPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    refine hpc (hpc' ▸ (pre_iff hC hp').mpr ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; omega
  have hold : ∀ k, j ≤ k → ∃ u, (tr.cfg k).threads[H]? = some u ∧ Holder P u := by
    intro k hk
    induction hk with
    | refl => exact ⟨t, ht, hh⟩
    | @step k hjk ih =>
      obtain ⟨u, hu, hhu⟩ := ih
      rcases same_or_instr k H hu with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', by unfold Holder; rw [e1]; exact hhu⟩
      · rcases holder_step hC hR ((inv k).thr H u hu).sinv hhu hso ho with h' | hpc
        · exact ⟨_, wt_self hu he, h'⟩
        · refine absurd ⟨_, wt_self hu he, ?_⟩ (hnot (k + 1) (Nat.le_succ_of_le hjk))
          rw [hpc, pre_iff hC (by decide)]; omega
  have hen : ∀ k, j ≤ k → InstrEnabledSem Arch.armv8 fuel H (tr.cfg k) := fun k hk => by
    obtain ⟨u, hu, hhu⟩ := hold k hk
    have hT := (inv k).thr H u hu
    obtain ⟨p, hp, hpc⟩ := hhu.pos hC
    refine instrEnabledSem_of hC hR hu hT.sinv (fun e => ?_) ((inv k).bnd H u hu)
      (.inr (hT.nac (.inl fun hpa => hpa.2 hhu)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hp' : p ∈ swPcs := by simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    have := hC.inj hp' (by decide) (hpc.symm.trans e)
    omega
  have hinfH := wfi hC hR hs h0 hwf H ⟨j, hen⟩
  have c13 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 13 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨⟨md, hst, -⟩, -⟩ := s13p hC hR ((inv k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    refine hnot (k' + 1) (by omega) ⟨_, wt_self hu' he, ?_⟩
    rw [hst, pre_iff hC (by decide)]; omega
  have c12 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 12 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨hst, -⟩ := s12p hC ((inv k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c13 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c11 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 11 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨-, hst, -⟩ := s11 hC ((inv k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c12 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c10 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 10 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH hu
    obtain ⟨v, hst, -⟩ := s10 hC ((inv k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c11 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  rcases hh with ⟨hpc, hz⟩ | hpc
  · obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hinfH ht
    obtain ⟨-, hst, -⟩ := s4 hC ((inv k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    have hz' : w32 u'.st.st.1.regs.X2 = 0#32 := by rw [e1]; exact hz
    simp only [hz', ↓reduceIte] at hst
    exact c10 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c10 j (Nat.le_refl _) t ht hpc
    · exact c11 j (Nat.le_refl _) t ht hpc
    · exact c12 j (Nat.le_refl _) t ht hpc
    · exact c13 j (Nat.le_refl _) t ht hpc

/-- **(a') No thread holds a pinned acquire-kind promise from `n` on.** -/
theorem acq_false {j : Nat} (hj : n ≤ j) {U : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[U]? = some u)
    {mz z : Time} (ha : AcqAt l U u (tr.cfg j).mem mz z) : False := by
  have inv := inv_at hC hR hs h0
  have keep : ∀ k, j ≤ k → ∃ u', (tr.cfg k).threads[U]? = some u' ∧ AcqAt l U u' (tr.cfg k).mem mz z := by
    intro k hk
    induction hk with
    | refl => exact ⟨u, hu, ha⟩
    | @step k hjk ih =>
      obtain ⟨u1, hu1, ha1⟩ := ih
      have hjk : j ≤ k := hjk
      rcases same_or_instr k U hu1 with ⟨u', hu', -, -, hp⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', (ha1.of_prom (hp _ ha1.prom)).mono (step_prefix k)⟩
      have hT := (inv k).thr U u1 hu1
      have hf := holder_false hC hR hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu1 he)
      have hf' := holder_false hC hR hs h0 hnd hwf hmf (j := k) (by omega) hu1
      obtain ⟨w, hw, hl, -⟩ := ha1.msg
      refine ⟨_, wt_self hu1 he, AcqAt.mono (step_prefix k) (AcqAt.of_prom ha1 ?_)⟩
      cases (step_solo hC hR (inv k).hlc hT.sinv hT.promIn hso ho).eff with
      | quiet _ hkeep _ => exact hkeep mz ha1.prom w hw hl
      | swpFresh _ _ _ hpr => rw [hpr]; exact ha1.prom
      | swpFul ts _ _ _ _ _ _ hpr _ _ hz =>
        by_cases e : mz = ts
        · subst e; exact (hf (hz z ha1.zero ha1.znot ha1.lt ha1.gap)).elim
        · rw [hpr]; exact (List.mem_erase_of_ne e).mpr ha1.prom
      | relFresh _ hh => exact (hf' hh).elim
      | relFul _ _ _ _ _ _ hh => exact (hf' hh).elim
  have hpa : ∀ k, j ≤ k → ∀ u', (tr.cfg k).threads[U]? = some u' → PreAcq P u' := fun k hk u' hu' => by
    obtain ⟨u2, hu2, ha2⟩ := keep k hk
    rw [hu'] at hu2; cases hu2
    obtain ⟨w, hw, hl, hv⟩ := ha2.msg
    rcases ((inv k).thr U u' hu').good.loc mz ha2.prom w hw with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd (hl.symm.trans h) (inv k).hlc
    · exact absurd h hv
  have hen : ∀ k, j ≤ k → InstrEnabledSem Arch.armv8 fuel U (tr.cfg k) := fun k hk => by
    obtain ⟨u2, hu2, ha2⟩ := keep k hk
    have hT := (inv k).thr U u2 hu2
    refine instrEnabledSem_of hC hR hu2 hT.sinv
      (fun e => absurd ((rkLe_iff hC (p := 16) (by decide) e 1).mp (hpa k hk u2 hu2).1) (by decide))
      ((inv k).bnd U u2 hu2) (.inr (hT.nac (.inr ⟨mz, z, ha2⟩)))
  obtain ⟨w, hw, hl, -⟩ := ha.msg
  obtain ⟨k, hk, u', hu', hc⟩ := memFair_catchup hmf
    (reads_inf hC hR hs h0 hu (wfi hC hR hs h0 hwf U ⟨j, hen⟩) hpa) hw hl
  obtain ⟨u2, hu2, ha2⟩ := keep k hk
  rw [hu'] at hu2; cases hu2
  have := ((inv k).thr U u' hu').coh mz ha2.prom w (get_le hk hw)
  rw [hl] at this
  exact absurd hc (Nat.not_le_of_lt this)

/-- **(b) From `n` on, every lock message is at or below a zero of the
lock.** -/
theorem no_above {j : Nat} (hj : n ≤ j) {ts : Time} {w : Msg} (hw : (tr.cfg j).mem.get? ts = some w)
    (hl : w.loc = L4 l) : ∃ z, ZeroAt (L4 l) (tr.cfg j).mem z ∧ ts ≤ z := by
  have I := inv_at hC hR hs h0 j
  let mem := (tr.cfg j).mem
  obtain ⟨Z, hZl, hZ, hZtop⟩ := exists_greatest (p := ZeroAt (L4 l) mem) (.inl ⟨rfl, I.init0⟩) mem.last
  refine Classical.byContradiction fun hno => ?_
  have hlt : Z < ts := Nat.lt_of_not_le fun h => hno ⟨Z, hZ, h⟩
  have htop : TopZ (L4 l) mem Z := fun ts' w' h1 hw' hl' hv' =>
    hZtop ts' h1 (mem.last_le_of_get?_eq_some hw') (.inr ⟨w', hw', hl', hv'⟩)
  obtain ⟨m, ⟨hzm, w', hw', hl'⟩, hmin⟩ := exists_least (p := fun m => Z < m ∧ ∃ w', mem.get? m = some w' ∧
    w'.loc = L4 l) ts ts (Nat.le_refl _) ⟨hlt, w, hw, hl⟩
  have hgap : Gap (L4 l) mem Z m := fun k wk h1 h2 hwk hlk => hmin k h2 ⟨h1, wk, hwk, hlk⟩
  obtain ⟨u, hu, ⟨hmu, hzn⟩ | ⟨hh, -⟩⟩ := I.held Z m w' hZ htop hzm hgap hw' hl'
  · exact acq_false hC hR hs h0 hnd hwf hmf hj hu
      ⟨hmu, ⟨w', hw', hl', htop m w' hzm hw' hl'⟩, hzm, hZ, hzn, hgap⟩
  · exact holder_false hC hR hs h0 hnd hwf hmf hj hu hh

/-- **(b) From `n` on, every lock message above the top zero at `n` has value
`0`.** -/
theorem above_zero {Z : Time}
    (hZtop : ∀ k, Z < k → k ≤ (tr.cfg n).mem.last → ¬ ZeroAt (L4 l) (tr.cfg n).mem k) :
    ∀ j, n ≤ j → ∀ ts w, Z < ts → (tr.cfg j).mem.get? ts = some w → w.loc = L4 l → w.val = 0 := by
  intro j hj
  induction hj with
  | refl =>
    intro ts w h1 hw hl
    obtain ⟨z, hz, hle⟩ := no_above hC hR hs h0 hnd hwf hmf (Nat.le_refl _) hw hl
    have hzl : z ≤ (tr.cfg n).mem.last := by
      rcases hz with ⟨rfl, -⟩ | ⟨wz, hwz, -⟩
      · exact Nat.zero_le _
      · exact (tr.cfg n).mem.last_le_of_get?_eq_some hwz
    exact (hZtop z (by omega_t) hzl hz).elim
  | @step k hk ih =>
    intro ts w h1 hw hl
    by_cases hle : ts ≤ (tr.cfg k).mem.last
    · exact ih ts w h1 (by rw [← (step_prefix k).get? hle]; exact hw) hl
    · obtain ⟨z, hz, hz'⟩ := no_above hC hR hs h0 hnd hwf hmf (Nat.le_succ_of_le hk) hw hl
      have hlast := last_step hC hR hs h0 k
      have hts := (tr.cfg (k + 1)).mem.last_le_of_get?_eq_some hw
      rcases hz with ⟨rfl, -⟩ | ⟨wz, hwz, -, hvz⟩
      · omega_t
      · have := (tr.cfg (k + 1)).mem.last_le_of_get?_eq_some hwz
        obtain rfl : z = ts := by omega_t
        rw [hw] at hwz; cases hwz; exact hvz

/-- **(c) With a view of the lock at or past `Z`, a spinning thread acquires
it**: contradiction. -/
theorem at_false {Z : Time} (hZ : ZeroAt (L4 l) (tr.cfg n).mem Z)
    (habove : ∀ j, n ≤ j → ∀ ts w, Z < ts → (tr.cfg j).mem.get? ts = some w → w.loc = L4 l → w.val = 0)
    {S m : Nat} {uS : Thread isa} (hm : n ≤ m) (hS0 : (tr.cfg m).threads[S]? = some uS)
    (hinf : InfOften fun k => InstrSem Arch.armv8 fuel S (tr.cfg k) (tr.cfg (k + 1)))
    (hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq P u)
    {j : Nat} (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t)
    (hc : Z ≤ t.views.getCoh (L4 l)) : False := by
  have tp := tpos hC hR hs h0 hS0 hinf hpre
  have inv := inv_at hC hR hs h0
  have hzk : ∀ k, n ≤ k → ZeroAt (L4 l) (tr.cfg k).mem Z := fun k hk => by
    have hp : (tr.cfg n).mem.Prefix (tr.cfg k).mem := by
      induction hk with
      | refl => exact Memory.Prefix.refl _
      | @step k _ ih => exact ih.trans (step_prefix k)
    exact hZ.mono hp
  let Q (p : Nat) : Prop := ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA p →
    Z ≤ t.views.getCoh (L4 l) → False
  have p3 : Q 3 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨tr', old, hst, hrd, hw, -⟩ := s3p hC ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    have h0' : old = 0 := read_zero hrd hw (hzk k (by omega)) (by rw [e2]; exact hc) (habove k (by omega))
    refine holder_false hC hR hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu he) (.inl ⟨by rw [hst], ?_⟩)
    rw [hst, w32_set2, h0']; rfl
  have p8 : Q 8 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s8 hC ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p7z : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 7 →
      w32 t.st.st.1.regs.X2 = 0#32 → Z ≤ t.views.getCoh (L4 l) → False := by
    intro j hj t ht hpc hz hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s7 hC ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    have hz' : w32 u.st.st.1.regs.X2 = 0#32 := by rw [e1]; exact hz
    simp only [hz', ↓reduceIte] at hst
    exact p8 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p6 : Q 6 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨ts, v, hst, hrd, hw⟩ := s6r hC ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    have hv : v = 0 := read_zero hrd hw (hzk k (by omega)) (by rw [e2]; exact hc) (habove k (by omega))
    exact p7z (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]) (by rw [hst, w32_set2, hv]; rfl)
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p7 : Q 7 := by
    intro j hj t ht hpc hc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · exact p7z j hj t ht hpc hz hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s7 hC ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    have hz' : ¬ w32 u.st.st.1.regs.X2 = 0#32 := by rw [e1]; exact hz
    simp only [hz', ↓reduceIte] at hst
    exact p6 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p4 : Q 4 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    have hpc' : u.st.st.2 = pcA 4 := by rw [e1]; exact hpc
    obtain ⟨p, hp, hpp, hz⟩ := tp _ (Nat.le_trans hj hk) hu
    have hp' : p ∈ swPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
    obtain rfl := hC.inj hp' (by decide) (hpp.symm.trans hpc')
    obtain ⟨-, hst, -⟩ := s4 hC ((inv k).thr S u hu).sinv.st hso ho hpc'
    simp only [hz rfl, ↓reduceIte] at hst
    exact p6 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  have p1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := adv hinf ht
    obtain ⟨-, hst, -⟩ := s1 hC ((inv k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (Nat.le_trans (by rw [e2]; exact hc) ((stepOne_dord _ hso ho).2.1 _))
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p1 j hj t ht hpc hc
  · exact p3 j hj t ht hpc hc
  · exact p4 j hj t ht hpc hc
  · exact p6 j hj t ht hpc hc
  · exact p7 j hj t ht hpc hc
  · exact p8 j hj t ht hpc hc

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. -/
theorem stuck_false {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
    (hT1 : ¬ SwpDoneG P T (tr.cfg n)) : False := by
  have inv := inv_at hC hR hs h0
  have pos : ∀ j U u, (tr.cfg j).threads[U]? = some u → ¬ SwpDoneG P U (tr.cfg j) →
      ∃ p ∈ swPcs, u.st.st.2 = pcA p ∧ p < 14 := fun j U u hu hnd' => by
    obtain ⟨-, p, hp, hpc, -⟩ := ((inv j).thr U u hu).sinv
    exact ⟨p, hp, hpc, Classical.byContradiction fun h => hnd' ⟨u, hu, fun hm => h ((pre_iff hC hp).mp (hpc ▸ hm))⟩⟩
  -- no configuration from `n` on is final
  have hstep : ∀ j, n ≤ j → ∃ k, StepSem Arch.armv8 fuel k (tr.cfg j) (tr.cfg (j + 1)) := by
    intro j hj
    rcases tr.step j with h | ⟨hf, -⟩
    · exact h
    exfalso
    obtain ⟨t, ht⟩ := get_persist hT0 j hj
    obtain ⟨p, hp, hpc, hlt⟩ := pos j T t ht (not_done hC hR hs h0 hnd hwf hmf (Nat.le_refl _) hT1 j hj)
    have hSt := ((inv j).thr T t ht).sinv.st
    obtain ⟨hlt', rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    have := (Array.all_eq_true.mp hf) T hlt'
    simp only [Bool.and_eq_true] at this
    exact not_halted hC hR hSt hp hpc (by omega) this.1
  -- a thread `S` taking infinitely many instruction steps
  obtain ⟨S, -, hSinf⟩ := inf_pigeon (fun k j => StepSem Arch.armv8 fuel k (tr.cfg j) (tr.cfg (j + 1)))
    (tr.cfg 0).threads.size n fun j hj => by
      obtain ⟨k, hk⟩ := hstep j hj
      refine ⟨k, ?_, hk⟩
      rw [← size_eq j]
      rcases hk with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact lt_size_of_get? ht
  have hSi := instr_inf (fun i tid t ht => dropBounded_of_sinv hC hR ((inv i).thr tid t ht).sinv) hstep hSinf
  obtain ⟨m, hm, uS, -, -, hS0, -⟩ := hSi n
  -- `S` is not finished at `m`: a finished thread has no two instruction steps left
  have hSnd : ¬ SwpDoneG P S (tr.cfg m) := by
    rintro ⟨u, hu, hpc⟩
    obtain ⟨k, -, u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hSi hu
    obtain ⟨hSt, p, hp, hpc', -⟩ := ((inv k).thr S u' hu').sinv
    have h14 : ¬ p < 14 := fun h => hpc (by rw [← e1, hpc']; exact (pre_iff hC hp).mpr h)
    have : p = 14 ∨ p = 16 := by simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hp; omega
    rcases this with rfl | rfl
    · obtain ⟨-, hst, -⟩ := s14 hC hSt hso ho hpc'
      obtain ⟨k2, -, u2, hu2, e3, -, outs2, oc2, hso2, -⟩ := adv hSi (wt_self hu' he)
      rw [stepOne_end ((inv k2).thr S u2 hu2).sinv.st (by rw [e3, hst])] at hso2; cases hso2
    · rw [stepOne_end hSt hpc'] at hso; cases hso
  -- so `S` spins from `m` on
  have hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq P u := by
    intro j hj u hu
    obtain ⟨p, hp, hpc, hlt⟩ := pos j S u hu (not_done hC hR hs h0 hnd hwf hmf hm hSnd j hj)
    have hnh : ¬ Holder P u := fun hh => holder_false hC hR hs h0 hnd hwf hmf (by omega) hu hh
    rw [preAcq_iff hC hp hpc]
    refine ⟨?_, fun h => hnh ((holder_iff hC hp hpc).mpr (.inl h))⟩
    have h10 : p ∉ [10, 11, 12, 13] := fun h => hnh ((holder_iff hC hp hpc).mpr (.inr h))
    revert hlt h10
    simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- the top zero of the lock at `n`; memory fairness brings `S` up to it
  obtain ⟨Z, -, hZ, hZtop⟩ := exists_greatest (p := ZeroAt (L4 l) (tr.cfg n).mem)
    (.inl ⟨rfl, (inv n).init0⟩) (tr.cfg n).mem.last
  have habove := above_zero hC hR hs h0 hnd hwf hmf hZtop
  rcases hZ with ⟨rfl, h00⟩ | ⟨w, hw, hl, hv⟩
  · exact at_false hC hR hs h0 hnd hwf hmf (.inl ⟨rfl, h00⟩) habove hm hS0 hSi hpre (Nat.le_refl _) hS0
      (Nat.zero_le _)
  obtain ⟨j, hj, t', ht', hc⟩ := memFair_catchup hmf (reads_inf hC hR hs h0 hS0 hSi hpre) (get_le hm hw) hl
  exact at_false hC hR hs h0 hnd hwf hmf (.inr ⟨w, hw, hl, hv⟩) habove hm hS0 hSi hpre hj ht' hc

end Stuck

end Start

/-! ## The theorems -/

include hC hR in
/-- **Deadlock-freedom of the workers of an SWP-spinlock program with
promises** (semantic machine): for any program with `SwpCode P` whose release
is a release write (`RelR P`), on a valid layout. -/
theorem swp_live_sem_gen (fuel : Nat) : SwpLiveSemUnderG P (StartG P) fuel := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, SwpDoneG P U (tr.cfg j) → SwpDoneG P U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hC hR hs h0 hnd hwf hmf ht (wait_not_done hC hw)

include hC hR in
/-- **Per-thread liveness of the one-shot workers of an SWP-spinlock program
with promises** (semantic machine). Not starvation-freedom of the lock. -/
theorem swp_live_oneShot_sem_gen (fuel : Nat) : SwpOneShotSemUnderG P (StartG P) fuel := by
  intro l c states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ SwpDoneG P tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := SpinCommon.stable_of_mono (fun k j => SwpDoneG P k (tr.cfg j))
    (tr.cfg 0).threads.size (fun k j ⟨_, ht, _⟩ => size_eq j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hC hR hs h0 hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist ht n hin
  exact stuck_false hC hR hs h0 (fun j hj U hd => hst j hj U hd) hwf hmf hu (hnd' n hin)

/-! ## The SWP and SWPL spinlocks -/

section Instances

/-- `swpWorker`'s release is a release store (`STLR`). -/
theorem relR_swp [Executable.ValidLayout (layout swpWorker)] : RelR swpWorker :=
  fun st _ h hx hd => .inl (SLR.SwpTrees.exec_stlr st (toAt h) hx hd)

/-- `swplWorker`'s release is a release swap (`SWPL`). -/
theorem relR_swpl [Executable.ValidLayout (layout swplWorker)] : RelR swplWorker :=
  fun st _ h hx hd => .inr (swpl_rel st h hx hd)

/-- **SWP-spinlock deadlock-freedom with promises** (`SWPA`/`STLR`, Stage 3,
on the machine with semantic certification): on a valid layout of
`swpWorker`, for every `fuel`, on every semantic trace from a start
configuration under `WeakFairSem ∧ MemFair`, if a thread waits in its
try/spin loop, then some thread not yet past its release later is. -/
theorem spin_swp_live_sem [Executable.ValidLayout (layout swpWorker)] (fuel : Nat) : SwpSpinLiveSem fuel :=
  (swp_live_sem_gen swpCode relR_swp fuel).mono fun _ _ _ => SpinSwpFam.startG_swp

/-- **Per-thread liveness of the one-shot SWP workers with promises**
(semantic machine). A property of these one-shot programs, not
starvation-freedom of the lock. -/
theorem spin_swp_live_oneShot_sem [Executable.ValidLayout (layout swpWorker)] (fuel : Nat) :
    SwpSpinLiveOneShotSem fuel :=
  (swp_live_oneShot_sem_gen swpCode relR_swp fuel).mono fun _ _ _ => SpinSwpFam.startG_swp

/-- **SWPL-spinlock deadlock-freedom with promises** (`SWPA`/`SWPL`, Stage 3,
semantic machine), on a valid layout of `swplWorker`. -/
theorem spin_swpl_live_sem [Executable.ValidLayout (layout swplWorker)] (fuel : Nat) : SwplSpinLiveSem fuel :=
  (swp_live_sem_gen swplCode relR_swpl fuel).mono fun _ _ _ => SpinSwpFam.startG_swpl

/-- **Per-thread liveness of the one-shot SWPL workers with promises**
(semantic machine). A property of these one-shot programs, not
starvation-freedom of the lock. -/
theorem spin_swpl_live_oneShot_sem [Executable.ValidLayout (layout swplWorker)] (fuel : Nat) :
    SwplSpinLiveOneShotSem fuel :=
  (swp_live_oneShot_sem_gen swplCode relR_swpl fuel).mono fun _ _ _ => SpinSwpFam.startG_swpl

end Instances

/-! ## Concrete instances -/

open Kraken.Promising.Live.SpinSwpFam (swpLiveLayout swpLiveValid swplLiveLayout swplLiveValid)

/-- `spin_swp_live_sem` at the concrete layout `SpinSwpFam.swpLiveLayout`: no
hypothesis left. -/
theorem spin_swp_live_sem_concrete (fuel : Nat) : @SwpSpinLiveSem swpLiveLayout fuel :=
  @spin_swp_live_sem swpLiveLayout swpLiveValid fuel

/-- `spin_swp_live_oneShot_sem` at the concrete layout `swpLiveLayout`. -/
theorem spin_swp_live_oneShot_sem_concrete (fuel : Nat) : @SwpSpinLiveOneShotSem swpLiveLayout fuel :=
  @spin_swp_live_oneShot_sem swpLiveLayout swpLiveValid fuel

/-- `spin_swpl_live_sem` at the concrete layout `SpinSwpFam.swplLiveLayout`: no
hypothesis left. -/
theorem spin_swpl_live_sem_concrete (fuel : Nat) : @SwplSpinLiveSem swplLiveLayout fuel :=
  @spin_swpl_live_sem swplLiveLayout swplLiveValid fuel

/-- `spin_swpl_live_oneShot_sem` at the concrete layout `swplLiveLayout`. -/
theorem spin_swpl_live_oneShot_sem_concrete (fuel : Nat) : @SwplSpinLiveOneShotSem swplLiveLayout fuel :=
  @spin_swpl_live_oneShot_sem swplLiveLayout swplLiveValid fuel

end Kraken.Promising.Live.SpinSemSwpLive
