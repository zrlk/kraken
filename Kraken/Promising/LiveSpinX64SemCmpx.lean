/-
**Stage 3: deadlock-freedom of the x64
`lock cmpxchg` spinlock with promises, on the machine with semantic
certification** (`spin_cmpx_live_sem : SpinX64Sem.CmpxSpinLiveSem fuel`, any
`fuel`), on a valid layout of `CmpxAbs.cmpxImageV`; and per-thread liveness of
its one-shot workers (`spin_cmpx_live_oneShot_sem`). The x64 counterpart of
`LiveSpinSemCas.lean` (AArch64 CAS), under `WeakFairSem Arch.tso ∧ MemFair
Arch.tso`. `MemFair` on x86 is a modelling assumption (as on AArch64): the
SDM does not state it; it is the per-thread form of eventual store
visibility.

On a semantic trace from a start configuration, `SpinX64SemCmpxInv.trace_invS`
gives `InvS` at every index. **TSO shortcut**: every worker certifies without
fresh writes (`TS.nac`), so every worker not at its end is always
instruction-enabled (`en`), and weak fairness drives every such thread
directly (no pigeonhole over stepping threads, unlike AArch64, where a
pre-acquire thread with a counter promise may be unable to certify). The core
lemma `stuck_false`: if from index `n` on no thread newly finishes, then
every thread is finished at `n`.

- (a) `holder_false`: no thread holds the lock at any `j ≥ n` (weak fairness
  drives it through its release to `jmp done`).
- (a') `acq_false`: no thread holds an acquire promise at any `j ≥ n`: it
  never fulfils it, so it stays pre-acquire, executes its `lock cmpxchg`
  infinitely often (`reads_inf`; the read is logged with promises too,
  `spec_rmwo_p_log`), and memory fairness brings its coherence view past its
  own promise, which a certifiable thread keeps above it (`InvS`).
- (b) The lock is `0` (`lock_zero`) and its last write constant (`lw_const`)
  from `n` on.
- (c) The waiting thread `T` itself spins from `n` on, with no promise (a
  pre-acquire thread with a promise holds an acquire promise, against (a'));
  memory fairness brings it up to date with the lock, after which its
  `lock cmpxchg` reads `0` and writes (`at_false`), against (a).
-/
import Kraken.Promising.LiveSpinX64SemCmpxInv
import Kraken.Promising.LiveSpinX64Sem
import Kraken.Promising.LiveSpinX64CmpxPF

namespace Kraken.Promising.Live.SpinX64SemCmpx

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinX64SemCmpxSolo Kraken.Promising.Live.SpinX64SemCmpxInv
open Kraken.Promising.Live.SpinX64CmpxInv (LkL CtL Static Holder Holder.pos stepOne_end s1 s2 s3 s4 s5 s6 s9)
open Kraken.Promising.Live.SpinX64CmpxPF (pre_iff)
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC)

/-! ## The read of a fencing RMW is logged, with any promise set -/

/-- A write's successors extend the log. A hoist candidate. -/
theorem writeSuccs_log {A : Arch} {tid : Nat} {iv : InstrViews} {c c' : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) :
    c.log ⊆ c'.log := by
  simp only [writeSuccs, List.mem_append, List.mem_filterMap, List.mem_ite_nil_right, List.mem_singleton] at h
  rcases h with ⟨t, -, h⟩ | ⟨-, rfl⟩
  · split at h
    · have aux : ∀ {p : Prop} [Decidable p] {x y : Ctx}, (if p then some x else none) = some y → x = y :=
        fun {p} _ _ _ h => by by_cases hp : p <;> simp [hp] at h; exact h
      cases aux h; exact fun _ hx => List.mem_append_left _ hx
    · cases h
  · exact fun _ hx => List.mem_append_left _ hx

/-- **An RMW under `rmwFence` logs its read**, with any promise set. A hoist candidate. -/
theorem spec_rmwo_p_log {I : ISA} {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Outcome I))} {o : Outcome I} (hA : A.rmwFence = true) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → I.State} (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) : ∃ tr v ν, TraceEv.read l tr v ν ∈ o.log := by
  obtain ⟨tree, c', hex', hr, -, -, -, hl⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  obtain ⟨tr', old', hx', -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, e3⟩ := hx'
  obtain ⟨ν, hν⟩ : ∃ ν, TraceEv.read l tr old ν ∈ c1.log := by
    first | (rw [← e3]; exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩)
          | (rw [e3]; exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩)
  refine ⟨tr, old, ν, ?_⟩
  rw [hl]
  cases hop : op old with
  | none =>
    simp only [hop] at h
    obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    exact TsoRmw.fence_log _ _ hν
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    obtain ⟨-, -, -, hl'⟩ := TsoRmw.rmwPost_keeps (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    refine TsoRmw.fence_log _ _ ?_; rw [hl']
    exact writeSuccs_log h2 hν

section Gen

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

/-! ## Positions -/

theorem pci_at {s : isa.State} (h : SInv s) {i : Nat} (hi : i ∈ spPcs) (hpc : s.st.2 = pcA i) : PcI s.st.1 i := by
  obtain ⟨-, j, hj, hpc', hI⟩ := h
  rw [addrOf_inj hi hj (hpc.symm.trans hpc')]; exact hI

/-- A pre-acquire worker is in its acquire loop, with `ZF` clear at the `jne`. -/
theorem pos_of_preAcq {t : Thread isa} (hS : SInv t.st) (h : PreAcq t) :
    ∃ p ∈ [1, 2, 3, 4], t.st.st.2 = pcA p ∧ (p = 4 → t.st.st.1.status.zf = false) := by
  obtain ⟨-, i, hi, hpc, -⟩ := hS
  have h' := (preAcq_iff hi hpc).mp h
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd h'.1 (by decide)
    | exact ⟨_, by decide, hpc, fun _ => Bool.eq_false_iff.mpr fun hz => h'.2 ⟨rfl, hz⟩⟩
    | exact ⟨_, by decide, hpc, fun e => absurd e (by decide)⟩

theorem ne10_of_preAcq {t : Thread isa} (h : PreAcq t) : t.st.st.2 ≠ pcA 10 := fun e =>
  absurd ((rkLe_iff (p := 10) (by decide) e 0).mp h.1) (by decide)

/-- A worker up to its release that does not hold the lock is pre-acquire. -/
theorem preAcq_of {t : Thread isa} (hS : SInv t.st) (hlt : t.st.st.2 ∈ SpinX64.cmpxPrePcs) (hnh : ¬ Holder t) :
    PreAcq t := by
  obtain ⟨-, p, hp, hpc, -⟩ := hS
  rw [hpc, pre_iff hp] at hlt
  rw [preAcq_iff hp hpc]
  refine ⟨?_, fun h => hnh ((holder_iff hp hpc).mpr (.inl h))⟩
  have h5 : p ∉ [5, 6, 7, 8] := fun h => hnh ((holder_iff hp hpc).mpr (.inr h))
  revert hlt h5
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A worker of rank at most `4` is up to its release. -/
theorem pre_of_rk4 {t : Thread isa} (hS : SInv t.st) (h : RkLe t 4) : t.st.st.2 ∈ SpinX64.cmpxPrePcs := by
  obtain ⟨-, p, hp, hpc, -⟩ := hS
  have h4 := (rkLe_iff hp hpc 4).mp h
  rw [hpc, pre_iff hp]
  revert h4
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Along a trace from a start configuration -/

section Start

variable {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.tso fuel isa}
  (hs : SpinX64.CmpxStart states initMem) (h0 : tr.cfg 0 = Config.init states initMem)

include hs h0

theorem inv_at (i : Nat) : InvS fuel (tr.cfg i) := trace_invS hs tr h0 i

omit hs h0 in
theorem wt_self {k U : Nat} {t : Thread isa} {oc : Outcome isa} (ht : (tr.cfg k).threads[U]? = some t)
    (he : tr.cfg (k + 1) = (tr.cfg k).withThread U oc.thread oc.mem) :
    (tr.cfg (k + 1)).threads[U]? = some oc.thread := tr.wt_self ht he

omit hs h0 in
theorem get_persist {U j : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[U]? = some t) :
    ∀ k, j ≤ k → ∃ t', (tr.cfg k).threads[U]? = some t' := tr.get_persist ht

/-- **TSO: a worker not at its end is always instruction-enabled** (it
certifies without fresh writes, `TS.nac`). -/
theorem en {k U : Nat} {u : Thread isa} (hu : (tr.cfg k).threads[U]? = some u) (h10 : u.st.st.2 ≠ pcA 10) :
    InstrEnabledSem Arch.tso fuel U (tr.cfg k) :=
  instrEnabledSem_of hu ((inv_at hs h0 k).thr U u hu).sinv h10 ((inv_at hs h0 k).bnd U u hu)
    (.inr ((inv_at hs h0 k).thr U u hu).nac)

theorem wfi (hwf : WeakFairSem Arch.tso fuel tr.cfg) : WeakFairInstrSem Arch.tso fuel tr.cfg :=
  weakFairInstrSem_of_weakFairSem tr (fun i tid t ht => dropBounded_of_sinv ((inv_at hs h0 i).thr tid t ht).sinv) hwf

/-- **A worker that never reaches its end takes infinitely many instruction
steps** (weak fairness and `en`). -/
theorem inf_of (hwf : WeakFairSem Arch.tso fuel tr.cfg) {U j : Nat} {u : Thread isa}
    (hu : (tr.cfg j).threads[U]? = some u)
    (hne : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[U]? = some u → u.st.st.2 ≠ pcA 10) :
    InfOften fun k => InstrSem Arch.tso fuel U (tr.cfg k) (tr.cfg (k + 1)) :=
  wfi hs h0 hwf U ⟨j, fun k hk => let ⟨u', hu'⟩ := get_persist hu k hk; en hs h0 hu' (hne k hk u' hu')⟩

/-- A finished thread stays finished. -/
theorem done_step (j U : Nat) (hd : SpinX64.CmpxDone U (tr.cfg j)) : SpinX64.CmpxDone U (tr.cfg (j + 1)) := by
  obtain ⟨t, ht, hpc⟩ := hd
  rcases tr.same_or_instr j U ht with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
  · exact ⟨u', hu', by rw [e1]; exact hpc⟩
  obtain ⟨hSt, i, hi, hpi, -⟩ := ((inv_at hs h0 j).thr U t ht).sinv
  have h9 : ¬ i < 9 := fun h => hpc (hpi ▸ (pre_iff hi).mpr h)
  have : i = 9 ∨ i = 10 := by
    simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  rcases this with rfl | rfl
  · obtain ⟨-, hst, -⟩ := s9 hSt hso ho hpi
    refine ⟨_, wt_self ht he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  · rw [stepOne_end hSt hpi] at hso; cases hso

theorem done_mono {j U : Nat} (hd : SpinX64.CmpxDone U (tr.cfg j)) :
    ∀ k, j ≤ k → SpinX64.CmpxDone U (tr.cfg k) := by
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

theorem tpos (j : Nat) (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t) :
    ∃ p ∈ [1, 2, 3, 4], t.st.st.2 = pcA p ∧ (p = 4 → t.st.st.1.status.zf = false) :=
  pos_of_preAcq ((inv_at hs h0 j).thr S t ht).sinv (hpre j hj t ht)

/-- **A spinning thread reads the lock infinitely often** (at its
`lock cmpxchg`, whose read is logged with promises too). -/
theorem reads_inf : InfOften (fun i => ∃ ts, ReadsAt Arch.tso tr.cfg S LkL ts i) := by
  have tp := tpos hs h0 hS0 hinf hpre
  let R (j : Nat) : Prop := ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.tso tr.cfg S LkL ts k
  have r3 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 3 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    have hSt := ((inv_at hs h0 k).thr S u hu).sinv.st
    obtain ⟨g, -, hex⟩ := exec_cmpxchg _ (hSt.at (by decide) (by decide) (by rw [e1]; exact hpc)) hSt.dl
    obtain ⟨ts, v, ν, hlog⟩ := spec_rmwo_p_log rfl hex hso ho
    exact ⟨k, hk, ts, u, outs, oc, hu, hso, ho, he, v, ν, hlog⟩
  have r2 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 2 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    obtain ⟨-, hst, -⟩ := s2 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r1 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 1 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    obtain ⟨-, ⟨md, -, -, hst⟩, -⟩ := s1 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    obtain ⟨k', hk', h⟩ := r2 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
    exact ⟨k', by omega, h⟩
  have r4 : ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA 4 → R j := by
    intro j hj t ht hpc
    obtain ⟨k, hk, u, hu, e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    have hpc' : u.st.st.2 = pcA 4 := by rw [e1]; exact hpc
    obtain ⟨p, hp, hpp, hz⟩ := tp _ (Nat.le_trans hj hk) hu
    obtain rfl := addrOf_inj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                                 simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by decide) (hpp.symm.trans hpc')
    obtain ⟨-, hst, -⟩ := s4 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho hpc'
    rw [hz rfl] at hst
    obtain ⟨k', hk', h⟩ := r1 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]; rfl)
    exact ⟨k', by omega, h⟩
  intro j0
  obtain ⟨t, ht⟩ := get_persist hS0 (max m j0) (Nat.le_max_left _ _)
  have hj := Nat.le_max_left m j0
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  have hR : R (max m j0) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact r1 _ hj t ht hpc
    · exact r2 _ hj t ht hpc
    · exact r3 _ hj t ht hpc
    · exact r4 _ hj t ht hpc
  obtain ⟨k, hk, h⟩ := hR
  exact ⟨k, by omega, h⟩

end Spinner

/-! ### The core lemma -/

section Stuck

variable {n : Nat} (hnd : ∀ j, n ≤ j → ∀ U, SpinX64.CmpxDone U (tr.cfg j) → SpinX64.CmpxDone U (tr.cfg n))
  (hwf : WeakFairSem Arch.tso fuel tr.cfg) (hmf : MemFair Arch.tso tr.cfg)

include hnd hwf hmf

/-- A thread not finished at some `j ≥ n` is never finished. -/
theorem not_done {j : Nat} (hj : n ≤ j) {U : Nat} (hnd' : ¬ SpinX64.CmpxDone U (tr.cfg j)) :
    ∀ k, j ≤ k → ¬ SpinX64.CmpxDone U (tr.cfg k) :=
  fun k hk hd => hnd' (done_mono hs h0 (hnd k (by omega) U hd) j hj)

/-- A thread never finished from `j` on is never at its end. -/
theorem ne10_of_nd {j U : Nat} (hnot : ∀ k, j ≤ k → ¬ SpinX64.CmpxDone U (tr.cfg k)) :
    ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[U]? = some u → u.st.st.2 ≠ pcA 10 := fun k hk u hu e =>
  hnot k hk ⟨u, hu, by rw [e, pre_iff (by decide)]; omega⟩

/-- **(a) No thread holds the lock from `n` on.** -/
theorem holder_false {j : Nat} (hj : n ≤ j) {H : Nat} {t : Thread isa} (ht : (tr.cfg j).threads[H]? = some t)
    (hh : Holder t) : False := by
  have hnot : ∀ k, j ≤ k → ¬ SpinX64.CmpxDone H (tr.cfg k) := by
    refine not_done hs h0 hnd hwf hmf hj fun ⟨t', ht', hpc⟩ => ?_
    rw [ht] at ht'; cases ht'
    obtain ⟨p, hp, hpc'⟩ := hh.pos
    refine hpc (hpc' ▸ (pre_iff ?_).mpr ?_) <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  have hinfH := inf_of hs h0 hwf ht (ne10_of_nd hs h0 hnd hwf hmf hnot)
  have c8 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 8 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinfH hu
    obtain ⟨hst, -⟩ := s8p ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    refine hnot (k' + 1) (by omega) ⟨_, wt_self hu' he, ?_⟩
    rw [hst, pre_iff (by decide)]; omega
  have c7 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 7 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinfH hu
    obtain ⟨md, -, hst, -⟩ := s7p ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c8 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c6 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 6 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinfH hu
    obtain ⟨md, -, hst, -⟩ := s6 ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c7 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  have c5 : ∀ k, j ≤ k → ∀ u, (tr.cfg k).threads[H]? = some u → u.st.st.2 = pcA 5 → False := by
    intro k hk u hu hpc
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinfH hu
    obtain ⟨md, -, hst, -⟩ := s5 ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact c6 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  rcases hh with ⟨hpc, hz⟩ | hpc
  · obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinfH ht
    obtain ⟨-, hst, -⟩ := s4 ((inv_at hs h0 k').thr H u' hu').sinv.st hso ho (by rw [e1]; exact hpc)
    rw [ite_eq_left (by rw [e1]; exact hz)] at hst
    exact c5 (k' + 1) (by omega) _ (wt_self hu' he) (by rw [hst])
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with hpc | hpc | hpc | hpc
    · exact c5 j (Nat.le_refl _) t ht hpc
    · exact c6 j (Nat.le_refl _) t ht hpc
    · exact c7 j (Nat.le_refl _) t ht hpc
    · exact c8 j (Nat.le_refl _) t ht hpc

/-- **(a') No thread holds an acquire promise from `n` on.** -/
theorem acq_false {j : Nat} (hj : n ≤ j) {U : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[U]? = some u)
    (ha : HasAcq u (tr.cfg j).mem) : False := by
  obtain ⟨ts, hts, w, hw, hl, hv⟩ := ha
  have keep : ∀ k, j ≤ k → ∃ u', (tr.cfg k).threads[U]? = some u' ∧ ts ∈ u'.prom := by
    intro k hk
    induction hk with
    | refl => exact ⟨u, hu, hts⟩
    | @step k hjk ih =>
      obtain ⟨u1, hu1, hts1⟩ := ih
      have hjk : j ≤ k := hjk
      rcases tr.same_or_instr k U hu1 with ⟨u', hu', -, -, hp⟩ | ⟨outs, oc, hso, ho, he⟩
      · exact ⟨u', hu', hp ts hts1⟩
      have hT := (inv_at hs h0 k).thr U u1 hu1
      have hf := holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu1 he)
      have hf' := holder_false hs h0 hnd hwf hmf (j := k) (by omega) hu1
      cases (step_solo (inv_at hs h0 k).hlc hT.sinv hT.promIn hso ho).eff with
      | quiet _ hkeep _ => exact ⟨_, wt_self hu1 he, hkeep ts hts1 w (tr.get_le hjk hw) hl⟩
      | acqFresh _ _ _ hh _ => exact (hf hh).elim
      | acqFul _ _ _ _ _ _ _ _ hh _ _ => exact (hf hh).elim
      | relFresh _ hh => exact (hf' hh).elim
      | relFul _ _ _ _ _ _ hh => exact (hf' hh).elim
  have hpa : ∀ k, j ≤ k → ∀ u', (tr.cfg k).threads[U]? = some u' → PreAcq u' := fun k hk u' hu' => by
    obtain ⟨u2, hu2, hts2⟩ := keep k hk
    rw [hu'] at hu2; cases hu2
    rcases (((inv_at hs h0 k).thr U u' hu').good (inv_at hs h0 k).hlc).loc ts hts2 w (tr.get_le hk hw) with
      ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd (hl.symm.trans h) (inv_at hs h0 k).hlc
    · exact absurd h hv
  have hinfU := inf_of hs h0 hwf hu fun k hk u' hu' => ne10_of_preAcq (hpa k hk u' hu')
  obtain ⟨k, hk, u', hu', hc⟩ := memFair_catchup hmf (reads_inf hs h0 hu hinfU hpa) hw hl
  obtain ⟨u2, hu2, hts2⟩ := keep k hk
  rw [hu'] at hu2; cases hu2
  have := ((inv_at hs h0 k).thr U u' hu').coh ts hts2 w (tr.get_le hk hw)
  rw [hl] at this
  exact absurd hc (Nat.not_le_of_lt this)

/-- No promise to the lock from `n` on: an acquire promise is (a'); a
release promise is held by a holder (a) or with an acquire promise (a'). -/
theorem no_lock_prom {j : Nat} (hj : n ≤ j) {U : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[U]? = some u)
    {ts : Time} (hts : ts ∈ u.prom) {w : Msg} (hw : (tr.cfg j).mem.get? ts = some w) : w.loc ≠ LkL := by
  intro hl
  have hT := (inv_at hs h0 j).thr U u hu
  have hg := hT.good (inv_at hs h0 j).hlc
  rcases hg.loc ts hts w hw with ⟨-, hv, -⟩ | ⟨h, -⟩ | ⟨-, -, h4⟩
  · exact acq_false hs h0 hnd hwf hmf hj hu ⟨ts, hts, w, hw, hl, hv⟩
  · exact (inv_at hs h0 j).hlc (hl.symm.trans h)
  by_cases hh : Holder u
  · exact holder_false hs h0 hnd hwf hmf hj hu hh
  exact acq_false hs h0 hnd hwf hmf hj hu
    (hg.acq (List.ne_nil_of_mem hts) (preAcq_of hT.sinv (pre_of_rk4 hT.sinv h4) hh))

/-- **(b) The lock is `0` from `n` on.** -/
theorem lock_zero (j : Nat) (hj : n ≤ j) : (tr.cfg j).mem.finalVal LkL = 0 :=
  Classical.byContradiction fun hne =>
    let ⟨_, _, hw, hl, _, hu, ho⟩ := (inv_at hs h0 j).held hne
    ho.elim (fun hp => no_lock_prom hs h0 hnd hwf hmf hj hu hp hw hl)
      (fun ⟨hh, _⟩ => holder_false hs h0 hnd hwf hmf hj hu hh)

/-- **(b) The lock's last write is constant from `n` on.** -/
theorem lw_const : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite LkL = (tr.cfg n).mem.lastWrite LkL := by
  intro j hj
  induction hj with
  | refl => rfl
  | @step k hk ih =>
    have hk : n ≤ k := hk
    rcases tr.step k with ⟨tid, ⟨t, outs, oc, ht, hso, ho, -, he⟩ | ⟨t, w, ht, -, -, he⟩⟩ | ⟨-, he⟩
    · have hT := (inv_at hs h0 k).thr tid t ht
      have hf := holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self ht he)
      have hf' := holder_false hs h0 hnd hwf hmf (j := k) hk ht
      rw [he]; show oc.mem.lastWrite LkL = _
      cases (step_solo (inv_at hs h0 k).hlc hT.sinv hT.promIn hso ho).eff with
      | quiet hm _ _ =>
        rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
        · exact ih
        · exact ((mem_frame _ { loc := CtL, val := v, tid } (Ne.symm (inv_at hs h0 k).hlc)).2.1).trans ih
      | acqFresh _ _ _ hh _ => exact (hf hh).elim
      | acqFul _ _ _ _ _ _ _ _ hh _ _ => exact (hf hh).elim
      | relFresh _ hh => exact (hf' hh).elim
      | relFul _ _ _ _ _ _ hh => exact (hf' hh).elim
    · by_cases hl : w.loc = LkL
      · refine (no_lock_prom hs h0 hnd hwf hmf (j := k + 1) (by omega) (by rw [he]; exact withThread_get_self ht)
          (ts := (tr.cfg k).mem.last + 1) (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (w := w) ?_ hl).elim
        rw [he]; exact Memory.get?_append_last _ _
      · rw [he]; exact (mem_frame _ w hl).2.1.trans ih
    · rw [he]; exact ih

/-- **(c) With an up-to-date view of the lock, a promise-free spinning thread
acquires it**: contradiction. -/
theorem at_false {S m : Nat} {uS : Thread isa} (hm : n ≤ m) (hS0 : (tr.cfg m).threads[S]? = some uS)
    (hinf : InfOften fun k => InstrSem Arch.tso fuel S (tr.cfg k) (tr.cfg (k + 1)))
    (hpre : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → PreAcq u)
    (hnp : ∀ j, m ≤ j → ∀ u, (tr.cfg j).threads[S]? = some u → u.prom = [])
    {j : Nat} (hj : m ≤ j) {t : Thread isa} (ht : (tr.cfg j).threads[S]? = some t)
    (hc : (tr.cfg n).mem.lastWrite LkL ≤ t.views.getCoh LkL) : False := by
  have tp := tpos hs h0 hS0 hinf hpre
  have lw := lw_const hs h0 hnd hwf hmf
  have lz := lock_zero hs h0 hnd hwf hmf
  let LW := (tr.cfg n).mem.lastWrite LkL
  let Q (p : Nat) : Prop := ∀ j, m ≤ j → ∀ t, (tr.cfg j).threads[S]? = some t → t.st.st.2 = pcA p →
    LW ≤ t.views.getCoh LkL → False
  have p3 : Q 3 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    have hpc' : u.st.st.2 = pcA 3 := by rw [e1]; exact hpc
    have hT := ((inv_at hs h0 k).thr S u hu).sinv
    have hz : eax u.st.st.1 = 0#32 := (pci_at hT (by decide) hpc').1 (.inr rfl)
    obtain ⟨md, -, tr', old, hst, -, hold, -, -, -, hcase⟩ :=
      s3 hT.st (hnp k (by omega) u hu) hso ho hpc'
    have hold := hold (by rw [lw k (by omega), e2]; exact hc)
    rw [lz _ (by omega)] at hold
    subst hold
    rcases hcase with ⟨hne, -⟩ | ⟨-, hzf, -⟩
    · exact hne (by rw [hz]; rfl)
    · exact holder_false hs h0 hnd hwf hmf (j := k + 1) (by omega) (wt_self hu he)
        (.inl ⟨by rw [hst], by rw [hst]; exact hzf⟩)
  have p2 : Q 2 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    obtain ⟨-, hst, -, hcoh⟩ := s2 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p3 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (by rw [SpinSwpStep.getCoh_congr hcoh, e2]; exact hc)
  have p1 : Q 1 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    obtain ⟨-, ⟨md, -, -, hst⟩, -, hcoh⟩ := s1 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho (by rw [e1]; exact hpc)
    exact p2 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst])
      (by rw [SpinSwpStep.getCoh_congr hcoh, e2]; exact hc)
  have p4 : Q 4 := by
    intro j hj t ht hpc hc
    obtain ⟨k, hk, u, hu, e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf ht
    have hpc' : u.st.st.2 = pcA 4 := by rw [e1]; exact hpc
    obtain ⟨p, hp, hpp, hz⟩ := tp _ (Nat.le_trans hj hk) hu
    obtain rfl := addrOf_inj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                                 simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by decide) (hpp.symm.trans hpc')
    obtain ⟨-, hst, -, hcoh⟩ := s4 ((inv_at hs h0 k).thr S u hu).sinv.st hso ho hpc'
    rw [hz rfl] at hst
    exact p1 (k + 1) (by omega) _ (wt_self hu he) (by rw [hst]; rfl)
      (by rw [SpinSwpStep.getCoh_congr hcoh, e2]; exact hc)
  obtain ⟨p, hp, hpc, -⟩ := tp _ hj ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact p1 j hj t ht hpc hc
  · exact p2 j hj t ht hpc hc
  · exact p3 j hj t ht hpc hc
  · exact p4 j hj t ht hpc hc

/-- **The core lemma**: if from `n` on no thread newly finishes, then every
thread is finished at `n`. The unfinished thread `T` itself spins, without
promises, forever: no pigeonhole over stepping threads is needed on TSO. -/
theorem stuck_false {T : Nat} {tT : Thread isa} (hT0 : (tr.cfg n).threads[T]? = some tT)
    (hT1 : ¬ SpinX64.CmpxDone T (tr.cfg n)) : False := by
  have hnot := not_done hs h0 hnd hwf hmf (Nat.le_refl _) hT1
  have hpre : ∀ j, n ≤ j → ∀ u, (tr.cfg j).threads[T]? = some u → PreAcq u := fun j hj u hu =>
    preAcq_of ((inv_at hs h0 j).thr T u hu).sinv
      (Classical.byContradiction fun h => hnot j hj ⟨u, hu, h⟩)
      (fun hh => holder_false hs h0 hnd hwf hmf hj hu hh)
  have hnp : ∀ j, n ≤ j → ∀ u, (tr.cfg j).threads[T]? = some u → u.prom = [] := fun j hj u hu =>
    Classical.byContradiction fun hne => acq_false hs h0 hnd hwf hmf hj hu
      ((((inv_at hs h0 j).thr T u hu).good (inv_at hs h0 j).hlc).acq hne (hpre j hj u hu))
  have hinf := inf_of hs h0 hwf hT0 (ne10_of_nd hs h0 hnd hwf hmf hnot)
  exact memFair_lastWrite_false hmf (reads_inf hs h0 hT0 hinf hpre) hT0 fun _ hj _ ht' hc =>
    at_false hs h0 hnd hwf hmf (Nat.le_refl _) hT0 hinf hpre hnp hj ht' hc

end Stuck

end Start

/-! ## The theorems -/

/-- **Deadlock-freedom of the x64 `lock cmpxchg` spinlock with promises**
(Stage 3, on the machine with semantic certification): on a valid layout of
`cmpxImageV`, for every `fuel`, on every semantic `Arch.tso` trace from a
start configuration under `WeakFairSem ∧ MemFair` (`MemFair` being a
modelling assumption on x86), if a thread waits in its acquire loop, then
some thread not yet past its release later is. -/
theorem spin_cmpx_live_sem (fuel : Nat) : SpinX64Sem.CmpxSpinLiveSem fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ∀ U, SpinX64.CmpxDone U (tr.cfg j) → SpinX64.CmpxDone U (tr.cfg i) :=
    fun j hj U hd => Classical.byContradiction fun hn => hno ⟨j, hj, U, hn, hd⟩
  obtain ⟨t, ht, -⟩ := id hw
  exact stuck_false hs h0 hnd hwf hmf ht (SpinX64CmpxPF.wait_not_done hw)

/-- **Per-thread liveness of the one-shot x64 `lock cmpxchg` workers with
promises** (semantic machine): every waiting thread eventually gets past its
release (from `stuck_false` and the finite number of threads). A property of
these one-shot programs, not starvation-freedom of the lock. -/
theorem spin_cmpx_live_oneShot_sem (fuel : Nat) : SpinX64Sem.CmpxSpinLiveOneShotSem fuel := by
  intro states initMem hs tr h0 ⟨hwf, hmf⟩ tid i hw
  apply Classical.byContradiction
  intro hno
  have hnd' : ∀ j, i ≤ j → ¬ SpinX64.CmpxDone tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨n, hin, hst⟩ := SpinCommon.stable_of_mono (fun k j => SpinX64.CmpxDone k (tr.cfg j))
    (tr.cfg 0).threads.size (fun k j ⟨_, ht, _⟩ => tr.size_eq j ▸ lt_size_of_get? ht)
    (fun k i j hij hd => done_mono hs h0 hd j hij) i
  obtain ⟨t, ht, -⟩ := hw
  obtain ⟨u, hu⟩ := get_persist ht n hin
  exact stuck_false hs h0 (fun j hj U hd => hst j hj U hd) hwf hmf hu (hnd' n hin)

end Gen

/-! ## Concrete instances: the `.kl` runner's executable -/

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete in
/-- `spin_cmpx_live_sem` at the `.kl` runner's layout `cmpxLayoutV`: no
hypothesis left. -/
theorem spin_cmpx_live_sem_concrete (fuel : Nat) : @SpinX64Sem.CmpxSpinLiveSem cmpxLayoutV fuel :=
  @spin_cmpx_live_sem cmpxLayoutV cmpxValidV fuel

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete in
/-- `spin_cmpx_live_oneShot_sem` at the runner's layout. -/
theorem spin_cmpx_live_oneShot_sem_concrete (fuel : Nat) :
    @SpinX64Sem.CmpxSpinLiveOneShotSem cmpxLayoutV fuel :=
  @spin_cmpx_live_oneShot_sem cmpxLayoutV cmpxValidV fuel

end Kraken.Promising.Live.SpinX64SemCmpx
