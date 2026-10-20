/-
**The staged-freezing liveness skeleton of
`treiber_pp`-shaped programs on the semantic machine** (ISA-neutral,
program-independent).

Two threads, thread `0` the pusher and thread `1` the popper, sharing a
location `l` (`top`) on a `TraceSem` trace (the machine with semantic
certification, promises included). The per-program facts the argument needs
are the fields of `Iface`; none is an assumption of a final theorem (each
instance proves them). **`skeleton`**: under `WeakFairSem`, every thread of
such a trace finishes. The argument (*staged freezing*, no rank):

- (A) the pusher steps only finitely often (`Iface.spin0`: a pusher that
  keeps executing finishes);
- (B) from then on only the popper steps;
- (C) so the popper keeps executing without finishing: by `Iface.spin1` its
  steps never change memory and `l` is eventually `0`;
- (D) so memory and the pusher are frozen, and the pusher, whenever it has a
  promise, is certifiable against the frozen memory (its last own step
  certified it, and nothing changed since);
- (E) a finished pusher left `l` non-zero (`Iface.pushed`), against (C); an
  unfinished one is always enabled (`NoStuck.enabledSem_of_thread`), so weak
  fairness makes it step, against (A).

Memory fairness is used only inside the instances' `spin0`/`spin1`.

Generic trace facts used by the instances (all on `TraceSem`, any ISA and
architecture):

- `walk`: a thread taking infinitely many instruction steps reaches a goal if
  each of its steps from a `P` state reaches the goal or a `P` state of
  smaller measure;
- `coh_mono`: a thread's coherence view never shrinks along a trace;
- `certPast`, `not_halted_of_prom`, `coh_lt_of_prom`: a thread with an
  outstanding promise was certified by its last own step against an earlier
  memory holding its promises; so it is not halted, and each promise lies
  above its coherence view of the promise's location;
- `cnt_le_of_prefix`, `lw_eq_of_cnt`, `top_const`: the number of writes to a
  location only grows; with the same number, the last write and the final
  value are the same; so a bounded number of writes makes both eventually
  constant;
- `finalVal_of_cnt_le_one`: with at most one write to `l` in memory, the
  final value of `l` is that write's;
- `promGood_of_certOkN`: the outstanding promises of a certifiable thread are
  messages its solo steps can write.
-/
import Kraken.Promising.LiveNoStuck
import Kraken.Promising.LiveTerm
import Kraken.Promising.LiveSpinCommon

namespace Kraken.Promising.Live.TreiberPp

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.NoStuck
open Kraken.Promising.Live.Term

variable {I : ISA} {A : Arch} {fuel : Nat}

/-! ## Generic step facts -/

theorem stepSem_get {k : Nat} {c c' : Config I} (h : StepSem A fuel k c c') : ∃ t, c.threads[k]? = some t := by
  rcases h with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩

/-- After its own step a thread is certifiable against the new memory. -/
theorem certOkN_of_stepSem {k : Nat} {c c' : Config I} (h : StepSem A fuel k c c') :
    ∃ t', c'.threads[k]? = some t' ∧ CertOkN A k t' c'.mem fuel := by
  rcases h with ⟨t, outs, o, ht, -, -, hc, rfl⟩ | ⟨t, w, ht, -, hc, rfl⟩
  · exact ⟨_, withThread_get_self ht, hc⟩
  · exact ⟨_, withThread_get_self ht, hc⟩

/-- Another thread's step leaves thread `k` unchanged. -/
theorem get_of_stepSem_ne {k k' : Nat} {c c' : Config I} (h : StepSem A fuel k' c c') (hne : k ≠ k') :
    c'.threads[k]? = c.threads[k]? := by
  rcases h with ⟨t, outs, o, ht, -, -, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · exact withThread_get_ne ht hne
  · exact withThread_get_ne ht hne

/-! ## The program interface -/

/-- **What the skeleton needs from the program**, for a trace `tr`, a
predicate `Done` (thread `k` has finished) and the shared location `l`. All
fields are per-program lemmas; none is an assumption of a final theorem. -/
structure Iface (tr : TraceSem A fuel I) (Done : Nat → Config I → Prop) (l : Loc) : Prop where
  size : ∀ j, (tr.cfg j).threads.size = 2
  done_mono : ∀ k j j', j ≤ j' → Done k (tr.cfg j) → Done k (tr.cfg j')
  done_nostep : ∀ k j, Done k (tr.cfg j) → ¬ StepSem A fuel k (tr.cfg j) (tr.cfg (j + 1))
  notdone_nonfinal : ∀ k j, k < 2 → ¬ Done k (tr.cfg j) → (tr.cfg j).final = false
  notdone_running : ∀ j t, (tr.cfg j).threads[0]? = some t → ¬ Done 0 (tr.cfg j) → t.halted = false
  drop : ∃ B, ∀ i tid t, (tr.cfg i).threads[tid]? = some t → DropBounded A B tid t
  ok : ∀ j, OkStepsPF A (tr.cfg j)
  init0 : ∀ t, (tr.cfg 0).threads[0]? = some t → t.prom = []
  /-- Spin(pusher): a pusher that keeps executing does not stay unfinished. -/
  spin0 : ∀ n, (∀ j, n ≤ j → ¬ Done 0 (tr.cfg j)) →
    InfOften (fun j => InstrSem A fuel 0 (tr.cfg j) (tr.cfg (j + 1))) → False
  /-- Spin(popper): a popper that keeps executing and never finishes never
  changes memory, and `l` is eventually `0`. -/
  spin1 : ∀ n, (∀ j, n ≤ j → ¬ Done 1 (tr.cfg j)) →
    InfOften (fun j => InstrSem A fuel 1 (tr.cfg j) (tr.cfg (j + 1))) →
      (∀ j, StepSem A fuel 1 (tr.cfg j) (tr.cfg (j + 1)) → (tr.cfg (j + 1)).mem = (tr.cfg j).mem) ∧
        ∃ m, ∀ j, m ≤ j → (tr.cfg j).mem.finalVal l = 0
  /-- A finished pusher left `l` non-zero, if the popper never changed memory. -/
  pushed : ∀ j, Done 0 (tr.cfg j) →
    (∀ k, StepSem A fuel 1 (tr.cfg k) (tr.cfg (k + 1)) → (tr.cfg (k + 1)).mem = (tr.cfg k).mem) →
      (tr.cfg j).mem.finalVal l ≠ 0

/-! ## The skeleton -/

/-- **Staged freezing**: under weak fairness, every thread of a trace with
the interface finishes, from every index (memory fairness is used only
inside `spin0`/`spin1`). -/
theorem skeleton (tr : TraceSem A fuel I) (Done : Nat → Config I → Prop) (l : Loc) (H : Iface tr Done l)
    (hwf : WeakFairSem A fuel tr.cfg) (tid : Nat) (htid : tid < 2) (i : Nat) :
    ∃ j, i ≤ j ∧ Done tid (tr.cfg j) := by
  apply Classical.byContradiction
  intro hno
  have hnd : ∀ j, i ≤ j → ¬ Done tid (tr.cfg j) := fun j hj hd => hno ⟨j, hj, hd⟩
  obtain ⟨B, hdrop⟩ := H.drop
  -- from `i` on some thread steps at every index
  have hstep : ∀ j, i ≤ j → ∃ k, StepSem A fuel k (tr.cfg j) (tr.cfg (j + 1)) := by
    intro j hj
    rcases tr.step j with h | ⟨hf, -⟩
    · exact h
    · rw [H.notdone_nonfinal tid j htid (hnd j hj)] at hf; cases hf
  have hlt : ∀ j k, StepSem A fuel k (tr.cfg j) (tr.cfg (j + 1)) → k < 2 := by
    intro j k h
    obtain ⟨t, ht⟩ := stepSem_get h
    have := lt_size_of_get? ht
    rw [H.size j] at this
    exact this
  -- a thread stepping infinitely often is never done
  have inf_nd : ∀ k, InfOften (fun j => StepSem A fuel k (tr.cfg j) (tr.cfg (j + 1))) →
      ∀ j, ¬ Done k (tr.cfg j) := by
    intro k hinf j hd
    obtain ⟨j', hj', hs⟩ := hinf j
    exact H.done_nostep k j' (H.done_mono k j j' hj' hd) hs
  -- (A) the pusher steps finitely often
  obtain ⟨k0, hk0, hfr⟩ : ∃ k0, i ≤ k0 ∧ ∀ j, k0 ≤ j → ¬ StepSem A fuel 0 (tr.cfg j) (tr.cfg (j + 1)) := by
    apply Classical.byContradiction
    intro hc
    have hinf : InfOften (fun j => StepSem A fuel 0 (tr.cfg j) (tr.cfg (j + 1))) := by
      intro n
      apply Classical.byContradiction
      intro hn
      exact hc ⟨max i n, Nat.le_max_left _ _, fun j hj hs => hn ⟨j, by omega, hs⟩⟩
    exact H.spin0 0 (fun j _ => inf_nd 0 hinf j) (tr.instr_inf hdrop hstep hinf)
  -- (B) from `k0` on, the popper steps at every index
  have hpop : ∀ j, k0 ≤ j → StepSem A fuel 1 (tr.cfg j) (tr.cfg (j + 1)) := by
    intro j hj
    obtain ⟨k, hk⟩ := hstep j (by omega)
    have h2 := hlt j k hk
    have : k ≠ 0 := fun e => hfr j hj (e ▸ hk)
    obtain rfl : k = 1 := by omega
    exact hk
  have hpinf : InfOften (fun j => StepSem A fuel 1 (tr.cfg j) (tr.cfg (j + 1))) :=
    fun n => ⟨max n k0, Nat.le_max_left _ _, hpop _ (Nat.le_max_right _ _)⟩
  -- (C) Spin(popper)
  obtain ⟨hnoapp, m, hm⟩ := H.spin1 0 (fun j _ => inf_nd 1 hpinf j)
    (tr.instr_inf hdrop (fun j hj => ⟨1, hpop j hj⟩) hpinf)
  -- (D) memory and the pusher are constant from `k0` on
  have hconst : ∀ d, (tr.cfg (k0 + d)).mem = (tr.cfg k0).mem ∧
      (tr.cfg (k0 + d)).threads[0]? = (tr.cfg k0).threads[0]? := by
    intro d
    induction d with
    | zero => exact ⟨rfl, rfl⟩
    | succ d ih =>
      have hs := hpop (k0 + d) (by omega)
      rw [← Nat.add_assoc, hnoapp _ hs, get_of_stepSem_ne hs (by decide)]
      exact ih
  --     the pusher is certifiable whenever it has a promise (the popper never changes memory)
  have hcert : ∀ j t, (tr.cfg j).threads[0]? = some t → t.prom ≠ [] → CertOkN A 0 t (tr.cfg j).mem fuel := by
    intro j
    induction j with
    | zero => intro t ht hp; exact absurd (H.init0 t ht) hp
    | succ j ih =>
      intro t ht hp
      rcases tr.step j with ⟨k, hk⟩ | ⟨-, he⟩
      · by_cases hk0' : k = 0
        · subst hk0'
          obtain ⟨t', ht', hc⟩ := certOkN_of_stepSem hk
          rw [ht'] at ht; cases ht; exact hc
        · have h2 := hlt j k hk
          obtain rfl : k = 1 := by omega
          rw [hnoapp j hk]
          rw [get_of_stepSem_ne hk (by decide)] at ht
          exact ih t ht hp
      · rw [he] at ht ⊢; exact ih t ht hp
  -- (E) the pusher
  by_cases hd0 : ∃ j, Done 0 (tr.cfg j)
  · obtain ⟨j0, hj0⟩ := hd0
    let J := max j0 k0
    have hJ : Done 0 (tr.cfg J) := H.done_mono 0 j0 J (Nat.le_max_left _ _) hj0
    have hne := H.pushed J hJ hnoapp
    obtain ⟨d, hd⟩ : ∃ d, J = k0 + d := ⟨J - k0, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, max J m = k0 + e := ⟨max J m - k0, by omega⟩
    have h1 := hm (max J m) (Nat.le_max_right _ _)
    rw [he, (hconst e).1, ← (hconst d).1, ← hd] at h1
    exact hne h1
  · have hd0 : ∀ j, ¬ Done 0 (tr.cfg j) := fun j h => hd0 ⟨j, h⟩
    obtain ⟨t0, ht0⟩ : ∃ t, (tr.cfg k0).threads[0]? = some t := by
      cases h : (tr.cfg k0).threads[0]? with
      | some t => exact ⟨t, rfl⟩
      | none =>
        have : 0 < (tr.cfg k0).threads.size := by rw [H.size]; decide
        rw [Array.getElem?_eq_getElem this] at h; cases h
    have hen : EvAlways (fun j => EnabledSem A fuel 0 (tr.cfg j)) := by
      refine ⟨k0, fun j hj => ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, j = k0 + d := ⟨j - k0, by omega⟩
      have ht : (tr.cfg (k0 + d)).threads[0]? = some t0 := by rw [(hconst d).2, ht0]
      exact enabledSem_of_thread (H.ok _) ht (.inl (H.notdone_running _ t0 ht (hd0 _)))
        (hcert _ t0 ht)
    obtain ⟨j, hj, hs⟩ := hwf 0 hen k0
    exact hfr j hj hs

/-! ## Generic trace facts for the instances -/

section Trace

variable (tr : TraceSem A fuel I)

/-- **A walk to a goal**: a thread `T` taking infinitely many instruction
steps reaches the goal `G` from every `P` state at or after `m`, if every
instruction step of `T` at or after `m` from a `P` state reaches `G` or a `P`
state of smaller measure `μ` (`P` and `μ` read the thread's state and views
only, which other threads' steps keep). -/
theorem walk {T m : Nat} (hinf : InfOften fun k => InstrSem A fuel T (tr.cfg k) (tr.cfg (k + 1)))
    (P : Thread I → Prop) (μ : I.State → Nat) (G : Nat → Prop)
    (hP : ∀ u u' : Thread I, P u → u'.st = u.st → u'.views = u.views → P u')
    (hstep : ∀ k u outs oc, m ≤ k → (tr.cfg k).threads[T]? = some u → P u →
      stepOne A u T (tr.cfg k).mem = some outs → .ok oc ∈ outs →
      tr.cfg (k + 1) = (tr.cfg k).withThread T oc.thread oc.mem → G k ∨ (P oc.thread ∧ μ oc.thread.st < μ u.st)) :
    ∀ j u, m ≤ j → (tr.cfg j).threads[T]? = some u → P u → ∃ k, j ≤ k ∧ G k := by
  intro j u hj hu hPu
  induction hμ : μ u.st using Nat.strongRecOn generalizing j u with
  | ind n ih =>
    obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
    rcases hstep k u' outs oc (by omega) hu' (hP u u' hPu e1 e2) hso ho he with hg | ⟨hP', hlt⟩
    · exact ⟨k, hk, hg⟩
    · rw [e1, hμ] at hlt
      obtain ⟨k', hk', hg⟩ := ih _ hlt (k + 1) oc.thread (by omega) (tr.wt_self hu' he) hP' rfl
      exact ⟨k', by omega, hg⟩

/-- **A thread's coherence view never shrinks** along a trace. -/
theorem coh_mono {T i j : Nat} (hij : i ≤ j) {u u' : Thread I} (hu : (tr.cfg i).threads[T]? = some u)
    (hu' : (tr.cfg j).threads[T]? = some u') (l : Loc) : u.views.getCoh l ≤ u'.views.getCoh l := by
  induction hij generalizing u' with
  | refl => rw [hu] at hu'; cases hu'; exact Nat.le_refl _
  | @step k hik ih =>
    obtain ⟨w, hw⟩ := tr.get_persist hu k hik
    rcases tr.same_or_instr k T hw with ⟨w', hw', -, e2, -⟩ | ⟨outs, oc, hso, ho, he⟩
    · rw [hw'] at hu'; cases hu'; rw [e2]; exact ih hw
    · rw [tr.wt_self hw he] at hu'; cases hu'; exact Nat.le_trans (ih hw) ((stepOne_dord _ hso ho).2.1 l)

variable (h0 : ∀ (k : Nat) (t : Thread I), (tr.cfg 0).threads[k]? = some t → t.prom = [])
  (hpl : ∀ (j k : Nat) (t : Thread I), (tr.cfg j).threads[k]? = some t → ∀ ts ∈ t.prom, ts ≤ (tr.cfg j).mem.last)
include h0 hpl

/-- **A thread with an outstanding promise was certified** (by its last own
step) against an earlier memory that holds its promises. -/
theorem certPast : ∀ j k t, (tr.cfg j).threads[k]? = some t → t.prom ≠ [] →
    ∃ M : Memory, M.Prefix (tr.cfg j).mem ∧ (∀ ts ∈ t.prom, ts ≤ M.last) ∧ CertOkN A k t M fuel := by
  intro j
  induction j with
  | zero => intro k t ht hp; exact absurd (h0 k t ht) hp
  | succ j ih =>
    intro k t ht hp
    rcases tr.step j with ⟨k', hk⟩ | ⟨-, he⟩
    · by_cases e : k = k'
      · subst e
        obtain ⟨t', ht', hc⟩ := certOkN_of_stepSem hk
        rw [ht'] at ht; cases ht
        exact ⟨_, Memory.Prefix.refl _, hpl (j + 1) k _ ht', hc⟩
      · rw [get_of_stepSem_ne hk e] at ht
        obtain ⟨M, hM, h1, h2⟩ := ih k t ht hp
        exact ⟨M, hM.trans (tr.step_prefix j), h1, h2⟩
    · rw [he] at ht ⊢; exact ih k t ht hp

/-- A thread with an outstanding promise is not halted. -/
theorem not_halted_of_prom {j k : Nat} {t : Thread I} (ht : (tr.cfg j).threads[k]? = some t) (hp : t.prom ≠ []) :
    t.halted = false := by
  obtain ⟨M, -, -, hc⟩ := certPast tr h0 hpl j k t ht hp
  cases hh : t.halted
  · rfl
  · exact absurd hc (not_certOkN_of_halted hh hp)

/-- **Every outstanding promise lies above the thread's coherence view** of
its location. -/
theorem coh_lt_of_prom {j k : Nat} {t : Thread I} (ht : (tr.cfg j).threads[k]? = some t) {ts : Time}
    (hts : ts ∈ t.prom) {w : Msg} (hw : (tr.cfg j).mem.get? ts = some w) : t.views.getCoh w.loc < ts := by
  obtain ⟨M, hM, hle, hc⟩ := certPast tr h0 hpl j k t ht (List.ne_nil_of_mem hts)
  exact coh_lt_of_certOkN hc hts (by rw [← hM.get? (hle ts hts)]; exact hw)

end Trace

/-! ## Counting writes -/

/-- Along a prefix the number of writes to `l` does not drop. -/
theorem cnt_le_of_prefix {m m' : Memory} (hp : m.Prefix m') (l : Loc) :
    m.cntBelow l m.last ≤ m'.cntBelow l m'.last := by
  rw [← cntBelow_prefix hp (Nat.le_refl _)]; exact cntBelow_le_last m' l _

/-- **The same number of writes to `l`: the same last write and final
value.** -/
theorem lw_eq_of_cnt {m m' : Memory} (hp : m.Prefix m') {l : Loc}
    (h : m'.cntBelow l m'.last = m.cntBelow l m.last) :
    m'.lastWrite l = m.lastWrite l ∧ m'.finalVal l = m.finalVal l := by
  have e1 := below_prefix hp (l := l) (Nat.le_refl m.last)
  have hlw : m'.lastWriteBelow l m'.last = m'.lastWriteBelow l m.last := by
    rcases Nat.lt_or_ge (m'.lastWriteBelow l m.last) (m'.lastWriteBelow l m'.last) with hlt | hge
    · have := cntBelow_lt_of_lastWriteBelow_lt hlt; omega
    · exact Nat.le_antisymm hge (lastWriteBelow_mono hp.last_le)
  have hlw' : m'.lastWrite l = m.lastWrite l := by unfold Memory.lastWrite; rw [hlw, e1.1]
  refine ⟨hlw', ?_⟩
  have h1 := m'.read?_lastWrite l
  rw [hlw', hp.read? (m.lastWrite_le l), m.read?_lastWrite l] at h1
  exact (Option.some.inj h1).symm

/-- **A bounded number of writes to `l` makes its last write and final value
eventually constant.** -/
theorem top_const (tr : TraceSem A fuel I) (l : Loc) {i K : Nat}
    (hb : ∀ j, i ≤ j → (tr.cfg j).mem.cntBelow l (tr.cfg j).mem.last ≤ K) :
    ∃ m, i ≤ m ∧ ∀ j, m ≤ j → (tr.cfg j).mem.lastWrite l = (tr.cfg m).mem.lastWrite l ∧
      (tr.cfg j).mem.finalVal l = (tr.cfg m).mem.finalVal l := by
  obtain ⟨m, hm, hc⟩ := SpinCommon.evconst (fun j => (tr.cfg j).mem.cntBelow l (tr.cfg j).mem.last)
    (fun _ _ h => cnt_le_of_prefix (tr.prefix_le h) l) K i hb
  exact ⟨m, hm, fun j hj => lw_eq_of_cnt (tr.prefix_le hj) (hc j hj)⟩

/-- **At most one write to `l`: the final value is that write's.** -/
theorem finalVal_of_cnt_le_one {m : Memory} {l : Loc} (h : m.cntBelow l m.last ≤ 1) {ts : Time} {w : Msg}
    (hw : m.get? ts = some w) (hl : w.loc = l) : m.finalVal l = w.val := by
  have h0 : ts ≠ 0 := fun e => by rw [e, m.get?_zero] at hw; cases hw
  have hr : m.read? l ts = some w.val := by simp [Memory.read?, h0, hw, hl]
  have hts := m.last_le_of_get?_eq_some hw
  have hbt : m.lastWriteBelow l ts = ts :=
    Nat.le_antisymm (m.lastWriteBelow_le l ts) (le_lastWriteBelow hr (Nat.le_refl _))
  have hc1 : 1 ≤ m.cntBelow l ts := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [cntBelow_succ_of_write hw hl]; omega
  have heq : m.lastWrite l = ts := by
    refine Nat.le_antisymm ?_ (le_lastWriteBelow hr hts)
    apply Classical.byContradiction
    intro hlt
    have hlt' : ts < m.lastWriteBelow l m.last := by
      unfold Memory.lastWrite at hlt; exact Nat.lt_of_not_le hlt
    have := @cntBelow_lt_of_lastWriteBelow_lt m l ts m.last (by rw [hbt]; exact hlt')
    have := cntBelow_le_last m l ts
    omega
  have := m.read?_lastWrite l
  rw [heq, hr] at this
  exact (Option.some.inj this).symm

/-! ## Certified promises -/

/-- **Every outstanding promise of a thread that can fulfil all of them alone
satisfies `Q`**, if every write of the thread's solo steps (from states
satisfying `SI`, which those steps keep) does. -/
theorem promGood_of_run {tid : Nat} (SI : I.State → Prop) (Q : Msg → Prop)
    (hstep : ∀ {t : Thread I} {mem : Memory} {outs} {o : Outcome I}, SI t.st → stepOne A t tid mem = some outs →
      .ok o ∈ outs → SI o.thread.st ∧
        ((o.mem = mem ∧ o.thread.prom = t.prom) ∨ ∃ w, WEff mem o.mem t.prom o.thread.prom w ∧ Q w)) :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → q.1.prom = [] → SI p.1.st →
      ∀ ts ∈ p.1.prom, ∀ w, p.2.get? ts = some w → Q w := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ ts hts; rw [hq] at hts; cases hts
  | step hs _ ih =>
    intro hr hSI ts hts w hw
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    obtain ⟨hSI', heff⟩ := hstep hSI hso ho
    have hle := Memory.last_le_of_get?_eq_some _ hw
    have hw' : o.mem.get? ts = some w := by
      rw [(stepOne_dord _ hso ho).2.2.1.get? hle]; exact hw
    rcases heff with ⟨-, hp⟩ | ⟨w', ⟨-, hp⟩ | ⟨ts', -, hw'', -, hp⟩, hQ⟩
    · exact ih hr hSI' ts (by rw [hp]; exact hts) w hw'
    · refine ih hr hSI' ts ?_ w hw'
      rw [hp]
      exact (List.mem_erase_of_ne (Nat.ne_of_lt (Nat.lt_succ_of_le hle))).2 (List.mem_append_left _ hts)
    · by_cases e : ts = ts'
      · subst e; rw [hw] at hw''; cases hw''; exact hQ
      · exact ih hr hSI' ts (by rw [hp]; exact (List.mem_erase_of_ne e).2 hts) w hw'

theorem promGood_of_certOkN {tid fuel : Nat} (SI : I.State → Prop) (Q : Msg → Prop)
    (hstep : ∀ {t : Thread I} {mem : Memory} {outs} {o : Outcome I}, SI t.st → stepOne A t tid mem = some outs →
      .ok o ∈ outs → SI o.thread.st ∧
        ((o.mem = mem ∧ o.thread.prom = t.prom) ∨ ∃ w, WEff mem o.mem t.prom o.thread.prom w ∧ Q w))
    {t : Thread I} {mem : Memory} (hc : CertOkN A tid t mem fuel) (hS : SI t.st) :
    ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → Q w :=
  let ⟨_, _, hr, hp⟩ := hc
  promGood_of_run SI Q hstep hr hp hS

end Kraken.Promising.Live.TreiberPp

