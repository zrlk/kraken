/-
**`Components` transfers to the two-slot lift** (the
pre-spawn half): a witness of `Components` at a one-slot configuration `d`
is one at `up d u` (`Spike/Lib/TwoSlot.lean`) when the extra thread `u` has
no private memory (`pl u.st a = none`) and holds no stack range of `d`'s
kernel (no held range of index `d.1.threads.size`). The thread map is
unchanged: the extra slot is dormant (`runs_up_lt`), so it is no running
target thread; its thread has no current stack range and owns no stack.
-/
import Spike.Lib.TwoSlot

namespace Spike.Lib.TwoSlot

open Kraken.Promising Scc.Sem Scc.Sem.Kernel

variable {I : ISA} {K : Abi I} {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat}

local notation "M" => ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf

/-- The current stack range of one of `d`'s threads is unchanged by the lift. -/
theorem stackRange_up {d : Config I × KState} {u : Thread I} {j : Nat} (hj : j < d.1.threads.size) :
    (M).stackRange (up d u) j = (M).stackRange d j := by
  show stackRangeOf K (up d u) j = stackRangeOf K d j
  unfold stackRangeOf
  simp only [up]
  erw [upC_get hj]
  rfl

/-- The extra thread has no current stack range when it holds no range. -/
theorem stackRange_up_size {d : Config I × KState} {u : Thread I}
    (hheld : ∀ h ∈ d.2.held, h.1 ≠ d.1.threads.size) :
    (M).stackRange (up d u) d.1.threads.size = none := by
  show stackRangeOf K (up d u) d.1.threads.size = none
  unfold stackRangeOf
  simp only [up]
  erw [upC_get_size]
  simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.and_eq_true, beq_iff_eq, not_and]
  intro h hm he
  exact absurd he (hheld h (by simpa [upX] using hm))

/-- A stack range of the lift is one of `d`'s threads'. -/
theorem stackRange_up_lt {d : Config I × KState} {u : Thread I} {j : Nat} {rg : Range}
    (hheld : ∀ h ∈ d.2.held, h.1 ≠ d.1.threads.size) (h : (M).stackRange (up d u) j = some rg) :
    j < d.1.threads.size ∧ (M).stackRange d j = some rg := by
  rcases Nat.lt_or_ge j d.1.threads.size with hj | hj
  · exact ⟨hj, (stackRange_up hj).symm.trans h⟩
  · exfalso
    rcases Nat.eq_or_lt_of_le hj with rfl | hj'
    · rw [stackRange_up_size hheld] at h; cases h
    · have : (up d u).1.threads[j]? = none := Array.getElem?_eq_none_iff.mpr (by simp [up]; omega)
      have h' : stackRangeOf K (up d u) j = some rg := h
      unfold stackRangeOf at h'
      rw [this] at h'
      cases h'

/-- The lift's thread `j` is `d`'s or the extra thread. -/
theorem up_get_cases {d : Config I × KState} {u : Thread I} {j : Nat} {tt : Thread I}
    (h : (up d u).1.threads[j]? = some tt) :
    (j < d.1.threads.size ∧ d.1.threads[j]? = some tt) ∨ (j = d.1.threads.size ∧ tt = u) := by
  rcases Nat.lt_or_ge j d.1.threads.size with hj | hj
  · left; refine ⟨hj, ?_⟩
    have := upC_get (u := u) hj
    rw [← this]; exact h
  · right
    rcases Nat.eq_or_lt_of_le hj with rfl | hj'
    · refine ⟨rfl, ?_⟩
      have := upC_get_size (c := d.1) (u := u)
      erw [this] at h; cases h; rfl
    · have : (up d u).1.threads[j]? = none := Array.getElem?_eq_none_iff.mpr (by simp [up]; omega)
      rw [this] at h; cases h

theorem lt_of_get {α : Type} {xs : Array α} {i : Nat} {x : α} (h : xs[i]? = some x) : i < xs.size := by
  rcases Nat.lt_or_ge i xs.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none_iff.mpr h'] at h; cases h

theorem upC_get_of {c : Config I} {u t : Thread I} {i : Nat} (h : c.threads[i]? = some t) :
    (upC c u).threads[i]? = some t := by
  rw [upC_get (lt_of_get h)]; exact h

/-- **`Components` transfers to the lift**: the same witness, for an extra
thread with no private memory holding no stack range. -/
theorem components_up {Λ : Layout} {w : Witness (M)} {d : Config I × KState} {u : Thread I} {s : TermRun.Cfg}
    (hn : d.1.threads.size = d.2.slots.size) (hpl : ∀ a, pl u.st a = none)
    (hheld : ∀ h ∈ d.2.held, h.1 ≠ d.1.threads.size) (h : Components (M) Λ w d s) :
    Components (M) Λ w (up d u) s where
  thr_total i hi := by
    obtain ⟨j, hj, hlt⟩ := h.thr_total i hi
    refine ⟨j, hj, ?_⟩
    show j < (upC d.1 u).threads.size
    rw [upC_size]; exact Nat.lt_succ_of_lt hlt
  thr_inj := h.thr_inj
  thr_onto j tt hr ht := by
    have hs := runs_up_lt hr
    have hj : j < d.1.threads.size := hn ▸ hs
    rcases up_get_cases ht with ⟨-, ht'⟩ | ⟨rfl, -⟩
    · exact h.thr_onto j tt ((runs_up hj hs).mp hr) ht'
    · exact absurd hj (Nat.lt_irrefl _)
  lbl_static := h.lbl_static
  lbl_range := h.lbl_range
  lbl_disj := h.lbl_disj
  lbl_mem := h.lbl_mem
  epoch_fixed := h.epoch_fixed
  mem_rep := h.mem_rep
  ts_first := h.ts_first
  ts_mono := h.ts_mono
  mem_onto := h.mem_onto
  pre_alloc hr k' m' hk hl := by
    rcases h.pre_alloc hr k' m' hk hl with h1 | ⟨tt, ht, hp⟩
    · exact .inl h1
    · exact .inr ⟨tt, upC_get_of ht, hp⟩
  env_rep i th j tt hs hw ht := by
    obtain ⟨j', hj', hlt⟩ := h.thr_total i (lt_of_get hs)
    rw [hw] at hj'; cases hj'
    rcases up_get_cases ht with ⟨-, ht'⟩ | ⟨h', -⟩
    · exact h.env_rep i th j tt hs hw ht'
    · subst h'; exact absurd hlt (Nat.lt_irrefl _)
  env_total := h.env_total
  stack_pool j rg hr := h.stack_pool j rg (stackRange_up_lt hheld hr).2
  stack_disj j j' rg rg' hne hr hr' :=
    h.stack_disj j j' rg rg' hne (stackRange_up_lt hheld hr).2 (stackRange_up_lt hheld hr').2
  stack_owned j rg hr j' tt' ht' a ha h1 h2 := by
    obtain ⟨hj, hr⟩ := stackRange_up_lt hheld hr
    rcases up_get_cases ht' with ⟨-, ht''⟩ | ⟨hj', htu⟩
    · exact h.stack_owned j rg hr j' tt' ht'' a ha h1 h2
    · subst htu
      show (pl tt'.st (BitVec.ofNat 64 a)).isSome ↔ _
      rw [hpl]; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      intro he; subst hj'; subst he; exact Nat.lt_irrefl _ hj
  stack_private j rg hr := h.stack_private j rg (stackRange_up_lt hheld hr).2
  stack_marked j pl' hm := by
    obtain ⟨tt, rg, v, ht, hr, hv, hc⟩ := h.stack_marked j pl' hm
    exact ⟨tt, rg, v, upC_get_of ht, (stackRange_up (lt_of_get ht)).trans hr, hv, hc⟩
  stack_unmarked := h.stack_unmarked
  env_imm := h.env_imm

end Spike.Lib.TwoSlot
