/-
**Condition (3) of Theorem 1′ for the SLR instance** (`SLR.Cond3`): every
annotated run (`AnnRun`) of a
path from `Config.init` to a final configuration is valid (`Valid`) at every
real index.

## The argument

Fix a real index `j`, its micro-index `μ₀ = pos j`, a thread `i` and an
outstanding promise `ts` of `i` at `cfg μ₀` (message `w`). Pending or not,
`ts` is in fact fulfilled later by `i` with a write permission for `w.loc`:

1. The last micro-configuration `cfg N` is the final configuration `π L`
   (`Config.VirtualOf.eq_of_final`), which has no promises. So there is a last
   `f ≥ μ₀` with `ts` outstanding at `i` on all of `cfg μ₀ … cfg f`
   (`exists_last`), and the micro-step at `f` removes it.
2. Promise and prepay steps only add promises, and an `np` step of another
   thread leaves `i`'s state alone; so the step at `f` is an `np` step of `i`,
   it writes `w` (`Written`), and `MicroStep.np`'s ownership conjunct gives
   `0 < ((rF f i).wr w.loc).q` (`MicroStep.owns_of_fulfil`).
3. Bounded reach through messages `≤ ts - 1` is pulled back from `f` to `μ₀`
   (`cond3_of_run`): across a step of another thread, a promise or a
   prepayment of another thread by `K2`; across `i`'s own `np` steps and
   prepayments by `K1` (`MicroStep.pull`), whose write-floor hypothesis holds
   because every micro thread state is a real thread state of the live path
   (`AnnRun.real`) still holding `ts`, so `Config.Live.wfloor_lt` bounds its
   floor `max vwNew vCAP` below `ts` (`AnnRun.wfloor_lt`).

So the conclusion holds for pending promises too; `Valid` asks only for the
non-pending ones.

## Generic chain

Proved generically (`MicroStep'.pull`, `AnnRun'.valid`, `cond3'`) for every
K2 frame `K` with `K2OK`: `MicroStep'.pull` applies `K2OK` to the erased
configuration `AnnRun'.erase` and the existing thread `i`. The existing names
are the instances at `GRF`, `K2₀` (end of file).
-/
import Kraken.Promising.SLR.Theorem1Run
import Kraken.Promising.SLR.Cond3

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## Machine facts -/

/-- A final configuration has no outstanding promises. -/
theorem Config.prom_nil_of_final {c : Config I} (hf : c.final = true) {i : Nat} {t : Thread I}
    (ht : c.threads[i]? = some t) : t.prom = [] := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  simp only [Config.final, Array.all_eq_true] at hf
  have := hf i hi
  simp_all

/-- An instruction step only extends memory. -/
theorem NPStepBy.mem_prefix {A : Arch} {s : Nat} {c c' : Config I} (h : NPStepBy A s c c') :
    c.mem.Prefix c'.mem := by
  obtain ⟨t, t', mem', -, ⟨outs, o, hso, ho, hq⟩, rfl⟩ := h
  simp only [Prod.mk.injEq] at hq
  obtain ⟨-, rfl⟩ := hq
  exact Memory.Prefix.stepOne hso ho

/-- An instruction step of `s` leaves every other thread alone. -/
theorem NPStepBy.get?_other {A : Arch} {s i : Nat} {c c' : Config I} (h : NPStepBy A s c c') (hne : s ≠ i) :
    c'.threads[i]? = c.threads[i]? := by
  obtain ⟨t, t', mem', ht, -, rfl⟩ := h
  rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht)]
  simp only [hne, ↓reduceIte]

/-- A promise of `s` keeps every promise of every thread. -/
theorem promised_keeps {c : Config I} {s : Nat} {t : Thread I} {w : Msg} (ht : c.threads[s]? = some t)
    {i : Nat} {ti : Thread I} (hti : c.threads[i]? = some ti) {ts : Time} (hts : ts ∈ ti.prom) :
    ∃ t', (Promised c s t w).threads[i]? = some t' ∧ ts ∈ t'.prom := by
  rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht)]
  by_cases hs : s = i
  · subst hs
    rw [ht] at hti
    cases hti
    simp only [↓reduceIte]
    exact ⟨_, rfl, List.mem_append_left _ hts⟩
  · simp only [hs, ↓reduceIte]
    exact ⟨ti, hti, hts⟩

/-! ## Micro-steps -/

section Micro

variable {K : K2Frame (model I)} {A : Arch} {c c' : Config I} {rF rF' : Nat → Res} {g g' : Ghost}

/-- A micro-step only extends memory. -/
theorem MicroStep'.mem_prefix (h : MicroStep' K A c rF g c' rF' g') : c.mem.Prefix c'.mem := by
  cases h with
  | np _ _ _ _ hs => exact NPStepBy.mem_prefix hs
  | promise => exact promised_prefix
  | prepay => exact promised_prefix

/-- **The transition lemma** (`cond3_of_run`'s `hstep`): bounded reach of
thread `i` through messages `≤ b ≤ c.mem.last` is pulled back across a
micro-step, provided `i`'s write floor after it is at most `b`: `K2` for a
step of another thread, nothing for a promise, `K1` for a step or a
prepayment of `i`. -/
theorem MicroStep'.pull (KOK : K2OK (model I) K) (h : MicroStep' K A c rF g c' rF' g') {T : Nat → Prop}
    (E : Erase rF g T c) (i : Nat) (hi : i < c.threads.size) {b : Time} (hb : b ≤ c.mem.last)
    (hfl : ∀ t', c'.threads[i]? = some t' → t'.views.wfloor ≤ b) {x : Loc}
    (hr : reachB (rF' i) g' x b) : reachB (rF i) g x b := by
  cases h with
  | np s t t' _ _ ht' hrF _ _ _ _ _ hK2 hK1 =>
    by_cases hs : s = i
    · subst hs
      exact hK1 b hb (hfl t' ht') x hr
    · rw [hrF i (Ne.symm hs)] at hr
      exact KOK rF g g' T c i c.mem.last E hi hK2 b hb x hr
  | promise => exact hr
  | prepay s t w ht hrF _ _ _ _ _ hK2 hK1 =>
    by_cases hs : s = i
    · subst hs
      refine hK1 b hb ?_ x hr
      have hget : (Promised c s t w).threads[s]? =
          some { t with prom := t.prom ++ [(c.mem.append { w with tid := s }).2] } := by
        rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht)]
        simp only [↓reduceIte]
      have := hfl _ hget
      exact this
    · rw [hrF i (Ne.symm hs)] at hr
      exact KOK rF g g' T c i c.mem.last E hi hK2 b hb x hr

/-- **The fulfilling step**: a micro-step after which thread `i` no longer
holds its outstanding promise `ts` (message `w`) is an `np` step of `i` that
writes `w`, so `i` owns `w.loc` before it. -/
theorem MicroStep'.owns_of_fulfil (h : MicroStep' K A c rF g c' rF' g') {i : Nat} {t : Thread I}
    (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom)
    (hn : ¬ ∃ t', c'.threads[i]? = some t' ∧ ts ∈ t'.prom) {w : Msg} (hw : c.mem.get? ts = some w) :
    0 < ((rF i).wr w.loc).q := by
  cases h with
  | np s t₀ t' ht₀ hs _ _ _ _ _ _ hown _ _ =>
    by_cases hsi : s = i
    · subst hsi
      rw [ht] at ht₀
      cases ht₀
      refine hown w ⟨ts, ?_, fun t'' h'' hm => hn ⟨t'', h'', hm⟩, .inr fun t₁ h₁ => ?_⟩
      · rw [(NPStepBy.mem_prefix hs).get? (Memory.last_le_of_get?_eq_some _ hw)]
        exact hw
      · rw [ht] at h₁
        cases h₁
        exact hts
    · exact absurd ⟨t, by rw [NPStepBy.get?_other hs hsi]; exact ht, hts⟩ hn
  | promise s t₀ w₀ ht₀ => exact absurd (promised_keeps ht₀ ht hts) hn
  | prepay s t₀ w₀ ht₀ => exact absurd (promised_keeps ht₀ ht hts) hn

end Micro

/-! ## Paths and annotated runs -/

section Run

variable {GV : PrepayGuard I} {K : K2Frame (model I)} {A : Arch} {fuel : Nat}

/-- Later configurations of a path are reachable from earlier ones. -/
theorem Path.reachableBetween (π : Path A fuel I) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ π.len) :
    Reachable A fuel (π.cfg j) (π.cfg k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction d with
  | zero => exact .refl _
  | succ d ih =>
    exact Reachable.trans A fuel (ih (by omega) (by omega)) (Reachable.single A fuel (π.step _ (by omega)))

/-- Every configuration of a path to a final configuration is live. -/
theorem Path.liveAt (π : Path A fuel I) (hf : (π.cfg π.len).final = true) {j : Nat} (hj : j ≤ π.len) :
    (π.cfg j).Live A fuel :=
  ⟨_, π.reachableBetween hj (Nat.le_refl _), hf⟩

variable {π : Path A fuel I} (R : AnnRun' GV K A π)

theorem AnnRun'.pos_le {j k : Nat} (hjk : j ≤ k) (hk : k ≤ π.len) : R.pos j ≤ R.pos k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (ih (by omega) (by omega)) (R.pos_mono _ (by omega))

/-- Micro-configurations only extend memory. -/
theorem AnnRun'.mem_prefix {μ ν : Nat} (hμν : μ ≤ ν) (hν : ν ≤ R.N) : (R.cfg μ).mem.Prefix (R.cfg ν).mem := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hμν
  induction d with
  | zero => exact .refl _
  | succ d ih => exact (ih (by omega) (by omega)).trans (R.step _ (by omega)).mem_prefix

/-- The last micro-configuration is the final configuration of the path. -/
theorem AnnRun'.cfg_N (hf : (π.cfg π.len).final = true) : R.cfg R.N = π.cfg π.len := by
  have := (R.virtual π.len (Nat.le_refl _)).eq_of_final hf
  rwa [R.pos_len] at this

/-- **The write floor at micro-configurations**: a micro thread state that
holds the promise `ts` has its write floor below `ts`, since it is a real
thread state of the live path holding `ts` (`AnnRun'.real`,
`Config.Live.wfloor_lt`). -/
theorem AnnRun'.wfloor_lt [I.LawfulState] (hf : (π.cfg π.len).final = true) {μ : Nat} (hμ : μ ≤ R.N)
    {s : Nat} {t : Thread I} (ht : (R.cfg μ).threads[s]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.wfloor < ts := by
  obtain ⟨j, tj, hj, htj, hv, hp⟩ := R.real μ hμ s t ht
  rw [show t.views.wfloor = tj.views.wfloor by rw [hv]]
  exact (π.liveAt hf hj).wfloor_lt htj (hp ts hts)

end Run

/-- The last index of an interval `[a, b]` up to which `P` holds
continuously from `a`, if `P a` and `¬ P b`. -/
theorem exists_last (P : Nat → Prop) {a b : Nat} (hab : a ≤ b) (ha : P a) (hb : ¬ P b) :
    ∃ f, a ≤ f ∧ f < b ∧ (∀ μ, a ≤ μ → μ ≤ f → P μ) ∧ ¬ P (f + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d generalizing a with
  | zero => exact absurd ha hb
  | succ d ih =>
    by_cases h : P (a + 1)
    · obtain ⟨f, h1, h2, h3, h4⟩ := ih (a := a + 1) h (by rwa [Nat.add_right_comm])
      refine ⟨f, by omega, by omega, fun μ hμ hμf => ?_, h4⟩
      rcases Nat.eq_or_lt_of_le hμ with rfl | hlt
      · exact ha
      · exact h3 μ hlt hμf
    · exact ⟨a, Nat.le_refl _, by omega, fun μ h1 h2 => by rwa [Nat.le_antisymm h2 h1], h⟩

/-- **Validity at every micro-configuration** of an annotated run of a path
to a final configuration (see the module docstring), including the hybrid
micro-configurations of replays and prepayments between real indices. -/
theorem AnnRun'.valid {GV : PrepayGuard I} {K : K2Frame (model I)} (KOK : K2OK (model I) K) {A : Arch} {fuel : Nat} [I.LawfulState] {π : Path A fuel I} (R : AnnRun' GV K A π)
    (hfin : (π.cfg π.len).final = true) {μ₀ : Nat} (hμ₀ : μ₀ ≤ R.N) :
    Valid (R.cfg μ₀) (R.rF μ₀) (R.g μ₀) := by
  intro i t ht ts hts _ w hw
  let P : Nat → Prop := fun μ => ∃ t', (R.cfg μ).threads[i]? = some t' ∧ ts ∈ t'.prom
  have hPN : ¬ P R.N := by
    rintro ⟨t', ht', hm⟩
    rw [R.cfg_N hfin] at ht'
    rw [Config.prom_nil_of_final hfin ht'] at hm
    exact List.not_mem_nil hm
  obtain ⟨f, hjf, hfN, hP, hPf⟩ := exists_last P hμ₀ ⟨t, ht, hts⟩ hPN
  have hget : ∀ μ, μ₀ ≤ μ → μ ≤ R.N → (R.cfg μ).mem.get? ts = some w := fun μ h1 h2 => by
    rw [(R.mem_prefix h1 h2).get? (Memory.last_le_of_get?_eq_some _ hw)]
    exact hw
  obtain ⟨tf, htf, hmf⟩ := hP f hjf (Nat.le_refl _)
  refine cond3_of_run (c := R.cfg) (rF := R.rF) (g := R.g) (k := i) (ts := ts) hjf
    (fun μ h1 h2 => Memory.last_le_of_get?_eq_some _ (hget μ h1 (by omega)))
    (fun μ h1 h2 b hb hfl hr => (R.step μ (by omega)).pull KOK (R.erase μ (by omega)) i
      (by obtain ⟨t', ht', -⟩ := hP μ h1 (by omega); exact lt_size_of_get? ht') hb hfl hr)
    (fun μ h1 h2 t' ht' => ?_)
    ((R.step f hfN).owns_of_fulfil htf hmf hPf (hget f hjf (by omega)))
  obtain ⟨t'', ht'', hm⟩ := hP μ (by omega) h2
  rw [ht'] at ht''
  cases ht''
  exact R.wfloor_lt hfin (by omega) ht' hm

/-- **Condition (3) of Theorem 1′ for the SLR instance** (see the module
docstring): every annotated run of a path from the
initial configuration to a final one is valid at every real index
(`AnnRun'.valid`: in fact at every micro index). -/
theorem cond3' {GV : PrepayGuard I} {K : K2Frame (model I)} (KOK : K2OK (model I) K) (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State) (initMem : List (Loc × Val)) :
    Cond3' (I := I) GV K A fuel states initMem := fun _ _ hfin R _ hμ =>
  R.valid KOK hfin hμ

/-! ## The existing names: instances at `GRF`, `K2₀` (`SLR/NPSafePGen.lean`) -/

section MergedMicro

variable {A : Arch} {c c' : Config I} {rF rF' : Nat → Res} {g g' : Ghost}

/-- A micro-step only extends memory. -/
theorem MicroStep.mem_prefix (h : MicroStep A c rF g c' rF' g') : c.mem.Prefix c'.mem := by
  npgen MicroStep'.mem_prefix

/-- **The transition lemma** (`cond3_of_run`'s `hstep`): bounded reach of
thread `i` through messages `≤ b ≤ c.mem.last` is pulled back across a
micro-step, provided `i`'s write floor after it is at most `b`: `K2` for a
step of another thread, nothing for a promise, `K1` for a step or a
prepayment of `i`. (At `K2₀` no erasure is needed, unlike `MicroStep'.pull`.) -/
theorem MicroStep.pull (h : MicroStep A c rF g c' rF' g') (i : Nat) {b : Time} (hb : b ≤ c.mem.last)
    (hfl : ∀ t', c'.threads[i]? = some t' → t'.views.wfloor ≤ b) {x : Loc}
    (hr : reachB (rF' i) g' x b) : reachB (rF i) g x b := by
  cases h with
  | np s t t' _ _ ht' hrF _ _ _ _ _ hK2 hK1 =>
    by_cases hs : s = i
    · subst hs
      exact hK1 b hb (hfl t' ht') x hr
    · rw [hrF i (Ne.symm hs)] at hr
      exact hK2 b hb _ x hr
  | promise => exact hr
  | prepay s t w ht hrF _ _ _ _ _ hK2 hK1 =>
    by_cases hs : s = i
    · subst hs
      refine hK1 b hb ?_ x hr
      have hget : (Promised c s t w).threads[s]? =
          some { t with prom := t.prom ++ [(c.mem.append { w with tid := s }).2] } := by
        rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht)]
        simp only [↓reduceIte]
      have := hfl _ hget
      exact this
    · rw [hrF i (Ne.symm hs)] at hr
      exact hK2 b hb _ x hr

/-- **The fulfilling step**: a micro-step after which thread `i` no longer
holds its outstanding promise `ts` (message `w`) is an `np` step of `i` that
writes `w`, so `i` owns `w.loc` before it. -/
theorem MicroStep.owns_of_fulfil (h : MicroStep A c rF g c' rF' g') {i : Nat} {t : Thread I}
    (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom)
    (hn : ¬ ∃ t', c'.threads[i]? = some t' ∧ ts ∈ t'.prom) {w : Msg} (hw : c.mem.get? ts = some w) :
    0 < ((rF i).wr w.loc).q := by
  npgen MicroStep'.owns_of_fulfil

end MergedMicro

section MergedRun

variable {A : Arch} {fuel : Nat}

variable {π : Path A fuel I} (R : AnnRun A π)

theorem AnnRun.pos_le {j k : Nat} (hjk : j ≤ k) (hk : k ≤ π.len) : R.pos j ≤ R.pos k := by
  npgen AnnRun'.pos_le

/-- Micro-configurations only extend memory. -/
theorem AnnRun.mem_prefix {μ ν : Nat} (hμν : μ ≤ ν) (hν : ν ≤ R.N) : (R.cfg μ).mem.Prefix (R.cfg ν).mem := by
  npgen AnnRun'.mem_prefix

/-- The last micro-configuration is the final configuration of the path. -/
theorem AnnRun.cfg_N (hf : (π.cfg π.len).final = true) : R.cfg R.N = π.cfg π.len := by
  npgen AnnRun'.cfg_N

/-- **The write floor at micro-configurations**: a micro thread state that
holds the promise `ts` has its write floor below `ts`, since it is a real
thread state of the live path holding `ts` (`AnnRun.real`,
`Config.Live.wfloor_lt`). -/
theorem AnnRun.wfloor_lt [I.LawfulState] (hf : (π.cfg π.len).final = true) {μ : Nat} (hμ : μ ≤ R.N)
    {s : Nat} {t : Thread I} (ht : (R.cfg μ).threads[s]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.wfloor < ts := by
  npgen AnnRun'.wfloor_lt

end MergedRun

/-- **Validity at every micro-configuration** of an annotated run of a path
to a final configuration (see the module docstring), including the hybrid
micro-configurations of replays and prepayments between real indices. -/
theorem AnnRun.valid {A : Arch} {fuel : Nat} [I.LawfulState] {π : Path A fuel I} (R : AnnRun A π)
    (hfin : (π.cfg π.len).final = true) {μ₀ : Nat} (hμ₀ : μ₀ ≤ R.N) :
    Valid (R.cfg μ₀) (R.rF μ₀) (R.g μ₀) := by
  npgen AnnRun'.valid

/-- **Condition (3) of Theorem 1′ for the SLR instance** (see the module
docstring): every annotated run of a path from the
initial configuration to a final one is valid at every real index
(`AnnRun.valid`: in fact at every micro index). -/
theorem cond3 (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State) (initMem : List (Loc × Val)) :
    Cond3 (I := I) A fuel states initMem := by
  npgen cond3'

end Kraken.Promising.SLR
