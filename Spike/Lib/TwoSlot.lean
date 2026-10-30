/-
**The two-slot lift**, for any ISA and `Kernel.Abi`: a
configuration of the canonical machine with one more thread `u` in one more
slot, dormant (`up d u`), steps as `d` does.

- `sysStep_up`, `xferStep_up`, `spawnStep_up` (a `clone` into one of `d`'s
  slots), `soloExec_up`/`certSem_up`/`certAfter_up` (certification ignores
  the extra slot), `stepSemC_up`: every kernel and certified thread step of
  `d`'s threads commutes with `up`.
- `step_up`: a step of `up d u` is a step of `d`, lifted, or a `clone` into
  the extra slot (index `d.1.threads.size`); `up_step`: every step of `d`
  is a step of `up d u`.
- `fault_up` (a fault of `up d u` is one of `d`'s: the extra slot is
  dormant, and with it `clone` faults in fewer cases), `exited_up`,
  `live_up`, `progress_up` (progress of `d` gives progress of `up d u`, for
  an `Inert` extra thread: halted, no promise), `inLayout_up`.

The per-ISA loads are `Spike/Lib/A64TwoSlot.lean` and
`Spike/Lib/X64TwoSlot.lean` (`load_two`, `load_one`: the `kernel 2` load is
the `kernel 1` load, lifted by the inert `dormantAt` thread).
-/
import Scc.Sem.KernelStep
import Scc.Sem.ExtSim

namespace Spike.Lib.TwoSlot

open Kraken.Promising Scc.Sem Scc.Sem.Kernel

variable {I : ISA} {K : Abi I}

/-! ## One dormant slot more -/

/-- The kernel state with one more slot, dormant. -/
def upX (x : KState) : KState := { x with slots := x.slots.push .dormant }

/-- The configuration with one more thread `u`. -/
def upC (c : Config I) (u : Thread I) : Config I := { c with threads := c.threads.push u }

/-- The machine configuration with one more thread `u` in one more slot,
dormant. -/
def up (d : Config I × KState) (u : Thread I) : Config I × KState := (upC d.1 u, upX d.2)

theorem push_get_lt {α : Type} {xs : Array α} {v : α} {i : Nat} (h : i < xs.size) :
    (xs.push v)[i]? = xs[i]? := by
  rw [Array.getElem?_push]; simp [Nat.ne_of_lt h]

theorem set_push {α : Type} {xs : Array α} {v a : α} {i : Nat} (h : i < xs.size) :
    (xs.push v).set! i a = (xs.set! i a).push v := by
  apply Array.ext_getElem?
  intro k
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_push,
    Array.size_setIfInBounds, Array.size_push]
  by_cases hk : i = k
  · subst hk; simp [Nat.ne_of_lt h, h, Nat.lt_succ_of_lt h]
  · simp [hk]

@[simp] theorem upC_mem (c : Config I) (u : Thread I) : (upC c u).mem = c.mem := rfl
@[simp] theorem upC_size (c : Config I) (u : Thread I) : (upC c u).threads.size = c.threads.size + 1 := by
  simp [upC]

theorem upC_get {c : Config I} {u : Thread I} {i : Nat} (h : i < c.threads.size) :
    (upC c u).threads[i]? = c.threads[i]? := push_get_lt h

theorem upC_get_size {c : Config I} {u : Thread I} : (upC c u).threads[c.threads.size]? = some u := by
  simp [upC]

theorem upC_withThread {c : Config I} {u t : Thread I} {i : Nat} {m : Memory} (h : i < c.threads.size) :
    (upC c u).withThread i t m = upC (c.withThread i t m) u := by
  simp only [upC, Config.withThread, set_push h]

theorem withThread_size {c : Config I} {tid : Nat} {t : Thread I} {m : Memory} :
    (c.withThread tid t m).threads.size = c.threads.size := by
  simp [Config.withThread]

theorem set_size {x : KState} {tid : Nat} {s : Slot} : (x.set tid s).slots.size = x.slots.size := by
  simp [KState.set]

@[simp] theorem upX_exited (x : KState) : (upX x).exited = x.exited := rfl
@[simp] theorem upX_held (x : KState) : (upX x).held = x.held := rfl
@[simp] theorem upX_pool (x : KState) : (upX x).pool = x.pool := rfl
@[simp] theorem upX_pmem (x : KState) : (upX x).pmem = x.pmem := rfl
@[simp] theorem upX_size (x : KState) : (upX x).slots.size = x.slots.size + 1 := by simp [upX]

theorem upX_get {x : KState} {i : Nat} (h : i < x.slots.size) : (upX x).slots[i]? = x.slots[i]? :=
  push_get_lt h

theorem upX_runs {x : KState} {i : Nat} (h : i < x.slots.size) : (upX x).runs i = x.runs i := by
  simp only [KState.runs, upX_get h]

theorem upX_wr {x : KState} {i : Nat} (h : i < x.slots.size) : (upX x).wr i = x.wr i := by
  simp only [KState.wr, upX_get h]

theorem upX_runs_size (x : KState) : (upX x).runs x.slots.size = false := by
  simp [KState.runs, upX]

theorem upX_set {x : KState} {i : Nat} {s : Slot} (h : i < x.slots.size) :
    (upX x).set i s = upX (x.set i s) := by
  simp only [upX, KState.set, set_push h]

theorem upX_mapped (x : KState) : mapped (upX x) = mapped x := rfl

/-! ## The kernel's steps of the other threads ignore the extra slot -/

variable (K) in
theorem back_up {tid : Nat} {c : Config I} {y y' : KState} {u t : Thread I} {r : BitVec 64} {x : KState}
    {es : List Ev} (ht : tid < c.threads.size) :
    back K tid (upC c u, y) t r (upX x) es = (back K tid (c, y') t r x es).map fun q => (q.1, up q.2 u) := by
  simp [back, up, upC_withThread ht]

variable (K) in
theorem sysStep_up {A : Arch} {tid : Nat} {d : Config I × KState} {u : Thread I} {p : Pick}
    (hn : d.1.threads.size = d.2.slots.size) (ht : tid < d.1.threads.size) :
    sysStep K A tid (up d u) p = (sysStep K A tid d p).map fun q => (q.1, up q.2 u) := by
  obtain ⟨c, x⟩ := d
  have hs : tid < x.slots.size := hn ▸ ht
  unfold sysStep
  simp only [up, upC_get ht]
  cases c.threads[tid]? with
  | none => rfl
  | some t =>
    simp only [ready, upX_runs hs, upX_exited, upX_wr hs, upC_mem]
    by_cases hr : (K.atSys t.st && x.runs tid && x.exited.isNone) = true
    · simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false]
      rcases callOf K t with _ | call
      · cases p <;> rfl
      · cases call <;> cases p <;> 
          simp only [upC_withThread ht, upX_set hs] <;> (repeat' split) <;>
          first
          | rfl
          | exact back_up K ht
          | simp [Option.map_map, Function.comp_def]
    · simp [hr]

variable (K) in
/-- **A `clone` into one of `d`'s slots commutes with the lift.** -/
theorem spawnStep_up {tid j : Nat} {d : Config I × KState} {u : Thread I} {r : BitVec 64}
    (hn : d.1.threads.size = d.2.slots.size) (ht : tid < d.1.threads.size) (hj : j < d.1.threads.size) :
    spawnStep K tid (up d u) j r = (spawnStep K tid d j r).map (up · u) := by
  obtain ⟨c, x⟩ := d
  have hs : tid < x.slots.size := hn ▸ ht
  have hjs : j < x.slots.size := hn ▸ hj
  unfold spawnStep
  simp only [up, upC_get ht]
  cases c.threads[tid]? with
  | none => rfl
  | some t =>
    simp only [ready, upX_runs hs, upX_exited, upC_mem, upX_get hjs, upC_size, upX_held]
    by_cases hr : (K.atSys t.st && x.runs tid && x.exited.isNone) = true
    · simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false]
      rcases callOf K t with _ | call
      · rfl
      cases call
      case clone stack tls =>
        have hiff : (x.slots[j]? = some .dormant ∧ j < c.threads.size + 1 ∧ 0 < r.toNat ∧ r.toNat < pidMax) ↔
            (x.slots[j]? = some .dormant ∧ j < c.threads.size ∧ 0 < r.toNat ∧ r.toNat < pidMax) :=
          ⟨fun ⟨a, _, b⟩ => ⟨a, hj, b⟩, fun ⟨a, _, b⟩ => ⟨a, Nat.lt_succ_of_lt hj, b⟩⟩
        have hj' : j < (c.withThread tid (retThread K t r) c.mem).threads.size := by
          rw [withThread_size]; exact hj
        by_cases hc : x.slots[j]? = some .dormant ∧ j < c.threads.size ∧ 0 < r.toNat ∧ r.toNat < pidMax
        · simp only [hc, Nat.lt_succ_of_lt hj, and_self, ite_true]
          split
          · simp only [Option.map_some, upC_withThread ht, upC_withThread hj', upX_set hjs]
          · simp only [Option.map_some, upC_withThread ht, upX_set hjs]
            rw [upC_withThread (by rw [withThread_size]; exact hj)]
            rfl
        · simp only [mt hiff.mp hc, hc, ite_false]; rfl
      all_goals rfl
    · simp [hr]

variable (K) in
theorem spawnStep_facts {tid j : Nat} {c c' : Config I × KState} {r : BitVec 64}
    (h : spawnStep K tid c j r = some c') :
    j < c.1.threads.size ∧ c'.1.threads.size = c.1.threads.size ∧ c'.2.slots.size = c.2.slots.size := by
  unfold spawnStep at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · rename_i hc
      refine ⟨hc.2.1, ?_⟩
      split at h <;> cases h <;> exact ⟨by simp only [withThread_size], set_size⟩
    · cases h
  · cases h

theorem fresh_up {c : Config I} {x : KState} {u : Thread I} {r : Range} :
    fresh (upC c u, upX x) r = fresh (c, x) r := rfl

variable (K) in
theorem takeStep_up {tid : Nat} {d : Config I × KState} {u : Thread I}
    (hn : d.1.threads.size = d.2.slots.size) (ht : tid < d.1.threads.size) :
    takeStep K tid (up d u) = (takeStep K tid d).map (up · u) := by
  obtain ⟨c, x⟩ := d
  have hs : tid < x.slots.size := hn ▸ ht
  unfold takeStep
  simp only [up, upC_get ht]
  cases c.threads[tid]? with
  | none => rfl
  | some t =>
    simp only [upX_runs hs, upX_exited, upC_mem, fresh_up]
    split
    · simp [upC_withThread ht]; rfl
    · rfl

variable (K) in
theorem releaseStep_up {tid : Nat} {d : Config I × KState} {u : Thread I}
    (hn : d.1.threads.size = d.2.slots.size) (ht : tid < d.1.threads.size) :
    releaseStep K tid (up d u) = (releaseStep K tid d).map (up · u) := by
  obtain ⟨c, x⟩ := d
  have hs : tid < x.slots.size := hn ▸ ht
  unfold releaseStep
  simp only [up, upC_get ht]
  cases c.threads[tid]? with
  | none => rfl
  | some t =>
    simp only [upX_runs hs, upX_exited, upX_held, upC_mem]
    split
    · simp [upC_withThread ht]; rfl
    · rfl

variable (K) in
theorem xferStep_up {k : XferKind} {tid : Nat} {d : Config I × KState} {u : Thread I}
    (hn : d.1.threads.size = d.2.slots.size) (ht : tid < d.1.threads.size) :
    xferStep K k tid (up d u) = (xferStep K k tid d).map (up · u) := by
  cases k
  · exact takeStep_up K hn ht
  · exact releaseStep_up K hn ht

/-! ## Kernel steps keep the number of threads -/

variable (K) in
theorem sysStep_size {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    (h : sysStep K A tid c p = some (es, c')) : c'.1.threads.size = c.1.threads.size := by
  unfold sysStep at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i t _ _
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> cases p <;> simp only [hcall] at h <;> (repeat' split at h) <;>
    simp only [back, Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals first
    | (obtain ⟨-, rfl⟩ := h; first | rfl | exact withThread_size)
    | (obtain ⟨_, _, -, rfl⟩ := h; exact withThread_size)

variable (K) in
theorem xferStep_size {k : XferKind} {tid : Nat} {c c' : Config I × KState}
    (h : xferStep K k tid c = some c') : c'.1.threads.size = c.1.threads.size := by
  cases k <;> simp only [xferStep, takeStep, releaseStep] at h <;> split at h <;> try cases h
  all_goals
    split at h
    · cases h; exact withThread_size
    · cases h

variable (K) in
theorem sysStep_slots {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    (h : sysStep K A tid c p = some (es, c')) : c'.2.slots.size = c.2.slots.size := by
  unfold sysStep at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i t _ _
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> cases p <;> simp only [hcall] at h <;> (repeat' split at h) <;>
    simp only [back, Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals first
    | (obtain ⟨-, rfl⟩ := h; first | rfl | exact set_size)
    | (obtain ⟨_, _, -, rfl⟩ := h; exact set_size)

variable (K) in
theorem xferStep_slots {k : XferKind} {tid : Nat} {c c' : Config I × KState}
    (h : xferStep K k tid c = some c') : c'.2.slots.size = c.2.slots.size := by
  cases k <;> simp only [xferStep, takeStep, releaseStep] at h <;> split at h <;> try cases h
  all_goals
    split at h
    · cases h; rfl
    · cases h

/-! ## Certification ignores the extra slot -/

variable (K) in
theorem solo_up {site : Option XferKind} {x : KState} {tid : Nat} {s : I.State} (h : tid < x.slots.size) :
    solo K site (upX x) tid s = up (solo K site x tid s) (Thread.init s) := by
  simp only [solo, up, upC, upX, Array.size_push, Array.replicate_succ, set_push h]
  rfl

theorem solo_size {site : Option XferKind} {x : KState} {tid : Nat} {s : I.State} :
    (solo K site x tid s).1.threads.size = (solo K site x tid s).2.slots.size := by
  simp [solo]

theorem stOf_up {tid : Nat} {d : Config I × KState} {u : Thread I} (h : tid < d.1.threads.size) :
    stOf tid (up d u) = stOf tid d := by
  simp only [stOf, up, upC_get h]

variable (K) in
theorem soloExec_up {A : Arch} {μ : Marks} {x : KState} {tid : Nat} (h : tid < x.slots.size) :
    soloExec K A μ (upX x) tid = soloExec K A μ x tid := by
  funext s
  have ht : tid < (solo K none x tid s).1.threads.size := by simp [solo, h]
  unfold soloExec
  split
  · rename_i k _
    have ht' : tid < (solo K (some k) x tid s).1.threads.size := by simp [solo, h]
    rw [solo_up K h, xferStep_up K solo_size ht']
    congr 3
    cases hc : xferStep K k tid (solo K (some k) x tid s) with
    | none => rfl
    | some c' =>
      simp only [Option.map_some, Option.bind_some]
      rw [stOf_up (by rw [xferStep_size K hc]; exact ht')]
  · simp only [solo_up K h, sysStep_up K solo_size ht]
    have key : ∀ r, ((sysStep K A tid (solo K none x tid s) (.ret r)).map
        fun q => (q.1, up q.2 (Thread.init s))).bind (fun q => stOf tid q.2) =
        (sysStep K A tid (solo K none x tid s) (.ret r)).bind (fun q => stOf tid q.2) := by
      intro r
      cases hc : sysStep K A tid (solo K none x tid s) (.ret r) with
      | none => rfl
      | some q =>
        obtain ⟨es, c'⟩ := q
        simp only [Option.map_some, Option.bind_some]
        exact stOf_up (by rw [sysStep_size K hc]; exact ht)
    simp only [key]

variable (K) in
theorem certSem_up {A : Arch} {μ : Marks} {x : KState} {tid : Nat} (h : tid < x.slots.size) :
    certSem K A μ (upX x) tid = certSem K A μ x tid := by
  simp only [certSem, soloExec_up K h]

variable (K) in
theorem certAfter_up {A : Arch} {μ : Marks} {tid : Nat} {d : Config I × KState} {u : Thread I}
    (ht : tid < d.1.threads.size) (hs : tid < d.2.slots.size) :
    CertAfter K A μ tid (up d u) ↔ CertAfter K A μ tid d := by
  simp only [CertAfter, up, upC_get ht, upC_mem, certSem_up K hs]

/-! ## Certified thread steps ignore the extra thread -/

theorem instrSemC_up {A : Arch} {cs : CertSem I} {tid : Nat} {c : Config I} {u : Thread I} {c'' : Config I}
    (ht : tid < c.threads.size) :
    InstrSemC A cs tid (upC c u) c'' ↔ ∃ c', InstrSemC A cs tid c c' ∧ c'' = upC c' u := by
  constructor
  · rintro ⟨t, outs, o, h1, h2, h3, h4, rfl⟩
    rw [upC_get ht] at h1
    exact ⟨_, ⟨t, outs, o, h1, h2, h3, h4, rfl⟩, upC_withThread ht⟩
  · rintro ⟨c', ⟨t, outs, o, h1, h2, h3, h4, rfl⟩, rfl⟩
    exact ⟨t, outs, o, by rw [upC_get ht]; exact h1, h2, h3, h4, (upC_withThread ht).symm⟩

theorem promSemC_up {A : Arch} {cs : CertSem I} {tid : Nat} {c : Config I} {u : Thread I} {c'' : Config I}
    (ht : tid < c.threads.size) :
    PromSemC A cs tid (upC c u) c'' ↔ ∃ c', PromSemC A cs tid c c' ∧ c'' = upC c' u := by
  constructor
  · rintro ⟨t, w, h1, h2, h3, rfl⟩
    rw [upC_get ht] at h1
    exact ⟨_, ⟨t, w, h1, h2, h3, rfl⟩, upC_withThread ht⟩
  · rintro ⟨c', ⟨t, w, h1, h2, h3, rfl⟩, rfl⟩
    exact ⟨t, w, by rw [upC_get ht]; exact h1, h2, h3, (upC_withThread ht).symm⟩

theorem stepSemC_up {A : Arch} {cs : CertSem I} {tid : Nat} {c : Config I} {u : Thread I} {c'' : Config I}
    (ht : tid < c.threads.size) :
    StepSemC A cs tid (upC c u) c'' ↔ ∃ c', StepSemC A cs tid c c' ∧ c'' = upC c' u := by
  unfold StepSemC
  rw [instrSemC_up ht, promSemC_up ht]
  constructor
  · rintro (⟨c', h, rfl⟩ | ⟨c', h, rfl⟩)
    · exact ⟨c', .inl h, rfl⟩
    · exact ⟨c', .inr h, rfl⟩
  · rintro ⟨c', h | h, rfl⟩
    · exact .inl ⟨c', h, rfl⟩
    · exact .inr ⟨c', h, rfl⟩

theorem stepSemC_size {A : Arch} {cs : CertSem I} {tid : Nat} {c c' : Config I} (h : StepSemC A cs tid c c') :
    c'.threads.size = c.threads.size := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> exact withThread_size

theorem lt_of_runs_up {x : KState} {tid : Nat} (h : (upX x).runs tid = true) : tid < x.slots.size := by
  rcases Nat.lt_or_ge tid x.slots.size with h' | h'
  · exact h'
  · exfalso
    rcases Nat.eq_or_lt_of_le h' with rfl | h''
    · rw [upX_runs_size] at h; cases h
    · have : (upX x).slots[tid]? = none := Array.getElem?_eq_none_iff.mpr (by simp; omega)
      simp [KState.runs, this] at h

/-! ## The machine's steps from a lifted configuration -/

section Machine

variable {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat}

local notation "M" => ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf

theorem runs_up {tid : Nat} {d : Config I × KState} {u : Thread I}
    (ht : tid < d.1.threads.size) (hs : tid < d.2.slots.size) :
    (M).runs (up d u) tid ↔ (M).runs d tid := by
  show (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  simp only [Kernel.hooks, up, upX_exited, upX_runs hs]
  erw [upC_get ht]

theorem runs_up_lt {tid : Nat} {d : Config I × KState} {u : Thread I} (h : (M).runs (up d u) tid) :
    tid < d.2.slots.size := by
  obtain ⟨-, -, h⟩ := h
  exact lt_of_runs_up (by simpa [Kernel.hooks, up] using h)

theorem atSys_up {tid : Nat} {d : Config I × KState} {u : Thread I} (ht : tid < d.1.threads.size) :
    (M).atSys (up d u) tid ↔ (M).atSys d tid := by
  show (∃ _, _) ↔ (∃ _, _)
  simp only [up]
  erw [upC_get ht]

theorem atAddr_up {a tid : Nat} {d : Config I × KState} {u : Thread I} (ht : tid < d.1.threads.size) :
    (M).AtAddr a (up d u) tid ↔ (M).AtAddr a d tid := by
  simp only [ExtMachine.AtAddr, up]
  erw [upC_get ht]
  exact Iff.rfl

theorem atSite_up {μ : Marks} {k : XferKind} {tid : Nat} {d : Config I × KState} {u : Thread I}
    (ht : tid < d.1.threads.size) :
    (M).AtSite μ k (up d u) tid ↔ (M).AtSite μ k d tid := by
  simp only [ExtMachine.AtSite, atAddr_up ht]

/-- **A step of the lifted configuration is a step of the one-slot
configuration, lifted** (the thread is one of `d`'s, the extra thread and
slot untouched), **or a `clone` into the extra slot** (index
`d.1.threads.size`). -/
theorem step_up {μ : Marks} {tid : Nat} {d : Config I × KState} {u : Thread I} {es : List Ev}
    {c' : (M).Cfg} (hn : d.1.threads.size = d.2.slots.size)
    (h : (M).Step μ tid (up d u) es c') :
    tid < d.1.threads.size ∧
      ((∃ d', (M).Step μ tid d es d' ∧ c' = up d' u) ∨
        (es = [] ∧ ∃ r, spawnStep K tid (up d u) d.1.threads.size r = some c' ∧ CertAfter K A μ tid c')) := by
  have hs : tid < d.2.slots.size := runs_up_lt h.runs
  have ht : tid < d.1.threads.size := hn ▸ hs
  refine ⟨ht, ?_⟩
  cases h with
  | @instr c₁ hr ha hk hst =>
    have hst' : StepSemC A (certSem K A μ d.2 tid) tid (upC d.1 u) c₁ := by
      have h0 : StepSemC A (certSem K A μ (upX d.2) tid) tid (upC d.1 u) c₁ := hst
      rwa [certSem_up K hs] at h0
    obtain ⟨c'', h1, rfl⟩ := (stepSemC_up ht).mp hst'
    refine .inl ?_
    exact ⟨(c'', d.2), .instr ((runs_up ht hs).mp hr) (fun h => ha ((atSys_up ht).mpr h))
      (fun k h => hk k ((atSite_up ht).mpr h)) h1, rfl⟩
  | spawn hr hy =>
    obtain ⟨j, r, h1, h2⟩ := hy
    have h1 : spawnStep K tid (up d u) j r = some c' := h1
    have hj := (spawnStep_facts K h1).1
    simp only [up, upC_size] at hj
    rcases Nat.lt_or_ge j d.1.threads.size with hj' | hj'
    · rw [spawnStep_up K hn ht hj'] at h1
      cases h3 : spawnStep K tid d j r with
      | none => rw [h3] at h1; cases h1
      | some d' =>
      rw [h3] at h1
      cases h1
      obtain ⟨-, e1, e2⟩ := spawnStep_facts K h3
      exact .inl ⟨d', .spawn ((runs_up ht hs).mp hr)
        ⟨j, r, h3, (certAfter_up K (e1 ▸ ht) (e2 ▸ hs)).mp h2⟩, rfl⟩
    · obtain rfl : j = d.1.threads.size := by omega
      exact .inr ⟨rfl, r, h1, h2⟩
  | sys hr hy hl ha he =>
    obtain ⟨p, h1, h2⟩ := hy
    have h1 : sysStep K A tid (up d u) p = some (es, c') := h1
    rw [sysStep_up K hn ht] at h1
    cases h3 : sysStep K A tid d p with
    | none => rw [h3] at h1; cases h1
    | some q =>
    obtain ⟨es', d'⟩ := q
    rw [h3] at h1
    cases h1
    have h1 := h3
    have ht' : tid < d'.1.threads.size := by rw [sysStep_size K h1]; exact ht
    have hs' : tid < d'.2.slots.size := by rw [sysStep_slots K h1]; exact hs
    refine .inl ?_
    exact ⟨d', .sys ((runs_up ht hs).mp hr) ⟨p, h1, (certAfter_up K ht' hs').mp h2⟩ hl
      (fun k hk => (ha k hk).imp fun a ⟨h1, h2⟩ => ⟨h1, (atAddr_up ht).mp h2⟩)
      (fun e he' k a hk h2 => he e he' k a hk ((atAddr_up ht).mpr h2)), rfl⟩
  | xfer k hr ha hx =>
    have hx' : xferStep K k tid (up d u) = some c' := hx
    rw [xferStep_up K hn ht] at hx'
    cases h1 : xferStep K k tid d with
    | none => rw [h1] at hx'; cases hx'
    | some d' =>
    rw [h1] at hx'
    cases hx'
    refine .inl ?_
    exact ⟨d', .xfer k ((runs_up ht hs).mp hr) ((atSite_up ht).mp ha) h1, rfl⟩

/-- **A step of the one-slot configuration is a step of the lifted
configuration** (a `clone` included: its slot is one of `d`'s). -/
theorem up_step {μ : Marks} {tid : Nat} {d d' : (M).Cfg} {u : Thread I} {es : List Ev}
    (hn : d.1.threads.size = d.2.slots.size) (h : (M).Step μ tid d es d') :
    (M).Step μ tid (up d u) es (up d' u) := by
  have ht : tid < d.1.threads.size := by
    obtain ⟨⟨t, ht⟩, -, -⟩ := h.runs
    exact (Array.getElem?_eq_some_iff.mp ht).1
  have hs : tid < d.2.slots.size := hn ▸ ht
  cases h with
  | instr hr ha hk hst =>
    refine .instr ((runs_up ht hs).mpr hr) (fun h => ha ((atSys_up ht).mp h))
      (fun k h => hk k ((atSite_up ht).mp h)) ?_
    show StepSemC A (certSem K A μ (upX d.2) tid) tid (upC d.1 u) (upC _ u)
    rw [certSem_up K hs]
    exact (stepSemC_up ht).mpr ⟨_, hst, rfl⟩
  | spawn hr hy =>
    obtain ⟨j, r, h1, h2⟩ := hy
    have h1 : spawnStep K tid d j r = some d' := h1
    obtain ⟨hj, e1, e2⟩ := spawnStep_facts K h1
    refine .spawn ((runs_up ht hs).mpr hr) ⟨j, r, ?_, (certAfter_up K (e1 ▸ ht) (e2 ▸ hs)).mpr h2⟩
    have e := spawnStep_up K (r := r) (u := u) hn ht hj
    simp only [h1] at e
    exact e
  | sys hr hy hl ha he =>
    obtain ⟨p, h1, h2⟩ := hy
    have h1 : sysStep K A tid d p = some (es, d') := h1
    have ht' : tid < d'.1.threads.size := lt_of_lt_of_eq ht (sysStep_size K h1).symm
    have hs' : tid < d'.2.slots.size := lt_of_lt_of_eq hs (sysStep_slots K h1).symm
    refine .sys ((runs_up ht hs).mpr hr) ⟨p, ?_, (certAfter_up K ht' hs').mpr h2⟩ hl
      (fun k hk => (ha k hk).imp fun a ⟨h1, h2⟩ => ⟨h1, (atAddr_up ht).mpr h2⟩)
      (fun e he' k a hk h2 => he e he' k a hk ((atAddr_up ht).mp h2))
    have e := sysStep_up K (A := A) (p := p) (u := u) hn ht
    simp only [h1] at e
    exact e
  | xfer k hr ha hx =>
    refine .xfer k ((runs_up ht hs).mpr hr) ((atSite_up ht).mpr ha) ?_
    show xferStep K k tid (up d u) = some (up d' u)
    have e := xferStep_up K (k := k) (u := u) hn ht
    simp only [show xferStep K k tid d = some d' from hx] at e
    exact e

/-! ### Faults, exit, liveness and progress -/

theorem dormants_up (x : KState) : (upX x).dormants.isEmpty = false := by
  rw [List.isEmpty_eq_false_iff_exists_mem]
  refine ⟨x.slots.size, ?_⟩
  simp [KState.dormants, upX]

/-- **A kernel fault of the lifted configuration is one of `d`'s**: the extra
slot is dormant, so the thread is one of `d`'s; at `clone` the lifted
configuration has a dormant slot, so it faults there in fewer cases. -/
theorem faultAt_up {tid : Nat} {d : Config I × KState} {u : Thread I}
    (hn : d.1.threads.size = d.2.slots.size) (h : faultAt K (up d u) tid = true) :
    faultAt K d tid = true := by
  have hr : (upX d.2).runs tid = true := by
    unfold faultAt at h
    split at h
    · simp only [up, Bool.and_eq_true] at h; exact h.1.1
    · cases h
  have hs : tid < d.2.slots.size := lt_of_runs_up hr
  have ht : tid < d.1.threads.size := hn ▸ hs
  unfold faultAt at h ⊢
  simp only [up, upC_get ht, upX_runs hs, upX_exited, dormants_up] at h
  split at h
  · rename_i t ht'
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with h2 | h2
    · refine .inl ⟨h2.1, ?_⟩
      have h3 := h2.2
      split at h3 <;> simp_all
    · exact .inr h2
  · cases h

theorem unmappedAt_up {tid : Nat} {d : Config I × KState} {u : Thread I}
    (hn : d.1.threads.size = d.2.slots.size) (h : unmappedAt K (up d u) tid) : unmappedAt K d tid := by
  obtain ⟨t, e, h1, h2, h3, h4, h5, h6⟩ := h
  have hs : tid < d.2.slots.size := lt_of_runs_up h2
  have ht : tid < d.1.threads.size := hn ▸ hs
  simp only [up, upC_get ht, upX_runs hs, upX_exited, upX_mapped] at h1 h2 h3 h6
  exact ⟨t, e, h1, h2, h3, h4, h5, h6⟩

theorem fault_up {d : Config I × KState} {u : Thread I} (hn : d.1.threads.size = d.2.slots.size)
    (h : (M).fault (up d u)) : (M).fault d := by
  rcases h with ⟨tid, m, ⟨⟨t, h1⟩, h2, h3⟩, h4, h5⟩ | h | h
  · have hr : (upX d.2).runs tid = true := by simpa [Kernel.hooks, up] using h3
    have hs : tid < d.2.slots.size := lt_of_runs_up hr
    have ht : tid < d.1.threads.size := hn ▸ hs
    refine .inl ⟨tid, m, ?_, ?_, ?_⟩
    · exact (runs_up ht hs).mp ⟨⟨t, h1⟩, h2, h3⟩
    · exact fun h => h4 ((atSys_up ht).mpr h)
    · obtain ⟨outs, hso, hm⟩ := h5
      refine ⟨outs, ?_, hm⟩
      simp only [stepThread, up] at hso ⊢
      erw [upC_get ht] at hso
      exact hso
  · obtain ⟨tid, h⟩ := h
    exact .inr (.inl ⟨tid, faultAt_up hn h⟩)
  · obtain ⟨tid, h⟩ := h
    exact .inr (.inr ⟨tid, unmappedAt_up hn h⟩)

/-- The extra thread is **inert**: halted, with no promise. -/
def Inert (u : Thread I) : Prop := u.halted = true ∧ u.prom = []

theorem final_up {c : Config I} {u : Thread I} (hu : Inert u) : (upC c u).final = c.final := by
  simp [Config.final, upC, hu.1, hu.2]

theorem exited_up {d : Config I × KState} {u : Thread I} (hu : Inert u) :
    (M).exited (up d u) = (M).exited d := by
  simp only [ExtMachine.ofHooks, Kernel.hooks, up, upX_exited, final_up hu]

theorem live_up {tid : Nat} {d : Config I × KState} {u : Thread I} (hn : d.1.threads.size = d.2.slots.size) :
    (M).live (up d u) tid ↔ (M).live d tid := by
  show (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  simp only [Kernel.hooks, up, upX_exited]
  rcases Nat.lt_or_ge tid d.2.slots.size with hs | hs
  · have ht : tid < d.1.threads.size := hn ▸ hs
    rw [upX_runs hs]
    erw [upC_get ht]
  · have h1 : (upX d.2).runs tid = false := by
      rcases Nat.eq_or_lt_of_le hs with rfl | h''
      · exact upX_runs_size _
      · have : (upX d.2).slots[tid]? = none := Array.getElem?_eq_none_iff.mpr (by simp; omega)
        simp [KState.runs, this]
    have h2 : d.2.runs tid = false := by
      have : d.2.slots[tid]? = none := Array.getElem?_eq_none_iff.mpr hs
      simp [KState.runs, this]
    simp [h1, h2]

/-- **Progress transfers to the lifted configuration.** -/
theorem progress_up {μ : Marks} {d : Config I × KState} {u : Thread I}
    (hn : d.1.threads.size = d.2.slots.size) (hu : Inert u) (h : (M).Progress μ d) :
    (M).Progress μ (up d u) := by
  obtain ⟨hf, hp⟩ := h
  refine ⟨fun h => hf (fault_up hn h), ?_⟩
  rw [exited_up hu]
  rcases hp with hp | ⟨⟨tid, hl⟩, hs⟩
  · exact .inl hp
  · refine .inr ⟨⟨tid, (live_up hn).mpr hl⟩, fun tid hl => ?_⟩
    obtain ⟨es, d', hst⟩ := hs tid ((live_up hn).mp hl)
    exact ⟨es, up d' u, up_step hn hst⟩

theorem inLayout_up {Λ : Layout} {d : Config I × KState} {u : Thread I} :
    @InLayout Λ (M) (up d u) ↔ @InLayout Λ (M) d := Iff.rfl

end Machine

end Spike.Lib.TwoSlot
