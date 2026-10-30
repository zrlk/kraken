/-
**The clone handover**, kernel side, for any ISA and
`Kernel.Abi`: a `clone` of a thread of `d` into the extra, dormant slot of
the lifted configuration `up d u` (`Spike.Lib.TwoSlot`, the second case of
`step_up`).

- `spawn_extra`: the step is taken at a `clone` call of a running thread
  `tid` of `d`, with a child thread id in `(0, pidMax)`; after it the
  configuration is `d`'s threads with `tid` returned (`retThread`, `ctid`)
  and the child (`childThread`) appended, the extra slot running, and
  either no range handed over or the range the parent holds that ends at
  the child's stack moved from the parent to the child, with its bytes.
- `handover_child`: the child's facts: state `Abi.child` of the parent's
  (private memory as `Abi.child` leaves it, with the handed range's bytes),
  no promise, the parent's views without forwarding and exclusive records:
  so the same `coh` (H1).
- `handover_parent`: the parent's: `Abi.ret` of its state (with the handed
  range erased from its private memory), its promises and views.
-/
import Spike.Lib.TwoSlot
import Scc.Sem.CertSys

namespace Spike.Lib.Handover

open Kraken.Promising Scc.Sem Scc.Sem.Kernel Spike.Lib.TwoSlot

variable {I : ISA} {K : Abi I}

theorem push_setIf_size {α : Type} {xs : Array α} {v a : α} :
    (xs.push v).setIfInBounds xs.size a = xs.push a := by
  apply Array.ext_getElem?
  intro k
  simp only [Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push]
  by_cases hk : xs.size = k
  · subst hk; simp
  · simp [hk, Ne.symm hk]

theorem push_set_size {α : Type} {xs : Array α} {v a : α} : (xs.push v).set! xs.size a = xs.push a := by
  rw [Array.set!_eq_setIfInBounds, push_setIf_size]

theorem upC_withThread_size {c : Config I} {u t : Thread I} {m : Memory} {i : Nat} (hi : i = c.threads.size) :
    (upC c u).withThread i t m = { threads := c.threads.push t, mem := m } := by
  subst hi; simp only [upC, Config.withThread, push_set_size]

theorem upX_set_size {x : KState} {s : Slot} {i : Nat} (hi : i = x.slots.size) :
    (upX x).set i s = { x with slots := x.slots.push s } := by
  subst hi; simp only [upX, KState.set, push_set_size]

/-- The range handover of a `clone`: the range thread `tid` holds that ends at
`stack`, if any. -/
def handed (x : KState) (tid stack : Nat) : Option (Nat × Range) :=
  x.held.find? fun h => h.1 == tid && h.2.lo + h.2.size == stack

variable (K) in
/-- The parent before its return: its private memory without the handed
range, if any. -/
def parentPre (x : KState) (tid : Nat) (t : Thread I) (stack : Nat) : Thread I :=
  match handed x tid stack with
  | none => t
  | some (_, rg) => { t with st := K.setDmem t.st (eraseRange (K.dmem t.st) rg) }

variable (K) in
/-- The child: `childThread`, with the handed range's bytes, if any. -/
def childAfter (x : KState) (tid : Nat) (t : Thread I) (stack tls : Nat) : Thread I :=
  let ch := childThread K t stack tls
  match handed x tid stack with
  | none => ch
  | some (_, rg) => { ch with st := K.setDmem ch.st (copyRange (K.dmem t.st) (K.dmem ch.st) rg) }

/-- The held ranges after the `clone`: the handed range, if any, moved to
the child (slot `x.slots.size`). -/
def heldAfter (x : KState) (tid stack : Nat) : List (Nat × Range) :=
  match handed x tid stack with
  | none => x.held
  | some (_, rg) => (x.slots.size, rg) :: x.held.erase (tid, rg)

variable (K) in
/-- **The configuration after a `clone` into the extra slot.** -/
def afterClone (d : Config I × KState) (tid : Nat) (t : Thread I) (stack tls : Nat) (r : BitVec 64) :
    Config I × KState :=
  ({ threads := (d.1.threads.set! tid (retThread K (parentPre K d.2 tid t stack) r)).push
        (childAfter K d.2 tid t stack tls), mem := d.1.mem },
    { d.2 with slots := d.2.slots.push (.run 0), held := heldAfter d.2 tid stack })

/-- **A `clone` into the extra slot** of `up d u`. -/
theorem spawn_extra {tid : Nat} {d : Config I × KState} {u : Thread I} {r : BitVec 64} {c' : Config I × KState}
    (hn : d.1.threads.size = d.2.slots.size) (ht : tid < d.1.threads.size)
    (h : spawnStep K tid (up d u) d.1.threads.size r = some c') :
    ∃ t stack tls, d.1.threads[tid]? = some t ∧ K.atSys t.st = true ∧ d.2.runs tid = true ∧
      d.2.exited = none ∧ callOf K t = some (.clone stack tls) ∧ 0 < r.toNat ∧ r.toNat < pidMax ∧
      c' = afterClone K d tid t stack tls r := by
  obtain ⟨c, x⟩ := d
  have hs : tid < x.slots.size := hn ▸ ht
  unfold spawnStep at h
  simp only [up, upC_get ht] at h
  split at h
  · cases h
  rename_i t ht'
  simp only [ready, upX_runs hs, upX_exited] at h
  split at h
  · cases h
  rename_i hr
  simp only [Bool.not_eq_true', Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.eq_false_iff, ne_eq] at hr
  replace hr := Classical.not_not.mp hr
  obtain ⟨⟨ha, hru⟩, hex⟩ := hr
  split at h
  · rename_i stack tls hcall
    have hd : (upX x).slots[c.threads.size]? = some .dormant := by
      rw [hn]; simp [upX]
    have hlt : c.threads.size < (upC c u).threads.size := by simp
    by_cases hc : 0 < r.toNat ∧ r.toNat < pidMax
    · simp only [hd, hlt, hc, and_self, ite_true, upX_held, upC_mem] at h
      refine ⟨t, stack, tls, ht', ha, hru, hex, hcall, hc.1, hc.2, ?_⟩
      have hwt : tid < (c.withThread tid (retThread K t r) c.mem).threads.size := by
        rw [withThread_size]; exact ht
      unfold afterClone parentPre childAfter heldAfter
      simp only [handed]
      split at h
      · rename_i hf
        rw [hf]
        cases h
        rw [upC_withThread ht, upC_withThread_size withThread_size.symm, upX_set_size hn]
        rfl
      · rename_i o rg hf
        rw [hf]
        cases h
        rw [upC_withThread ht, upC_withThread_size withThread_size.symm, upX_set_size hn]
        simp only [hn]
        rfl
    · simp [hc] at h
  · cases h

/-! ## The threads after the handover -/

section Facts

variable {d : Config I × KState} {tid : Nat} {t : Thread I} {stack tls : Nat} {r : BitVec 64}

theorem afterClone_mem : (afterClone K d tid t stack tls r).1.mem = d.1.mem := rfl

theorem afterClone_size : (afterClone K d tid t stack tls r).1.threads.size = d.1.threads.size + 1 := by
  simp [afterClone]

theorem afterClone_slots : (afterClone K d tid t stack tls r).2.slots = d.2.slots.push (.run 0) := rfl

theorem afterClone_exited : (afterClone K d tid t stack tls r).2.exited = d.2.exited := rfl

theorem afterClone_parent (ht : tid < d.1.threads.size) :
    (afterClone K d tid t stack tls r).1.threads[tid]? = some (retThread K (parentPre K d.2 tid t stack) r) := by
  simp only [afterClone, Array.getElem?_push, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
    Array.getElem?_setIfInBounds, Nat.ne_of_lt ht, ite_false, ht, ite_true]

theorem afterClone_child :
    (afterClone K d tid t stack tls r).1.threads[d.1.threads.size]? = some (childAfter K d.2 tid t stack tls) := by
  have := Array.getElem?_push_size (xs := d.1.threads.set! tid (retThread K (parentPre K d.2 tid t stack) r))
    (x := childAfter K d.2 tid t stack tls)
  simpa [afterClone] using this

theorem afterClone_other {k : Nat} (hk : k ≠ tid) (hlt : k < d.1.threads.size) :
    (afterClone K d tid t stack tls r).1.threads[k]? = d.1.threads[k]? := by
  simp only [afterClone, Array.getElem?_push, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
    Array.getElem?_setIfInBounds, Nat.ne_of_lt hlt, ite_false, Ne.symm hk]

theorem parentPre_prom : (parentPre K d.2 tid t stack).prom = t.prom := by
  unfold parentPre; split <;> rfl

theorem parentPre_views : (parentPre K d.2 tid t stack).views = t.views := by
  unfold parentPre; split <;> rfl

theorem parentPre_st : (parentPre K d.2 tid t stack).st = t.st ∨
    ∃ rg, handed d.2 tid stack = some (tid, rg) ∧
      (parentPre K d.2 tid t stack).st = K.setDmem t.st (eraseRange (K.dmem t.st) rg) := by
  unfold parentPre
  split
  · exact .inl rfl
  · rename_i o rg hf
    have : o = tid := by
      have := List.find?_some hf
      simp at this
      exact this.1
    subst this
    exact .inr ⟨rg, hf, rfl⟩

/-- The returned parent keeps its promises and views (only register views
of the result registers are reset). -/
theorem retThread_views (t : Thread I) (r : BitVec 64) : (retThread K t r).views = t.views := by
  unfold retThread
  generalize K.retRegs = regs
  suffices ∀ (u : Thread I), (regs.foldl (fun t reg => t.setRegView reg 0 0) u).views = u.views from this _
  induction regs with
  | nil => intro u; rfl
  | cons a l ih => intro u; exact (ih _).trans rfl

theorem childAfter_prom : (childAfter K d.2 tid t stack tls).prom = [] := by
  unfold childAfter; split <;> rfl

/-- **H1**: the child has the parent's views, without the forwarding and
exclusive records: the same `coh`. -/
theorem childAfter_views :
    (childAfter K d.2 tid t stack tls).views = { t.views with fwdb := [], xclb := none } := by
  unfold childAfter; split <;> rfl

theorem childAfter_st : (childAfter K d.2 tid t stack tls).st = K.child t.st stack tls ∨
    ∃ rg, handed d.2 tid stack = some (tid, rg) ∧
      (childAfter K d.2 tid t stack tls).st =
        K.setDmem (K.child t.st stack tls) (copyRange (K.dmem t.st) (K.dmem (K.child t.st stack tls)) rg) := by
  unfold childAfter
  split
  · exact .inl rfl
  · rename_i o rg hf
    have : o = tid := by
      have := List.find?_some hf
      simp at this
      exact this.1
    subst this
    exact .inr ⟨rg, hf, rfl⟩

/-- The handed range ends at the child's stack pointer. -/
theorem handed_end {x : KState} {o : Nat} {rg : Range} (h : handed x tid stack = some (o, rg)) :
    o = tid ∧ rg.lo + rg.size = stack ∧ (tid, rg) ∈ x.held := by
  have h1 := List.find?_some h
  simp at h1
  exact ⟨h1.1, h1.2, h1.1 ▸ List.mem_of_find?_eq_some h⟩

/-- A nonempty range is a stack for a stack pointer at its top. -/
theorem onStack_top {rg : Range} (h : 0 < rg.size) : onStack rg (rg.lo + rg.size) = true := by
  simp [onStack]; omega

/-- **The child's current stack range is the handed range**, when the
child's stack pointer is on it (`onStack`; at `sp = stack` that is
`0 < rg.size`, `onStack_top`). -/
theorem afterClone_stackRange {rg : Range} (hn : d.1.threads.size = d.2.slots.size) (hf : handed d.2 tid stack = some (tid, rg))
    (hsp : onStack rg (K.sp (childAfter K d.2 tid t stack tls).st) = true) :
    stackRangeOf K (afterClone K d tid t stack tls r) d.1.threads.size = some rg := by
  unfold stackRangeOf
  rw [afterClone_child]
  simp only
  have hh : (afterClone K d tid t stack tls r).2.held = (d.2.slots.size, rg) :: d.2.held.erase (tid, rg) := by
    show heldAfter d.2 tid stack = _
    unfold heldAfter; rw [hf]
  rw [hh, hn]
  simp [hsp]

/-- Both threads after the handover have no promise, if the parent had none. -/
theorem afterClone_prom (ht : tid < d.1.threads.size) (hp : t.prom = []) :
    ∀ k t', (afterClone K d tid t stack tls r).1.threads[k]? = some t' →
      (k = tid ∨ k = d.1.threads.size) → t'.prom = [] := by
  rintro k t' h (rfl | rfl)
  · rw [afterClone_parent ht] at h; cases h; rw [retThread_prom, parentPre_prom, hp]
  · rw [afterClone_child] at h; cases h; exact childAfter_prom

end Facts

/-- **No outstanding promise is certified at a `clone`**: the certifying run
would start with a step at the call, and `certSem` has none there
(`soloExec`: a `clone` ends a certifying run). The `clone`
analogue of `Kernel.prom_nil_of_write`. -/
theorem prom_nil_of_clone {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {stack tls : Nat} (hs : siteAt K μ t.st = none) (ha : K.atSys t.st = true)
    (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = some (.clone stack tls))
    (hcert : CertOkC A (certSem K A μ x tid) tid t mem) : t.prom = [] := by
  obtain ⟨tf, mf, hrun, hpf⟩ := hcert
  cases hrun with
  | refl => exact hpf
  | step hst _ =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hst
    obtain ⟨tree, st, c', hex, hr, -, -⟩ := stepOneWith_runOut A hso ho
    have hex' : (certSem K A μ x tid).exec t.st = some (leaves []) := by
      change soloExec K A μ x tid t.st = _
      simp only [soloExec, hs, ha, ite_true, hd]
    rw [hex'] at hex
    cases hex
    obtain ⟨i, -⟩ := (Lower.run_choose_iff A tid _).mp hr
    exact i.elim0

/-! ## The machine's `clone` into the extra slot -/

section Machine

variable {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat}

local notation "M" => ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf

/-- **A step of the lifted configuration** is a step of `d`, lifted, or **a
`clone` into the extra slot**, to `afterClone`: thread `tid` of `d` runs, is
at a `clone` call, and is certified (as the returned parent) after it. -/
theorem step_up_cases {μ : Marks} {tid : Nat} {d : Config I × KState} {u : Thread I} {es : List Ev}
    {c' : (M).Cfg} (hn : d.1.threads.size = d.2.slots.size) (h : (M).Step μ tid (up d u) es c') :
    tid < d.1.threads.size ∧
      ((∃ d', (M).Step μ tid d es d' ∧ c' = up d' u) ∨
        (es = [] ∧ ∃ t stack tls r, d.1.threads[tid]? = some t ∧ K.atSys t.st = true ∧
          d.2.runs tid = true ∧ d.2.exited = none ∧ callOf K t = some (.clone stack tls) ∧
          0 < r.toNat ∧ r.toNat < pidMax ∧ c' = afterClone K d tid t stack tls r ∧ CertAfter K A μ tid c')) := by
  obtain ⟨ht, h | ⟨hes, r, hsp, hc⟩⟩ := step_up hn h
  · exact ⟨ht, .inl h⟩
  · obtain ⟨t, stack, tls, h1, h2, h3, h4, h5, h6, h7, rfl⟩ := spawn_extra hn ht hsp
    exact ⟨ht, .inr ⟨hes, t, stack, tls, r, h1, h2, h3, h4, h5, h6, h7, rfl, hc⟩⟩

/-- **Conversely, a `clone` of a thread of `d` into the extra slot is a step
of the lifted configuration**, given the parent certified after it. -/
theorem clone_step {μ : Marks} {tid : Nat} {d : Config I × KState} {u : Thread I} {t : Thread I}
    {stack tls : Nat} {r : BitVec 64} (hn : d.1.threads.size = d.2.slots.size)
    (ht : d.1.threads[tid]? = some t) (ha : K.atSys t.st = true) (hr : d.2.runs tid = true)
    (hx : d.2.exited = none) (hcall : callOf K t = some (.clone stack tls)) (h0 : 0 < r.toNat)
    (hp : r.toNat < pidMax) (hc : CertAfter K A μ tid (afterClone K d tid t stack tls r)) :
    (M).Step μ tid (up d u) [] (afterClone K d tid t stack tls r) := by
  have hlt : tid < d.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  have hs : tid < d.2.slots.size := hn ▸ hlt
  refine .spawn ?_ ⟨d.1.threads.size, r, ?_, hc⟩
  · refine ⟨⟨t, ?_⟩, ?_, ?_⟩
    · show (upC d.1 u).threads[tid]? = _; rw [upC_get hlt]; exact ht
    · exact hx
    · show ¬ (upX d.2).runs tid = false; rw [upX_runs hs, hr]; simp
  · obtain ⟨c, x⟩ := d
    simp only at ht hr hx hn hs hlt
    show spawnStep K tid (upC c u, upX x) c.threads.size r = _
    unfold spawnStep
    have hd : (upX x).slots[c.threads.size]? = some .dormant := by
      rw [hn]; simp [upX]
    have hlt' : c.threads.size < (upC c u).threads.size := by simp
    simp only [upC_get hlt, ht, ready, ha, upX_runs hs, hr, upX_exited, hx, Option.isNone_none, Bool.and_self,
      Bool.not_true, Bool.false_eq_true, ite_false, hcall, hd, hlt', h0, hp, and_self, ite_true, upX_held, upC_mem]
    unfold afterClone parentPre childAfter heldAfter
    simp only [handed]
    split
    · rename_i hf
      rw [hf]
      rw [upC_withThread hlt, upC_withThread_size withThread_size.symm, upX_set_size hn]
      rfl
    · rename_i o rg hf
      rw [hf]
      rw [upC_withThread hlt, upC_withThread_size withThread_size.symm, upX_set_size hn]
      simp only [hn]
      rfl

end Machine

end Spike.Lib.Handover
