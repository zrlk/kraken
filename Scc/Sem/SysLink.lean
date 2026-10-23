/-
**The kernel step at a system call, for any ISA and `Abi`**: the facts a
proof about a system-call cell needs to take a kernel step, stated for an
arbitrary `K : Kernel.Abi I`. The per-ISA cell facts (`atSys`, `nr`, `arg`,
`ret` at a `CellAt`) are in `Scc/Sem/SysA64.lean` and `Scc/Sem/SysX64.lean`
(separate files: the two ISAs' Kraken syntax cannot be imported together).

- **Certification.** `certExec_of_decode`: at a supported call `certExec K`
  is the choice over `certSuccs K s call`; `certSuccs_ne_nil`: but for
  `exit` and `exit_group` that choice has a branch; `silentTree_choose`,
  `certExec_silent`: so `certExec K` there is a `SilentTree` whose leaves are
  the states `certSuccs` lists.
- **Every kernel step.** `sysStep_cases`: a `sysStep` of a thread is taken at
  a system call (`ready`), of a decoded call, and is one of: a `write` byte
  (the `out` event for fd 1, nothing for fd 2, the thread as `readByte`
  leaves it); a return (no event, `writeErr` at a refused `write`,
  `cloneErr` at a refused `clone`), the thread resuming in a state
  `certSuccs` lists with its promises and memory unchanged; `exit` (no
  event, the slot ends); `exit_group` (the `exit` or, at the abort status,
  `abort` event, the process ends). A successful `clone` is
  `Kernel.spawnStep_ret_mem`.
-/
import Scc.Sem.Kernel
import Kraken.Promising.Lower.Silent

namespace Scc.Sem.Kernel

open Kraken.Promising Kraken.Promising.Lower

variable {I : ISA} {K : Abi I}

/-! ## Certification -/

/-- **`certExec K` at a supported call** is the choice over the states
`certSuccs` lists. -/
theorem certExec_of_decode {s : I.State} {call : Call} (hs : K.atSys s = true)
    (hd : decode K.nrs (K.nr s) (K.arg s) = some call) :
    certExec K s = some (.choose (certSuccs K s call).length fun i => .done (certSuccs K s call)[i]) := by
  simp [certExec, hs, hd]

/-- **A call that returns has a successor**: but for `exit` and
`exit_group`, `certSuccs` is not empty. -/
theorem certSuccs_ne_nil (s : I.State) {call : Call} (hx : call ≠ .exit) (hg : ∀ v, call ≠ .exitGroup v) :
    certSuccs K s call ≠ [] := by
  cases call with
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | write _ _ n => simp [certSuccs, results]
  | futexWait => simp [certSuccs, results]
  | futexWake n => simp [certSuccs, results]
  | rtSigaction => simp [certSuccs, results]
  | archSetFs a => simp [certSuccs]
  | clone _ _ => simp [certSuccs, results]

/-- A choice over a non-empty list is a silent tree of its members. -/
theorem silentTree_choose {σ : Type} {l : List σ} (h : l ≠ []) :
    SilentTree (· ∈ l) (.choose l.length fun i => .done l[i]) :=
  ⟨List.length_pos_iff.mpr h, fun _ => List.getElem_mem _⟩

/-- **`certExec K` at a supported call that returns is silent**: a
`SilentTree` whose leaves are the states `certSuccs` lists. -/
theorem certExec_silent {s : I.State} {call : Call} (hs : K.atSys s = true)
    (hd : decode K.nrs (K.nr s) (K.arg s) = some call) (hx : call ≠ .exit) (hg : ∀ v, call ≠ .exitGroup v) :
    ∃ t, certExec K s = some t ∧ SilentTree (· ∈ certSuccs K s call) t :=
  ⟨_, certExec_of_decode hs hd, silentTree_choose (certSuccs_ne_nil s hx hg)⟩

/-! ## Every kernel step -/

/-- The kernel's byte read keeps the thread's state. -/
theorem readByte_st {A : Arch} {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    (h : readByte K A t mem a rd = some (b, t')) : t'.st = t.st := by
  unfold readByte at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/-- The events of a returning `sysStep`: none, `writeErr` at a refused
`write`, `cloneErr` at a refused `clone`. -/
def RetEvents (call : Call) (r : BitVec 64) (es : List Ev) : Prop :=
  es = [] ∨ (es = [.writeErr] ∧ (∃ fd buf n, call = .write fd buf n) ∧ writeRefused r = true) ∨
    (es = [.cloneErr] ∧ ∃ stack tls, call = .clone stack tls)

/-- **The cases of a `sysStep`** of thread `tid` (in state `t`), given that
a `write` has at most `n` bytes out (`hwr`, as for `sysStep_ret_mem`): the
thread is at a system call, its slot runs, the process has not exited, the
call decodes, and the step is a `write` byte, a return (to a state
`certSuccs` lists), an `exit` or an `exit_group`. -/
theorem sysStep_cases {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    {t : Thread I} (ht : c.1.threads[tid]? = some t) (h : sysStep K A tid c p = some (es, c'))
    (hwr : ∀ fd buf n, callOf K t = some (.write fd buf n) → c.2.wr tid ≤ n) :
    ready K tid c t = true ∧ ∃ call, callOf K t = some call ∧
      ((∃ fd buf n rd b t', call = .write fd buf n ∧ p = .byte rd ∧ c.2.wr tid < n ∧
          readByte K A t c.1.mem (buf + c.2.wr tid) rd = some (b, t') ∧ t'.st = t.st ∧
          es = (if fd = 1 then [.out b] else []) ∧
          c' = (c.1.withThread tid t' c.1.mem, c.2.set tid (.run (c.2.wr tid + 1)))) ∨
        (∃ r, p = .ret r ∧ call ≠ .exit ∧ (∀ v, call ≠ .exitGroup v) ∧ RetEvents call r es ∧
          c'.1.mem = c.1.mem ∧ ∃ t', c'.1.threads[tid]? = some t' ∧ t'.st ∈ certSuccs K t.st call ∧
            t'.prom = t.prom) ∨
        (call = .exit ∧ p = .ret 0 ∧ es = [] ∧ c' = (c.1, c.2.set tid .exited)) ∨
        (∃ v, call = .exitGroup v ∧
          ((p = .ret 0 ∧ es = [.exit (exitCode v)] ∧ c' = (c.1, { c.2 with exited := some (.exit (exitCode v)) })) ∨
            (∃ k, p = .abort k ∧ v % 256 = abortStatus ∧ es = [.abort k] ∧
              c' = (c.1, { c.2 with exited := some (.abort k) }))))) := by
  have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  have hback : ∀ (u : Thread I) (r' : BitVec 64) (x : KState) (es' : List Ev), u.prom = t.prom →
      back K tid c u r' x es' = some (es, c') →
        es = es' ∧ c'.1.mem = c.1.mem ∧ ∀ t', c'.1.threads[tid]? = some t' → t'.prom = t.prom := by
    intro u r' x es' hu hb
    simp only [back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine ⟨rfl, rfl, fun t' h' => ?_⟩
    simp only [withThread_get, hlt, and_self, ite_true, Option.some.injEq] at h'
    subst h'; simp [hu]
  have h0 := h
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  cases hr : ready K tid c t
  · simp [hr] at h
  simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false] at h
  refine ⟨rfl, ?_⟩
  rcases hcall : callOf K t with _ | call
  · rw [hcall] at h; cases p <;> simp at h
  rw [hcall] at h
  refine ⟨call, rfl, ?_⟩
  have hwr' : ∀ fd buf n, call = .write fd buf n → c.2.wr tid ≤ n := fun fd buf n e => hwr fd buf n (e ▸ hcall)
  have hretc : ∀ r (u : Thread I) x es', p = .ret r → call ≠ .exit → (∀ v, call ≠ .exitGroup v) →
      u.prom = t.prom → back K tid c u r x es' = some (es, c') → RetEvents call r es' →
      (∃ r, p = .ret r ∧ call ≠ .exit ∧ (∀ v, call ≠ .exitGroup v) ∧ RetEvents call r es ∧
          c'.1.mem = c.1.mem ∧ ∃ t', c'.1.threads[tid]? = some t' ∧ t'.st ∈ certSuccs K t.st call ∧
            t'.prom = t.prom) := by
    intro r u x es' hp hx hg hu hb hev
    subst hp
    obtain ⟨rfl, hm, hpr⟩ := hback u r x es' hu hb
    obtain ⟨t', h1, h2⟩ := sysStep_ret_mem ht hcall h0 hwr' hx hg
    exact ⟨r, rfl, hx, hg, hev, hm, t', h1, h2, hpr t' h1⟩
  cases call with
  | write fd buf n =>
    cases p with
    | byte rd =>
      simp only at h
      split at h
      · rename_i hj
        obtain ⟨⟨b, t'⟩, hb, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .inl ⟨fd, buf, n, rd, b, t', rfl, rfl, hj, hb, readByte_st hb, rfl, rfl⟩
      · cases h
    | ret r =>
      simp only at h
      refine .inr (.inl ?_)
      split at h
      · split at h
        · exact hretc r t _ _ rfl (by simp) (by simp) rfl h (.inl rfl)
        · cases h
      · split at h
        · exact hretc r t _ _ rfl (by simp) (by simp) rfl h (.inl rfl)
        · split at h
          · rename_i hw
            exact hretc r t _ _ rfl (by simp) (by simp) rfl h (.inr (.inl ⟨rfl, ⟨_, _, _, rfl⟩, hw⟩))
          · cases h
    | abort k => simp at h
  | exit =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · rename_i hr0
        subst hr0
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))
      · cases h
    | byte _ | abort _ => simp at h
  | exitGroup v =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · rename_i hr0
        subst hr0
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inr (.inr ⟨v, rfl, .inl ⟨rfl, rfl, rfl⟩⟩))
      · cases h
    | abort k =>
      simp only at h
      split at h
      · rename_i hv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inr (.inr ⟨v, rfl, .inr ⟨k, rfl, hv, rfl, rfl⟩⟩))
      · cases h
    | byte _ => simp at h
  | futexWait =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · exact .inr (.inl (hretc r t _ _ rfl (by simp) (by simp) rfl h (.inl rfl)))
      · cases h
    | byte _ | abort _ => simp at h
  | futexWake n =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · exact .inr (.inl (hretc r t _ _ rfl (by simp) (by simp) rfl h (.inl rfl)))
      · cases h
    | byte _ | abort _ => simp at h
  | rtSigaction =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · exact .inr (.inl (hretc r t _ _ rfl (by simp) (by simp) rfl h (.inl rfl)))
      · cases h
    | byte _ | abort _ => simp at h
  | clone stack tls =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · exact .inr (.inl (hretc r t _ _ rfl (by simp) (by simp) rfl h (.inr (.inr ⟨rfl, _, _, rfl⟩))))
      · cases h
    | byte _ | abort _ => simp at h
  | archSetFs a =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · exact .inr (.inl (hretc r { t with st := K.setTp t.st a } _ _ rfl (by simp) (by simp) rfl h (.inl rfl)))
      · cases h
    | byte _ | abort _ => simp at h

end Scc.Sem.Kernel
