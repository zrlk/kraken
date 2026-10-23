/-
**Kernel steps at a system call with outstanding promises** (`Scc/DESIGN.md`
§9.0): a thread certified under the solo projection of the kernel step
(`Kernel.certSem`) at a supported system call other than `write` and
`clone`, with promises outstanding, has a kernel step (`sys_progress`).

- `sysStep_of_solo`: the converse of `sysStep_solo`. A return of `r` from
  the solo configuration of the thread's state is also a return of `r` from
  the real configuration (no byte of a `write` out), to the same state, with
  memory and kernel state unchanged and no event, for calls other than
  `exit`, `exit_group` and `clone` (whose returns from the solo
  configuration end the slot or the process, or emit `cloneErr`).
- `sys_progress`: the certifying run cannot be empty (promises are
  outstanding), so it starts with a certification step at the call. At
  `exit` and `exit_group` there is none (`certSuccs` is empty). Elsewhere the
  step picks a return `r` of `sysStep` from the solo configuration
  (`soloExec`), the real configuration returns the same `r` to the same
  thread (`sysStep_of_solo`, `finishInstr_svcDeps`), and the rest of the
  certifying run certifies after the kernel step, whose kernel state and
  memory are the ones before it (`CertAfter`).

`write` is not covered: its `writeTree` branches load the buffer's bytes in
one certification step where the kernel transfers them in one step each, and
a `write` with bytes out returns from a configuration the solo one is not
(`soloExec` resets the count to 0). Consumers rule out promises at a `write`
instead (`WriteNoProm` in `Spike/Lib/A64Consumer.lean`).
-/
import Scc.Sem.CertStep

namespace Scc.Sem

open Kraken Kraken.Promising

namespace Kernel

variable {I : ISA} {K : Abi I}

/-- **The real configuration returns what the solo one returns** (the
converse of `sysStep_solo`): a return of `r` from the solo configuration of
a ready thread's state, at a call other than `exit`, `exit_group` and
`clone`, with no byte of a `write` out, is also a return of `r` from the
real configuration, to the same state, with no event, memory and kernel
state unchanged. -/
theorem sysStep_of_solo {A : Arch} {tid : Nat} {c : Config I × KState} {t : Thread I} {x : KState}
    {r : BitVec 64} {es' : List Ev} {c'' : Config I × KState} {call : Call}
    (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hc : callOf K t = some call)
    (hw : ∀ fd buf n, call = .write fd buf n → c.2.wr tid = 0)
    (hx : call ≠ .exit) (hg : ∀ v, call ≠ .exitGroup v) (hcl : ∀ st tl, call ≠ .clone st tl)
    (h : sysStep K A tid (solo K none x tid t.st) (.ret r) = some (es', c'')) :
    ∃ es c', sysStep K A tid c (.ret r) = some (es, c') ∧ stOf tid c' = stOf tid c'' ∧
      c'.1.mem = c.1.mem ∧ c'.2 = c.2 ∧ es = es' := by
  have hlt' : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  have hat : K.atSys t.st = true := by simp [ready] at hr; exact hr.1.1
  unfold sysStep at h ⊢
  rw [ht]
  simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false]
  split at h
  · cases h
  rename_i t0 ht0
  have hlt : tid < x.slots.size := by
    have := (Array.getElem?_eq_some_iff.mp ht0).1
    simpa [solo] using this
  have hts : t0 = Thread.init t.st := by simpa [solo, hlt] using ht0.symm
  subst hts
  have hrd : ready K tid (solo K none x tid t.st) (Thread.init t.st) = true := by
    simp [ready, solo, KState.runs, hlt, Thread.init, hat]
  have hwr : (solo K none x tid t.st).2.wr tid = 0 := solo_wr hlt
  have hco : callOf K (Thread.init t.st) = callOf K t := rfl
  simp only [hrd, Bool.not_true, Bool.false_eq_true, ite_false, hco, hc, hwr] at h ⊢
  have hls : tid < (solo K none x tid t.st).1.threads.size := by simp [solo, hlt]
  cases call with
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | clone st tl => exact absurd rfl (hcl st tl)
  | write fd buf n =>
    have hw0 := hw fd buf n rfl
    simp only [hw0, Nat.lt_irrefl, ite_false] at h ⊢
    (repeat' split at h) <;> (try cases h)
    all_goals simp only [*, back, Option.some.injEq, ite_true, ite_false, Prod.mk.injEq]
    all_goals exact ⟨_, _, ⟨rfl, rfl⟩, by simp [stOf, withThread_get, hls, hlt', Thread.init], rfl, rfl, rfl⟩
  | _ =>
    simp only at h ⊢
    (repeat' split at h) <;> (try cases h)
    all_goals simp only [*, back, Option.some.injEq, ite_true, Prod.mk.injEq]
    all_goals exact ⟨_, _, ⟨rfl, rfl⟩, by simp [stOf, withThread_get, hls, hlt', Thread.init], rfl, rfl, rfl⟩

/-- **The first certification step at a system call other than `write` and
`clone`** picks a return of `sysStep` from the solo configuration: some `r`
returned there to the state the step leaves. -/
theorem certSem_step_sys_ret {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I} {call : Call}
    (hs : siteAt K μ t.st = none) (ha : K.atSys t.st = true)
    (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = some call) (hnw : ∀ fd buf n, call ≠ .write fd buf n)
    (hcl : ∀ st tl, call ≠ .clone st tl)
    (hstep : (certSem K A μ x tid).step A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ r ∈ results call, ∃ es' c'', sysStep K A tid (solo K none x tid t.st) (.ret r) = some (es', c'') ∧
      stOf tid c'' = some o.thread.st ∧
      o.thread ∈ finishInstr t (svcDeps K) (instrViews t (svcDeps K)) o.thread.st
        (Live.TicketStep.ctx0 tid t mem) ∧ o.mem = mem := by
  obtain ⟨tree, st, c', hex, hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  have hdc : (certSem K A μ x tid).deps t.st = svcDeps K := by
    change certDeps K t.st = _
    simp [certDeps, ha]
  rw [hdc] at hth hr
  change soloExec K A μ x tid t.st = some tree at hex
  have hex' : soloExec K A μ x tid t.st = some (leaves ((results call).filterMap fun r =>
      (sysStep K A tid (solo K none x tid t.st) (.ret r)).bind fun (_, c') => stOf tid c')) := by
    cases call with
    | write fd buf n => exact absurd rfl (hnw fd buf n)
    | clone st tl => exact absurd rfl (hcl st tl)
    | _ => simp only [soloExec, hs, ha, ite_true, hd]
  rw [hex'] at hex
  cases hex
  obtain ⟨i, hi⟩ := (Lower.run_choose_iff A tid _).mp hr
  obtain ⟨rfl, rfl⟩ := (Lower.run_done_iff A tid _).mp hi
  have hmem := List.getElem_mem (l := (results call).filterMap fun r =>
    (sysStep K A tid (solo K none x tid t.st) (.ret r)).bind fun (_, c') => stOf tid c') i.isLt
  obtain ⟨r, hr, hb⟩ := List.mem_filterMap.mp hmem
  obtain ⟨⟨es', c''⟩, hss, hst⟩ := Option.bind_eq_some_iff.mp hb
  have hst' := finishInstr_st hth
  refine ⟨r, hr, es', c'', hss, ?_, ?_, hm⟩
  · rw [hst']; exact hst
  · rw [hst']; exact hth

/-- **No outstanding promise is certified at `exit` or `exit_group`**: the
certifying run would start with a step at the call, and there is none
(`results` is empty). -/
theorem prom_nil_of_exit {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {call : Call} (hs : siteAt K μ t.st = none) (ha : K.atSys t.st = true)
    (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = some call) (hx : call = .exit ∨ ∃ v, call = .exitGroup v)
    (hcert : CertOkC A (certSem K A μ x tid) tid t mem) : t.prom = [] := by
  obtain ⟨tf, mf, hrun, hpf⟩ := hcert
  cases hrun with
  | refl => exact hpf
  | step hst _ =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hst
    have hnw : ∀ fd buf n, call ≠ .write fd buf n := by
      rcases hx with rfl | ⟨v, rfl⟩ <;> intro _ _ _ h <;> cases h
    have hcl : ∀ st tl, call ≠ .clone st tl := by
      rcases hx with rfl | ⟨v, rfl⟩ <;> intro _ _ h <;> cases h
    obtain ⟨r, hrm, -⟩ := certSem_step_sys_ret hs ha hd hnw hcl hso ho
    rcases hx with rfl | ⟨v, rfl⟩ <;> simp [results] at hrm

/-- **A return at a call other than `write`, `clone`, `exit` and
`exit_group` emits no event.** -/
theorem sysStep_ret_nil {A : Arch} {tid : Nat} {c c' : Config I × KState} {t : Thread I} {call : Call}
    {r : BitVec 64} {es : List Ev} (ht : c.1.threads[tid]? = some t) (hc : callOf K t = some call)
    (hnw : ∀ fd buf n, call ≠ .write fd buf n) (hcl : ∀ st tl, call ≠ .clone st tl) (hx : call ≠ .exit)
    (hg : ∀ v, call ≠ .exitGroup v) (h : sysStep K A tid c (.ret r) = some (es, c')) : es = [] := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  cases call with
  | write fd buf n => exact absurd rfl (hnw fd buf n)
  | clone st tl => exact absurd rfl (hcl st tl)
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | _ =>
    simp only at h
    (repeat' split at h) <;> simp only [back, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
      exact h.1.symm

/-- **A system call with outstanding promises has a kernel step** (other
than `write` and `clone`): thread `tid`, ready at a supported call off the
transfer sites with promises outstanding and certified under `certSem`,
has a return `r` of `sysStep` after which it is certified (`CertAfter`).
The certifying run starts with a step at the call; at `exit` and
`exit_group` there is none (`results` is empty), elsewhere it picks a return
of the solo configuration (`certSem_step_sys_ret`), which the real
configuration also takes to the same thread (`sysStep_of_solo`,
`sysStep_ret_shape`), memory and kernel state unchanged, so the run's tail
certifies after it. -/
theorem sys_progress {A : Arch} {μ : Marks} {tid : Nat} {c : Config I × KState} {t : Thread I} {call : Call}
    (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hs : siteAt K μ t.st = none)
    (hc : callOf K t = some call) (hnw : ∀ fd buf n, call ≠ .write fd buf n)
    (hcl : ∀ st tl, call ≠ .clone st tl) (hp : t.prom ≠ [])
    (hcert : CertOkC A (certSem K A μ c.2 tid) tid t c.1.mem) :
    ∃ r es c', sysStep K A tid c (.ret r) = some (es, c') ∧ CertAfter K A μ tid c' := by
  have hat : K.atSys t.st = true := by simp [ready] at hr; exact hr.1.1
  obtain ⟨tf, mf, hrun, hpf⟩ := hcert
  cases hrun with
  | refl => exact absurd hpf hp
  | step hst hrest =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hst
    obtain ⟨r, hrm, es', c'', hss, hsto, hth, hom⟩ := certSem_step_sys_ret hs hat hc hnw hcl hso ho
    have hx : call ≠ .exit := by rintro rfl; simp [results] at hrm
    have hg : ∀ v, call ≠ .exitGroup v := by rintro v rfl; simp [results] at hrm
    obtain ⟨es, c', hsr, hst', hcm, hck, -⟩ :=
      sysStep_of_solo ht hr hc (fun fd buf n h => absurd h (hnw fd buf n)) hx hg hcl hss
    obtain ⟨-, s0, ht', -⟩ := sysStep_ret_shape ht hc hsr (fun fd buf n h => absurd h (hnw fd buf n)) hx hg
    have hos : o.thread.st = K.ret s0 r := by
      have : stOf tid c' = some (K.ret s0 r) := by simp [stOf, ht']
      rw [hst', hsto] at this
      exact Option.some.inj this
    rw [hos, finishInstr_svcDeps] at hth
    have hoe : o.thread = retThread K { t with st := s0 } r := List.mem_singleton.mp hth
    refine ⟨r, es, c', hsr, fun t' ht2 => ?_⟩
    rw [ht', hoe.symm] at ht2
    cases ht2
    rw [hck, hcm]
    refine ⟨tf, mf, ?_, hpf⟩
    rw [hom] at hrest
    exact hrest

end Kernel

end Scc.Sem
