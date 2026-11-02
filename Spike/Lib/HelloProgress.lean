/-
**hello.w on AArch64: after the spawn the machine has progress** (row
`HelloAssembly.HelloRowsW.post_progress`, the twin of
`WakeProgress.post_progress_of` and `WakeMapped.hmapped_of` at hello's
worker data `PT1h`, frame-aware rows `OutTS` and kernel relation `KRH`).

wake's worker makes no `write` and no `exit_group`; hello's makes `print`'s
`write(1, …)` and, in the abort-write phase, `write(2, …)` and
`exit_group abortStatus` (`WCompatH.sysOkH`). A `write` always has a step
(`-EINTR` before any byte, `Kernel.sys_writeIntr`; the count after some,
`Kernel.sys_writeRet`) and no certified promise
(`Kernel.prom_nil_of_write`); `exit_group` at the abort status has a step at
an abort site (`Kernel.sys_exitGroupAbort`) and off one
(`Kernel.sys_exitGroup`). So the progress skeleton is wake's with the
supported calls widened (`CallOKH`).

- `CallOKH`, `TOkH`, `tOk_stepH`, `progress_ofH`: `WakeProgress.CallOK`,
  `TOk`, `tOk_step`, `progress_of` with `write` and `exit_group` at the
  abort status admitted.
- `outTS_ok`: an `OutTS` row off a system call is `WakeProgress.RowOK`.
- `outL_call`, `worker_callH`: the worker's call at a system call is
  decoded, not `clone`, and `CallOKH` (`WCompatH.sysOkH`).
- `hmapped_ofH`: `WakeMapped.hmapped_of` at `PT1h` and `KRH`.
- `post_progress_ofH`, `post_progressH`: `post_progress` from `Post`, and
  `HelloRowsW.post_progress`'s statement, from the named facts:
  * `hK`: the worker's memory side has the kernel ABI at every frame
    stack (`rfl`-like at `HelloWorkerRR.helloDR`'s `hK`);
  * `hoffM` (main off every abort site; `WakeM0.MSide.off` at the target's
    marks), `hhalt0`, `hmapM` (main's side, as wake's);
  * `hhalt1`, `hmapW` (the worker's side at
    frames).
-/
import Spike.Lib.WakeProgress
import Spike.Lib.WakeMapped
import Spike.Lib.HelloAssembly

namespace Spike.Lib.HelloProgress

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.ExtThread Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeW1 Spike.Lib.Inv2Core
open Spike.Lib.WakeProgress (RowOK outL_ok outT_ok fence_ok fence_no_error runs_true CallOK main_call)
open Kraken.Promising.Live.TicketStep (ctx0)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloW1 (WSideH PT1h WCompatH)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.A64HelloWriteK (KRH)
open Spike.Lib.A64Consumer (K0)

/-! ## Progress of the two-slot machine with hello's calls -/

/-- **The supported calls of hello's progress argument**: no `clone`, an
`exit_group` off every abort site or at the abort status. The worker's
calls take only the second branch (`WCompatH.sysOkH` gives its
`exit_group` at `abortStatus` alone); main's take the first (`main_call`). -/
def CallOKH (μ : Marks) (s : isaLSE2.State) (call : Call) : Prop :=
  (∀ st tl, call ≠ .clone st tl) ∧
    ∀ v, call = .exitGroup v → (∀ k a, μ.abortAt k = some a → pcOf s ≠ a) ∨ v % 256 = abortStatus

/-- wake's supported calls are hello's. -/
theorem callOKH_of_callOK {μ : Marks} {s : isaLSE2.State} {call : Call} (h : CallOK μ s call) :
    CallOKH μ s call :=
  ⟨h.2.1, fun v e => .inl (h.2.2 v e)⟩

/-- **The facts about a running thread `th` (slot `tid`) progress needs**
(`WakeProgress.TOk` with `CallOKH`). -/
structure TOkH (μ : Marks) (t : Cfg) (tid : Nat) (th : Thread isaLSE2) : Prop where
  exec : (isaLSE2.exec th.st).isSome
  site : siteAt abi μ th.st = none
  cert : th.prom ≠ [] → CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 tid) tid th t.1.mem
  row : abi.atSys th.st = false → RowOK Arch.armv8 th tid t.1.mem
  mapped : abi.atSys th.st = false → ∀ e, isaLSE2.exec th.st = some e →
    ¬ Touches (fun l w => Kernel.mapped t.2 w l = false) e
  sys : abi.atSys th.st = true → ∃ call, callOf abi th = some call ∧ CallOKH μ th.st call

/-- **The step of a running thread** from its `TOkH` facts
(`WakeProgress.tOk_step`); at a `write` the kernel's `-EINTR` or count
return (none with promises, `Kernel.prom_nil_of_write`), at `exit_group`
at an abort site its abort. -/
theorem tOk_stepH {μ : Marks} {t : Cfg} {tid : Nat} {th : Thread isaLSE2}
    (ht : t.1.threads[tid]? = some th) (hrk : t.2.runs tid = true) (hxk : t.2.exited = none)
    (h : TOkH μ t tid th) : ∃ es c', (machine (kernel 2)).Step μ tid t es c' := by
  have hruns : (machine (kernel 2)).runs t tid :=
    ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs tid = false); rw [hrk]; simp⟩
  have hsn := h.site
  have hsite : ∀ k, ¬ (machine (kernel 2)).AtSite μ k t tid := by
    rintro k ⟨a, ha, t2, ht2, hpc⟩
    cases (show some t2 = some th from ht2.symm.trans ht)
    have hn := siteAt_eq_none_iff.mp hsn
    cases k
    · subst hpc; exact hn.1 ha
    · subst hpc; exact hn.2 ha
  cases hs : abi.atSys th.st
  · have hnsys : ¬ (machine (kernel 2)).atSys t tid := fun ⟨t2, ht2, h2⟩ => by
      cases (show some t2 = some th from ht2.symm.trans ht)
      have h3 : abi.atSys th.st = true := h2
      rw [hs] at h3; cases h3
    by_cases hpn : th.prom = []
    · obtain ⟨outs, o, hso, ho, hpo⟩ := (h.row hs).2.1 hpn
      exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
    · obtain ⟨t', mem', hr, hp'⟩ := h.cert hpn
      cases hr with
      | refl => exact absurd hp' hpn
      | step hs1 hrest =>
        obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
        replace hso : stepOne Arch.armv8 th tid t.1.mem = some outs :=
          (Kernel.certSem_step_of_not_site (x := t.2) hsn hs).symm.trans hso
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
  · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
    obtain ⟨call, hc, hcl, hab⟩ := h.sys hs
    have hsys : ∀ c', (kernel 2).sys μ tid t [] c' → ∃ es c', (machine (kernel 2)).Step μ tid t es c' :=
      fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
    by_cases hpn : th.prom = []
    rotate_left
    · cases call with
      | write fd buf n => exact absurd (Kernel.prom_nil_of_write hsn hs hc (h.cert hpn)) hpn
      | exitGroup v => exact absurd (Kernel.prom_nil_of_exit hsn hs hc (.inr ⟨v, rfl⟩) (h.cert hpn)) hpn
      | exit => exact absurd (Kernel.prom_nil_of_exit hsn hs hc (.inl rfl) (h.cert hpn)) hpn
      | clone st tl => exact absurd rfl (hcl st tl)
      | _ =>
        obtain ⟨r, es, c', h', hca⟩ := Kernel.sys_progress ht hr hsn hc (fun _ _ _ h => by cases h)
          (fun _ _ h => by cases h) hpn (h.cert hpn)
        obtain rfl := Kernel.sysStep_ret_nil ht hc (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun h => by cases h) (fun _ h => by cases h) h'
        exact hsys c' ⟨.ret r, h', hca⟩
    cases call with
    | write fd buf n =>
      cases hj : t.2.wr tid with
      | zero => exact hsys _ (Kernel.sys_writeIntr (K := abi) Arch.armv8 2 ht hr hpn hc hj)
      | succ j => exact hsys _ (Kernel.sys_writeRet (K := abi) Arch.armv8 2 ht hr hpn hc (by omega))
    | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.armv8 2 ht hr hpn hc)
    | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.armv8 2 ht hr hpn hc)
    | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.armv8 2 ht hr hpn hc)
    | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.armv8 2 ht hr hpn hc)
    | exitGroup v =>
      by_cases hat : ∃ k a, μ.abortAt k = some a ∧ pcOf th.st = a
      · obtain ⟨k, a, ha, hpc⟩ := hat
        have hv : v % 256 = abortStatus := (hab v rfl).resolve_left fun hoff => hoff k a ha hpc
        exact ⟨_, _, .sys hruns (Kernel.sys_exitGroupAbort (K := abi) Arch.armv8 2 k ht hr hpn hc hv) (by simp)
          (fun k' hk => by
            simp only [List.mem_singleton, Ev.abort.injEq] at hk
            subst hk; exact ⟨a, ha, th, ht, hpc⟩)
          (fun e he => by simp at he)⟩
      · have hnoab : ∀ k a, μ.abortAt k = some a → ¬ (machine (kernel 2)).AtAddr a t tid :=
          fun k a ha ⟨t2, ht2, hpc⟩ => by
            cases (show some t2 = some th from ht2.symm.trans ht); exact hat ⟨k, a, ha, hpc⟩
        exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.armv8 2 ht hr hpn hc) (by simp)
          (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
    | exit =>
      refine hsys _ ⟨.ret 0, by simp [sysStep, ht, hr, hc] <;> rfl, certAfter_of_prom abi fun t' h' => ?_⟩
      cases (show some th = some t' from ht.symm.trans h')
      exact hpn
    | clone st tl => exact absurd rfl (hcl st tl)

/-- **Progress of the two-slot machine from per-thread facts**
(`WakeProgress.progress_of` at `TOkH`). -/
theorem progress_ofH {μ : Marks} {t : Cfg} (hx : t.2.exited = none)
    (h0 : ∃ th, t.1.threads[0]? = some th ∧ t.2.runs 0 = true)
    (hok : ∀ tid th, t.1.threads[tid]? = some th → t.2.runs tid = true → TOkH μ t tid th) :
    (machine (kernel 2)).Progress μ t := by
  have nh : ∀ tid th, t.1.threads[tid]? = some th → t.2.runs tid = true → th.halted = false := by
    intro tid th ht hr
    have he := (hok tid th ht hr).exec
    simp only [Thread.halted]
    cases hh : isaLSE2.exec th.st
    · rw [hh] at he; cases he
    · rfl
  refine ⟨?_, .inr ⟨?_, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, hd⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, hr, -, hns, hex, htouch⟩))
    · have hr := runs_true hd
      have hsy : abi.atSys t1.st = false := by
        cases h : abi.atSys t1.st
        · rfl
        · exact absurd ⟨t1, ht1, h⟩ hns
      have hs' : stepOne Arch.armv8 t1 tid t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      exact ((hok tid t1 ht1 hr).row hsy).2.2 outs hs' m hm
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        have hr : t.2.runs tid = true := by
          cases h : t.2.runs tid
          · simp [h] at hf
          · rfl
        have hT := hok tid t1 ht1 hr
        rw [nh tid t1 ht1 hr, Bool.or_false] at hf
        cases hsy : abi.atSys t1.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, hcl, -⟩ := hT.sys hsy
          rw [hd] at hf
          cases call with
          | clone st tl => exact hcl st tl rfl
          | _ => simp at hf
      · cases hf
    · exact (hok tid t1 ht1 hr).mapped hns e hex htouch
  · obtain ⟨th, ht, hr⟩ := h0
    exact ⟨0, hx, by show ¬ (t.2.runs 0 = false); rw [hr]; simp, th, ht,
      fun h => by rw [nh 0 th ht hr] at h; cases h.1⟩
  · obtain ⟨hx', hd, th, ht, -⟩ := hl
    have hr := runs_true hd
    exact tOk_stepH ht hr hx (hok tid th ht hr)

/-! ## The worker's rows -/

section Rows

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}

/-- **An `OutTS` row off a system call is `RowOK`**: a row at the frames
reached (`outL_ok`, `outT_ok`), a silent frame step, or a fence. -/
theorem outTS_ok {ms : List TermRun.Frame → MemSide isaLSE2} {X : FragS isaLSE2} {t : Thread isaLSE2}
    {tid : Nat} {mem : Memory} {c : Ctl} {fs : List TermRun.Frame} (hb : t.Bnd mem.last)
    (hK : ∀ fs, (ms fs).K = some abi) (hns : abi.atSys t.st = false) (h : OutTS p lbl ms X t.st c fs) :
    RowOK Arch.armv8 t tid mem := by
  cases h with
  | pre c₁ fs₁ _ h => exact outL_ok Arch.armv8 hb (hK fs₁) hns h
  | frame s' c' fs' he _ _ =>
    refine ⟨by rw [he]; rfl, fun hp => ?_, fun _ hs m => stepOne_silent_no_error Arch.armv8 tid he (silentTree_done s') hs m⟩
    obtain ⟨s0, -, hall⟩ := stepOne_silent_exists Arch.armv8 tid (mem := mem) he (silentTree_done s')
    obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (isaLSE2.deps t.st) (instrViews t (isaLSE2.deps t.st)) s0
      (ctx0 tid t mem)
    obtain ⟨outs, o, hs, ho, rfl, -⟩ := hall th hth
    exact ⟨outs, o, hs, ho, (finishInstr_relKey hth).1.trans hp⟩
  | fnc k s' c' fs' he _ _ =>
    exact ⟨by rw [he]; rfl, fun hp => fence_ok Arch.armv8 hp he, fun _ hs m => fence_no_error Arch.armv8 he hs m⟩
  | top c₁ _ h => exact outT_ok Arch.armv8 hb (hK []) hns h

/-- **An `OutL` row whose instruction, if any, faults (at a system call,
`WCompatH.sysExec`) is a decoded call other than `clone`**: `Out.sys` (`SysOk`) or `Out.emit` (a
`write`). -/
theorem outL_call {ms : MemSide isaLSE2} {X : Frag isaLSE2} {s : isaLSE2.State} {c : Ctl}
    (hK : ms.K = some abi) (hsx : ∀ t, isaLSE2.exec s = some t → ∃ m, t = .fault m)
    (h : OutL p lbl ms X s c) :
    ∃ call, decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ ∀ st tl, call ≠ .clone st tl := by
  cases h with
  | out r =>
    cases r with
    | sys K call hK' ha hd hok => rw [hK] at hK'; cases hK'; exact ⟨call, hd, hok.2.1⟩
    | emit K buf n Pw Qw hK' ha hd => rw [hK] at hK'; cases hK'; exact ⟨_, hd, fun _ _ h => by cases h⟩
    | choice P tree he hsil hX =>
      obtain ⟨m, rfl⟩ := hsx _ he
      cases hsil
    | _ =>
      obtain ⟨m, hm⟩ := hsx _ ‹isaLSE2.exec s = some _›
      cases hm
  | ldSt _ _ _ _ _ _ _ _ _ he =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm

end Rows

variable {Q : WakeRel} {D : WSideH Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch} {AbW : isaLSE2.State → Prop}

/-- **The worker's call at a system call** is supported (`CallOKH`): its
row at the frames reached is `Out.sys` (not `clone`), `Out.emit` (a
`write`) or `OutT.texit` (`exit`); an `exit_group` is at the abort status
(`WCompatH.sysOkH`). -/
theorem worker_callH (hC : WCompatH Q D μ Λ arch AbW) (hK : ∀ w fs, (D.ms w fs).K = some abi) {w : Q.ι}
    {st : isaLSE2.State} {c : Ctl} {fs : List TermRun.Frame} (hwi : D.Wi w st c fs) (hat : abi.atSys st = true) :
    ∃ call, decode abi.nrs (abi.nr st) (abi.arg st) = some call ∧ CallOKH μ st call := by
  have hsx : ∀ t, isaLSE2.exec st = some t → ∃ m, t = .fault m := fun t => hC.sysExec w _ _ _ t hwi hat
  have hok : ∀ call, decode abi.nrs (abi.nr st) (abi.arg st) = some call → (∀ st tl, call ≠ .clone st tl) →
      ∃ call, decode abi.nrs (abi.nr st) (abi.arg st) = some call ∧ CallOKH μ st call := by
    intro call hd hcl
    refine ⟨call, hd, hcl, fun v e => ?_⟩
    rcases hC.sysOkH w _ _ _ _ hwi hat hd with h | ⟨_, _, h⟩ | ⟨-, ⟨_, _, h⟩ | h⟩ | ⟨-, h⟩
    · rw [h] at e; cases e
    · rw [h] at e; cases e
    · rw [h] at e; cases e
    · rw [h] at e; cases e; exact .inr rfl
    · exact absurd e (h v)
  cases D.closed w _ _ _ hwi with
  | pre c₁ fs₁ _ h =>
    obtain ⟨call, hd, hcl⟩ := outL_call (hK w fs₁) hsx h
    exact hok call hd hcl
  | frame s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | fnc k s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | top c₁ _ h =>
    cases h with
    | outL h =>
      obtain ⟨call, hd, hcl⟩ := outL_call (hK w []) hsx h
      exact hok call hd hcl
    | unpk _ _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm
    | texit K a hK' ha hd =>
      rw [hK w []] at hK'; cases hK'
      exact hok .exit hd fun _ _ h => by cases h
    | fnc _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm

/-! ## No unmapped access -/

/-- **`hmapped`** (`WakeMapped.hmapped_of` at `PT1hE` and `KRH`): main's
invariant (`hM`) and the worker's at any frames (`hW`) touch only locations
`K0` maps off a system call. -/
theorem hmapped_ofH (hpt1 : Q.PT1 = HelloEmitPh.PT1hE D) (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    {E : Entry}
    (hM : ∀ w s c, M.Mi w s c → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e)
    (hW : ∀ w s c fs, D.Wi w s c fs → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e) :
    ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → t.2.exited = none →
      ∀ tid th e, t.1.threads[tid]? = some th → t.2.runs tid = true → abi.atSys th.st = false →
        isaLSE2.exec th.st = some e → ¬ Touches (fun l w => Kernel.mapped t.2 w l = false) e := by
  intro t s hP hr hx tid th e hth _ hs he
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, -, h0, h1, -⟩, hK⟩ := hP
  rw [hKR] at hK
  replace hK := hK.1
  have hm := A64HelloWriteK.krh_live hK
  simp only [WakeRel.PTw, ite_true, show (1 : Nat) ≠ 0 from by decide, ite_false] at h0 h1
  rw [hT] at hth
  rcases tid with _ | _ | tid
  · cases (show t0 = th by simpa using hth)
    rw [hPT0] at h0
    obtain ⟨hmi, -⟩ := h0.2
    have hl : s0.term ≠ WakeMLive.wlRet := hm hx s0 (by rw [hS]; rfl)
    have hmi' : M.Mi w th.st (Ctl.of s0) := by
      first
        | exact hmi.resolve_right hl
        | exact hmi
    exact WakeMapped.noTouch_of_K0 hr (hM w _ _ hmi' hs e he)
  · cases (show t1 = th by simpa using hth)
    rw [hpt1] at h1
    obtain ⟨_, _, hw⟩ := HelloEmitPh.PT1hE.wi h1
    exact WakeMapped.noTouch_of_K0 hr (hW w _ _ _ hw hs e he)
  · simp at hth

/-! ## hello.w after the spawn -/

/-- **`post_progress`** at hello (`WakeProgress.post_progress_of` at
`PT1h`, `OutTS` and `KRH`): main's `TOk` as wake's, the worker's from its
frame-aware rows (`outTS_ok`, `worker_callH`). The named hypotheses are
wake's (`hca`, `hmapped`, `hoffM`, `hhalt0`, `hhalt1`, the last at frames)
and `hK`. -/
theorem post_progress_ofH (hC : WCompatH Q D μ Λ arch AbW) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1) (hK : ∀ w fs, (D.ms w fs).K = some abi)
    (hoffM : ∀ w s c, M.Mi w s c → ∀ k a, μ.abortAt k = some a → pcOf s ≠ a)
    (hhalt0 : ∀ w s c, M.Mi w s c → abi.atSys s = true → (isaLSE2.exec s).isSome)
    (hhalt1 : ∀ w s c fs, D.Wi w s c fs → abi.atSys s = true → (isaLSE2.exec s).isSome)
    {t : Cfg} {s : TermRun.Cfg} (hP : Q.Post Λ t s)
    (hca : CertAll μ t)
    (hmapped : t.2.exited = none → ∀ tid th e, t.1.threads[tid]? = some th → t.2.runs tid = true →
      abi.atSys th.st = false →
      isaLSE2.exec th.st = some e → ¬ Touches (fun l w => Kernel.mapped t.2 w l = false) e) :
    (machine (kernel 2)).Progress μ t ∧ InLayout (M := machine (kernel 2)) Λ t := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, core, h0, h1, -⟩, hK'⟩ := hP
  refine ⟨?_, Consumer1.inLayout_of_memIn core.memIn⟩
  rw [hKR] at hK'
  replace hK' := hK'.1
  obtain ⟨-, ⟨j, hsl0⟩, -, -, hm, -⟩ := hK'
  cases hx : t.2.exited with
  | some o => exact Kernel.exited_progress abi (o := o) hx
  | none =>
  simp only [WakeRel.PTw] at h0 h1
  rw [hPT0] at h0
  rw [hC.pt1] at h1
  have ht0 : t.1.threads[0]? = some t0 := by rw [hT]; rfl
  have ht1 : t.1.threads[1]? = some t1 := by rw [hT]; rfl
  have hr0 : t.2.runs 0 = true := by simp [KState.runs, hsl0]
  have hmi : M.Mi w t0.st (Ctl.of s0) :=
    h0.2.1.resolve_right (hm hx s0 (by rw [hS]; rfl))
  obtain ⟨_, _, hwi⟩ := HelloEmitPh.PT1hE.wi h1
  refine progress_ofH hx ⟨t0, ht0, hr0⟩ fun tid th ht hr => ?_
  rcases tid with _ | _ | n
  · cases (show some t0 = some th from ht0.symm.trans ht)
    have hrow : abi.atSys t0.st = false → RowOK Arch.armv8 t0 0 t.1.mem :=
      fun hs => outL_ok Arch.armv8 core.bnd0 (hC0.K0 w) hs (M.closed w _ _ hmi)
    refine ⟨?_, hC0.noSite0 w _ _ hmi, fun hp => (hca hx 0 t0 ht0 hr hp).certOkC, hrow,
      fun hs e hex => hmapped hx 0 t0 e ht0 hr hs hex, fun hs => ?_⟩
    · cases hs : abi.atSys t0.st
      · exact (hrow hs).1
      · exact hhalt0 w _ _ hmi hs
    · obtain ⟨call, hd, hok⟩ := main_call hC0 hoffM hmi hs
      exact ⟨call, hd, callOKH_of_callOK hok⟩
  · cases (show some t1 = some th from ht1.symm.trans ht)
    have hrow : abi.atSys t1.st = false → RowOK Arch.armv8 t1 1 t.1.mem :=
      fun hs => outTS_ok core.bnd1 (hK w) hs (D.closed w _ _ _ hwi)
    refine ⟨?_, hC.noSite w _ _ _ hwi, fun hp => (hca hx 1 t1 ht1 hr hp).certOkC, hrow,
      fun hs e hex => hmapped hx 1 t1 e ht1 hr hs hex, fun hs => ?_⟩
    · cases hs : abi.atSys t1.st
      · exact (hrow hs).1
      · exact hhalt1 w _ _ _ hwi hs
    · exact worker_callH hC hK hwi hs
  · rw [hT] at ht; simp at ht

open Spike.Lib.HelloW1Store (NoWrite)
open Spike.Lib.HelloAssembly (HelloCompat)

/-- **`HelloRowsW.post_progress`** from the named facts: `post_progress_ofH`
with `hmapped_ofH`. -/
theorem post_progressH {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D} {E : Entry}
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = KRHE D r0 r1) (hC : HelloCompat Q D M μ Λ arch AbW hcw hem)
    (hK : ∀ w fs, (D.ms w fs).K = some abi)
    (hoffM : ∀ w s c, M.Mi w s c → ∀ k a, μ.abortAt k = some a → pcOf s ≠ a)
    (hhalt0 : ∀ w s c, M.Mi w s c → abi.atSys s = true → (isaLSE2.exec s).isSome)
    (hhalt1 : ∀ w s c fs, D.Wi w s c fs → abi.atSys s = true → (isaLSE2.exec s).isSome)
    (hmapM : ∀ w s c, M.Mi w s c → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e)
    (hmapW : ∀ w s c fs, D.Wi w s c fs → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e) :
    ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → CertAll μ t →
      (machine (kernel 2)).Progress μ t ∧ InLayout (M := machine (kernel 2)) Λ t :=
  fun t s hP hri hca => post_progress_ofH hC.1 hC.2.2.2 hPT0 hKR hK hoffM hhalt0 hhalt1 hP hca
    (hmapped_ofH hC.1.pt1 hPT0 hKR hmapM hmapW t s hP hri)

/-- info: 'Spike.Lib.HelloProgress.post_progressH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_progressH

end Spike.Lib.HelloProgress
