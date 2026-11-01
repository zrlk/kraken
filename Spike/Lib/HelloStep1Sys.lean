/-
**hello.w on AArch64: the worker's kernel system calls in the print phase
keep `Post`** (C4, row B8-gen1-sys, step (c): `HelloStep1D.SysStepP` off
`print`'s `write` to fd 1). The twin of `WakeW1.post_sys` with `print`'s
abort path (`WCompatH.sysOkH`).

At a system call of the worker, `sysOkH` leaves:
- `exit`: the worker's exit row (`atTexit`, excluded by `SysStepP`'s premise);
- `write(1, …)`: `print`'s write (`Write1StepP`, EmitStepP's, a premise);
- in the abort-write phase `AbW`, `write(2, …)` (`post_write2H`: a byte keeps
  the state, the source stutters; a return lands where the row's `Out.sys`
  lists) or `exit_group(abortStatus)` (`post_exitGroupH`: the abort ends the
  process, the source stutters; the exit event is off every abort site,
  `WakeM0.exit_off0`, while `AbExit` puts the call at one);
- neither a `write` nor `exit_group`: no `clone` (`HelloStep1D.noClone`), and
  the call returns where the row lists (`post_backH`).

- `post_exitedH`: `Post` once the process exited (`KRHE`); `krW_krhe`: the
  kernel relation after a worker step setting its slot running or keeping
  the kernel state; `wrOk2_of`: `WrOk2` at `KRHE`.
- `outL_sysRow`, `sys_rowsH`: the worker's row at a call other than `exit`
  and `write(1, …)` is `Out.sys`, after a frame run.
- `WrOk2` (bytes out of `write(2, …)` at most its length, `wrOk2_of`),
  `AbExit`, `Write1StepP`: the premises (the abort phase's `exit_group` at an
  abort site; `print`'s write step).
- `sysStepP_of`: `SysStepP` from them.
-/
import Spike.Lib.HelloStep1D
import Spike.Lib.HelloPostAb

namespace Spike.Lib.HelloStep1Sys

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh StorePh WCompatH KrW)
open Spike.Lib.HelloW1Store (NoWrite relW)
open Spike.Lib.HelloAssembly (HelloCompat)
open Spike.Lib.HelloStep1P (post_frameRunH)
open Spike.Lib.HelloStep1D (SysStepP PartsH.post noClone)
open Spike.Lib.A64HelloWriteK (KRH krh_set1_run krh_frame1)
open Spike.Lib.HelloKRE (KRHE WrOth)
open Spike.Lib.WakeOwn (wakeOwn)

/-! ## The premises -/

/-- **A `write(2, …)` of the worker has at most its length out** (from the
kernel-side relation's bytes-out link, KRHE). -/
def WrOk2 (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc buf n, PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → abi.atSys t1.st = true →
    callOf abi t1 = some (.write 2 buf n) → t.2.wr 1 ≤ n

/-- **The abort-write phase's `exit_group` is at an abort site**
(`scc_rt_abort_write`'s `svc`, `μ.abortAt .writeErr`). -/
def AbExit {ι : Type} (D : WSideH ι) (μ : Marks) (AbW : isaLSE2.State → Prop) : Prop :=
  ∀ w s c fs v, D.Wi w s c fs → AbW s → abi.atSys s = true →
    decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → ∃ k a, μ.abortAt k = some a ∧ pcOf s = a

/-- **`print`'s `write` to fd 1 keeps `Post`** (B8-gen1-EmitStepP). -/
def Write1StepP (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t' (p : Pick) buf n, PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc →
    HelloStep1.PrivAt Λ t → PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 → SrcSem.mainExit s = [] → abi.atSys t1.st = true →
    callOf abi t1 = some (.write 1 buf n) → (machine (kernel 2)).Step μ 1 t es t' →
    sysStep abi Arch.armv8 1 t p = some (es, t') → CertAfter abi Arch.armv8 μ 1 t' →
    ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {AbW : isaLSE2.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)} {r0 r1 : Q.ι → Range}

/-! ## The kernel relation -/

/-- **`Post` once the process has exited** (`WakeM0.post_exited0` at
`KRHE`: the slots and threads kept). -/
theorem post_exitedH (hKR : Q.KR = KRHE D r0 r1) {t : Cfg} {s : TermRun.Cfg} (hpost : Q.Post Λ t s) :
    ∀ o, Q.Post Λ (t.1, { t.2 with exited := some o }) s := by
  intro o
  obtain ⟨w, hi, hk⟩ := hpost
  refine ⟨w, hi, ?_⟩
  rw [hKR] at hk ⊢
  obtain ⟨⟨hn, h0, h1, hh, -, htr⟩, hl⟩ := hk
  exact ⟨⟨hn, h0, h1, hh, fun hx => (by cases hx), htr⟩, HelloKRE.lk_frame0 hl rfl rfl rfl⟩

/-- **`KrW` at `KRHE`** after a step of the worker setting its slot running
or keeping the kernel state (`krh_frame1`, `krh_set1_run`), with the link at
the new count from a `write` to another descriptor (`WrOth`). -/
theorem krW_krhe (hKR : Q.KR = KRHE D r0 r1) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t1' : Thread isaLSE2} {mem' : Memory} {s1' : TermRun.TTh} {k' : KState}
    (hk : k' = t.2 ∨ ∃ m, k' = t.2.set 1 (.run m)) (hL : 0 < k'.wr 1 → WrOth t1' (k'.wr 1)) :
    KrW Q D w t s t1' mem' s1' k' := by
  intro s' hs0 hs1' htr hW
  have hk0 := h.kr
  rw [hKR] at hk0 ⊢
  have hf : KRH r0 r1 w (t.1.withThread 1 t1' mem', t.2) s' :=
    krh_frame1 w t _ s s' hk0.1 rfl hs0 (fun _ hx => by simpa only [SrcSem.traceOf, htr] using hx)
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  have hg : (t.1.withThread 1 t1' mem').threads[1]? = some t1' := Live.Sem.withThread_get_self ht1
  refine ⟨?_, fun hp => ⟨t1', s1', hg, hs1', .inr (hL hp)⟩, fun u1 v1 h1 h2 hn => ?_⟩
  · rcases hk with rfl | ⟨m, rfl⟩
    · exact hf
    · exact krh_set1_run m hf _
  · obtain rfl : u1 = t1' := Option.some.inj (h1.symm.trans hg)
    obtain rfl : v1 = s1' := Option.some.inj (h2.symm.trans hs1')
    exact absurd hW hn

/-- **`WrOk2` at `KRHE`**: mid-`write(2, …)` the link is `WrOth` at its
length. -/
theorem wrOk2_of (hKR : Q.KR = KRHE D r0 r1) : WrOk2 Q D Λ := by
  intro w t s t0 t1 s0 s1 ts tp sp oc buf n h _ hc
  have hk := h.kr
  rw [hKR] at hk
  rcases Nat.eq_zero_or_pos (t.2.wr 1) with h0 | hp
  · omega
  obtain ⟨u1, _, h1, _, hE⟩ := hk.2.1 hp
  obtain rfl : u1 = t1 := Option.some.inj (h1.symm.trans (by rw [h.th]; rfl))
  rcases hE with ⟨buf', n', -, -, -, hd, -⟩ | ⟨fd, buf', n', -, -, hd, hj⟩
  · exact absurd (Option.some.inj (hc.symm.trans hd)) (by simp)
  · have e := Option.some.inj (hc.symm.trans hd)
    cases e
    exact hj

/-! ## The `Out.sys` row -/

/-- **An `OutL` row at a system call other than `write(1, …)` is
`Out.sys`** (under the machine's kernel model), at a state whose
instruction faults: the `emit` row is a `write` to fd 1, every other row
runs an instruction. -/
theorem outL_sysRow {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {X : Frag isaLSE2} {st : isaLSE2.State} {c : Ctl} (hK : ms.K = some abi) (hl : OutL p lbl ms X st c)
    (hsx : ∀ tr, isaLSE2.exec st = some tr → ∃ m, tr = .fault m) {call : Call}
    (hd : decode abi.nrs (abi.nr st) (abi.arg st) = some call) (hn1 : ∀ buf n, call ≠ .write 1 buf n) :
    ∀ s' ∈ certSuccs abi st call, ∃ c', LocalRun p c c' ∧ X s' c' := by
  cases hl with
  | out r =>
    cases r with
    | sys K call' hK' ha hd' hok hX =>
      rw [hK] at hK'; cases hK'
      obtain rfl : call' = call := Option.some.inj (hd'.symm.trans hd)
      exact hX
    | emit K buf n Pw Qw hK' ha hd' =>
      rw [hK] at hK'; cases hK'
      exact (hn1 buf n (Option.some.inj (hd'.symm.trans hd)).symm).elim
    | choice P tree he hsil hX =>
      obtain ⟨m, rfl⟩ := hsx _ he
      cases hsil
    | _ =>
      obtain ⟨m, hm⟩ := hsx _ ‹isaLSE2.exec st = some _›
      cases hm
  | ldSt _ _ _ _ _ _ _ _ _ he =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm

/-- **At a system call of the worker other than `exit` and `write(1, …)`
the row is `Out.sys`**, after a frame run (the twin of `WakeW1.sys_rows`):
the `texit` row is at `exit`, the frame and fence rows run an instruction. -/
theorem sys_rowsH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hat : abi.atSys t1.st = true) {call : Call}
    (hc : callOf abi t1 = some call) (hnx : call ≠ .exit) (hn1 : ∀ buf n, call ≠ .write 1 buf n) :
    ∃ c₁ fs₁, FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, fs₁) ∧
      ∀ s' ∈ certSuccs abi t1.st call, ∃ c', LocalRun helloSrc c₁ c' ∧ D.Wi w s' c' fs₁ := by
  have hsx : ∀ tr, isaLSE2.exec t1.st = some tr → ∃ m, tr = .fault m := fun tr he =>
    hC.1.sysExec w _ _ _ _ h.pt1.1 hat he
  have hK : ∀ fs, (D.ms w fs).K = some abi := fun fs => by rw [hms w fs]; exact hC.2.1.K w
  cases D.closed w _ _ _ h.pt1.1 with
  | pre c₁ fs₁ hr₁ hl => exact ⟨c₁, fs₁, hr₁, outL_sysRow (hK fs₁) hl hsx hc hn1⟩
  | frame s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | fnc k s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | top c₁ hr₁ hT =>
    cases hT with
    | outL hl => exact ⟨c₁, [], hr₁, outL_sysRow (hK []) hl hsx hc hn1⟩
    | unpk _ _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm
    | texit K a hK' ha hd' ht =>
      rw [hK []] at hK'; cases hK'
      exact (hnx (Option.some.inj (hd'.symm.trans hc)).symm).elim
    | fnc _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm

/-! ## The calls -/

section Calls

variable (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
  (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Q.own = wakeOwn) (hex : SrcSem.mainExit s = [])
  (hat : abi.atSys t1.st = true)
include hC hms h hown hex hat

/-- **A returning call keeps `Post`** (the twin of `WakeW1.post_sys`): neither
`write`, `exit`, `exit_group` nor `clone`, the call returns
(`sysStep_back`) to a state the row lists (`sysStep_cases`, `sys_rowsH`). -/
theorem post_backH (hKR : Q.KR = KRHE D r0 r1) {call : Call} (hc : callOf abi t1 = some call)
    (hnw : ∀ fd buf n, call ≠ .write fd buf n)
    (hnx : call ≠ .exit) (hg : ∀ v, call ≠ .exitGroup v) (hcl : ∀ st tl, call ≠ .clone st tl) {p : Pick}
    {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.armv8 1 t p = some (es, t'))
    (hca : CertAfter abi Arch.armv8 μ 1 t') :
    es = [] ∧ ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ t' s' := by
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  obtain ⟨-, call', hc', hcases⟩ := sysStep_cases ht1 hs (fun fd buf n hw =>
    absurd (Option.some.inj (hc.symm.trans hw)) (hnw fd buf n))
  rw [hc] at hc'
  cases hc'
  obtain ⟨t'', ht'', hmem⟩ : ∃ t'', t'.1.threads[1]? = some t'' ∧ t''.st ∈ certSuccs abi t1.st call := by
    rcases hcases with ⟨fd, buf, n, -, -, -, hw, -⟩ | ⟨r, -, -, -, -, -, t'', ht'', hm, -⟩ | ⟨hw, -⟩ |
      ⟨v, hw, -⟩
    · exact absurd hw (hnw fd buf n)
    · exact ⟨t'', ht'', hm⟩
    · exact absurd hw hnx
    · exact absurd hw (hg v)
  obtain ⟨rfl, u, r, rfl, hv, hp, hrv, hwv⟩ := WakeW1.sysStep_back ht1 hc hnw hnx hg hcl hs
  refine ⟨rfl, ?_⟩
  have hget : (t.1.withThread 1 (retThread abi u r) t.1.mem).threads[1]? = some (retThread abi u r) :=
    Live.Sem.withThread_get_self ht1
  rw [hget] at ht''
  cases ht''
  have hub : u.Bnd t.1.mem.last :=
    ⟨hv ▸ h.core.bnd1.views, by unfold Thread.RegsLe; rw [hrv, hwv]; exact h.core.bnd1.regs⟩
  obtain ⟨c₁, fs₁, hr₁, hX⟩ := sys_rowsH hC hms h hat hc hnx fun buf n => hnw 1 buf n
  obtain ⟨c', hr, hwi⟩ := hX _ hmem
  have h0 : t.2.wr 1 = 0 := by
    have hk := h.kr
    rw [hKR] at hk
    exact HelloKRE.wr1_zero hk.2 ht1 (.inr fun fd buf n hw => hnw fd buf n (Option.some.inj (hc.symm.trans hw)))
  exact post_frameRunH hC.1 h hown hex (t1' := retThread abi u r)
    (krW_krhe hKR h (.inl rfl) fun hp => absurd h0 (Nat.pos_iff_ne_zero.mp hp)) (q' := (c', fs₁))
    (by rw [retThread_prom, hp])
    (ExtThread.bnd_retThread abi hub r) (by rw [retThread_views abi u r, retThread_prom, hv, hp]; exact h.core.cov1)
    (fun hn => hC.2.1.noProm w _ _ _ hn (hca _ hget)) (hr₁.trans (FrameRun.ofLocal hr fs₁)) hwi

/-- **The abort path's `write(2, …)` keeps `Post`**: a byte keeps the
worker's state and memory (the source stutters at the same row, the slot's
bytes out advanced); a return lands where the row's `Out.sys` lists, the
slot's count reset or kept (`write_ret_cases`); no observable event. -/
theorem post_write2H (hKR : Q.KR = KRHE D r0 r1) {buf n : Nat} (hc : callOf abi t1 = some (.write 2 buf n))
    (hwr : t.2.wr 1 ≤ n) {p : Pick} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.armv8 1 t p = some (es, t'))
    (hca : CertAfter abi Arch.armv8 μ 1 t') :
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  obtain ⟨-, call', hc', hcases⟩ := sysStep_cases ht1 hs (fun fd buf' n' hw => by
    rw [hc] at hw
    cases hw
    exact hwr)
  rw [hc] at hc'
  cases hc'
  rcases hcases with ⟨fd, buf', n', rd, b, t1', hw, rfl, hlt, hrb, hst, rfl, rfl⟩ |
    ⟨r, rfl, -, -, -, -, t'', ht'', hm, -⟩ | ⟨hw, -⟩ | ⟨v, hw, -⟩
  · -- a byte: the state kept, the source stutters; the link at the new count
    cases hw
    have hget : (t.1.withThread 1 t1' t.1.mem).threads[1]? = some t1' := Live.Sem.withThread_get_self ht1
    have hL : WrOth t1' ((t.2.set 1 (.run (t.2.wr 1 + 1))).wr 1) := by
      have := HelloKRE.wr_set_run_le t.2 1 (t.2.wr 1 + 1)
      exact ⟨2, buf, n, by decide, by rw [hst]; exact hat, by rw [hst]; exact hc, by omega⟩
    obtain ⟨s', hr, hp⟩ := post_frameRunH hC.1 h hown hex (t1' := t1')
      (krW_krhe hKR h (.inr ⟨_, rfl⟩) fun _ => hL) (q' := (Ctl.of s1, s1.stack))
      (Kernel.readByte_prom hrb) (ExtThread.bnd_readByte abi h.core.bnd1 hrb) (HelloFrz.readByte_cohL hrb h.core.cov1)
      (fun hn => hC.2.1.noProm w _ _ _ hn (hca _ hget)) (.refl _) (by rw [hst]; exact h.pt1.1)
    exact ⟨s', by simpa using hr, hp⟩
  · -- a return, where the row lists; no byte out after it
    obtain ⟨c₁, fs₁, hr₁, hX⟩ := sys_rowsH hC hms h hat hc (fun h' => by cases h') fun _ _ h' => by cases h'
    have key : ∀ k', (k' = t.2 ∨ ∃ m, k' = t.2.set 1 (.run m)) → k'.wr 1 = 0 →
        t' = (t.1.withThread 1 (retThread abi t1 r) t.1.mem, k') →
        ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ t' s' := by
      rintro k' hk hk0 rfl
      have hget : (t.1.withThread 1 (retThread abi t1 r) t.1.mem).threads[1]? = some (retThread abi t1 r) :=
        Live.Sem.withThread_get_self ht1
      rw [hget] at ht''
      cases ht''
      obtain ⟨c', hr, hwi⟩ := hX _ hm
      exact post_frameRunH hC.1 h hown hex (t1' := retThread abi t1 r)
        (krW_krhe hKR h hk fun hp => absurd hk0 (Nat.pos_iff_ne_zero.mp hp)) (q' := (c', fs₁))
        (by rw [retThread_prom])
        (ExtThread.bnd_retThread abi h.core.bnd1 r)
        (by rw [retThread_views abi t1 r, retThread_prom]; exact h.core.cov1)
        (fun hn => hC.2.1.noProm w _ _ _ hn (hca _ hget)) (hr₁.trans (FrameRun.ofLocal hr fs₁)) hwi
    rcases HelloPostAb.write_ret_cases ht1 hc hs with ⟨-, -, rfl, rfl⟩ | ⟨h0, -, rfl, rfl⟩ | ⟨h0, -, rfl, rfl⟩
    · exact key _ (.inr ⟨0, rfl⟩) (HelloKRE.wr_set_run0_self _ _) rfl
    · exact key _ (.inl rfl) h0 rfl
    · obtain ⟨s', hr, hp⟩ := key _ (.inl rfl) h0 rfl
      exact ⟨s', hr, hp⟩
  · cases hw
  · cases hw

omit hms hown hex in
/-- **The abort path's `exit_group` keeps `Post`**: the abort ends the
process, the source stutters (`post_exitedH`); the exit event is off every
abort site (`WakeM0.exit_off0`), while the call is at one (`AbExit`). -/
theorem post_exitGroupH (hKR : Q.KR = KRHE D r0 r1) (hAbX : AbExit D μ AbW) (hab : AbW t1.st) {v : Nat}
    (hc : callOf abi t1 = some (.exitGroup v)) {p : Pick} {es : List Ev} {t' : Cfg}
    (hst : (machine (kernel 2)).Step μ 1 t es t') (hs : sysStep abi Arch.armv8 1 t p = some (es, t')) :
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  obtain ⟨-, call', hc', hcases⟩ := sysStep_cases ht1 hs (fun fd buf n hw => by rw [hc] at hw; cases hw)
  rw [hc] at hc'
  cases hc'
  rcases hcases with ⟨_, _, _, _, _, _, hw, -⟩ | ⟨_, -, -, hg', -⟩ | ⟨hw, -⟩ | ⟨v', hw, hcase⟩
  · cases hw
  · exact absurd rfl (hg' v)
  · cases hw
  · cases hw
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨k, -, -, rfl, rfl⟩
    · -- an exit event: off every abort site, but the call is at one
      obtain ⟨k, a, ha, hpc⟩ := hAbX w _ _ _ v h.pt1.1 hab hat hc
      exact (WakeM0.exit_off0 hst (List.mem_singleton_self _) k a ha ⟨t1, ht1, hpc⟩).elim
    · -- the abort: the process ends, the source stutters
      exact ⟨s, .refl _, post_exitedH hKR (PartsH.post hC.1.pt1 h) _⟩

end Calls

/-! ## The obligation -/

/-- **`SysStepP`** (row B8-gen1-sys, step (c)): the worker's system calls in
the print phase keep `Post`, given `print`'s `write` to fd 1
(`Write1StepP`) and the abort path's `exit_group` at an abort site
(`AbExit`); the bytes out of its `write(2, …)` by `wrOk2_of`; `hms` (`rfl`
at `HelloAssemblyI.DH`), `hown`, `hKR` (`rfl` at `helloQ`). -/
theorem sysStepP_of (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (hown : Q.own = wakeOwn) (hKR : Q.KR = KRHE D r0 r1) (hAbX : AbExit D μ AbW)
    (hw1 : Write1StepP Q D μ Λ arch) : SysStepP Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' p h hpk hP hnt hex hst hs hca
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  obtain ⟨hat, call, hc⟩ := WakeW1.sysStep_ready ht1 hs
  have hnx : call ≠ .exit := by
    rintro rfl
    have hT : Q.atTexit = WakeW1.atTexit := hC.2.1.atTexit
    exact hnt (by rw [hT]; exact ⟨t1, ht1, hat, hc⟩)
  rcases hC.1.sysOkH w _ _ _ call h.pt1.1 hat hc with hx | ⟨buf, n, rfl⟩ | ⟨hab, ⟨buf, n, rfl⟩ | rfl⟩ | ⟨hnw, hg⟩
  · -- `exit`: the exit row
    exact (hnx hx).elim
  · exact hw1 w t s t0 t1 s0 s1 ts tp sp oc es t' p buf n h hpk hP hex hat hc hst hs hca
  · exact post_write2H hC hms h hown hex hat hKR hc (wrOk2_of hKR w t s t0 t1 s0 s1 ts tp sp oc buf n h hat hc) hs hca
  · exact post_exitGroupH hC h hat hKR hAbX hab hc hst hs
  · by_cases hcl : ∃ st tl, call = .clone st tl
    · obtain ⟨st, tl, rfl⟩ := hcl
      exact (noClone hC hms h hat hc).elim
    · obtain ⟨rfl, s', hr, hp⟩ := post_backH hC hms h hown hex hat hKR hc hnw hnx hg (fun st tl e => hcl ⟨st, tl, e⟩)
        hs hca
      exact ⟨s', hr, hp⟩

/-- info: 'Spike.Lib.HelloStep1Sys.sysStepP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sysStepP_of

end Spike.Lib.HelloStep1Sys
