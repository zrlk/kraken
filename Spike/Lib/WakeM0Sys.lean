/-
**main's system calls after the spawn** (`post_step0`). The thread-0 counterpart of `Spike/Lib/WakeW1Sys.lean` and of
`WakeW1Post.sys_rows`.

- `sys_rows0`: at a system call of main the row is `Out.sys` (the `emit`
  row is a `write`, excluded by `WCompat0.noWrite0`; every instruction row's
  instruction is not the fault `WCompat0.sysExec0` asks there).
- `post_sys0`: a returning system call of main (neither `exit_group`, nor,
  by the row's `SysOk` and `WCompat0.noWrite0`, `exit`, `clone` or `write`)
  keeps `Post` (`post_keep0`: the successor the row lists, no promise at a
  no-promise state by `CertAfter`).
- `post_exited0`: the process exiting (`exit_group`'s kernel state, any
  outcome) keeps `Post`: neither memory nor thread changes, and `KR`'s
  `MainLive` holds vacuously once the process has exited.
-/
import Spike.Lib.WakeM0Instr
import Spike.Lib.WakeW1Post

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **At a system call of main the row is `Out.sys`**: the `emit` row is a
`write` (`WCompat0.noWrite0`), every instruction row's instruction is not the
fault `WCompat0.sysExec0` asks there. -/
theorem sys_rows0 (hC0 : WCompat0 Q M μ Λ) {st : isaLSE2.State} {c : Ctl} (hmi : M.Mi w st c)
    (hat : abi.atSys st = true) {call : Call} (hd : decode abi.nrs (abi.nr st) (abi.arg st) = some call) :
    SysOk wakeSrc (M.ms w) st c call ∧
      ∀ s' ∈ certSuccs abi st call, ∃ c', LocalRun wakeSrc c c' ∧ M.Mi w s' c' := by
  cases M.closed w _ _ hmi with
  | out r =>
    cases r with
    | sys K call' hK ha hd' hok hX =>
      rw [hC0.K0 w] at hK; cases hK
      have e : call' = call := Option.some.inj (hd'.symm.trans hd)
      subst e
      exact ⟨hok, hX⟩
    | emit K buf n Pw Qw hK ha hd' =>
      rw [hC0.K0 w] at hK; cases hK
      exact absurd hd' (hC0.noWrite0 w _ _ 1 buf n hmi ha)
    | choice P tree he hsil hX =>
      obtain ⟨m, rfl⟩ := hC0.sysExec0 w _ _ _ hmi hat he
      cases hsil
    | _ =>
      obtain ⟨m, hm⟩ := hC0.sysExec0 w _ _ _ hmi hat ‹isaLSE2.exec st = some _›
      cases hm
  | ldSt _ _ _ _ _ _ _ _ _ he =>
    obtain ⟨m, hm⟩ := hC0.sysExec0 w _ _ _ hmi hat he
    cases hm

/-- **A returning system call of main keeps `Post`**: the call is not
`exit_group` (`hg`), nor `exit` or `clone` (the row's `SysOk`) nor `write`
(`WCompat0.noWrite0`), so it returns (`sysStep_back`) to a state the row
lists (`sysStep_cases`), with no event; no promise at a no-promise state
(`CertAfter`, `WCompat0.noProm0`). main's state and control are given in
`Mi` (`hmi`). -/
theorem post_sys0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hmi : M.Mi w t0.st (Ctl.of s0))
    {call : Call} (hat : abi.atSys t0.st = true) (hd : decode abi.nrs (abi.nr t0.st) (abi.arg t0.st) = some call)
    (hg : ∀ v, call ≠ .exitGroup v)
    {p : Pick} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.armv8 0 t p = some (es, t'))
    (hca : CertAfter abi Arch.armv8 μ 0 t') :
    es = [] ∧ ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ t' s' := by
  obtain ⟨hok, hX⟩ := sys_rows0 hC0 hmi hat hd
  have hc : callOf abi t0 = some call := hd
  have hnx : call ≠ .exit := hok.1
  have hcl : ∀ st tl, call ≠ .clone st tl := hok.2.1
  have hnw : ∀ fd buf n, call ≠ .write fd buf n := fun fd buf n e =>
    hC0.noWrite0 w _ _ fd buf n hmi hat (e ▸ hd)
  have ht0 : t.1.threads[0]? = some t0 := by rw [h.th]; rfl
  obtain ⟨-, call', hc', hcases⟩ := sysStep_cases ht0 hs (fun fd buf n hw => by
    exact absurd (Option.some.inj (hc.symm.trans hw)) (hnw fd buf n))
  rw [hc] at hc'
  cases hc'
  obtain ⟨t'', ht'', hmem⟩ : ∃ t'', t'.1.threads[0]? = some t'' ∧ t''.st ∈ certSuccs abi t0.st call := by
    rcases hcases with ⟨fd, buf, n, -, -, -, hw, -⟩ | ⟨r, -, -, -, -, -, t'', ht'', hm, -⟩ | ⟨hw, -⟩ |
      ⟨v, hw, -⟩
    · exact absurd hw (hnw fd buf n)
    · exact ⟨t'', ht'', hm⟩
    · exact absurd hw hnx
    · exact absurd hw (hg v)
  obtain ⟨rfl, u, r, rfl, hv, hp, hrv, hwv⟩ := sysStep_back ht0 hc hnw hnx hg hcl hs
  refine ⟨rfl, ?_⟩
  have hget : (t.1.withThread 0 (retThread abi u r) t.1.mem).threads[0]? = some (retThread abi u r) :=
    Live.Sem.withThread_get_self ht0
  rw [hget] at ht''
  cases ht''
  have hub : u.Bnd t.1.mem.last :=
    ⟨hv ▸ h.core.bnd0.views, by unfold Thread.RegsLe; rw [hrv, hwv]; exact h.core.bnd0.regs⟩
  obtain ⟨c', hr, hmi'⟩ := hX _ hmem
  exact post_keep0 hC hC0 hPT0 hKR hown h (t0' := retThread abi u r) (by rw [retThread_prom, hp])
    (ExtThread.bnd_retThread abi hub r)
    (by rw [retThread_views abi u r, retThread_prom, hv, hp]; exact h.core.cov0)
    (fun hn => hC0.noProm0 w _ _ _ hn (hca _ hget)) (by rw [retThread_views abi u r, hv]; exact h.preC) hr hmi'

/-- **The process exiting keeps `Post`** (`exit_group`'s kernel state, with
any outcome): the configuration and the source are kept, and `KR`'s
`MainLive` holds vacuously once the process has exited. -/
theorem post_exited0 (hKR : Q.KR = WakeKR.KR r0 r1) {t : Cfg} {s : TermRun.Cfg} (hpost : Q.Post Λ t s)
    (o : Outcome) : Q.Post Λ (t.1, { t.2 with exited := some o }) s := by
  obtain ⟨w, hi, hk⟩ := hpost
  refine ⟨w, hi, ?_⟩
  rw [hKR] at hk ⊢
  obtain ⟨hn, h0, h1, hh, -, htr⟩ := hk
  exact ⟨hn, h0, h1, hh, fun hx => (by cases hx), htr⟩

/-- info: 'Spike.Lib.WakeM0.post_sys0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_sys0

end Spike.Lib.WakeM0
