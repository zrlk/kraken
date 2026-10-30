/-
**The worker's system calls other than `exit`** (data in `Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

- `sysStep_back`: a system-call step of a call that is neither `write`,
  `exit`, `exit_group` nor `clone` returns: no event, the thread returned
  (`retThread`, the thread pointer possibly set first), memory and kernel
  state kept.
- `post_sys`: the worker's system-call step at the `Out.sys` row keeps
  `Post` (`post_keep`: the successor one the row lists, its owned words by
  `WCompat.ownSys`, no promise at a no-promise state by `CertAfter`).
-/
import Spike.Lib.WakeW1Instr

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt

/-- **A returning system call**: neither `write`, `exit`, `exit_group` nor
`clone`, the step emits nothing and returns the thread (its state possibly
with the thread pointer set), memory and kernel state kept. -/
theorem sysStep_back {A : Arch} {tid : Nat} {c c' : Config isaLSE2 × KState} {p : Pick} {es : List Ev}
    {t : Thread isaLSE2} {call : Call} (ht : c.1.threads[tid]? = some t) (hc : callOf abi t = some call)
    (hnw : ∀ fd buf n, call ≠ .write fd buf n) (hx : call ≠ .exit) (hg : ∀ v, call ≠ .exitGroup v)
    (hcl : ∀ st tl, call ≠ .clone st tl) (h : sysStep abi A tid c p = some (es, c')) :
    es = [] ∧ ∃ (u : Thread isaLSE2) (r : BitVec 64), c' = (c.1.withThread tid (retThread abi u r) c.1.mem, c.2) ∧
      u.views = t.views ∧ u.prom = t.prom ∧ u.rview = t.rview ∧ u.wview = t.wview := by
  unfold sysStep at h
  rw [ht] at h
  simp only [hc] at h
  split at h
  · cases h
  cases call with
  | write fd buf n => exact absurd rfl (hnw fd buf n)
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | clone st tl => exact absurd rfl (hcl st tl)
  | futexWait | futexWake _ | rtSigaction | archSetFs _ =>
    cases p with
    | ret r =>
      simp only at h
      split at h
      · simp only [back, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, _, r, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    | _ => simp at h

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **The worker's system call at the `Out.sys` row keeps `Post`**: the call
returns (`sysStep_back`: neither `write` nor `exit_group` by
`WCompat.sysOk`, nor `exit` or `clone` by the row's `SysOk`), to a state the
row lists (`sysStep_cases`), its owned words kept (`WCompat.ownSys`), no
promise at a no-promise state (`CertAfter`). -/
theorem post_sys (hC : WCompat Q D μ Λ arch) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hex : SrcSem.mainExit s = []) {call : Call} (hat : abi.atSys t1.st = true)
    (hd : decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some call)
    (hok : SysOk wakeSrc (D.ms w) t1.st (Ctl.of s1) call)
    (hx : ∀ s' ∈ certSuccs abi t1.st call, ∃ c', LocalRun wakeSrc (Ctl.of s1) c' ∧ D.Wi w s' c')
    {p : Pick} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.armv8 1 t p = some (es, t'))
    (hca : CertAfter abi Arch.armv8 μ 1 t') :
    es = [] ∧ ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ t' s' := by
  have hc : callOf abi t1 = some call := hd
  have hnx : call ≠ .exit := hok.1
  have hcl : ∀ st tl, call ≠ .clone st tl := hok.2.1
  obtain ⟨hnw, hg⟩ := (hC.sysOk w _ _ call h.pt1.1 hat hd).resolve_left hnx
  have ht1 := h.t1_get
  obtain ⟨-, call', hc', hcases⟩ := sysStep_cases ht1 hs (fun fd buf n hw => by
    exact absurd (Option.some.inj (hc.symm.trans hw)) (hnw fd buf n))
  rw [hc] at hc'
  cases hc'
  obtain ⟨t'', ht'', hmem⟩ : ∃ t'', t'.1.threads[1]? = some t'' ∧ t''.st ∈ certSuccs abi t1.st call := by
    rcases hcases with ⟨fd, buf, n, -, -, -, hw, -⟩ | ⟨r, -, -, -, -, -, t'', ht'', hm, -⟩ | ⟨hw, -⟩ |
      ⟨v, hw, -⟩
    · exact absurd hw (hnw fd buf n)
    · exact ⟨t'', ht'', hm⟩
    · exact absurd hw hnx
    · exact absurd hw (hg v)
  obtain ⟨rfl, u, r, rfl, hv, hp, hrv, hwv⟩ := sysStep_back ht1 hc hnw hnx hg hcl hs
  refine ⟨rfl, ?_⟩
  have hget : (t.1.withThread 1 (retThread abi u r) t.1.mem).threads[1]? = some (retThread abi u r) :=
    Live.Sem.withThread_get_self ht1
  rw [hget] at ht''
  cases ht''
  have hub : u.Bnd t.1.mem.last :=
    ⟨hv ▸ h.core.bnd1.views, by unfold Thread.RegsLe; rw [hrv, hwv]; exact h.core.bnd1.regs⟩
  obtain ⟨c', hr, hwi⟩ := hx _ hmem
  refine post_keep hC h hex (t1' := retThread abi u r) (by rw [retThread_prom, hp]) (ExtThread.bnd_retThread abi hub r)
    (by rw [retThread_views abi u r, retThread_prom, hv, hp]; exact h.core.cov1) ?_
    (fun hn => hC.noProm w _ _ _ hn (hca _ hget)) hr hwi
  rw [hC.ownSys w _ _ call h.pt1.1 hat hd _ hmem, retThread_prom, hp]
  exact h.own1

end Spike.Lib.WakeW1
