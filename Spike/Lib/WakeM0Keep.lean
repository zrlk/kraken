/-
**main's steps that keep memory and promises** (`post_step0`). The thread-0 counterpart of
`Spike/Lib/WakeW1Keep.lean`'s `post_keep`.

- `Parts.mCtl`: main's control invariant at its source thread.
- `post_keep0`: a step of main replacing thread 0 by a thread with the same
  promises, memory and kernel state kept, matched by a local run of main's
  source into `Mi`, keeps `Post` (a silent row, a choice, a runtime load, a
  fence, a system call's return). main's source stays off its return
  (`WCompat0.live0`), so `main` has not returned along the run, and has no
  promise (`PT0`), so it is certified.
-/
import Spike.Lib.WakeW1Keep
import Spike.Lib.WakeM0Frame
import Spike.Lib.WakeM0Src
import Spike.Lib.WakeM0Ctl
import Spike.Lib.WakeM0Core
import Spike.Lib.WakeM0Compat
import Spike.Lib.WakeOwn

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.WorkerSrcStep
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1
open Spike.Lib.WakeMLive (wlRet)

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

namespace Parts

variable {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

theorem _root_.Spike.Lib.WakeW1.Parts.s0_get (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : s.ths[0]? = some s0 := by
  rw [h.ths]; rfl

/-- `Parts`' `PT0` at `hPT0`. -/
theorem _root_.Spike.Lib.WakeW1.Parts.pt0M (hPT0 : Q.PT0 = PT0 M) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    PT0 M w t.1.mem s.mem t0 s0 := by
  have := h.pt0; rw [hPT0] at this; exact this

/-- main's control invariant at its source thread. -/
theorem _root_.Spike.Lib.WakeW1.Parts.mCtl (hPT0 : Q.PT0 = PT0 M) (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    MCtl (M.cw w) (Ctl.of s0) :=
  ⟨rfl, (h.pt0M hPT0).2.2.2.1, (h.pt0M hPT0).2.2.2.2.1⟩

/-- **main's state and control are in `Mi`** while the process runs: `PT0`
puts them there or main's source at `wlRet`, which `KR`'s `MainLive`
excludes before the exit. -/
theorem _root_.Spike.Lib.WakeW1.Parts.mi0 (hPT0 : Q.PT0 = PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hx : t.2.exited = none) : M.Mi w t0.st (Ctl.of s0) := by
  refine (h.pt0M hPT0).1.resolve_right fun hr => ?_
  have hk := h.kr
  rw [hKR] at hk
  exact WakeKR.kr_live hk hx s0 h.s0_get hr

end Parts

/-- **A step of main keeping memory, promises and the kernel state, matched
by a local run of main's source, keeps `Post`**: thread 0 replaced by `t0'`
(same promises, its bound, cover, no-promise fact and `PreC` at the
memory), main's source after a local run from its control to `c'` with
`Mi w t0'.st c'`. -/
theorem post_keep0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn) {w : Q.ι} {t : Cfg} {s : TermRun.Cfg}
    {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    {oc : Option (Nat × Nat)} (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t0' : Thread isaLSE2} {c' : Ctl} (hp : t0'.prom = t0.prom) (hb : t0'.Bnd t.1.mem.last)
    (hcov : CohCoversL t0'.views t0'.prom t.1.mem ((Q.P w).cov 0))
    (hnp : (Q.P w).noProm t0'.st → t0'.prom = [])
    (hpre : PreC (Q.SR w) (Q.C w).cT t.1.mem t0'.views)
    (hr : LocalRun wakeSrc (Ctl.of s0) c') (hmi : M.Mi w t0'.st c') :
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 t0' t.1.mem, t.2) s' := by
  have hpt0 := h.pt0M hPT0
  have hctl' := localRun_mCtl hr (h.mCtl hPT0)
  let s0' : TermRun.TTh := { s0 with term := c'.term, env := c'.env }
  have hc'eq : Ctl.of s0' = c' := by
    obtain ⟨tm, en, hd⟩ := c'
    have : hd = none := hctl'.hold
    subst this; rfl
  have hlive : c'.term ≠ wlRet := hC0.live0 w _ _ hmi
  have hs' : ({ s with ths := s.ths.set! 0 s0' } : TermRun.Cfg).ths = #[s0', s1] := by
    show s.ths.set! 0 s0' = _
    rw [h.ths]; rfl
  have hex' : SrcSem.mainExit { s with ths := s.ths.set! 0 s0' } = [] :=
    mainExit_of_notRet hs' hctl'.term hlive
  have hrun : (wakeS arch).Run s [] { s with ths := s.ths.set! 0 s0' } :=
    WakeM0Src.localRunS_run_source_0 (P := srcPo 2 arch wakeSrc) rfl hr.toS h.s0_get rfl rfl hpt0.2.2.1
      hpt0.2.1 hpt0.2.2.2.2.2.1 hex'
  refine ⟨_, hrun, post_frame0' (s := s) (ts' := ts) (tp' := tp) (sp' := sp) hC hPT0 hKR h.th hs' rfl rfl h.pt1 h.prot h.kr
    (.inl rfl) ⟨rfl, rfl, rfl⟩ ?_ hpre ?_ hlive⟩
  · refine core0_same h.core (by simp) hp rfl hb hcov h.core.scov0 ?_ ?_ ?_ hnp
    · simp only [ite_true, hown, WakeOwn.wakeOwn]; intro L v h0; simp at h0
    · intro L v v' h0; simp [hown, WakeOwn.wakeOwn] at h0
    · intro L v h0; simp [hown, WakeOwn.wakeOwn] at h0
  · exact ⟨.inl (hc'eq ▸ hmi), hpt0.2.1, hpt0.2.2.1, hctl'.term, hctl'.env, hpt0.2.2.2.2.2.1, hpt0.2.2.2.2.2.2⟩

/-- info: 'Spike.Lib.WakeM0.post_keep0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_keep0

end Spike.Lib.WakeM0
