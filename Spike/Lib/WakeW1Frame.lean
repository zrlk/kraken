/-
**Reassembling `Post` after a worker step** (data in `Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

A step of the worker (thread 1) replaces its thread, possibly appends to
the target memory, keeps the kernel state, and runs the source worker,
possibly pushing to the source memory. Main's side (`PreC`, `PT0`, `KR`) is
kept by the frame facts of `WCompat`; the core, `PT1` and the protocol at
the new configuration are the row's.

- `withThread1`: thread 1 replaced in a two-thread configuration.
- `post_frame`: the new core, `PT1` and `HelloProt`, with the memories'
  growth (`W1Mem`), give `Post` at the new configurations.
-/
import Spike.Lib.WakeW1Compat

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.Inv2Core Spike.Lib.Inv2Read
open Spike.Lib.HelloProt

/-- **Thread 1 replaced** in a two-thread configuration. -/
theorem withThread1 {I : ISA} {c : Config I} {t0 t1 t1' : Thread I} {mem : Memory}
    (h : c.threads = #[t0, t1]) : (c.withThread 1 t1' mem).threads = #[t0, t1'] := by
  simp [Config.withThread, h]

/-- **`PreC` across a worker step**: the target memory kept or one message
appended after the spawn. -/
theorem preC_w1 {I : ISA} {P : Inv2Params I} {R : SpawnRec} {cT : Loc} {cS : WeakMem.Address} {tm tm' : Memory}
    {sm sm' : WeakMem.Memory} {vs : Views} (h : PreC R cT tm vs) (hT : R.T ≤ tm.last)
    (hm : W1Mem P cS tm sm tm' sm') : PreC R cT tm' vs := by
  rcases hm.1 with rfl | ⟨w, rfl, -, -⟩
  · exact h
  · exact h.append hT w

/-- **`Post` after a worker step**: from `Post`'s parts before (main's
thread `t0` and its source thread `s0`, `PreC`, `PT0`, `KR`, the spawn
before the memory's end), the
memories' growth, and the new core, `PT1` and protocol, with the kernel
state kept. -/
theorem post_frame {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
    (hC : WCompat Q D μ Λ arch) {w : Q.ι} {t : Cfg} {s s' : TermRun.Cfg} {t0 t1 t1' : Thread isaLSE2}
    {s0 s1' : TermRun.TTh} {mem' : Memory} {ts' : Nat → Option Nat} {tp' sp' : List Nat}
    {s1 : TermRun.TTh} (hth : t.1.threads = #[t0, t1]) (hs : s.ths = #[s0, s1]) (hs' : s'.ths = #[s0, s1'])
    (hpre : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views) (hpt0 : Q.PT0 w t.1.mem s.mem t0 s0)
    (hkr : Q.KR w t s) (hT : (Q.SR w).T ≤ t.1.mem.last)
    (hm : W1Mem (Q.P w) (Q.C w).cS t.1.mem s.mem mem' s'.mem)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1'.stack)
      mem' t0 t1' s'.mem s0 s1' ts' tp' sp')
    (hpt1 : PT1 D w mem' s'.mem t1' s1')
    (hprot : HelloProt (Q.SR w) (Q.C w) (Q.pT w) mem' t0 t1' s'.mem s0 s1' ts' tp' sp')
    (htr : s'.trace = s.trace) :
    Q.Post Λ (t.1.withThread 1 t1' mem', t.2) s' := by
  have hth' := withThread1 (t1' := t1') (mem := mem') hth
  refine ⟨w, ⟨t0, t1', s0, s1', ts', tp', sp', hth', hs', hcore, ?_, ?_, hprot⟩, ?_⟩
  · simp only [WakeRel.PTw]
    exact ⟨preC_w1 hpre hT hm, hC.pt0 w _ _ t0 s0 _ _ hpt0 hm⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    exact hpt1
  · refine hC.kr w t _ s s' hkr rfl ?_ (by rw [hs', hs]; rfl) htr
    show (t.1.withThread 1 t1' mem').threads[0]? = t.1.threads[0]?
    rw [hth', hth]; rfl

end Spike.Lib.WakeW1
