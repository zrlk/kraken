/-
**Reassembling `Post` after a step of main** (`post_step0`). The thread-0 counterpart of `Spike/Lib/WakeW1Frame.lean`.

A step of main (thread 0) replaces its thread, possibly appends one message
of its own off `cT` to the target memory, keeps the kernel state and the
source memory (main's source only loads), and runs main's source thread.
The worker's side (`PT1`, the protocol `CProt`) is kept: `PT1` reads only
the source memory and the worker's threads, `CProt` reads the target memory
only at `cT` and below its end.

- `withThread0`: thread 0 replaced in a two-thread configuration.
- `cProt_append0`: a target message off `cT` keeps `CProt`.
- `post_frame0'`: the new core, main's `PreC` and `PT0` (at `hPT0`), the
  memory kept or one message off `cT` appended, main's source off its return,
  give `Post` at the new configurations (`KR` at `hKR`).
-/
import Spike.Lib.WakeW1Frame
import Spike.Lib.WakeM0
import Spike.Lib.WakeKR

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc Spike.Lib.Inv2Core Spike.Lib.Inv2Read
open Spike.Lib.HelloProt Spike.Lib.WakeW1
open Spike.Lib.WakeMLive (wlRet MainLive)

/-- **Thread 0 replaced** in a two-thread configuration. -/
theorem withThread0 {I : ISA} {c : Config I} {t0 t1 t0' : Thread I} {mem : Memory}
    (h : c.threads = #[t0, t1]) : (c.withThread 0 t0' mem).threads = #[t0', t1] := by
  simp [Config.withThread, h]

/-- **A target message off `cT` keeps the `c` protocol.** -/
theorem cProt_append0 {I : ISA} {R : SpawnRec} {C : CRec I} {oc : Option (Nat × Nat)} {tm : Memory}
    {t1 : Thread I} {sm : WeakMem.Memory} {s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    (h : CProt R C oc tm t1 sm s1 ts tp sp) {m : Msg} (hm : m.loc ≠ C.cT) :
    CProt R C oc (tm.append m).1 t1 sm s1 ts tp sp := by
  obtain ⟨hT, hS, hl⟩ := (cProt_iff _ _ _).mp h
  refine (cProt_iff _ _ _).mpr ⟨⟨fun k w hk hTk hloc => ?_, fun Tc kc hoc => ?_, hT.prom_worker, hT.pass_done,
    hT.pass_prom⟩, hS, hl⟩
  · rcases Inv2Rely.get?_append_cases hk with ⟨-, rfl⟩ | ⟨-, hk'⟩
    · exact absurd hloc hm
    · exact hT.tmsg k w hk' hTk hloc
  · obtain ⟨h1, h2, w, hg, h3⟩ := hT.some_msg Tc kc hoc
    exact ⟨h1, h2, w, by rw [Scc.Sem.Memory.get?_append_le (Kraken.Promising.Memory.le_last_of_get? hg)]; exact hg,
      h3⟩

/-- **`Post` after a step of main**: from `Post`'s worker parts before
(`PT1`, the protocol, `KR`), the target memory kept or one message off `cT`
appended, the source memory kept, and the new core, `PreC` and `PT0`, with
the kernel state kept and main's source off its return. -/
theorem post_frame0' {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
    {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch} (hC : WCompat Q D μ Λ arch) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) {w : Q.ι} {t : Cfg} {s s' : TermRun.Cfg} {t0 t1 t0' : Thread isaLSE2}
    {s1 s0' : TermRun.TTh} {mem' : Memory} {ts' : Nat → Option Nat} {tp' sp' : List Nat}
    {oc : Option (Nat × Nat)} {ts : Nat → Option Nat} {tp sp : List Nat}
    (hth : t.1.threads = #[t0, t1]) (hs' : s'.ths = #[s0', s1]) (hsm : s'.mem = s.mem)
    (hstr : s'.trace = s.trace)
    (hpt1 : PT1 D w t.1.mem s.mem t1 s1) (hprot : CProt (Q.SR w) (Q.C w) oc t.1.mem t1 s.mem s1 ts tp sp)
    (hkr : Q.KR w t s)
    (hm : mem' = t.1.mem ∨ ∃ m : Msg, mem' = (t.1.mem.append m).1 ∧ m.loc ≠ (Q.C w).cT)
    (hbk : ts' = ts ∧ tp' = tp ∧ sp' = sp)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0'.st s0'.stack else Q.own w 1 t1.st s1.stack)
      mem' t0' t1 s'.mem s0' s1 ts' tp' sp')
    (hpre : PreC (Q.SR w) (Q.C w).cT mem' t0'.views) (hpt0 : PT0 M w mem' s'.mem t0' s0')
    (hlive : s0'.term ≠ wlRet) :
    Q.Post Λ (t.1.withThread 0 t0' mem', t.2) s' := by
  obtain ⟨rfl, rfl, rfl⟩ := hbk
  have hth' := withThread0 (t0' := t0') (mem := mem') hth
  refine ⟨w, ⟨t0', t1, s0', s1, ts', tp', sp', hth', hs', hcore, ?_, ?_, oc, ?_⟩, ?_⟩
  · simp only [WakeRel.PTw, ite_true]
    exact ⟨hpre, by rw [hPT0]; exact hpt0⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    rw [hsm]
    exact hpt1
  · rw [hsm]
    rcases hm with rfl | ⟨m, rfl, hl⟩
    · exact hprot
    · exact cProt_append0 hprot hl
  · rw [hKR] at hkr ⊢
    obtain ⟨hn, h0, h1, hh, -, htr⟩ := hkr
    refine ⟨hn, h0, h1, hh, fun _ s0'' h => ?_, by simp only [SrcSem.traceOf, hstr] at htr ⊢; exact htr⟩
    rw [hs'] at h
    cases (show some s0' = some s0'' from h)
    exact hlive

/-- info: 'Spike.Lib.WakeM0.post_frame0'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_frame0'

end Spike.Lib.WakeM0
