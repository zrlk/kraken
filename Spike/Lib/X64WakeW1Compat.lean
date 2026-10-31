/-
**The worker's compatibility facts** (hello plan 1.6): what the
worker's steps after the spawn (`post_step1`, `unpark_src`) need of the
rest of the proof's data, as one hypothesis `WCompat`, one field per
fact.

- `W1Mem`: how a worker step changes the two memories (target: unchanged or
  one message of thread 1 in its footprint; source: unchanged or one message
  to `c`).
- `WCompat Q D μ Λ arch`: the relation `Q`'s data against the worker's side
  `D` (`Spike.Lib.X64WakeW1.WSide`).

x86-64 twin of `Spike/Lib/WakeW1Compat.lean` (same names, namespaces with the
`X64` prefix).

Difference from AArch64: `WCompatX.own1 : ∀ w s,
Q.own w 1 s [] = []` is replaced by `ownConst1` and `ownMp1` (as
`X64WakeM0Compat`'s `own0` change), so that the worker may own its TCB word
`tcbW` (`X64WakeOwnX.wakeOwnXW`). Followed in `X64WakeW1Prom` (`CInv`'s new
fields `own`, `cov`) and `X64WakeW1Unpk`.
-/
import Spike.Lib.X64WakeW1
import Spike.Lib.Consumer1
import Spike.Lib.X64Ext

namespace Spike.Lib.X64WakeW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.WorkerSrc Spike.Lib.Inv2Core

/-- **How a worker step changes the memories**: the target memory is kept
or gets one message of thread 1 in its footprint; the source memory is kept
or gets one message to the flag's source address `cS`. -/
def W1Mem {I : ISA} (P : Inv2Params I) (cS : WeakMem.Address) (tm : Memory) (sm : WeakMem.Memory)
    (tm' : Memory) (sm' : WeakMem.Memory) : Prop :=
  (tm' = tm ∨ ∃ w : Msg, tm' = (tm.append w).1 ∧ w.tid = 1 ∧ P.foot 1 w.loc) ∧
    (sm' = sm ∨ ∃ m : WeakMem.Msg, sm' = sm.push m ∧ m.loc = cS)

/-- **The worker's compatibility facts**, per ghost record `w`. `μ` is the loaded program's marks,
`Λ` the layout, `arch`
the source architecture. -/
structure WCompat (Q : WakeRel) (D : WSide Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) :
    Prop where
  /-- `WakeRel`'s worker data is this file's. -/
  pt1 : Q.PT1 = PT1 D
  atUnpk : Q.atUnpk = atUnpk
  atTexit : Q.atTexit = atTexit
  /-- The rows' placement is the spawn's. -/
  lbl : ∀ w, D.lbl w = (Q.SR w).lbl
  /-- The rows' kernel model is the machine's. -/
  K : ∀ w, (D.ms w).K = some abi
  /-- The rows' runtime invariant is the relation's. -/
  G : ∀ w, (D.ms w).G = Q.G w
  /-- The rows' owned words are the worker's (empty stack). -/
  own : ∀ w s, (D.ms w).own s = Q.own w 1 s []
  /-- A word the worker may write as the runtime's is in its
  footprint, outside every label placed at the spawn, in a shared region. -/
  mpW : ∀ w L, (D.ms w).mp L true →
    (Q.P w).foot 1 L ∧ ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize L ∧ Consumer1.LocIn Λ.shared L
  /-- The worker's states are in the wide fragment. -/
  wide : ∀ w s c, D.Wi w s c → Scc.Cert.WideX64.WideSt s
  /-- The worker is at no transfer site. -/
  noSite : ∀ w s c, D.Wi w s c → siteAt abi μ s = none
  /-- (`Spike.Lib.X64.SvcFault.sysExec_of_exe`, `Lower.X64.exec_syscall` at the row's `syscall` cell) At a system call
  the worker's instruction, if any, faults: only the system-call rows
  (`Out.sys`, `OutT.texit`) apply there. -/
  sysExec : ∀ w s c t, D.Wi w s c → abi.atSys s = true → isa.exec s = some t → ∃ m, t = .fault m
  /-- The worker's system calls other than `exit` are neither
  `write` nor `exit_group`. -/
  sysOk : ∀ w s c call, D.Wi w s c → abi.atSys s = true → decode abi.nrs (abi.nr s) (abi.arg s) = some call →
    call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)
  /-- The worker's instructions keep its owned words
  (`Consumer1.OwnTree`) ... -/
  ownInstr : ∀ w s c tree, D.Wi w s c → abi.atSys s = false → isa.exec s = some tree →
    Consumer1.OwnTree (fun s => Q.own w 1 s []) (Q.own w 1 s []) tree
  /-- ... and so do its system calls' returns ... -/
  ownSys : ∀ w s c call, D.Wi w s c → abi.atSys s = true → decode abi.nrs (abi.nr s) (abi.arg s) = some call →
    ∀ s' ∈ certSuccs abi s call, Q.own w 1 s' [] = Q.own w 1 s []
  /-- ... which are in its cover set ... -/
  ownCov : ∀ w s L v, (L, v) ∈ Q.own w 1 s [] → (Q.P w).cov 1 L
  /-- ... and none of main's. -/
  ownDisj : ∀ w s0 fs s L v v', (L, v) ∈ Q.own w 0 s0 fs → (L, v') ∈ Q.own w 1 s [] → False
  /-- The flag's record is hello's, at the worker's pointer
  word `D.cw w` for `c`. -/
  C : ∀ w, Q.C w = helloC (Q.C w).cT (Q.C w).cS (Q.C w).passT Promises.Knobs.all arch (D.cw w)
  /-- (spawn rows) The pointer word is an untagged locative to `cS`. -/
  cwv : ∀ w, (D.cw w).val = .loc (Q.C w).cS 0
  /-- (`rfl` at the instantiation `D.S w := (Q.SR w).S`)
  The worker side's spawn size is the spawn record's source size
  (`SpawnRec.S`). -/
  S : ∀ w, D.S w = (Q.SR w).S
  /-- `cT` is the word placed for `cS` at the spawn, in a shared
  region and in the worker's footprint; `cS` is not frozen. -/
  cT : ∀ w, ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
    (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label
  cTin : ∀ w, Consumer1.LocIn Λ.shared (Q.C w).cT
  cTfoot : ∀ w, (Q.P w).foot 1 (Q.C w).cT
  cSfrz : ∀ w, ¬ (Q.P w).frzS (Q.C w).cS
  /-- The source memory is not empty at the spawn (the
  promise of `c` at view `S - 1`, G3). -/
  Spos : ∀ w, 0 < (Q.SR w).S
  /-- (`WakeLocs.OK`) The worker's footprint meets the placed labels
  only at `cT`. -/
  footLab : ∀ w L, (Q.P w).foot 1 L → InLabel (Q.SR w).lbl (Q.SR w).lsize L → L = (Q.C w).cT
  /-- The target store point is the source one under the rows'
  invariant. -/
  pass : ∀ w s c, D.Wi w s c → ((Q.C w).passT s ↔ (c.term = wkUnpark ∨ c.term = .ret .unit))
  /-- (`WakeP.noProm_prom`) A certified worker at a no-promise state has
  no promise. -/
  noProm : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
    CertOkC Arch.tso (certSem abi Arch.tso μ x 1) 1 t mem → t.prom = []
  /-- main has not returned while the process runs ... -/
  mainLive : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = []
  /-- ... and main's source thread id is its own. -/
  tid0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.tidLbl = some (mainTidLbl 2)
  /-- main's per-thread relation is stable under a worker step. -/
  pt0 : ∀ w tm sm t0 s0 tm' sm', Q.PT0 w tm sm t0 s0 → W1Mem (Q.P w) (Q.C w).cS tm sm tm' sm' →
    Q.PT0 w tm' sm' t0 s0
  /-- (`kr_frame1`) The kernel relation is stable under a step of the
  worker that keeps the kernel state, main's target and source threads and
  the source trace (the trace premise). -/
  kr : ∀ w t t' s s', Q.KR w t s → t'.2 = t.2 → t'.1.threads[0]? = t.1.threads[0]? → s'.ths[0]? = s.ths[0]? →
    s'.trace = s.trace → Q.KR w t' s'

/-- **The worker's compatibility facts: additions to `WCompat`**. -/
structure WCompatX (Q : WakeRel) (D : WSide Q.ι) : Prop where
  /-- The worker's flag store value `1` is a `G` value at `cT`. -/
  Gc : ∀ w, Q.G w (Q.C w).cT 1
  /-- (x86-64, replacing `own1 : ∀ w s,
  Q.own w 1 s [] = []`, as `WCompat0.own0`'s change) the worker's owned words
  do not depend on its state (`rfl` at `X64WakeOwn.wakeOwn`,
  `X64WakeOwn.ownConst1`, and at `X64WakeOwnX.wakeOwnXW`, `ownConst1XW`; on
  x86-64 the worker may own its TCB word `tcbW`) ... -/
  ownConst1 : ∀ w s s', Q.own w 1 s' [] = Q.own w 1 s []
  /-- (with `ownConst1`) ... and it never writes one as the
  runtime's (`X64WakeOwn.ownMp1`, `X64WakeOwnX.ownMp1XW`); they are in its
  cover set by `WCompat.ownCov`. -/
  ownMp1 : ∀ w s L v, (L, v) ∈ Q.own w 1 s [] → ¬ (D.ms w).mp L true
  /-- (`WakeM0.PT0.promises_nil`) main's source thread has no promise
  after the spawn (the worker's fulfilment erases its `kc` from `sp`). -/
  sp0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.promises = []
  /-- (`WakeM0.pt0_permit`, a congruence: `PT0` does not read the
  permit) main's per-thread relation is stable under a worker step that
  also sets main's source permit (the source `unpark`). -/
  pt0p : ∀ w tm sm t0 s0 tm' sm' (p : Option Nat), Q.PT0 w tm sm t0 s0 →
    W1Mem (Q.P w) (Q.C w).cS tm sm tm' sm' → Q.PT0 w tm' sm' t0 { s0 with permit := p }
  /-- (a congruence of `kr_frame1`: `KR` reads only main's source
  term) the kernel relation is stable under a worker step that keeps the
  kernel state, main's target thread and the source trace and sets main's
  source permit (the trace premise). -/
  krp : ∀ w t t' s s' (s0 : TermRun.TTh) (p : Option Nat), Q.KR w t s → t'.2 = t.2 →
    t'.1.threads[0]? = t.1.threads[0]? → s.ths[0]? = some s0 → s'.ths[0]? = some { s0 with permit := p } →
    s'.trace = s.trace → Q.KR w t' s'

end Spike.Lib.X64WakeW1
