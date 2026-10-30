/-
**wake.w on AArch64: the `spawn` obligation** (`WakeObligations.spawn`):
main's `clone` into slot 1 is the source `spawn`, a source run with no
observable event to `Post` after `afterClone`.

The obligation is assembled from parts, each a named hypothesis of
`spawn_of` with its owner:

- the pre side at the clone (`hpre`, owner: the pre-spawn half): the
  clone is main's (`tid = 0`), the source run to the spawned configuration,
  and the one-thread facts `post_startW` reads (`SpawnPre`): `Inv1` and the
  memory facts, the flag's last write, the source threads' promises and
  views, the spawned worker's source thread, the kernel state for `KR`;
- main's relation at the parent (`hmain`, owner: main's side;
  `MainAfter.main_closed_wake` into `Mi`);
- the worker at the child (`hwork`, owner: the worker's side): the child
  in `Wi`, before its pass on both sides, its source views before the
  spawn (`HelloProt.helloProt_start`);
- the frozen words in both cover sets and the footprints outside the other
  thread's (`hfrz`, `hfoot`, owner: the relation's parameters).

`KR` at the clone is `WakeKR.kr_start`, `Post` is `WakeStart.post_startW`.

- `SpawnPrem`: the premises of the `spawn` field.
- `SpawnPre`: the pre side's facts at the clone.
- `spawn_of`: the `spawn` field.
-/
import Spike.Lib.WakeStart
import Spike.Lib.WakeKR

namespace Spike.Lib.WakeSpawn

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WakeT1
open Spike.Lib.WakeW1

/-- **The premises of the `spawn` field** at the clone of thread `tid` (the
`clone stack tls` call of `th`, the child's id `r`). -/
def SpawnPrem (Q : WakeRel) (Λ : Scc.Sem.Layout) (asm : String) (E : Entry) (tid : Nat) (d : Cfg)
    (s : TermRun.Cfg) (th : Thread isaLSE2) (stack tls : Nat) (r : BitVec 64) : Prop :=
  Q.R1 d s ∧ d.1.threads.size = d.2.slots.size ∧ d.1.threads[tid]? = some th ∧ abi.atSys th.st = true ∧
    d.2.runs tid = true ∧ d.2.exited = none ∧ callOf abi th = some (.clone stack tls) ∧ 0 < r.toNat ∧
    r.toNat < pidMax ∧
    CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r)

/-- **The pre side's facts at main's clone**: the one-thread facts of `d`
`post_startW` reads, at the spawned source configuration `s` (threads `s0`,
`s1`) and the ghost record `w`; the spawned worker's source thread; the
kernel state and source for `KR` (one running slot, the held list
`[(0, r1 w), (0, r0 w)]` with the handed range ending at `stack`, main's
source not returned, no observed event). -/
structure SpawnPre (Q : WakeRel) (Λ : Scc.Sem.Layout) (D : WSide Q.ι) (r0 r1 : Q.ι → Range) (w : Q.ι)
    (d : Cfg) (th : Thread isaLSE2) (stack : Nat) (s : TermRun.Cfg) (s0 s1 : TermRun.TTh)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat)
    (j : Nat) (own₀ : List (Loc × Val)) : Prop where
  SR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩
  threads : d.1.threads = #[th]
  ths : s.ths = #[s0, s1]
  inv1 : Inv1 Λ lbl lsize ts th d.1.mem s.mem
  prom : th.prom = []
  msgs : Consumer1.OwnMsgs d.1.mem
  memIn : Consumer1.MemIn Λ d.1.mem
  fits : Consumer1.MemFits d.1.mem
  memInv : MemInv (Q.G w) d.1.mem
  bnd : th.Bnd d.1.mem.last
  own : ExtRows.OwnOk own₀ d.1.mem th.prom
  sp0 : s0.promises = []
  sp1 : s1.promises = []
  scov0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc
  scov1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc
  /-- The flag's last write before the spawn is `0` ... -/
  flag : d.1.mem.read? (Q.C w).cT j = some 0
  /-- ... and no later message is to it. -/
  flagLast : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT
  /-- The spawned worker's source thread: one frame, no type variables, at
  `wkTail` with its argument `EnvBody`. -/
  st1 : s1.stack = []
  σ1 : s1.σs = []
  term1 : s1.term = wkTail
  env1 : EnvBody (D.cw w) s1.env
  /-- The kernel state for `KR`. -/
  slots : ∃ k, d.2.slots = #[.run k]
  held : d.2.held = [(0, r1 w), (0, r0 w)]
  top : (r1 w).lo + (r1 w).size = stack
  live : ∀ s0', s.ths[0]? = some s0' → s0'.term ≠ WakeMLive.wlRet
  trace : SrcSem.traceOf s = []

/-- **The `spawn` field.** -/
theorem spawn_of {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {asm : String} {E : Entry} {Q : WakeRel}
    {D : WSide Q.ι} {r0 r1 : Q.ι → Range} {P0 : Q.ι → Cfg → TermRun.Cfg → TermRun.TTh → Prop}
    (hown : Q.own = WakeOwn.wakeOwn) (hPT1 : Q.PT1 = PT1 D) (hKR : Q.KR = WakeKR.KR r0 r1)
    /- (the relation's parameters) the frozen words in both cover sets, the
    footprints outside the other thread's -/
    (hfrz : ∀ w i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ w i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    /- (the pre-spawn half: `R1` at the clone) the clone is main's, with a
    source run to the spawned configuration, the pre side's facts, and the
    facts `P0` about main's source thread `s0` that main's side reads (left
    abstract here: the instance fixes them, e.g. its frame, term,
    environment, label and control) -/
    (hpre : ∀ tid d s th stack tls r, SpawnPrem Q Λ asm E tid d s th stack tls r →
      tid = 0 ∧ ∃ s' w s0 s1 lbl lsize ts j own₀, (wakeS arch).Run s [] s' ∧
        SpawnPre Q Λ D r0 r1 w d th stack s' s0 s1 lbl lsize ts j own₀ ∧ P0 w d s' s0)
    /- (main's side: `MainAfter.main_closed_wake` into `Mi`) main's relation
    at the parent -/
    (hmain : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀, SpawnPrem Q Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' → SpawnPre Q Λ D r0 r1 w d th stack s' s0 s1 lbl lsize ts j own₀ →
      P0 w d s' s0 →
      Q.PT0 w d.1.mem s'.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    /- (the worker's side) the child in `Wi`, before its pass on both
    sides, its source views before the spawn -/
    (hwork : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀, SpawnPrem Q Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' → SpawnPre Q Λ D r0 r1 w d th stack s' s0 s1 lbl lsize ts j own₀ →
      D.Wi w (childAfter abi d.2 0 th stack tls).st (Ctl.of s1) ∧
        ¬ (Q.C w).passT (childAfter abi d.2 0 th stack tls).st ∧ ¬ (Q.C w).passS s1 ∧
        (Q.C w).mviewS s1 < (Q.SR w).S ∧ (Q.C w).obS s1 < (Q.SR w).S) :
    ∀ tid d s th stack tls (r : BitVec 64), Q.R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (afterClone abi d tid th stack tls r) s' := by
  intro tid d s th stack tls r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hP : SpawnPrem Q Λ asm E tid d s th stack tls r := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨rfl, s', w, s0, s1, lbl, lsize, ts, j, own₀, hrun, hS, hP0⟩ := hpre _ _ _ _ _ _ _ hP
  obtain ⟨hW, hpT, hpS, hmv, hob⟩ := hwork d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ hP hrun hS
  obtain ⟨k, hsl⟩ := hS.slots
  have hK : Q.KR w (afterClone abi d 0 th stack tls r) s' := by
    rw [hKR]
    exact WakeKR.kr_start hsl hS.held hS.top hS.live hS.trace
  have hT : d.1.mem.last ≤ (Q.SR w).T := by rw [hS.SR]; exact Nat.le_refl _
  have hSz : s'.mem.size ≤ (Q.SR w).S := by rw [hS.SR]; exact Nat.le_refl _
  refine ⟨s', hrun, WakeStart.post_startW hown hPT1 hS.SR hS.threads hS.ths hS.inv1 hS.prom hS.msgs hS.memIn
    hS.fits hS.memInv hS.bnd hS.own hS.sp0 hS.sp1 hS.scov0 hS.scov1 (hfrz w) (hfoot w) hS.flag hS.flagLast
    (hmain d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ hP hrun hS hP0) hW hS.st1 hS.σ1 hS.term1 hS.env1
    (helloProt_start hT hSz hpT hpS ⟨hmv, hob⟩) hK⟩

/-- info: 'Spike.Lib.WakeSpawn.spawn_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeSpawn.spawn_of

end Spike.Lib.WakeSpawn
