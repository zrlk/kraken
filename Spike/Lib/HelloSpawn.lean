/-
**hello.w on AArch64: the `spawn` obligation** (`WakeObligations.spawn`;
the twin of `Spike.Lib.WakeSpawn` and `Spike.Lib.WakeStart` at hello's
worker side `HelloW1.WSideH` and kernel relation `A64HelloWriteK.KRH`):
main's `clone` into slot 1 is the source `spawn`, a source run with no
observable event to `Post` after `afterClone`.

The obligation is assembled from parts, each a named hypothesis of
`spawn_ofH` with its owner, as `WakeSpawn.spawn_of`'s: the pre side at the
clone (`hpre`), main's relation at the parent (`hmain`), the worker at the
child (`hwork`: the child in `Wi` at the empty stack of frames, before its
pass on both sides, its store bounds), the frozen words and footprints
(`hfrz`, `hfoot`).

- `pt1_startH`: hello's worker relation `PT1h` at the spawn (given the
  buffer's `BufV`): the child in
  `Wi`, the source worker at `.tail "worker" …` on one frame with no type
  variables, in the print phase (`HelloW1.printPh_spawn`: the packet's
  words the buffer's locative, its word and byte counts, the pointer word
  `D.cw w`, main's id), no promise.
- `post_startH`: `WakeOwn.post_startO` with `Q.PT1 = PT1hE D` (at `PT1h`).
- `SpawnPreH`: the pre side's facts at the clone (`WakeSpawn.SpawnPre`'s,
  the spawned worker's at hello's packet).
- `spawn_ofH`: the `spawn` field (`KRH` at the clone by `krh_of_kr` of
  `WakeKR.kr_start`).
-/
import Spike.Lib.WakeSpawn
import Spike.Lib.HelloQ

namespace Spike.Lib.HelloSpawn

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WakeT1
open Spike.Lib.HelloW1 (WSideH PT1h printPh_spawn)
open Spike.Lib.WakeW1 (mainTidW)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.A64HelloWriteK (KRH krh_of_kr)

/-- **The spawned worker's packet**: the source worker's argument is the
slice's three words (the buffer's locative, its word count `D.mB w ≠ 0`,
its byte count `D.nB w`), the pointer word `D.cw w` and main's id. -/
def PktH {ι : Type} (D : WSideH ι) (w : ι) (env : TermRun.Env) : Prop :=
  ∃ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), env = [("a", T, [w0, w1, w2, D.cw w, w4])] ∧
    w4.val = mainTidW ∧ w0.val = .loc ⟨D.bufL w, 0⟩ 0 ∧ w1.val = .num (D.mB w) ∧ D.mB w ≠ 0 ∧
    w2.val = .num (D.nB w)

/-- **hello's worker relation at the spawn**: the child in `Wi` (empty
stack of frames), the source worker at `.tail "worker" …` on one frame
with no type variables and hello's packet, no promise on either side (so
no promise spans an `emit`: the spawn witness of `PT1h`'s clause
`s1.promises = [] ∨ NoEmit`). -/
theorem pt1_startH {ι : Type} (D : WSideH ι) (w : ι) (tm : Memory) (sm : WeakMem.Memory) {t1 : Thread isaLSE2}
    {s1 : TermRun.TTh} (hW : D.Wi w t1.st (Ctl.of s1) []) (hst : s1.stack = []) (hσ : s1.σs = [])
    (ht : s1.term = .tail "worker" [] (.var "a") []) (henv : PktH D w s1.env) (hp : s1.promises = [])
    (hp1 : t1.prom = []) (hB : HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) sm) :
    PT1h D w tm sm t1 s1 := by
  obtain ⟨T, w0, w1, w2, w4, he, hj, h0, h1, hm, h2⟩ := henv
  refine ⟨hst ▸ hW, hσ, .inl ⟨printPh_spawn hj h0 h1 hm h2 hst ht he, hB, HelloW1.pTermH_spawn ht,
    .inl hp⟩, ?_, ?_, ?_⟩
  · rw [hp]; exact Nat.zero_le _
  · intro k hk; rw [hp] at hk; cases hk
  · rw [hp1]; exact List.nodup_nil

/-- **`Post` at the clone with hello's worker relation**: `post_startO` at
`Q.PT1 = PT1hE D`, the spawned worker built by `pt1_startH` (at `PT1h`). -/
theorem post_startH {Λ : Scc.Sem.Layout} {Q : WakeRel} {D : WSideH Q.ι} (hQ : Q.own = WakeOwn.wakeOwn)
    (hQ1 : Q.PT1 = HelloEmitPh.PT1hE D) {w : Q.ι}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isaLSE2} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {own₀ : List (Loc × Val)}
    (hSR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv (Q.G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    {j : Nat} (hj : d.1.mem.read? (Q.C w).cT j = some 0)
    (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT)
    (hPT0 : Q.PT0 w d.1.mem s.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    (hW1 : D.Wi w (childAfter abi d.2 0 th stack tls).st (Ctl.of s1) []) (hst1 : s1.stack = [])
    (hσ1 : s1.σs = []) (ht1 : s1.term = .tail "worker" [] (.var "a") []) (henv1 : PktH D w s1.env)
    (hB : HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem)
    (hProt : HelloProt (Q.SR w) (Q.C w) (Q.pT w) d.1.mem (retThread abi (parentPre abi d.2 0 th stack) r)
      (childAfter abi d.2 0 th stack tls) s.mem s0 s1 ts [] [])
    (hKR : Q.KR w (afterClone abi d 0 th stack tls r) s) :
    Q.Post Λ (afterClone abi d 0 th stack tls r) s := by
  have hPT1 : Q.PT1 w d.1.mem s.mem (childAfter abi d.2 0 th stack tls) s1 := by
    rw [hQ1]
    exact .inl <| pt1_startH D w _ _ hW1 hst1 hσ1 ht1 henv1 hsp1 childAfter_prom hB
  exact WakeOwn.post_startO hQ hSR h1 hs hi hp hmsgs hin hfits hG hb hown hsp0 hsp1 hs0 hs1 hfrz hfoot hj hjl
    hPT0 hPT1 hProt hKR

/-- **The pre side's facts at main's clone** (`WakeSpawn.SpawnPre`'s, the
spawned worker's source thread at hello's packet `PktH`). -/
structure SpawnPreH (Q : WakeRel) (Λ : Scc.Sem.Layout) (D : WSideH Q.ι) (r0 r1 : Q.ι → Range) (w : Q.ι)
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
  `worker`'s tail call with hello's packet. -/
  st1 : s1.stack = []
  σ1 : s1.σs = []
  term1 : s1.term = .tail "worker" [] (.var "a") []
  env1 : PktH D w s1.env
  /-- The published buffer in the source memory at the spawn
  (`HelloW1.bufV_spawn`). -/
  buf : HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem
  /-- The kernel state for `KRH`. -/
  slots : ∃ k, d.2.slots = #[.run k]
  held : d.2.held = [(0, r1 w), (0, r0 w)]
  top : (r1 w).lo + (r1 w).size = stack
  live : ∀ s0', s.ths[0]? = some s0' → s0'.term ≠ WakeMLive.wlRet
  trace : SrcSem.traceOf s = []

/-- **The `spawn` field at hello.** -/
theorem spawn_ofH {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {asm : String} {E : Entry} {Q : WakeRel}
    {p : CoreTerm.Prog} {D : WSideH Q.ι} {r0 r1 : Q.ι → Range} {P0 : Q.ι → Cfg → TermRun.Cfg → TermRun.TTh → Prop}
    (hown : Q.own = WakeOwn.wakeOwn) (hPT1 : Q.PT1 = HelloEmitPh.PT1hE D) (hKR : Q.KR = KRHE D r0 r1)
    /- (the relation's parameters) the frozen words in both cover sets, the
    footprints outside the other thread's -/
    (hfrz : ∀ w i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ w i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    /- (the pre-spawn half: `R1` at the clone) the clone is main's, with a
    source run to the spawned configuration, the pre side's facts and the
    facts `P0` about main's source thread `s0` main's side reads -/
    (hpre : ∀ tid d s th stack tls r, SpawnPrem Q Λ asm E tid d s th stack tls r →
      tid = 0 ∧ ∃ s' w s0 s1 lbl lsize ts j own₀, (srcS p arch).Run s [] s' ∧
        SpawnPreH Q Λ D r0 r1 w d th stack s' s0 s1 lbl lsize ts j own₀ ∧ P0 w d s' s0)
    /- (main's side) main's relation at the parent -/
    (hmain : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀, SpawnPrem Q Λ asm E 0 d s th stack tls r →
      (srcS p arch).Run s [] s' → SpawnPreH Q Λ D r0 r1 w d th stack s' s0 s1 lbl lsize ts j own₀ →
      P0 w d s' s0 →
      Q.PT0 w d.1.mem s'.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    /- (the worker's side) the child in `Wi`, before its pass on both
    sides, its store bounds below the spawn -/
    (hwork : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀, SpawnPrem Q Λ asm E 0 d s th stack tls r →
      (srcS p arch).Run s [] s' → SpawnPreH Q Λ D r0 r1 w d th stack s' s0 s1 lbl lsize ts j own₀ →
      D.Wi w (childAfter abi d.2 0 th stack tls).st (Ctl.of s1) [] ∧
        ¬ (Q.C w).passT (childAfter abi d.2 0 th stack tls).st ∧ ¬ (Q.C w).passS s1 ∧
        (Q.C w).mviewS s1 < (Q.SR w).S ∧ (Q.C w).obS s1 < (Q.SR w).S) :
    ∀ tid d s th stack tls (r : BitVec 64), Q.R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (srcS p arch).Run s [] s' ∧ Q.Post Λ (afterClone abi d tid th stack tls r) s' := by
  intro tid d s th stack tls r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hP : SpawnPrem Q Λ asm E tid d s th stack tls r := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨rfl, s', w, s0, s1, lbl, lsize, ts, j, own₀, hrun, hS, hP0⟩ := hpre _ _ _ _ _ _ _ hP
  obtain ⟨hW, hpT, hpS, hmv, hob⟩ := hwork d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ hP hrun hS
  obtain ⟨k, hsl⟩ := hS.slots
  have hK : Q.KR w (afterClone abi d 0 th stack tls r) s' := by
    rw [hKR]
    refine ⟨krh_of_kr (WakeKR.kr_start hsl hS.held hS.top hS.live hS.trace),
      Spike.Lib.HelloKRE.lk_wr0 (by simp [afterClone, KState.wr, hsl]) fun t1 s1' ht hs => ?_⟩
    -- the worker at thread 1 is the child, in `Wi` (`hwork`)
    have ht' : t1 = childAfter abi d.2 0 th stack tls := by
      simp [afterClone, hS.threads] at ht; exact ht.symm
    have hs' : s1' = s1 := by rw [hS.ths] at hs; simpa using hs.symm
    subst ht' hs'
    rw [hS.st1]; exact hW
  have hT : d.1.mem.last ≤ (Q.SR w).T := by rw [hS.SR]; exact Nat.le_refl _
  have hSz : s'.mem.size ≤ (Q.SR w).S := by rw [hS.SR]; exact Nat.le_refl _
  refine ⟨s', hrun, post_startH hown hPT1 hS.SR hS.threads hS.ths hS.inv1 hS.prom hS.msgs hS.memIn
    hS.fits hS.memInv hS.bnd hS.own hS.sp0 hS.sp1 hS.scov0 hS.scov1 (hfrz w) (hfoot w) hS.flag hS.flagLast
    (hmain d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ hP hrun hS hP0) hW hS.st1 hS.σ1 hS.term1 hS.env1
    hS.buf
    (helloProt_start hT hSz hpT hpS ⟨hmv, hob⟩) hK⟩

/-- info: 'Spike.Lib.HelloSpawn.spawn_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_ofH

end Spike.Lib.HelloSpawn
