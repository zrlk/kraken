/-
**hello.w on x86-64: the spawn obligation at hello's relation** (the twin of `Spike/Lib/HelloSpawnR.lean`; x86-64
wake's `X64WakeSpawnR`'s `PreR` / `HPre` / `HView` / `spawn_R` at `X64HelloQ.helloQ`, generic in the records `ι`
and the worker side `D`): `spawn_RH`, the `spawn` hypothesis of hello's assembly, from the pre-spawn segment end
(`HPreH`), main's invariant at the parent (`HMainRH`), the child in the worker side's invariant (`HWiH`) and the
target store point (`hpass`, `WCompatH.pass`).

- `PreRH`: the pre side's facts at main's clone: `X64HelloSpawn.SpawnPreH` at the record `w`, `w`'s flag at
  `c`'s address `⟨l, 0⟩`, main's source thread `s0`'s `PT0` facts (`X64WakeM0.PT0` but `Mi`), and
  `X64WakeSpawnLt.LtPre` (the run shape and the spawn's stack bound), main at its `clone`
  (`X64HelloPreA.ClonePreH` at the record's ranges), and the spawned configuration as main's `spawn` at hello's
  packet (`hsp`).
- `HPreH` (the pre-spawn segment end; `X64HelloHPre`), `HMainRH` (main's `Mi` past the clone; open), `HWiH` (the
  child in `D.Wi` at the empty stack of frames; the worker segment's entry).
- `FrP`: the type of what `HPreH` adds at the clone besides `PreRH` and `HMainRH`/`HWiH` assume (hello's instance:
  main's source thread and the invariant at the clone); a parameter because `PreRH` has no data.
- `hViewH`: the worker's store bounds at `PreRH` (`X64HelloSpawnLt.hview_RH` at `PktH`'s pointer word).
- `spawn_RH`: the `spawn` field, `Post` by `X64HelloSpawn.post_startH` (each thread owning its TCB self word,
  both words in the clone's own list by `SpawnPreH.self`).

**Where this differs from AArch64** (forced by the x86-64 shape): the threads are over `X64.isa`, the assembly an
`Scc.Sem.X64.Asm` and the certificate's architecture `Arch.tso` (AArch64: `isaLSE2`, a `String`, `Arch.armv8`, as
`X64WakeSpawn.SpawnPrem`); `ClonePreH` takes no label prefix (x86-64 labels are not numbered per program,
`X64HelloPreA`); the packet type `pktTy` is `X64HelloSplit`'s; the worker side, kernel relation and spawn pieces are
the x86-64 twins (`X64HelloW1`, `X64HelloWriteK.krh_of_kr`, `X64HelloKRE.lk_wr0`, `X64WakeKR.kr_start`,
`X64HelloSpawn`, `X64HelloSpawnLt`). The statements and proofs are otherwise the AArch64 ones.
-/
import Spike.Lib.X64HelloSpawn
import Spike.Lib.X64HelloSpawnLt
import Spike.Lib.X64HelloClonePreH
import Spike.Lib.X64HelloW1Print

namespace Spike.Lib.X64HelloSpawnR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.X64WakeT1
open Spike.Lib.X64HelloSrc (helloS)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64HelloSpawn (SpawnPreH PktH post_startH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakeM0 (MTerm EnvC)
open Spike.Lib.X64HelloWriteK (krh_of_kr)

/-- The type of `HPreH`'s extra clone facts `Fr lbl lsize th s` (see the module doc). -/
abbrev FrP : Type :=
  (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Thread isa → TermRun.Cfg → Prop

section Inst

variable {ι : Type} (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (SR : ι → SpawnRec)
  (cT : ι → Loc) (cS : ι → WeakMem.Address) (pT : ι → Loc) (Pa : ι → Inv2Params isa)
  (G : ι → Loc → Val → Prop) (passT : State → Prop) (M : X64WakeM0.MSide ι) (D : WSideH ι) (r0 r1 : ι → Range)
  (Λ : Scc.Sem.Layout) (asm : Scc.Sem.X64.Asm) (E : Entry) (Fr : FrP)

/-- **The pre side's facts at main's clone** (see the module doc). -/
structure PreRH (w : ι) (d : Cfg) (th : Thread isa) (stack : Nat) (s s' : TermRun.Cfg) (s0 s1 : TermRun.TTh)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat)
    (j : Nat) (own₀ : List (Loc × Val)) (l : WeakMem.AllocLabel) : Prop where
  pre : SpawnPreH (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ D r0 r1 w d th stack s' s0 s1 lbl lsize
    ts j own₀
  hcS : cS w = ⟨l, 0⟩
  stack0 : s0.stack = []
  σ0 : s0.σs = []
  term0 : MTerm s0.term
  env0 : EnvC (M.cw w) s0.env
  prom0 : s0.promises = []
  tid0 : s0.tidLbl = some (mainTidLbl 2)
  hlt : ∃ T, X64WakeSpawnLt.LtPre s s' l T
  /-- main at its `clone` (`wc_main`'s clone, `X64HelloPreA.cloneAtH`), over the
  record's ranges: where main's invariant past the clone starts (`HMainRH`). -/
  clone : ∃ X, X64HelloPreA.ClonePreH Λ (r0 w) (r1 w) X lbl d s
  /-- The spawned configuration is main's `spawn` of `worker` at hello's
  packet, from its one source thread with `c` bound to `⟨l, 0⟩` (wake's
  `PreR.hc` and `PreR.hsp`). -/
  hsp : ∃ th0 ws, s.ths = #[th0] ∧
    TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    s' = TermSpawnStep.spawnCfg s 0 th0 "t" X64WakeM0.mTail "worker" [] X64HelloSplit.pktTy ws
  /-- The flag's target word is `c`'s placed word (the record's, `hrec`). -/
  hcT : cT w = Scc.Sem.wordLoc ((lbl l).getD 0 + 8 * 0)
  /-- `c`'s label holds a word (a source message to `⟨l, 0⟩` before the
  spawn, `MemRelP.lbl_mem`). -/
  hlsz : 0 < lsize l

/-- **The pre-spawn segment's end**: at the clone of thread `tid`, `tid =
0`, a source run to the spawned configuration and `PreRH`. -/
def HPreH : Prop :=
  ∀ tid d s th stack tls r,
    SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E tid d s th stack tls r →
    tid = 0 ∧ ∃ s' w s0 s1 lbl lsize ts j own₀ l, (helloS arch).Run s [] s' ∧
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l ∧
      Fr lbl lsize th s

/-- **main's invariant past the clone** (open; the twin of
`WakeSpawnR.HMainR`'s conclusion, `main_closed_ws` into `Mi`). -/
def HMainRH : Prop :=
  ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
    SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
    (helloS arch).Run s [] s' →
    PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
    Fr lbl lsize th s →
    M.Mi w (retThread abi (parentPre abi d.2 0 th stack) r).st (Ctl.of s0)

/-- **The child in the worker side's invariant** (open; the worker's segment
entry, `X64HelloWorkerRR.helloDR_entry` at the child's state). -/
def HWiH : Prop :=
  ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
    SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
    (helloS arch).Run s [] s' →
    PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
    Fr lbl lsize th s →
    D.Wi w (childAfter abi d.2 0 th stack tls).st (Ctl.of s1) []

/-- **The worker's store bounds at `PreRH`** (`hview_RH`). -/
theorem hViewH {w : ι} {d : Cfg} {th : Thread isa} {stack : Nat} {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {j : Nat} {own₀ : List (Loc × Val)} {l : WeakMem.AllocLabel}
    (hR : PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l) :
    ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).C w).mviewS s1 <
        ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).SR w).S ∧
      ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).C w).obS s1 <
        ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).SR w).S := by
  obtain ⟨T', w0, w1, w2, w4, he, -⟩ := hR.pre.env1
  obtain ⟨T, hlt⟩ := hR.hlt
  have hS : (SR w).S = s'.mem.size := by
    have := congrArg SpawnRec.S hR.pre.SR
    exact this
  exact X64HelloSpawnLt.hview_RH hS hR.hcS hR.pre.ths he (by simp) hlt

/-- **The `spawn` hypothesis at `helloQ`** (see the module doc). -/
theorem spawn_RH
    /- (the relation's parameters) the frozen words in both cover sets, the
    footprints outside the other thread's -/
    (hfrz : ∀ w i l, i < 2 → (Pa w).frz l → (Pa w).cov i l)
    (hfoot : ∀ w i j l, i < 2 → j < 2 → i ≠ j → (Pa w).foot j l → ¬ (Pa w).cov i l)
    /- (`WCompatH.pass`) the target store point -/
    (hpass : X64HelloW1.PassH D passT)
    /- each thread owns its TCB self word, `T` main's and `W` the worker's (`post_startH`'s
    `Q.own = wakeOwnXW T W`), distinct, each in its thread's cover set -/
    {T W : BitVec 64} (hown : (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).own = X64WakeOwnX.wakeOwnXW T W)
    (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩) (hcovT : ∀ w, (Pa w).cov 0 ⟨T, 8⟩) (hcovW : ∀ w, (Pa w).cov 1 ⟨W, 8⟩)
    /- the pre-spawn segment's end -/
    (hpre : HPreH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E Fr)
    /- OPEN: main's invariant past the clone -/
    (hMainR : HMainRH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E Fr)
    /- the child's entry -/
    (hWi : HWiH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E Fr) :
    ∀ tid d s th stack tls (r : BitVec 64), (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).R1 d s →
      d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th → abi.atSys th.st = true →
      d.2.runs tid = true → d.2.exited = none → callOf abi th = some (.clone stack tls) → 0 < r.toNat →
      r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (helloS arch).Run s [] s' ∧
        (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).Post Λ (afterClone abi d tid th stack tls r) s' := by
  intro tid d s th stack tls r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hP : SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E tid d s th stack tls r :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨rfl, s', w, s0, s1, lbl, lsize, ts, j, own₀, l, hrun, hR, hFr⟩ := hpre _ _ _ _ _ _ _ hP
  have hS := hR.pre
  have hmi := hMainR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  have hW1 := hWi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR hFr
  have hlt := hViewH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ hR
  have hPT0 : (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).PT0 w d.1.mem s'.mem
      (retThread abi (parentPre abi d.2 0 th stack) r) s0 :=
    ⟨.inl hmi, hR.stack0, hR.σ0, hR.term0, hR.env0, hR.prom0, hR.tid0⟩
  have hpT : ¬ ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).C w).passT
      (childAfter abi d.2 0 th stack tls).st := by
    show ¬ passT _
    have hph : X64HelloW1.PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 := by
      obtain ⟨T, w0, w1, w2, w4, he, hj, h0, h1, hm, h2⟩ := hS.env1
      exact X64HelloW1.printPh_spawn hj h0 h1 hm h2 hS.st1 hS.term1 he
    rw [hpass w _ s1 (by rw [hS.st1]; exact hW1) (.inl hph)]
    simp [WorkerSrc.WPass, hS.term1, WorkerSrc.wkUnpark]
  have hpS : ¬ ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).C w).passS s1 := by
    show ¬ WorkerSrc.WPass s1
    simp [WorkerSrc.WPass, hS.term1, WorkerSrc.wkUnpark]
  obtain ⟨k, hsl⟩ := hS.slots
  have hK : (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).KR w (afterClone abi d 0 th stack tls r) s' :=
    ⟨krh_of_kr (X64WakeKR.kr_start hsl hS.held hS.top hS.live hS.trace),
      X64HelloKRE.lk_wr0 (by simp [afterClone, KState.wr, hsl]) fun t1 s1' ht hs => by
        -- the worker at thread 1 is the child, in `Wi` (`hWi`)
        have ht' : t1 = childAfter abi d.2 0 th stack tls := by
          simp [afterClone, hS.threads] at ht; exact ht.symm
        have hs' : s1' = s1 := by rw [hS.ths] at hs; simpa using hs.symm
        subst ht' hs'
        rw [hS.st1]; exact hW1⟩
  have hT : d.1.mem.last ≤ ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).SR w).T := by
    rw [hS.SR]; exact Nat.le_refl _
  have hSz : s'.mem.size ≤ ((helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).SR w).S := by
    rw [hS.SR]; exact Nat.le_refl _
  -- both self words at the clone (`SpawnPreH.self`) join the clone's own list
  have hSW := hS.self T W hown
  exact ⟨s', hrun, post_startH hown hTW rfl hS.SR hS.threads hS.ths hS.inv1 hS.prom hS.msgs
    hS.memIn hS.fits hS.memInv hS.bnd (X64HelloSelfWords.ownOk_selfPairs hS.own hSW)
    (X64HelloSelfWords.selfPairs_T own₀) (X64HelloSelfWords.selfPairs_W own₀) (hcovT w) (hcovW w)
    hS.sp0 hS.sp1 hS.scov0 hS.scov1 (hfrz w) (hfoot w) hS.flag hS.flagLast
    hPT0 hW1 hS.st1 hS.σ1 hS.term1 hS.env1 hS.buf (HelloProt.helloProt_start hT hSz hpT hpS hlt) hK⟩

end Inst

/-- info: 'Spike.Lib.X64HelloSpawnR.spawn_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_RH

end Spike.Lib.X64HelloSpawnR

/-- info: 'Spike.Lib.X64HelloSpawnR.hViewH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSpawnR.hViewH
