/-
**hello.w on AArch64: the worker's certified promises in the print phase**
(C4, row B8-gen1-prom; the twin of `Spike/Lib/WakeW1Prom.lean` at `PartsH`,
the rows frame-aware as in `Spike/Lib/HelloStep1D.lean`).

A promise of the worker is certified by a run of the worker alone under the
certification semantics. From the worker's invariant (`CInvH`: `Wi` at a
source thread in a phase, `PhH`, with the `G` values of the messages not
promised) every step of that run is one of the frame-aware rows
(`WSideH.closed`): after a frame run of the source worker, it keeps memory
and promises, or writes a `Good` message; it writes `cT` only at the store,
from before the store point (`cstep_shapeH`). So every promise the run
fulfils is `Good`, and the run fulfils at most one promise of `cT`, none
past the store (`cstepH`). In the print phase a certified promise is then
out of every placed label (the source stutters) or the promise of `c`'s `1`
with no `c` message yet: the source worker promises `kc`, certified by the
run through `print` (`certified_printPh`; `post_prom1H`). That run exists
since the target's certification passes `print`'s return before any `emit`
(`noEmit_of_certOkC`: with an `emit` ahead the `cT` promise is never
fulfilled; WeakCore 621ec97a, no promise spans an emit).

- `PhH`, `phase_endH`, `ctl_atQ`, `exclH`: the phases a frame run from a
  phase reaches, and the rows excluded there.
- `EmitAhead`, `emitAhead_or_noEmit`, `noEmit_of_leave`, `emitAhead_frameRun`:
  an `emit` ahead or none, kept by frame runs.
- `bufV_push`: the buffer fact after a message to `c`.
- `CInvH`, `ShapeH`: the certification run's invariant and one step's shape.
- `cstep_shapeH`, `cstepH`: one certification step from `CInvH`.
- `CInvE`, `cstepE`, `noEmit_of_certOkC`: the refutation, no certified
  `cT` promise with an `emit` ahead.
- `cTinH`, `cInvH_prom`: `CInvH` at the promising configuration.
- `prom_goodH`: a certified promise is `Good`, with the potential bound.
- `post_prom1H`: `HelloStep1P.PromStepP`, the promise row in the print
  phase keeps `Post` (with `hms`, `hown` as `HelloStep1D.printStep1_of`).
-/
import Spike.Lib.HelloStep1D
import Spike.Lib.WakeW1Prom

namespace Spike.Lib.HelloProm1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh StorePh BufV WCompatH post_frameH storePh_not_printPh
  printPh_not_pass certified_printPh)
open Spike.Lib.HelloW1Store (NoWrite relW envCJ_consW)
open Spike.Lib.HelloAssembly (HelloCompat)
open Spike.Lib.HelloStep1P (atQ phase_frameRun pTermH_frameRun PromStepP)
open Spike.Lib.HelloStep1D (okOp okE okE_pTermT)
open Spike.Lib.WakeT1 (srcPo)
open Spike.Lib.WakeOwn (wakeOwn)
open Spike.Lib.WakeW1 (Good cntT passB countP_erase_le countP_erase_of_false certOkC_pot stepOne_rmw_casesG
  stepOne_silent_keep stepOne_load_keep inLabel_wordLoc envCJ_cons EnvCJ)

/-! ## The phases under frame runs -/

section Phase

variable {ι : Type} {D : WSideH ι} {w : ι}

/-- **The worker's phases**: the print phase at a print-phase term, or the
store phase. -/
abbrev PhH (D : WSideH ι) (w : ι) (s1 : TermRun.TTh) : Prop :=
  (PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 ∧ HelloW1.PTermH s1) ∨ StorePh (D.cw w) s1

/-- **A frame run from a phase** ends in a phase, past the store point iff
its start is. -/
theorem phase_endH {cS : WeakMem.Address} (hcv : (D.cw w).val = .loc cS 0) {s1 : TermRun.TTh} (hph : PhH D w s1)
    {q' : Ctl × List TermRun.Frame} (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') :
    PhH D w (atQ s1 q') ∧ (WPass (atQ s1 q') ↔ WPass s1) := by
  obtain ⟨h1, -, h3⟩ := phase_frameRun hcv hr rfl rfl (hph.imp_left And.left)
  refine ⟨?_, h3⟩
  rcases h1 with hP' | hS'
  · exact .inl ⟨hP', pTermH_frameRun hcv hr rfl rfl hph hP'⟩
  · exact .inr hS'

/-- The source thread at a frame run's end has the run's control. -/
theorem ctl_atQ {s1 : TermRun.TTh} {q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') : Ctl.of (atQ s1 q') = q'.1 := by
  have hh : q'.1.hold = none := hr.hold_none rfl
  obtain ⟨⟨_, _, _⟩, _⟩ := q'
  simp only at hh
  subst hh
  rfl

/-- **The rows excluded in a phase**: a `let` of an operation print-phase
terms do not bind, other than a store and an `unpark`. -/
theorem exclH {s1 : TermRun.TTh} {c₁ : Ctl} {fs₁ : List TermRun.Frame} (hE : PhH D w (atQ s1 (c₁, fs₁)))
    {x : String} {op : Op} {e : Expr} (ht : c₁.term = .let_ x op e) (hop : okOp op = false)
    (hns : ∀ a b o, op ≠ .store true a b o) (hnu : ∀ a, op ≠ .ext .unpark a) : False := by
  rcases hE with ⟨-, hT⟩ | ⟨-, hw, -⟩
  · have h1 : okE c₁.term = true := okE_pTermT hT
    rw [ht] at h1
    simp [okE, hop] at h1
  · have hw' : c₁.term = wkStore ∨ c₁.term = wkUnpark ∨ c₁.term = .ret .unit := hw
    rcases hw' with hw' | hw' | hw' <;> rw [hw'] at ht
    · simp only [wkStore, Expr.let_.injEq] at ht
      exact hns _ _ _ ht.2.1.symm
    · simp only [wkUnpark, Expr.let_.injEq] at ht
      exact hnu _ ht.2.1.symm
    · cases ht

end Phase

/-! ## No `emit` ahead: the dichotomy and the passage -/

section NoEmitPh

variable {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {cS : WeakMem.Address}

/-- **An `emit` ahead**: in the print phase with no frame run to `print`'s
return (`NoEmit`), i.e. a byte's load and `emit` still to come. -/
def EmitAhead (l : WeakMem.AllocLabel) (n m : Nat) (cw : TermRun.Word) (s1 : TermRun.TTh) : Prop :=
  PrintPh l n m cw s1 ∧ ¬ HelloW1.NoEmit cw s1

/-- **The dichotomy**: in the print phase, an `emit` ahead or none. -/
theorem emitAhead_or_noEmit {s1 : TermRun.TTh} (h : PrintPh l n m cw s1) :
    EmitAhead l n m cw s1 ∨ HelloW1.NoEmit cw s1 := by
  by_cases hN : HelloW1.NoEmit cw s1
  · exact .inr hN
  · exact .inl ⟨h, hN⟩

/-- **A `ret` in the print phase** is `print`'s `ret ()`, on its call's
frame. -/
theorem ret_of_printPh {s1 : TermRun.TTh} {a : At} (h : PrintPh l n m cw s1) (ht : s1.term = .ret a) :
    a = .unit ∧ ∃ w0 w1 w2 w4 : TermRun.Word, w4.val = WakeW1.mainTidW ∧
      s1.stack = [HelloW1.uFrame w0 w1 w2 cw w4] := by
  obtain ⟨w0, w1, w2, w4, hj, -, -, -, -, ⟨-, hr⟩ | ⟨hst, a', hr, ha⟩⟩ := h
  · rcases HelloW1.localRunS_cases hr with he | ⟨c₁, hl⟩
    · have h' : s1.term = HelloSplit.workerCallH := congrArg Ctl.term he
      rw [h'] at ht
      simp [HelloSplit.workerCallH] at ht
    · exact (hl.not_ret a ht).elim
  · rcases HelloW1.localRunS_cases hr with rfl | ⟨c₁, hl⟩
    · obtain ⟨⟨k, -, hk⟩ | ⟨k, mw, b, -, hk⟩ | ⟨ht', -⟩, -⟩ := ha
      · have h' := congrArg Ctl.term hk
        simp only [Ctl.of] at h'
        rw [ht] at h'
        simp [HelloPrintSrcPub.ldCP] at h'
      · have h' := congrArg Ctl.term hk
        simp only [Ctl.of] at h'
        rw [ht] at h'
        simp [HelloPrintSrcPub.emitCP, PrintSrc.printEmit] at h'
      · have h' : s1.term = .ret .unit := ht'
        rw [ht] at h'
        cases h'
        exact ⟨rfl, w0, w1, w2, w4, hj, hst⟩
    · exact (hl.not_ret a ht).elim

/-- **The passage**: a frame run from the print phase that leaves it passes
`print`'s return, so its start has no `emit` ahead (the only step out of
the print phase is the return, `printPh_frameStep`). -/
theorem noEmit_of_leave {q q' : Ctl × List TermRun.Frame} (hr : FrameRun helloSrc q q') :
    ∀ {s1 : TermRun.TTh}, Ctl.of s1 = q.1 → s1.stack = q.2 → PrintPh l n m cw s1 →
      ¬ PrintPh l n m cw (atQ s1 q') → HelloW1.NoEmit cw s1 := by
  induction hr with
  | refl q =>
    intro s1 hc hst hP hP'
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    exact (hP' hP).elim
  | @step q q₁ q' hs _ ih =>
    intro s1 hc hst hP hP'
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    have hh : q₁.1.hold = none := hs.hold_none
    have hc₁ : Ctl.of (atQ s1 q₁) = q₁.1 := by
      obtain ⟨⟨_, _, _⟩, _⟩ := q₁
      simp only at hh
      subst hh
      rfl
    by_cases hP₁ : PrintPh l n m cw (atQ s1 q₁)
    · obtain ⟨w0, w1, w2, w4, env, hj, hN⟩ := ih hc₁ rfl hP₁ hP'
      rw [hc₁] at hN
      exact ⟨w0, w1, w2, w4, env, hj, .step hs hN⟩
    · rcases HelloStep1P.FrameStep.inv hs with ⟨c', hl, rfl⟩ | ⟨x, f, iss, a, e, d, t, ws, -, -, -, rfl⟩ |
        ⟨a, fr, fs, t, ws, hc, -, -, -, -⟩
      · exact (hP₁ (HelloW1.printPh_step hP hl)).elim
      · rcases HelloStep1P.printPh_frameStep hP hs with h1 | ⟨hS, -⟩
        · exact (hP₁ h1).elim
        · exact absurd hS.1 (List.cons_ne_nil _ _)
      · obtain ⟨rfl, w0, w1, w2, w4, hj, hst⟩ := ret_of_printPh hP hc
        refine ⟨w0, w1, w2, w4, s1.env, hj, ?_⟩
        have e1 : Ctl.of s1 = ⟨.ret .unit, s1.env, none⟩ := by
          have hc' : s1.term = .ret .unit := hc
          show (⟨s1.term, s1.env, none⟩ : Ctl) = _
          rw [hc']
        rw [e1, hst]
        exact .refl _

/-- **An `emit` ahead is kept by a frame run** (it stays in the print phase
by the passage `noEmit_of_leave`; no `emit` ahead at its end would give
none at its start). -/
theorem emitAhead_frameRun {s1 : TermRun.TTh} (h : EmitAhead l n m cw s1) {q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') : EmitAhead l n m cw (atQ s1 q') := by
  refine ⟨Classical.byContradiction fun hP' => h.2 (noEmit_of_leave hr rfl rfl h.1 hP'), ?_⟩
  rintro ⟨w0, w1, w2, w4, env, hj, hN⟩
  rw [ctl_atQ hr] at hN
  exact h.2 ⟨w0, w1, w2, w4, env, hj, hr.trans hN⟩

end NoEmitPh

/-- **The buffer fact after a message to `c`** (`BufV.mono`'s argument: the
new message is to `c`'s address, which no buffer word is). -/
theorem bufV_push {l : WeakMem.AllocLabel} {m S : Nat} {cw : TermRun.Word} {sm : WeakMem.Memory}
    {cS : WeakMem.Address} {msg : WeakMem.Msg} (h : BufV l m S cw sm) (hcw : cw.val = .loc cS 0)
    (hl : msg.loc = cS) : BufV l m S cw (sm.push msg) := by
  obtain ⟨hS, wv, hb⟩ := h
  refine ⟨by rw [Array.size_push]; omega, wv, fun i hi => ?_⟩
  obtain ⟨hne, j, msg0, ⟨⟨m0, hm0, hml⟩, hlast⟩, hj, hv, hjS, hvw⟩ := hb i hi
  have hjn : j ≠ sm.size := by omega
  refine ⟨hne, j, msg0, ⟨⟨m0, ?_, hml⟩, fun k m' hk hm' hl' => ?_⟩, ?_, hv, hjS, hvw⟩
  · simpa [Array.getElem?_push, hjn] using hm0
  · rw [Array.getElem?_push] at hm'
    split at hm'
    · cases hm'
      exact hne (by rw [hcw, ← hl, hl'])
    · exact hlast k m' hk hm' hl'
  · simpa [Array.getElem?_push, hjn] using hj

/-! ## The certification run's invariant -/

/-- **The certification run's invariant** at the ghost record `w`: the
worker's state in `Wi` at a source thread in a phase, the messages not
promised and the initial values `G` values, the promises in memory. -/
structure CInvH (Q : WakeRel) (D : WSideH Q.ι) (w : Q.ι) (x : Thread isaLSE2 × Memory) : Prop where
  wi : ∃ s1 : TermRun.TTh, D.Wi w x.1.st (Ctl.of s1) s1.stack ∧ PhH D w s1
  msgs : MsgsExcept (fun m => Q.G w m.loc m.val) x.1.prom x.2
  init : ∀ l, Q.G w l (x.2.initVal l)
  le : ∀ p ∈ x.1.prom, p ≤ x.2.last

/-- **One certification step's shape**: from a source thread `s1` to `s1'`
(in `Wi` in a phase; past a frame run from `s1`, at its end or with its end
in the store phase), memory and promises kept with the store point, or a
`Good` message written (appended, or fulfilling a promise of it): off `cT`
keeping the store point, at `cT` from before it to past it. -/
abbrev ShapeH (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) (w : Q.ι) (s1 : TermRun.TTh)
    (x y : Thread isaLSE2 × Memory) : Prop :=
  ∃ s1' : TermRun.TTh, D.Wi w y.1.st (Ctl.of s1') s1'.stack ∧ PhH D w s1' ∧
    (∃ q', FrameRun helloSrc (Ctl.of s1, s1.stack) q' ∧ (s1' = atQ s1 q' ∨ StorePh (D.cw w) (atQ s1 q'))) ∧
    ((y.2 = x.2 ∧ y.1.prom = x.1.prom ∧ (WPass s1' ↔ WPass s1)) ∨
     ∃ L V, Good Q Λ w ⟨L, V, 1⟩ ∧
       ((y.2 = (x.2.append ⟨L, V, 1⟩).1 ∧ y.1.prom = x.1.prom) ∨
        (∃ q ∈ x.1.prom, x.2.get? q = some ⟨L, V, 1⟩ ∧ y.2 = x.2 ∧ y.1.prom = x.1.prom.erase q)) ∧
       (L ≠ (Q.C w).cT → (WPass s1' ↔ WPass s1)) ∧ (L = (Q.C w).cT → ¬ WPass s1 ∧ WPass s1'))

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {AbW : isaLSE2.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D} {w : Q.ι}

/-- **One certification step of the worker from `CInvH`, by the
frame-aware rows** (`WakeW1.cstep_shape`; the source worker's frame run
first, `phase_endH`), from any source thread `s1` in `Wi` in a phase. -/
theorem cstep_shapeH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT) {k : KState} {x y : Thread isaLSE2 × Memory}
    {s1 : TermRun.TTh} (hwi : D.Wi w x.1.st (Ctl.of s1) s1.stack) (hph : PhH D w s1)
    (hq : CInvH Q D w x) (hs : ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 x y) :
    ShapeH Q D Λ w s1 x y := by
  obtain ⟨outs, o, hso, ho, rfl⟩ := hs
  have hC2 := hC.2.1
  have hx := hC.2.2.1
  have hcv := hC.1.cwv w
  have hsite := hC.1.noSite w _ _ _ hwi
  have hK : ∀ fs, (D.ms w fs).K = some abi := fun fs => by rw [hms w fs]; exact hC2.K w
  have hG' : ∀ fs, (D.ms w fs).G = Q.G w := fun fs => by rw [hms w fs]; exact hC2.G w
  have hownM : ∀ fs s, (D.ms w fs).own s = [] := fun fs s => by
    rw [hms w fs]; exact (hC2.own w s).trans (hx.own1 w s)
  have hmpG : ∀ fs a V, (D.ms w fs).mp (wordLoc a) true → Q.G w (wordLoc a) V → V.toNat < 2 ^ 64 →
      Good Q Λ w ⟨wordLoc a, V, 1⟩ ∧ wordLoc a ≠ (Q.C w).cT := by
    intro fs a V hmp hG hf
    rw [hms w fs] at hmp
    obtain ⟨hf1, hout, hin⟩ := hC2.mpW w _ hmp
    have hne : wordLoc a ≠ (Q.C w).cT := fun e => hout (by rw [e]; exact hcTin)
    exact ⟨⟨hf1, hin, hG, rfl, hf, fun e => absurd e hne⟩, hne⟩
  have hnext : ∀ {st : isaLSE2.State} {q' : Ctl × List TermRun.Frame},
      FrameRun helloSrc (Ctl.of s1, s1.stack) q' → D.Wi w st q'.1 q'.2 →
      ∃ s1' : TermRun.TTh, D.Wi w st (Ctl.of s1') s1'.stack ∧ PhH D w s1' ∧
        (∃ q', FrameRun helloSrc (Ctl.of s1, s1.stack) q' ∧ (s1' = atQ s1 q' ∨ StorePh (D.cw w) (atQ s1 q'))) ∧
        (WPass s1' ↔ WPass s1) := by
    intro st q' hr hX
    obtain ⟨hph', hpi⟩ := phase_endH hcv hph hr
    refine ⟨atQ s1 q', ?_, hph', ⟨q', hr, .inl rfl⟩, hpi⟩
    rw [ctl_atQ hr]; exact hX
  have hkeep : ∀ {q' : Ctl × List TermRun.Frame}, FrameRun helloSrc (Ctl.of s1, s1.stack) q' →
      D.Wi w o.thread.st q'.1 q'.2 → o.mem = x.2 → o.thread.prom = x.1.prom →
      ShapeH Q D Λ w s1 x (o.thread, o.mem) := fun hr hX hm hp =>
    let ⟨s1', hw', hph', hR, hpi⟩ := hnext hr hX
    ⟨s1', hw', hph', hR, .inl ⟨hm, hp, hpi⟩⟩
  have hsx : abi.atSys x.1.st = true → ∀ tr, isaLSE2.exec x.1.st = some tr → ∃ m, tr = .fault m :=
    fun hat tr he => hC.1.sysExec w _ _ _ _ hwi hat he
  cases hat : abi.atSys x.1.st
  · rw [certSem_step_of_not_site hsite hat] at hso
    have hOutL : ∀ (c₁ : Ctl) (fs₁ : List TermRun.Frame), FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, fs₁) →
        OutL helloSrc (D.lbl w) (D.ms w fs₁) (fun s c => D.Wi w s c fs₁) x.1.st c₁ →
        ShapeH Q D Λ w s1 x (o.thread, o.mem) := by
      intro c₁ fs₁ hr₁ hl
      obtain ⟨hE, hpi₁⟩ := phase_endH hcv hph hr₁
      cases hl with
      | out r =>
        cases r with
        | silent s' c' he hr hX =>
          obtain ⟨hm, hp, hst⟩ := stepOne_silent_keep he (Lower.silentTree_done s') hso ho
          exact hkeep (hr₁.trans (FrameRun.ofLocal hr fs₁)) (hst ▸ hX) hm hp
        | choice P tree he hsil hX =>
          obtain ⟨hm, hp, hP⟩ := stepOne_silent_keep he hsil hso ho
          obtain ⟨c', hr, hX'⟩ := hX _ hP
          exact hkeep (hr₁.trans (FrameRun.ofLocal hr fs₁)) hX' hm hp
        | load kl A g x' a e ty w' he ht =>
          exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
        | store kr A V s' x' a b e ty tb wa wb he ht hea hva heb hvb hX htag =>
          rcases hE with ⟨-, hT⟩ | hS
          · have h1 : okE c₁.term = true := okE_pTermT hT
            rw [ht] at h1
            simp [okE, okOp] at h1
          have hst : c₁.term = wkStore := by
            have hw' : c₁.term = wkStore ∨ c₁.term = wkUnpark ∨ c₁.term = .ret .unit := hS.2.1
            rcases hw' with hw' | hw' | hw'
            · exact hw'
            · rw [hw'] at ht; simp [wkUnpark] at ht
            · rw [hw'] at ht; cases ht
          obtain rfl : fs₁ = [] := hS.1
          have hcj : EnvCJ (D.cw w) c₁.env := hS.2.2
          have hnp : ¬ WPass s1 := fun hp => by
            obtain ⟨-, h' | h'⟩ := hpi₁.mpr hp <;>
              (change c₁.term = _ at h'; rw [hst] at h'; simp [wkStore, wkUnpark] at h')
          rw [hst] at ht
          simp only [wkStore, Expr.let_.injEq] at ht
          obtain ⟨rfl, hop, rfl⟩ := ht
          simp only [Op.store.injEq, true_and, and_true] at hop
          obtain ⟨rfl, rfl⟩ := hop
          obtain ⟨cty, cμ, cu, hcv', hcell, hcu⟩ := hcj.1
          have hwa : wa = D.cw w := by
            rw [hcv'] at hea; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea
            exact hea.2.symm
          subst hwa
          obtain ⟨a', hcT, hcTa, hcTo⟩ : ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
              (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label := hC2.cT w
          have hlbl : D.lbl w = (Q.SR w).lbl := hC2.lbl w
          rw [hcv, hlbl] at hva
          obtain ⟨-, x0, hx0, hA⟩ := hva
          rw [hcTa] at hx0; cases hx0
          have hA' : A = BitVec.ofNat 64 a' := by
            apply BitVec.eq_of_toNat_eq
            have := A.isLt
            simp only [BitVec.toNat_ofNat]
            omega
          subst hA'
          simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at heb
          obtain ⟨-, rfl⟩ := heb
          have hV : V = 1 := by
            apply BitVec.eq_of_toNat_eq
            change 1 < 2 ^ 64 ∧ V.toNat = 1 at hvb
            rw [hvb.2]; rfl
          subst hV
          have he' : isaLSE2.exec x.1.st = some (.store kr false (wordLoc a') 1 fun _ => .done s') := he
          obtain ⟨hst', hc⟩ := stepOne_store_cases Arch.armv8 he' hso ho hq.le
          have hgood : Good Q Λ w ⟨wordLoc a', 1, 1⟩ :=
            ⟨by rw [← hcT]; exact hC2.cTfoot w, by rw [← hcT]; exact hC2.cTin w, by rw [← hcT]; exact hx.Gc w,
              rfl, show (1 : Val).toNat < 2 ^ 64 by decide, fun _ => rfl⟩
          refine ⟨atQ s1 (⟨wkUnpark, ("d", .unit, []) :: c₁.env, none⟩, []),
            by rw [hst']; exact hX, .inr ⟨rfl, .inr (.inl rfl), envCJ_cons hcj _ _⟩, ⟨_, hr₁, .inr hS⟩,
            .inr ⟨wordLoc a', 1, hgood, ?_, fun hne => absurd hcT.symm hne, fun _ => ⟨hnp, rfl, .inl rfl⟩⟩⟩
          rcases hc with ⟨q, hq', hg, -, hm, hp⟩ | ⟨hm, hp⟩
          · exact .inr ⟨q, hq', hg, hm, hp⟩
          · exact .inl ⟨hm, hp⟩
        | rtStore kr L V s' c' he hrt hmp hG hr hX =>
          have hwide := hC.1.wide w _ _ _ hwi
          have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
          have hfit : V.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
          rw [hG' fs₁] at hG
          obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
          obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.armv8 he hso ho hq.le
          obtain ⟨hgood, hne⟩ := hmpG fs₁ a V hmp hG hfit
          obtain ⟨s1', hw', hph', hR, hpi⟩ := hnext (hr₁.trans (FrameRun.ofLocal hr fs₁)) (hst ▸ hX)
          refine ⟨s1', hw', hph', hR, .inr ⟨wordLoc a, V, hgood, ?_, fun _ => hpi, fun e => absurd e hne⟩⟩
          rcases hc with ⟨q, hq', hg, -, hm, hp⟩ | ⟨hm, hp⟩
          · exact .inr ⟨q, hq', hg, hm, hp⟩
          · exact .inl ⟨hm, hp⟩
        | rtLoad kl L g c' he hrt hmp hr hX =>
          obtain ⟨hm, hp⟩ := stepOne_load_keep he hso ho
          obtain ⟨v, hst, hG⟩ := stepOne_load_msgsExcept (G := Q.G w) he hso ho hq.msgs hq.init
          rw [← hG' fs₁] at hG
          refine hkeep (hr₁.trans (FrameRun.ofLocal hr fs₁)) ?_ hm hp
          rw [hst]; exact hX v hG fun u hu => by simp [hownM] at hu
        | rtRmw k' L op g c' he hrt hmp hr hX =>
          have hwide := hC.1.wide w _ _ _ hwi
          have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
          have hfit : ∀ old v, op old = some v → v.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
          obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
          obtain ⟨old, tr, hst, hrd, hn, hc⟩ := stepOne_rmw_casesG Arch.armv8 he hso ho hq.le
          have hGo := msgsExcept_read (G := Q.G w) hq.msgs hq.init hrd hn
          rw [← hG' fs₁] at hGo
          obtain ⟨hGn, hXo⟩ := hX old hGo (fun u hu => by simp [hownM] at hu)
          have hrun := hr₁.trans (FrameRun.ofLocal hr fs₁)
          rcases hc with ⟨-, hm, hp⟩ | ⟨new, hop, hc⟩
          · exact hkeep hrun (hst ▸ hXo) hm hp
          · have hGn' := hGn new hop
            rw [hG' fs₁] at hGn'
            obtain ⟨hgood, hne⟩ := hmpG fs₁ a new hmp hGn' (hfit old new hop)
            obtain ⟨s1', hw', hph', hR, hpi⟩ := hnext hrun (hst ▸ hXo)
            refine ⟨s1', hw', hph', hR,
              .inr ⟨wordLoc a, new, hgood, ?_, fun _ => hpi, fun e => absurd e hne⟩⟩
            rcases hc with ⟨q, hq', hg, hm, hp⟩ | ⟨hm, hp⟩
            · exact .inr ⟨q, hq', hg, hm, hp⟩
            · exact .inl ⟨hm, hp⟩
        | sys K call hK' ha =>
          rw [hK fs₁] at hK'; cases hK'; rw [hat] at ha; cases ha
        | holdLoad kl A g x' sa u v e he hxs =>
          obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs
          · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
          · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
        | xchgStore kr A V s' x' sa u v e tv wv wold he hxs =>
          obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs
          · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
          · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
        | ctrRmw k' op g x' τ e n he hrt hm hs =>
          rcases hs with ⟨a, -, -, ht, -⟩ | ⟨-, a, -, ⟨_, ht⟩, -⟩
          · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
          · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
        | alloc s' A x' a τ e ta ws k' wold old us he ht =>
          exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
        | newStore kr A V s' x' a t e w' wold old _ he hm ht =>
          obtain ⟨_, ht⟩ := ht
          exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
        | emit K buf n Pw Qw hK' ha =>
          rw [hK fs₁] at hK'; cases hK'; rw [hat] at ha; cases ha
        | fence k' s' c' he hr hX =>
          obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
          cases hr with
          | loc hr => exact hkeep (hr₁.trans (FrameRun.ofLocal hr fs₁)) (hst ▸ hX) hm hp
          | pub _ hps _ =>
            obtain ⟨-, -, x', a, e, ta, ta', ws, hpt, -⟩ := hps
            rcases hpt with ⟨ht, -⟩ | ⟨r, ht, -⟩
            · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
            · exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
      | ldSt kl A g x' a e ty w' V he ht =>
        exact (exclH hE ht rfl (fun _ _ _ h' => Op.noConfusion h') (fun _ h' => Op.noConfusion h')).elim
    cases D.closed w _ _ _ hwi with
    | pre c₁ fs₁ hr₁ hl => exact hOutL c₁ fs₁ hr₁ hl
    | frame s' c' fs' he hr hX =>
      obtain ⟨hm, hp, hst⟩ := stepOne_silent_keep he (Lower.silentTree_done s') hso ho
      exact hkeep hr (hst ▸ hX) hm hp
    | fnc k' s' c' fs' he hr hX =>
      obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
      exact hkeep hr (hst ▸ hX) hm hp
    | top c₁ hr₁ hT =>
      cases hT with
      | outL hl => exact hOutL c₁ [] hr₁ hl
      | unpk k' A B op g x' a e ty jw he hrt hmp hop ht hh hev hv hA hX =>
        obtain ⟨hE, hpi₁⟩ := phase_endH hcv hph hr₁
        rcases hE with ⟨-, hT⟩ | hS
        · have h1 : okE c₁.term = true := okE_pTermT hT
          rw [ht] at h1
          simp [okE, okOp] at h1
        have hst : c₁.term = wkUnpark := by
          have hw' : c₁.term = wkStore ∨ c₁.term = wkUnpark ∨ c₁.term = .ret .unit := hS.2.1
          rcases hw' with hw' | hw' | hw'
          · rw [hw'] at ht; simp [wkStore] at ht
          · exact hw'
          · rw [hw'] at ht; cases ht
        have hcj : EnvCJ (D.cw w) c₁.env := hS.2.2
        have hpast : WPass s1 := hpi₁.mp ⟨hS.1, .inl hst⟩
        rw [hst] at ht
        simp only [wkUnpark, Expr.let_.injEq] at ht
        obtain ⟨rfl, -, rfl⟩ := ht
        have hL : (⟨A, 8⟩ : Loc) = wordLoc A.toNat := ExtRows.loc_wordLoc rfl
        rw [hL] at he hmp hX
        obtain ⟨old, tr, hst', hrd, hn, hc⟩ := stepOne_rmw_casesG Arch.armv8 he hso ho hq.le
        have hGo := msgsExcept_read (G := Q.G w) hq.msgs hq.init hrd hn
        rw [← hG' []] at hGo
        obtain ⟨hG1, hXo⟩ := hX old hGo (fun u hu => by simp [hownM] at hu)
        rw [hG' []] at hG1
        rcases hc with ⟨hop', -⟩ | ⟨new, hop', hc⟩
        · rw [hop old] at hop'; cases hop'
        have hn1 : new = 1 := by rw [hop old] at hop'; exact (Option.some.inj hop').symm
        subst hn1
        obtain ⟨hgood, hne⟩ := hmpG [] _ 1 hmp hG1 (show (1 : Val).toNat < 2 ^ 64 by decide)
        refine ⟨atQ s1 (⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: c₁.env, none⟩, []),
          by rw [hst']; exact hXo, .inr ⟨rfl, .inr (.inr rfl), envCJ_consW hcj _ _⟩, ⟨_, hr₁, .inr hS⟩,
          .inr ⟨_, 1, hgood, ?_, fun _ => ⟨fun _ => hpast, fun _ => ⟨rfl, .inr rfl⟩⟩, fun e => absurd e hne⟩⟩
        rcases hc with ⟨q, hq', hg, hm, hp⟩ | ⟨hm, hp⟩
        · exact .inr ⟨q, hq', hg, hm, hp⟩
        · exact .inl ⟨hm, hp⟩
      | texit K a hK' ha =>
        rw [hK []] at hK'; cases hK'; rw [hat] at ha; cases ha
      | fnc k' s' c' he hr hX =>
        obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
        exact hkeep (hr₁.trans (FrameRun.ofLocal hr [])) (hst ▸ hX) hm hp
  · have hsx' := hsx hat
    have hOutL : ∀ (c₁ : Ctl) (fs₁ : List TermRun.Frame), FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, fs₁) →
        OutL helloSrc (D.lbl w) (D.ms w fs₁) (fun s c => D.Wi w s c fs₁) x.1.st c₁ →
        ShapeH Q D Λ w s1 x (o.thread, o.mem) := by
      intro c₁ fs₁ hr₁ hl
      cases hl with
      | out r =>
        cases r with
        | sys K call hK' ha hd hok hX =>
          rw [hK fs₁] at hK'; cases hK'
          obtain ⟨hm, hp, hmem⟩ := certSem_step_sys hsite ha hd hok.2.1 hso ho
          obtain ⟨c', hr, hX'⟩ := hX _ hmem
          exact hkeep (hr₁.trans (FrameRun.ofLocal hr fs₁)) hX' hm hp
        | emit K buf n Pw Qw hK' ha hd =>
          -- a `write` ends a certifying run: `certSem` has no step there
          rw [hK fs₁] at hK'; cases hK'
          exfalso
          obtain ⟨tree, st, c', hex, hr, -, -⟩ := stepOneWith_runOut Arch.armv8 hso ho
          have hex' : (certSem abi Arch.armv8 μ k 1).exec x.1.st = some (leaves []) := by
            change soloExec abi Arch.armv8 μ k 1 x.1.st = _
            simp only [soloExec, hsite, ha, ite_true, hd]
          rw [hex'] at hex
          cases hex
          obtain ⟨i, -⟩ := (Lower.run_choose_iff Arch.armv8 1 _).mp hr
          exact i.elim0
        | choice P tree he hsil hX =>
          obtain ⟨m, rfl⟩ := hsx' _ he
          cases hsil
        | _ =>
          obtain ⟨m, hm⟩ := hsx' _ ‹isaLSE2.exec x.1.st = some _›
          cases hm
      | ldSt _ _ _ _ _ _ _ _ _ he =>
        obtain ⟨m, hm⟩ := hsx' _ he
        cases hm
    cases D.closed w _ _ _ hwi with
    | pre c₁ fs₁ hr₁ hl => exact hOutL c₁ fs₁ hr₁ hl
    | frame s' c' fs' he _ _ =>
      obtain ⟨m, hm⟩ := hsx' _ he
      cases hm
    | fnc k' s' c' fs' he _ _ =>
      obtain ⟨m, hm⟩ := hsx' _ he
      cases hm
    | top c₁ hr₁ hT =>
      cases hT with
      | outL hl => exact hOutL c₁ [] hr₁ hl
      | unpk _ _ _ _ _ _ _ _ _ _ he =>
        obtain ⟨m, hm⟩ := hsx' _ he
        cases hm
      | texit K a hK' ha hd =>
        rw [hK []] at hK'; cases hK'
        obtain ⟨-, -, hmem⟩ := certSem_step_sys hsite ha hd (fun _ _ => nofun) hso ho
        simp [certSuccs, results] at hmem
      | fnc _ _ _ he =>
        obtain ⟨m, hm⟩ := hsx' _ he
        cases hm

/-- **One certification step of the worker from `CInvH`** (`WakeW1.cstep`):
it lands in `CInvH`, every promise it fulfils is of a `Good` message, and
it lowers the count of promises of `cT` by no more than it lowers `passB`. -/
theorem cstepH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT) {k : KState} {x y : Thread isaLSE2 × Memory}
    (hq : CInvH Q D w x) (hs : ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 x y) :
    CInvH Q D w y ∧ (∀ p ∈ x.1.prom, p ∉ y.1.prom → ∀ m, x.2.get? p = some m → Good Q Λ w m) ∧
      cntT (Q.C w).cT x + passB Q w y ≤ cntT (Q.C w).cT y + passB Q w x := by
  obtain ⟨c, hwi, hph⟩ := hq.wi
  obtain ⟨c', hwi', hph', -, hcase⟩ := cstep_shapeH (Λ := Λ) hC hms hcTin hwi hph hq hs
  have hB0 : ∀ {z : Thread isaLSE2 × Memory} {sz : TermRun.TTh}, D.Wi w z.1.st (Ctl.of sz) sz.stack →
      PhH D w sz → WPass sz → passB Q w z = 0 :=
    fun h hz hp => by unfold passB; rw [ite_eq_left ((hC.1.pass w _ _ h (hz.imp_left And.left)).mpr hp)]
  have hB1 : ∀ {z : Thread isaLSE2 × Memory} {sz : TermRun.TTh}, D.Wi w z.1.st (Ctl.of sz) sz.stack →
      PhH D w sz → ¬ WPass sz → passB Q w z = 1 :=
    fun h hz hp => by
      unfold passB; rw [ite_eq_right fun h' => hp ((hC.1.pass w _ _ h (hz.imp_left And.left)).mp h')]
  have hBe : (WPass c' ↔ WPass c) → passB Q w y = passB Q w x := fun hi => by
    by_cases hp : WPass c
    · rw [hB0 hwi hph hp, hB0 hwi' hph' (hi.mpr hp)]
    · rw [hB1 hwi hph hp, hB1 hwi' hph' fun h => hp (hi.mp h)]
  rcases hcase with ⟨hm, hp, hpi⟩ | ⟨L, V, hg, hw, hne, heq⟩
  · refine ⟨⟨⟨c', hwi', hph'⟩, msgsExcept_of_eq hq.msgs hm hp, by rw [hm]; exact hq.init,
      by rw [hm, hp]; exact hq.le⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2, ?_⟩
    have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by unfold cntT; rw [hm, hp]
    have hb := hBe hpi
    omega
  · by_cases hL : L = (Q.C w).cT
    · obtain ⟨hnp, hpp⟩ := heq hL
      have hbx : passB Q w x = 1 := hB1 hwi hph hnp
      rcases hw with ⟨hm, hp⟩ | ⟨q, hqp, hgq, hm, hp⟩
      · refine ⟨⟨⟨c', hwi', hph'⟩, hm ▸ hp ▸ msgsExcept_append hq.msgs hg.2.2.1,
          fun l => by rw [hm, (Memory.Prefix.append _ _).initVal]; exact hq.init l,
          fun p hp1 => ?_⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2, ?_⟩
        · rw [hp] at hp1; rw [hm, Memory.last_append]; exact Nat.le_succ_of_le (hq.le p hp1)
        · have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by
            unfold cntT; rw [hp]
            apply List.countP_congr
            intro p hp1
            rw [hm, (Memory.Prefix.append _ _).get? (hq.le p hp1)]
          have hby : passB Q w y = 0 := hB0 hwi' hph' hpp
          omega
      · refine ⟨⟨⟨c', hwi', hph'⟩, hm ▸ hp ▸ msgsExcept_erase hq.msgs hgq hg.2.2.1,
          by rw [hm]; exact hq.init, fun p hp1 => by rw [hp] at hp1; rw [hm]; exact hq.le p (List.mem_of_mem_erase hp1)⟩,
          fun p hp1 hp2 m hgm => ?_, ?_⟩
        · have hpq : p = q := Classical.byContradiction fun hpq =>
            hp2 (by rw [hp]; exact (List.mem_erase_of_ne hpq).mpr hp1)
          subst hpq; rw [hgq] at hgm; cases hgm; exact hg
        · have hby : passB Q w y = 0 := hB0 hwi' hph' hpp
          have hf : cntT (Q.C w).cT x ≤ cntT (Q.C w).cT y + 1 := by
            unfold cntT; rw [hp, hm]; exact countP_erase_le _ _ _
          omega
    · have hb := hBe (hne hL)
      rcases hw with ⟨hm, hp⟩ | ⟨q, hqp, hgq, hm, hp⟩
      · refine ⟨⟨⟨c', hwi', hph'⟩, hm ▸ hp ▸ msgsExcept_append hq.msgs hg.2.2.1,
          fun l => by rw [hm, (Memory.Prefix.append _ _).initVal]; exact hq.init l,
          fun p hp1 => ?_⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2, ?_⟩
        · rw [hp] at hp1; rw [hm, Memory.last_append]; exact Nat.le_succ_of_le (hq.le p hp1)
        · have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by
            unfold cntT; rw [hp]
            apply List.countP_congr
            intro p hp1
            rw [hm, (Memory.Prefix.append _ _).get? (hq.le p hp1)]
          omega
      · refine ⟨⟨⟨c', hwi', hph'⟩, hm ▸ hp ▸ msgsExcept_erase hq.msgs hgq hg.2.2.1,
          by rw [hm]; exact hq.init, fun p hp1 => by rw [hp] at hp1; rw [hm]; exact hq.le p (List.mem_of_mem_erase hp1)⟩,
          fun p hp1 hp2 m hgm => ?_, ?_⟩
        · have hpq : p = q := Classical.byContradiction fun hpq =>
            hp2 (by rw [hp]; exact (List.mem_erase_of_ne hpq).mpr hp1)
          subst hpq; rw [hgq] at hgm; cases hgm; exact hg
        · have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by
            unfold cntT; rw [hp, hm]
            apply countP_erase_of_false
            simp [hgq, hL]
          omega

/-! ## The refutation: no certified promise with an `emit` ahead -/

/-- **The certification run's invariant with an `emit` ahead**: `CInvH`, at
a source thread in a phase with an `emit` ahead (so in the print phase,
before the store point). -/
def CInvE (Q : WakeRel) (D : WSideH Q.ι) (w : Q.ι) (x : Thread isaLSE2 × Memory) : Prop :=
  CInvH Q D w x ∧ ∃ s1 : TermRun.TTh, D.Wi w x.1.st (Ctl.of s1) s1.stack ∧ PhH D w s1 ∧
    EmitAhead (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1

/-- **One certification step from `CInvE`** lands in `CInvE` and never
lowers the count of promises of `cT`: the `emit` ahead is kept
(`emitAhead_frameRun`; the store phase is not the print phase), so both ends
are before the store point and `cstepH`'s bound has `passB = 1` on both
sides. -/
theorem cstepE (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT) {k : KState} {x y : Thread isaLSE2 × Memory}
    (hq : CInvE Q D w x) (hs : ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 x y) :
    CInvE Q D w y ∧ cntT (Q.C w).cT x + 0 ≤ cntT (Q.C w).cT y + 0 := by
  obtain ⟨hH, s1, hwi, hph, hE⟩ := hq
  obtain ⟨s1', hwi', hph', ⟨q', hr, hend⟩, -⟩ := cstep_shapeH (Λ := Λ) hC hms hcTin hwi hph hH hs
  have hE' := emitAhead_frameRun hE hr
  have hE'' : EmitAhead (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1' := by
    rcases hend with rfl | hS
    · exact hE'
    · exact absurd hE'.1 (storePh_not_printPh hS (hC.1.cwv w))
  obtain ⟨hH', -, hb⟩ := cstepH (Λ := Λ) hC hms hcTin hH hs
  refine ⟨⟨hH', s1', hwi', hph', hE''⟩, ?_⟩
  have hB1 : ∀ {z : Thread isaLSE2 × Memory} {sz : TermRun.TTh}, D.Wi w z.1.st (Ctl.of sz) sz.stack →
      PhH D w sz → PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) sz → passB Q w z = 1 :=
    fun h hz hP => by
      unfold passB
      rw [ite_eq_right fun h' => printPh_not_pass hP ((hC.1.pass w _ _ h (hz.imp_left And.left)).mp h')]
  have h1 := hB1 hwi hph hE.1
  have h2 := hB1 hwi' hph' hE''.1
  omega

/-- **No certified promise of `cT` with an `emit` ahead** (the refutation
lemma; WeakCore 621ec97a: no promise spans an emit). From `CInvH` at a
source thread in the print phase, with a promise of `cT` outstanding, a
certification run must pass `print`'s return before the worker's `emit`:
an `emit` ahead is kept by every certification step (`cstepE`), the count
of promises of `cT` never drops, so the run never empties the promises
(`certOkC_pot` with bound `0`). So the dichotomy `emitAhead_or_noEmit`
leaves `NoEmit`. -/
theorem noEmit_of_certOkC (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT) {k : KState} {t : Thread isaLSE2} {mem : Memory}
    {s1 : TermRun.TTh} (hq : CInvH Q D w (t, mem)) (hwi : D.Wi w t.st (Ctl.of s1) s1.stack) (hph : PhH D w s1)
    (hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1) (hcnt : 0 < cntT (Q.C w).cT (t, mem))
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 t mem) : HelloW1.NoEmit (D.cw w) s1 := by
  rcases emitAhead_or_noEmit hP with hE | hN
  · have h0 := certOkC_pot (P := CInvE Q D w) (cntT (Q.C w).cT) (fun _ => 0)
      (fun x hx' => by unfold cntT; rw [hx']; rfl) (fun x y hx' hs => cstepE hC hms hcTin hx' hs)
      ⟨hq, s1, hwi, hph, hE⟩ hc
    exact absurd h0 (Nat.not_le_of_lt hcnt)
  · exact hN

/-! ## The promise row -/

variable {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **The kernel relation past a step of the worker keeping its target state,
its source control and frames** (`HelloW1.KrW` at `KRHE`, the kernel state
kept): `KRH` by `krh_frame1`, the `write` link by `lk_congr1` (a promise,
also mid-`write`). -/
theorem krW_prom {r0 r1 : Q.ι → Range} (hKR : Q.KR = HelloKRE.KRHE D r0 r1) {w : Q.ι} {t1' : Thread isaLSE2}
    {mem' : Memory} {s1' : TermRun.TTh} (hkr : Q.KR w t s) (hth : t.1.threads = #[t0, t1])
    (hs1 : s.ths[1]? = some s1) (hst : t1'.st = t1.st) (hc : Ctl.of s1' = Ctl.of s1)
    (hfs : s1'.stack = s1.stack) : HelloW1.KrW Q D w t s t1' mem' s1' t.2 := by
  intro s' hs0 hs1' htr _
  rw [hKR] at hkr ⊢
  have ht1 : t.1.threads[1]? = some t1 := by rw [hth]; rfl
  exact ⟨A64HelloWriteK.krh_frame1 w t _ s s' hkr.1 rfl hs0
      (fun c hx => by simpa only [SrcSem.traceOf, htr] using hx),
    HelloKRE.lk_congr1 hkr.2 ht1 hs1 (Live.Sem.withThread_get_self ht1) hs1' hst hc hfs rfl⟩

/-- `cT` is in the worker's labels. -/
theorem cTinH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
  obtain ⟨a', hcT, hx', ho⟩ := hC.2.1.cT w
  rw [show (Q.C w).cT = wordLoc a' from hcT]; exact inLabel_wordLoc h.core.mem hwf hx' ho

/-- **`CInvH` at the promising configuration** (the start of a certified
promise's run). -/
theorem cInvH_prom (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (m : Msg) :
    CInvH Q D w (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) :=
  { wi := ⟨s1, h.pt1.1, h.pt1.2.2.1.imp_left fun x => ⟨x.1, x.2.2.1⟩⟩
    msgs := msgsExcept_promise (Scc.Sem.MemInv.msgsExcept h.core.memInv _) m
    init := fun l => by
      show Q.G w l ((t.1.mem.append m).1.initVal l)
      rw [(Memory.Prefix.append _ _).initVal]; exact h.core.memInv.1 l
    le := fun p hp => by
      show p ≤ (t.1.mem.append m).1.last
      rw [Memory.last_append]
      rcases List.mem_append.mp hp with hp | hp
      · exact Nat.le_succ_of_le (HelloStep1Rt.prom_leH h p hp)
      · rw [List.mem_singleton.mp hp]; exact Nat.le_refl _ }

/-- **A certified promise of the worker is `Good`, with the potential
bound** (`WakeW1.prom_good`): from `CInvH` at the promising configuration,
`cstepH` gives `StepG` and the bound (`certOkC_pot`). -/
theorem prom_goodH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) {m : Msg}
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 (Live.Sem.promThread t1 t.1.mem m)
      (t.1.mem.append m).1) :
    Good Q Λ w m ∧ cntT (Q.C w).cT (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) ≤
      passB Q w (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) := by
  have hcTin := cTinH hC hwf h
  have hq := cInvH_prom h m
  have hG : StepG Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 (CInvH Q D w) (Good Q Λ w) :=
    fun x y hx' hs _ => ⟨(cstepH hC hms hcTin hx' hs).1, (cstepH hC hms hcTin hx' hs).2.1⟩
  refine ⟨certOkC_prom_good_cfg hG hq hc (p := t.1.mem.last + 1) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    (Scc.Sem.Memory.get?_append_new), ?_⟩
  exact certOkC_pot (P := CInvH Q D w) (cntT (Q.C w).cT) (passB Q w)
    (fun x hx' => by unfold cntT; rw [hx']; rfl)
    (fun x y hx' hs => ⟨(cstepH hC hms hcTin hx' hs).1, (cstepH hC hms hcTin hx' hs).2.2⟩) hq hc

/-- **The worker's certified promise in the print phase keeps `Post`**
(`HelloStep1P.PromStepP`; `WakeW1.post_prom1`): the promised message is
`Good` (`prom_goodH`). Off `cT` it is out of every placed label and the
source stutters (`post_localH`); at `cT` it is the worker's `1` before its
store with no `c` message yet, and the source worker promises `kc`
(`prom_c_src`, certified through `print` by `certified_printPh` on the
buffer fact `bufV_push`; `cProtS_prom`). -/
theorem post_prom1H (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : Q.own = wakeOwn) {r0 r1 : Q.ι → Range}
    (hKR : Q.KR = HelloKRE.KRHE D r0 r1) : PromStepP Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc m h hP hex hwt hc
  have hC1 := hC.1
  have hC2 := hC.2.1
  obtain ⟨⟨hf, hin, hG, hb8, hfit, hv1⟩, hcnt⟩ := prom_goodH hC hwf hms h hc
  have hT0 := ((cProt_iff _ _ _).mp h.prot).1
  have hpl := HelloStep1Rt.prom_leH h
  have hlast : (t.1.mem.append m).1.last = t.1.mem.last + 1 := Memory.last_append _ _
  have hnew : (t.1.mem.append m).2 = t.1.mem.last + 1 := rfl
  have hO : ∀ i st fs, Q.own w i st fs = [] := fun _ _ _ => by rw [hown]; rfl
  have hB : BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem := by
    rcases h.pt1.2.2.1 with ⟨-, hB, -⟩ | hS
    · exact hB
    · exact absurd hP (storePh_not_printPh hS (hC1.cwv w))
  have hTm : HelloW1.PTermH s1 := by
    rcases h.pt1.2.2.1 with ⟨-, -, hT, -⟩ | hS
    · exact hT
    · exact absurd hP (storePh_not_printPh hS (hC1.cwv w))
  have hb : (Live.Sem.promThread t1 t.1.mem m).Bnd (t.1.mem.append m).1.last := by
    have hle : t.1.mem.last ≤ (t.1.mem.append m).1.last := by rw [hlast]; exact Nat.le_succ _
    exact ⟨h.core.bnd1.views.mono hle, h.core.bnd1.regs.mono hle⟩
  have hcov : CohCoversL (Live.Sem.promThread t1 t.1.mem m).views (Live.Sem.promThread t1 t.1.mem m).prom
      (t.1.mem.append m).1 ((Q.P w).cov 1) := Inv2Rely.CohCoversL.promise h.core.cov1 m
  have hpr : ∀ k ∈ (Live.Sem.promThread t1 t.1.mem m).prom, (Q.SR w).T < k ∧
      ∃ w', (t.1.mem.append m).1.get? k = some w' ∧ w'.tid = 1 := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom1 k hk
      exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩
    · rw [List.mem_singleton.mp hk]
      exact ⟨Nat.lt_succ_of_le h.core.T_le, m, Scc.Sem.Memory.get?_append_new, hwt⟩
  have hnp : (Q.P w).noProm (Live.Sem.promThread t1 t.1.mem m).st → (Live.Sem.promThread t1 t.1.mem m).prom = [] :=
    fun hn => hC2.noProm w _ _ _ hn hc
  have hfresh : t.1.mem.last + 1 ∉ t1.prom := fun hm' => by
    have h1 : @LE.le Nat instLENat (t.1.mem.last + 1) t.1.mem.last := hpl _ hm'
    omega
  have hnd : (Live.Sem.promThread t1 t.1.mem m).prom.Nodup :=
    List.nodup_append.mpr ⟨h.pt1.2.2.2.2.2, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb' => by rw [List.mem_singleton.mp hb']; rintro rfl; exact hfresh ha⟩
  have hnpT : ¬ (Q.C w).passT t1.st := by
    rw [hC1.pass w _ s1 h.pt1.1 (.inl hP)]; exact printPh_not_pass hP
  by_cases hL : m.loc = (Q.C w).cT
  · -- at `cT`: the worker's `1` before its store, no `c` message yet
    have hv : m.val = 1 := hv1 hL
    have hnewT : ((t.1.mem.append m).1.get? (t.1.mem.last + 1)).map Msg.loc = some (Q.C w).cT := by
      rw [Scc.Sem.Memory.get?_append_new]; simp [hL]
    have hcntE : cntT (Q.C w).cT (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) =
        t1.prom.countP (fun p => decide (((t.1.mem.append m).1.get? p).map Msg.loc = some (Q.C w).cT)) + 1 := by
      unfold cntT
      show List.countP _ (t1.prom ++ [t.1.mem.last + 1]) = _
      have hdec : decide (((t.1.mem.append m).1.get? (t.1.mem.last + 1)).map Msg.loc = some (Q.C w).cT) = true :=
        decide_eq_true hnewT
      rw [List.countP_append]
      simp only [List.countP_cons, List.countP_nil, hdec, ite_true]
    have hoc : oc = none := by
      cases oc with
      | none => rfl
      | some pr =>
        exfalso
        obtain ⟨Tc, kc⟩ := pr
        have hTp := hT0.prom_worker Tc kc rfl (hT0.pass_prom hnpT Tc kc rfl)
        obtain ⟨-, -, w', hg', hl', -⟩ := hT0.some_msg Tc kc rfl
        have hpos : 0 < t1.prom.countP
            (fun p => decide (((t.1.mem.append m).1.get? p).map Msg.loc = some (Q.C w).cT)) :=
          List.countP_pos_iff.mpr ⟨Tc, hTp, by simp [Scc.Sem.Memory.get?_append_le (hpl Tc hTp), hg', hl']⟩
        have h1 : passB Q w (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) ≤ 1 := by
          unfold passB; split <;> omega
        omega
    subst hoc
    have hs1p : s1.promises = [] := by
      cases hp : s1.promises with
      | nil => rfl
      | cons k ks =>
        obtain ⟨Tc, hTc⟩ := h.src_prom hC1 (show k ∈ s1.promises by rw [hp]; exact List.mem_cons_self)
        cases hTc
    obtain ⟨a', hcT, hcTa, hcTo⟩ : ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
        (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label := hC2.cT w
    have hm : m = ⟨wordLoc a', 1, 1⟩ := by
      obtain ⟨L, V, tid⟩ := m
      simp only at hL hv hwt
      rw [hL, hcT, hv, hwt]
    subst hm
    -- the source worker's promise of `kc`, certified through `print`
    obtain ⟨hT0', hS, hlink⟩ := (cProt_iff _ _ _).mp h.prot
    have hnpS : ¬ (Q.C w).passS s1 := fun hp => hnpT (hlink.mpr hp)
    have hlt := hS.pre_lt hnpS
    rw [hC1.C w] at hlt
    have hSle : (Q.SR w).S ≤ s.mem.size := h.core.S_le
    have hSpos := hC2.Spos w
    let s1' : TermRun.TTh := { s1 with promises := s1.promises ++ [s.mem.size] }
    obtain ⟨hg1, hgm⟩ := promise_get h.s1_get (Q.C w).cS (.num 1) ((Q.SR w).S - 1)
    have hB' : BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) (s.mem.push ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩) :=
      bufV_push hB (hC1.cwv w) rfl
    -- no `emit` ahead: the promise's certification passes `print`'s return
    have hN' : HelloW1.NoEmit (D.cw w) s1 :=
      noEmit_of_certOkC hC hms (cTinH hC hwf h) (cInvH_prom h _) h.pt1.1 (.inl ⟨hP, hTm⟩) hP
        (by rw [hcntE]; exact Nat.succ_pos _) hc
    have hDS : D.S w = (Q.SR w).S := hC1.S w
    have hcert : TermRun.Certified helloSrc (srcPo 2 arch helloSrc).k (srcPo 2 arch helloSrc).arch
        (TermRun.promise s 1 (Q.C w).cS (.num 1) ((Q.SR w).S - 1)) 1 :=
      certified_printPh (s1 := s1') hN' hg1 h.pt1.2.1 (by simp [s1', hs1p]) (by rw [hgm]; simp) (hC1.cwv w)
        (Nat.le_pred_of_lt hlt.1) (Nat.lt_of_lt_of_le hlt.2 hSle)
    have hstep := prom_c_src (P := srcPo 2 arch helloSrc) (p := helloSrc) rfl
      (by rw [h.ths]; simp) (by omega) hcert hex
    have hrun : (helloS arch).Run s [] (TermRun.promise s 1 (Q.C w).cS (.num 1) ((Q.SR w).S - 1)) :=
      LRun.step (step := fun c es c' => ∃ i, (helloS arch).step i c es c') ⟨1, hstep⟩ (LRun.refl _)
    have hs' : (TermRun.promise s 1 (Q.C w).cS (.num 1) ((Q.SR w).S - 1)).ths = #[s0, s1'] := by
      unfold TermRun.promise; rw [h.s1_get]; show s.ths.set! 1 s1' = _; rw [h.ths]; rfl
    -- the memory relation: `Tc ↦ kc`, both mirrored
    have hvr : ValRep (Q.SR w).lbl (WeakMem.Val.num 1) (BitVec.toNat (1 : Val)) := ⟨by decide, rfl⟩
    have hmem := h.core.mem.store (a := a') (v := 1) (tid := 1)
      (m := ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩) hcTa hcTo hvr true
    have hcore := core1_append h.core
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack
        else Q.own w 1 (Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩).st s1'.stack)
      (w := ⟨wordLoc a', 1, 1⟩) (t1' := Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩)
      (sm' := s.mem.push ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩) (s1' := s1')
      (ts' := fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k)
      (tp' := tp ++ [t.1.mem.last + 1]) (sp' := sp ++ [s.mem.size])
      (by simp) rfl hf (.inr ⟨_, rfl⟩) hmem
      (fun k hk => by
        rcases List.mem_append.mp hk with hk | hk
        · rcases h.core.tp_prom k hk with h0 | h1
          · exact .inl h0
          · exact .inr (List.mem_append_left _ h1)
        · exact .inr (List.mem_append_right _ hk))
      (fun k w' hk hg' hin' => by
        rcases hk with hk0 | hk1
        · obtain ⟨-, w0, hg0, -⟩ := h.core.prom0 k hk0
          rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg0)] at hg'
          exact List.mem_append_left _ (h.core.prom_tp k w' (.inl hk0) hg' hin')
        · rcases List.mem_append.mp hk1 with hk1 | hk1
          · rw [Scc.Sem.Memory.get?_append_le (hpl k hk1)] at hg'
            exact List.mem_append_left _ (h.core.prom_tp k w' (.inr hk1) hg' hin')
          · exact List.mem_append_right _ hk1)
      (fun k => by
        show k ∈ sp ++ [s.mem.size] ↔ k ∈ s0.promises ∨ k ∈ s1.promises ++ [s.mem.size]
        rw [List.mem_append, List.mem_append, h.core.sp_prom k, or_assoc])
      rfl hin hfit hG hb hcov
      (Inv2Rely.frzS_push h.core.frzS (hC2.cSfrz w)) (Inv2Rely.scov_push h.core.scov0 (hC2.cSfrz w))
      (Inv2Rely.scov_push h.core.scov1 (hC2.cSfrz w)) (fun L v hm' => by simp [hO] at hm')
      (fun L v v' _ h1 => by simp [hO] at h1) (fun L v h1 => by simp [hO] at h1) hpr hnp
    -- the protocol at `oc = (Tc, kc)`
    have hT' : CProtT (Q.SR w) (Q.C w) (some (t.1.mem.last + 1, s.mem.size)) (t.1.mem.append ⟨wordLoc a', 1, 1⟩).1
        (Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩)
        (fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k) (tp ++ [t.1.mem.last + 1]) :=
      { tmsg := fun k w' hk hTk hl => by
          by_cases hk' : k = t.1.mem.last + 1
          · subst hk'
            rw [Scc.Sem.Memory.get?_append_new] at hk
            cases hk
            exact ⟨_, rfl, rfl⟩
          · obtain ⟨kc, hoc', -⟩ := hT0.tmsg k w' (CohCoversP.get?_append_ne hk hk') hTk hl
            cases hoc'
        some_msg := fun Tc kc hoc' => by
          cases hoc'
          exact ⟨Nat.lt_succ_of_le h.core.T_le, by simp, _, Scc.Sem.Memory.get?_append_new, hcT.symm, rfl, rfl⟩
        prom_worker := fun Tc kc hoc' _ => by
          cases hoc'; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        pass_done := fun hp => absurd hp hnpT
        pass_prom := fun _ Tc kc hoc' => by
          cases hoc'; exact List.mem_append_right _ (List.mem_singleton.mpr rfl) }
    have hS' := cProtS_prom (Tc := t.1.mem.last + 1) (tp' := tp ++ [t.1.mem.last + 1]) (sp' := sp ++ [s.mem.size])
      hS hSle hSpos (by rw [hC1.C w]; exact helloC_vs.1) (by rw [hC1.C w]; exact helloC_vs.2)
    have hpt1 : PT1h D w (t.1.mem.append ⟨wordLoc a', 1, 1⟩).1 (s.mem.push ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩)
        (Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩) s1' :=
      ⟨h.pt1.1, h.pt1.2.1, .inl ⟨hP, hB', hTm, .inr hN'⟩, by simp [s1', hs1p],
        fun k hk => by
          have hk' : k = s.mem.size := by simpa [s1', hs1p] using hk
          subst hk'
          exact ⟨by rw [hDS]; exact hSle, ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩, by simp, hC1.cwv w⟩, hnd⟩
    refine ⟨_, hrun, post_frameH (ts' := fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k)
      (tp' := tp ++ [t.1.mem.last + 1]) (sp' := sp ++ [s.mem.size])
      hC1 h.th h.ths hs' h.preC h.pt0 (krW_prom hKR h.kr h.th h.s1_get rfl rfl rfl) h.core.T_le ?_ ?_ ?_ ?_ (by unfold TermRun.promise; split <;> rfl)⟩
    · rw [hgm]; exact ⟨.inr ⟨_, rfl, rfl, hf⟩, .inr ⟨_, rfl, rfl⟩⟩
    · rw [hgm]; exact hcore
    · rw [hgm]; exact hpt1
    · rw [hgm]
      exact ⟨_, (cProt_iff _ _ _).mpr ⟨hT', hS', ⟨fun hp => absurd hp hnpT,
        fun hp => absurd ((HelloW1.PartsH.passS_iff (w := w) hC1 s1).mpr
          ((HelloW1.PartsH.passS_iff (w := w) hC1 s1').mp hp)) hnpS⟩⟩⟩
  · -- off `cT`: out of every placed label, the source stutters
    have hout : ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize m.loc := fun hi => hL (hC2.footLab w _ hf hi)
    have hT' : CProtT (Q.SR w) (Q.C w) oc (t.1.mem.append m).1 t1 ts tp :=
      { hT0 with
        tmsg := fun k w' hk hTk hl => by
          by_cases hk' : k = t.1.mem.last + 1
          · subst hk'
            rw [Scc.Sem.Memory.get?_append_new] at hk
            cases hk
            exact absurd hl hL
          · exact hT0.tmsg k w' (CohCoversP.get?_append_ne hk hk') hTk hl
        some_msg := fun Tc kc hoc => by
          obtain ⟨h1, h2, w', hg', h3⟩ := hT0.some_msg Tc kc hoc
          exact ⟨h1, h2, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg',
            h3⟩ }
    have hcore := core1_append h.core
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack
        else Q.own w 1 (Live.Sem.promThread t1 t.1.mem m).st s1.stack)
      (w := m) (t1' := Live.Sem.promThread t1 t.1.mem m) (sm' := s.mem)
      (s1' := atQ s1 (Ctl.of s1, s1.stack)) (ts' := ts) (tp' := tp)
      (sp' := sp) (by simp) hwt hf (.inl rfl) (h.core.mem.runtime_write hout)
      (fun k hk => by
        rcases h.core.tp_prom k hk with h0 | h1
        · exact .inl h0
        · exact .inr (List.mem_append_left _ h1))
      (fun k w' hk hg' hin' => by
        rcases hk with hk0 | hk1
        · obtain ⟨-, w0, hg0, -⟩ := h.core.prom0 k hk0
          rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg0)] at hg'
          exact h.core.prom_tp k w' (.inl hk0) hg' hin'
        · rcases List.mem_append.mp hk1 with hk1 | hk1
          · rw [Scc.Sem.Memory.get?_append_le (hpl k hk1)] at hg'
            exact h.core.prom_tp k w' (.inr hk1) hg' hin'
          · rw [List.mem_singleton.mp hk1, hnew, Scc.Sem.Memory.get?_append_new] at hg'
            cases hg'
            exact absurd hin' hout)
      h.core.sp_prom hb8 hin hfit hG hb hcov h.core.frzS h.core.scov0 h.core.scov1
      (fun L v hm' => by simp [hO] at hm') (fun L v v' _ h1 => by simp [hO] at h1)
      (fun L v h1 => by simp [hO] at h1) hpr hnp
    exact HelloStep1Rt.post_localH hC1 h hex
      (krW_prom hKR h.kr h.th h.s1_get rfl (ctl_atQ (FrameRun.refl _)) rfl) (.inr ⟨m, rfl, hwt, hf⟩) hcore hT'
      (fun Tc kc hoc htp => List.mem_append_left _ (hT0.prom_worker Tc kc hoc htp)) (fun k hk => hk) hnd
      (FrameRun.refl _) h.pt1.1

/-- info: 'Spike.Lib.HelloProm1.cstep_shapeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cstep_shapeH

/-- info: 'Spike.Lib.HelloProm1.cstepH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cstepH

/-- info: 'Spike.Lib.HelloProm1.emitAhead_frameRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitAhead_frameRun

/-- info: 'Spike.Lib.HelloProm1.noEmit_of_certOkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noEmit_of_certOkC

/-- info: 'Spike.Lib.HelloProm1.post_prom1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_prom1H

end Spike.Lib.HelloProm1
