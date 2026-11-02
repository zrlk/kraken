/-
**hello.w: the source side of a byte of `print`'s `write`** (C4, row
design (a′)): mid-`write(1, …)` each byte the kernel
writes is matched by the source worker's run through one byte of the
published loop (`HelloByteOutP.ByteOutP`): a local run to the element's
`idx` (`loadCP`), the `idx`, the load of the word, the lane, the `emit`,
and a local run after it into the emit row's next byte control.

- `ldCP_noStep`, `wcP_noStep`: the load and `print`'s call take no local
  step; `localRunS_tot`: two local runs from a control are ordered;
  `localRunS_hold`: a local run from a control with no hold ends at one.
- `byteOut_pin`: a local run from a print-phase control to an element's
  `idx` is inside `print` on the slice's words (the buffer at the start of
  the phase's label), below `printN`, and the `idx`'s control is the
  phase's.
- `printPh_nextCP`, `pTermT_nextCP`, `pTermT_run`: after a byte's `emit`
  the worker is in the print phase at a print-phase term, and stays so
  along local runs.
- `loadCP_byte_vs`: `HelloPrintSrcPub.loadCP_byte_i` with the views and
  the message the load leaves (`HelloW1.ldVs`).
-/
import Spike.Lib.HelloW1Cert
import Spike.Lib.HelloByteOutP

namespace Spike.Lib.HelloEmitSrc

open CoreLang CoreTerm TermRun TermExtStep
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (envP wcP workerCallH)
open Spike.Lib.PrintSrc (printN printNext printEmit printLane)
open Spike.Lib.HelloPrintSrcPub (PrintCP loadCP ldCP laneCP emitCP nextCP elemW printLPD_find outCfgI
  loadEnvP printLoadP)
open Spike.Lib.HelloW1 (PrintPh PAnchor PTermT PTermH uFrame ldVs localRunS_after localRunS_cases
  pAnchor_noStep retAnchor printPh_run)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self getElem?_set!_ne mainExit_eq localRunS_solo
  localRunS_run_source_i certified_of_solo emit_src_i tstep_source_i)
open Scc.Sem.MemRel (SLatest)

/-! ## Local runs -/

/-- **The load takes no local step** (its successors depend on memory). -/
theorem ldCP_noStep {pw wn lw : Word} {m k : Nat} {c : Ctl} : ¬ LocalStepS helloSrc (ldCP pw wn m k lw) c := by
  intro h
  have := h.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := (ldCP pw wn m k lw).term, env := (ldCP pw wn m k lw).env } rfl rfl rfl rfl
  simp [TermRun.tstep, ldCP, TermRun.evalOp, TermRun.evalAt, TermRun.lookupE] at this
  obtain ⟨_, _, _, h1, -⟩ := this
  split at h1
  · rename_i u _ hc _
    split at h1
    · rename_i us hu
      simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, rfl⟩ := hc
      simp only [accs, Option.some.injEq] at hu
      subst hu
      simp [loadUnits, Promises.stepLoad, stOf] at h1
    · cases h1
  · cases h1

/-- **`print`'s call takes no local step** (it pushes a frame). -/
theorem wcP_noStep {w0 w1 w2 cw w4 : Word} {c : Ctl} : ¬ LocalStepS helloSrc (wcP w0 w1 w2 cw w4) c := by
  intro hs
  have := hs.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := (wcP w0 w1 w2 cw w4).term, env := (wcP w0 w1 w2 cw w4).env } rfl rfl rfl rfl
  simp [TermRun.tstep, wcP, HelloSplit.workerCallH, TermRun.callFrame, TermRun.enter, TermRun.ol,
    HelloPrintSrcPub.printPD_find, envP, TermRun.evalAt, TermRun.lookupE] at this

/-- **Two local runs from a control are ordered** (local steps are
deterministic). -/
theorem localRunS_tot {p : Prog} {c a b : Ctl} (ha : LocalRunS p c a) (hb : LocalRunS p c b) :
    LocalRunS p a b ∨ LocalRunS p b a := by
  induction ha generalizing b with
  | refl => exact .inl hb
  | @step c c₁ a hs hr ih =>
    cases hb with
    | refl => exact .inr (.step hs hr)
    | step hs' hr' =>
      obtain rfl := HelloW1.localStepS_det hs hs'
      exact ih hr'

/-- **A local run from a control with no hold ends at one.** -/
theorem localRunS_hold {p : Prog} {c c' : Ctl} (h : LocalRunS p c c') (hh : c.hold = none) : c'.hold = none := by
  induction h with
  | refl => exact hh
  | step hs _ ih => exact ih hs.1

/-- **From an element's `idx`** a local run reaches the load at most. -/
theorem loadCP_reach {pw wn : Word} {l : WeakMem.AllocLabel} {m k : Nat} (hpw : pw.val = .loc ⟨l, 0⟩ 0)
    {a : Ctl} (h : LocalRunS helloSrc (loadCP pw wn m k) a) :
    a = loadCP pw wn m k ∨ a = ldCP pw wn m k (elemW pw l (k / 8)) := by
  cases h with
  | refl => exact .inl rfl
  | step hs hr =>
    obtain rfl := HelloW1.localStepS_det hs (HelloPrintSrcPub.printCP_idx hpw)
    cases hr with
    | refl => exact .inr rfl
    | step hs' _ => exact (ldCP_noStep hs').elim

/-- **A local run from a print-phase control to an element's `idx`** is
inside `print`, on the slice's words (the buffer at the start of the
phase's label `l`, `n` bytes, `m ≠ 0` words), below `printN n m`; the
`idx`'s control is the phase's (the loop's `m` enters it only as
`m - 1 - k / 8`). -/
theorem byteOut_pin {l l' : WeakMem.AllocLabel} {n m : Nat} {cw : Word} {s1 : TTh} {pw wn : Word} {m' k : Nat}
    (hP : PrintPh l n m cw s1) (hpw : pw.val = .loc ⟨l', 0⟩ 0)
    (hr : LocalRunS helloSrc (Ctl.of s1) (loadCP pw wn m' k)) :
    (∃ w1 w4, s1.stack = [uFrame pw w1 wn cw w4] ∧ w1.val = .num m ∧ w4.val = WakeW1.mainTidW) ∧
      pw.val = .loc ⟨l, 0⟩ 0 ∧ wn.val = .num n ∧ m ≠ 0 ∧ k < printN n m ∧ loadCP pw wn m' k = loadCP pw wn m k := by
  have hnl : ∀ {a : Ctl}, (∀ a₁, ¬ LocalStepS helloSrc a a₁) → a ≠ loadCP pw wn m' k := by
    rintro a hn rfl
    exact hn _ (HelloPrintSrcPub.printCP_idx hpw)
  obtain ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, ⟨hst, hr'⟩ | ⟨hst, a, hr', ha⟩⟩ := hP
  · exfalso
    rcases localRunS_tot hr' hr with h | h
    · rcases localRunS_cases h with e | ⟨_, hs⟩
      · exact absurd (congrArg Ctl.term e) (by simp [wcP, workerCallH, loadCP, printLoadP])
      · exact wcP_noStep hs
    · rcases loadCP_reach hpw h with e | e
      · exact absurd (congrArg Ctl.term e) (by simp [wcP, workerCallH, loadCP, printLoadP])
      · exact absurd (congrArg Ctl.term e) (by simp [wcP, workerCallH, ldCP])
  · rcases localRunS_tot hr' hr with h | h
    · rcases localRunS_cases h with e | ⟨_, hs⟩
      · exact (hnl ha.2 e).elim
      · exact (pAnchor_noStep ha hs).elim
    · rcases loadCP_reach hpw h with rfl | rfl
      · exact (hnl ha.2 rfl).elim
      obtain ⟨⟨k'', hk, e⟩ | ⟨k'', mw, b, -, e⟩ | ⟨ht, -⟩, -⟩ := ha
      · have e2 := congrArg Ctl.env e
        simp only [ldCP, List.cons.injEq] at e2
        obtain ⟨-, e3⟩ := e2
        have e4 : loadCP pw wn m' k = loadCP w0 w2 m k'' := by
          simp only [loadCP] at e3 ⊢
          rw [e3]
        simp only [loadCP, loadEnvP, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at e3
        obtain ⟨hw2, hk1, -, -, -, hpw0, -⟩ := e3
        subst hpw0 hw2
        have hkk : k = k'' := by simpa [cst, Promises.TVal.mk0] using hk1
        subst hkk
        exact ⟨⟨w1, w4, hst, h1, hj⟩, h0, h2, hm, hk, e4⟩
      · exact absurd (congrArg Ctl.term e) (by simp [ldCP, emitCP, printLane, printEmit])
      · exact absurd ht (by simp [ldCP])

/-! ## After the byte's `emit` -/

/-- **After a byte's `emit` the worker is in the print phase**: inside
`print` on the slice's words, the loop runs on to the next byte's load or to
`print`'s return, both anchors. -/
theorem printPh_nextCP {l : WeakMem.AllocLabel} {n m : Nat} {cw : Word} {s1 : TTh} {pw w1 wn w4 mw : Word}
    {k b : Nat} (hst : s1.stack = [uFrame pw w1 wn cw w4]) (hj : w4.val = WakeW1.mainTidW)
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (h1 : w1.val = .num m) (hm : m ≠ 0) (hwn : wn.val = .num n)
    (hk : k < printN n m) (ht : s1.term = (nextCP pw wn m k (elemW pw l (k / 8)) mw b).term)
    (he : s1.env = (nextCP pw wn m k (elemW pw l (k / 8)) mw b).env) : PrintPh l n m cw s1 := by
  refine ⟨pw, w1, wn, w4, hj, hpw, h1, hm, hwn, .inr ⟨hst, ?_⟩⟩
  have hc : Ctl.of s1 = nextCP pw wn m k (elemW pw l (k / 8)) mw b := by
    show (⟨s1.term, s1.env, none⟩ : Ctl) = _
    rw [ht, he]; rfl
  rw [hc]
  obtain ⟨c', hr, hc'⟩ := HelloPrintSrcPub.printCP_next (p := helloSrc) (lw := elemW pw l (k / 8)) (mw := mw)
    (b := b) printLPD_find hwn hk
  by_cases hk' : k + 1 < printN n m
  · refine ⟨_, hr.trans ((HelloPrintSrcPub.printCP_load printLPD_find hc' hk').trans
      (.single (HelloPrintSrcPub.printCP_idx hpw))), .inl ⟨k + 1, hk', rfl⟩, fun _ h => ldCP_noStep h⟩
  · have e : k + 1 = printN n m := by omega
    rw [e] at hc'
    obtain ⟨env, hr'⟩ := HelloPrintSrcPub.printP_done_run (p := helloSrc) hc'
    exact ⟨_, hr.trans hr', retAnchor rfl rfl⟩

/-- **After a byte's `emit` the worker is at a print-phase term.** -/
theorem pTermT_nextCP {pw wn lw mw : Word} {m k b : Nat} : PTermT (nextCP pw wn m k lw mw b).term :=
  .inr (.inr (by
    simp [nextCP, PrintSvc.printTerms, HelloPrintSrcPub.printLBodyP, HelloPrintSrcPub.printLoadP,
      PrintSrc.printAdv, printLane, printEmit, printNext]))

/-- **A local run keeps the print-phase terms.** -/
theorem pTermT_run {c c' : Ctl} (h : LocalRunS helloSrc c c') (ht : PTermT c.term) : PTermT c'.term := by
  induction h with
  | refl => exact ht
  | step hs _ ih => exact ih (HelloW1.pTermT_step hs ht)

/-! ## One byte, with its views -/

/-- **The worker after one byte of the published loop**: thread `th` past
the `emit` of byte `k` (lane `k % 8` of word `k / 8`, read as its latest
message `jm`, `msg`), the load's views (`ldVs`) and undefined count. -/
def byteTh (th : TTh) (pairs : List Nat) (pw wn : Word) (l : WeakMem.AllocLabel) (m k jm : Nat) (msg : WeakMem.Msg)
    (b : Nat) : TTh :=
  { th with term := printNext, env := (nextCP pw wn m k (elemW pw l (k / 8)) ⟨msg.val, msg.view, jm⟩ b).env,
            vs := ldVs th.vs pairs ⟨l, k / 8⟩ jm msg.view,
            undefs := th.undefs + countUndef [⟨msg.val, msg.view, jm⟩] }

variable {P : SrcParams} {p : Prog}

/-- **`HelloPrintSrcPub.loadCP_byte_i` with the views**: thread `i ≠ 0` at
the element's `idx`, the word's latest message `jm` of value `v`: the `idx`,
the load, the lane and the `emit` are a source run whose trace is the byte
`laneN .w8 v (k % 8)`, landing at `byteTh`, once that landing is
certified (and then the start is certified). -/
theorem loadCP_byte_vs (hP : UsesWc P p) {s : Cfg} {i : Nat} {th : TTh} {pw wn : Word}
    {l : WeakMem.AllocLabel} {m k jm v : Nat} {msg : WeakMem.Msg} (hi0 : i ≠ 0) (hi : s.ths[i]? = some th)
    (ht : th.term = (loadCP pw wn m k).term) (he : th.env = (loadCP pw wn m k).env) (hσ : th.σs = [])
    (hpr : th.promises = []) (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hex : mainExit s = [])
    (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s) (hcell : SLatest s.mem ⟨l, k / 8⟩ jm) (hm : s.mem[jm]? = some msg)
    (hv : msg.val = .num v) :
    Certified p P.k P.arch (outCfgI s i (byteTh th s.pairs pw wn l m k jm msg (laneN .w8 v (k % 8)))
        (laneN .w8 v (k % 8))) i →
      Certified p P.k P.arch s i ∧ (source P p).Run s [.out ⟨laneN .w8 v (k % 8) % 256, Nat.mod_lt _ (by decide)⟩]
        (outCfgI s i (byteTh th s.pairs pw wn l m k jm msg (laneN .w8 v (k % 8))) (laneN .w8 v (k % 8))) := by
  intro hc
  -- the `idx`
  have l1 := HelloPrintSrcPub.printCP_idx (p := p) (wn := wn) (m := m) (k := k) hpw
  let lw := elemW pw l (k / 8)
  let th1 : TTh := { th with term := (ldCP pw wn m k lw).term, env := (ldCP pw wn m k lw).env }
  have hi1 : ({ s with ths := s.ths.set! i th1 } : Cfg).ths[i]? = some th1 := getElem?_set!_self hi th1
  -- the load
  let mw : Word := ⟨msg.val, msg.view, jm⟩
  have h2 := HelloW1.src_load_vs (gOf p P.k P.arch { s with ths := s.ths.set! i th1 } i) s.mem s.pairs th1
    (x := "wd") (l := .var "l")
    (e := printLane) (μ := .pub) (sg := false) (w := .w8) (pw := lw) (a := ⟨l, k / 8⟩) (gg := 0) rfl rfl rfl
    hcell hm
  let th2 : TTh := { th1 with
    term := printLane
    env := ("wd", Ty.lanes false .w8, [mw]) :: th1.env
    vs := ldVs th1.vs s.pairs ⟨l, k / 8⟩ jm msg.view
    undefs := th1.undefs + countUndef [mw] }
  let s2 : Cfg := { s with ths := s.ths.set! i th2 }
  have hm2 : s2 ∈ threadSteps p P.k P.arch { s with ths := s.ths.set! i th1 } i := by
    have := SrcMem.mem_threadSteps hi1 h2
    simpa [s2, set!_set!] using this
  have hi2 : s2.ths[i]? = some th2 := getElem?_set!_self hi th2
  -- the lane
  have l3 := HelloPrintSrcPub.printCP_lane (p := p) (pw := pw) (wn := wn) (lw := lw) (mw := mw) (m := m) (k := k)
    (v := v) hv
  have ht2 : th2.term = (laneCP pw wn m k lw mw).term := rfl
  have he2' : th2.env = (laneCP pw wn m k lw mw).env := rfl
  let b := laneN .w8 v (k % 8)
  let th3 : TTh := { th2 with term := (emitCP pw wn m k lw mw b).term, env := (emitCP pw wn m k lw mw b).env }
  let s3 : Cfg := { s with ths := s.ths.set! i th3 }
  have hi3 : s3.ths[i]? = some th3 := getElem?_set!_self hi th3
  -- the `emit`
  let s4 := extCfg s3 i th3 "r" .emit printNext [cst (.num b)] []
  have ht3 : th3.term = .let_ "r" (.ext .emit (.var "x")) printNext := rfl
  have ha3 : evalAt th3.env (.var "x") = some (.fix false .w8, [cst (.num b)]) := rfl
  have hp3 : th3.promises = [] := hpr
  have e4 : s4 = outCfgI s i (byteTh th s.pairs pw wn l m k jm msg b) b := by
    simp [s4, s3, outCfgI, extCfg, ExtName.events, th3, th2, th1, byteTh, mw]
    rfl
  rw [← e4] at hc
  -- certificates backwards (no promise at the `emit`: the empty run)
  have hσ2 : th2.σs = [] := hσ
  have hc3 : Certified p P.k P.arch s3 i := WorkerSrcStep.certified_nil hi3 hp3
  have hsolo3 := localRunS_solo (k := P.k) (arch := P.arch) (LocalRunS.single l3) hi2 ht2 he2' hσ2
  have hc2 : Certified p P.k P.arch s2 i := by
    refine certified_of_solo ?_ hc3
    simpa [s2, s3, th3, set!_set!] using hsolo3
  have hc1 : Certified p P.k P.arch { s with ths := s.ths.set! i th1 } i :=
    certified_of_solo (.thread hm2 (.refl _)) hc2
  -- the run
  have r1 := localRunS_run_source_i hP hi0 (LocalRunS.single l1) hi ht he hσ hex hc1
  have hex1 : mainExit { s with ths := s.ths.set! i th1 } = [] :=
    (mainExit_eq (by simp only [getElem?_set!_ne _ hi0])).trans hex
  have r2 : (source P p).step i { s with ths := s.ths.set! i th1 } [] s2 := by
    have h := tstep_source_i (mem' := s.mem) (pairs' := s.pairs) hP hi0 hi1 h2
      (by simpa [s2, set!_set!] using hc2) hex1
    simpa [s2, set!_set!] using h
  have hex2 : mainExit s2 = [] := (mainExit_eq (by simp only [s2, getElem?_set!_ne _ hi0])).trans hex
  have r3 : (source P p).Run s2 [] s3 := by
    have h := localRunS_run_source_i hP hi0 (LocalRunS.single l3) hi2 ht2 he2' hσ2 hex2
      (by simpa [s2, s3, th3, set!_set!] using hc3)
    simpa [s2, s3, th3, set!_set!] using h
  have hex3 : mainExit s3 = [] := (mainExit_eq (by simp only [s3, getElem?_set!_ne _ hi0])).trans hex
  have hx3 : ∀ c, Ev.exit c ∉ P.hooks.trace s3 := by
    rw [traceThs_wc hP]; exact hx
  have r4 := emit_src_i hP hi0 hi3 ht3 hp3 ha3 rfl hc hex3 hx3
  have R := r1.trans (LRun.step ⟨i, r2⟩ (r3.trans (LRun.step ⟨i, r4⟩ (LRun.refl _))))
  simp only [List.nil_append, List.append_nil] at R
  rw [← e4]
  exact ⟨certified_of_solo (localRunS_solo (LocalRunS.single l1) hi ht he hσ) hc1, R⟩

/-! ## A byte of the emit row, at the source worker -/

/-- **The source worker after a byte of the emit row**: at control `c2`,
with the load's views (`ldVs`) and undefined count; frames, promises and the
rest kept. -/
def emitTh (s1 : TTh) (pairs : List Nat) (l : WeakMem.AllocLabel) (k jm : Nat) (msg : WeakMem.Msg) (c2 : Ctl) :
    TTh :=
  { s1 with term := c2.term, env := c2.env, vs := ldVs s1.vs pairs ⟨l, k / 8⟩ jm msg.view,
            undefs := s1.undefs + countUndef [⟨msg.val, msg.view, jm⟩] }

/-- **The source configuration after a byte of the emit row**: thread 1
`s1'`, the byte `b` appended to the trace. -/
def emitCfg (s : Cfg) (s1' : TTh) (b : Nat) : Cfg :=
  { s with ths := s.ths.set! 1 s1', trace := s.trace ++ [.out b] }

theorem nextCP_congr {pw wn lw mw : Word} {m m' k b : Nat} (h : loadCP pw wn m' k = loadCP pw wn m k) :
    nextCP pw wn m' k lw mw b = nextCP pw wn m k lw mw b := by
  have he := congrArg Ctl.env h
  simp only [nextCP, emitCP, laneCP, ldCP, he]

/-- **A byte of the emit row at the source worker** (`ByteOutP` at its
control): the worker (thread 1, in the print phase
on the label `l`, the buffer's words with latest messages, `BufV`) runs
locally to the element's `idx` of byte `k` (`a = b0 + k`, `lbl l = some
b0`, `k / 8 < m`), reads word `k / 8`'s latest message `jm` of value `v`,
emits lane `k % 8` of it and runs locally into `Φ`, at `c2`: in the print
phase at a print-phase term; the run is a source run once its end is
certified. -/
theorem emit_byte_src {arch : WeakMem.Arch} {s : Cfg} {s1 : TTh} {l : WeakMem.AllocLabel} {n m S : Nat} {cw : Word}
    {lbl : WeakMem.AllocLabel → Option Nat} {I : Kraken.Promising.ISA} {st : I.State} {a : Nat} {Φ : Ctl → Prop}
    (hi : s.ths[1]? = some s1) (hσ : s1.σs = []) (hpr : s1.promises = []) (hP : PrintPh l n m cw s1)
    (hB : HelloW1.BufV l m S cw s.mem)
    (hbo : HelloByteOutP.ByteOutP helloSrc lbl st a (Ctl.of s1) Φ) (hex : mainExit s = [])
    (hx : ∀ c, Ev.exit c ∉ SrcSem.traceOf s) :
    ∃ (b0 k jm v : Nat) (c2 : Ctl) (msg : WeakMem.Msg), lbl l = some b0 ∧ a = b0 + k ∧ k / 8 < m ∧
      SLatest s.mem ⟨l, k / 8⟩ jm ∧
      s.mem[jm]? = some msg ∧ msg.val = .num v ∧ Φ c2 ∧ c2.hold = none ∧
      PrintPh l n m cw (emitTh s1 s.pairs l k jm msg c2) ∧ PTermH (emitTh s1 s.pairs l k jm msg c2) ∧
      (Certified helloSrc Promises.Knobs.all arch (emitCfg s (emitTh s1 s.pairs l k jm msg c2) (laneN .w8 v (k % 8)))
          1 →
        (HelloSrc.helloS arch).Run s [.out ⟨laneN .w8 v (k % 8) % 256, Nat.mod_lt _ (by decide)⟩]
          (emitCfg s (emitTh s1 s.pairs l k jm msg c2) (laneN .w8 v (k % 8)))) := by
  obtain ⟨pw, wn, l', b0, m', k, hpw, hl, ha, hrun, hQ⟩ := hbo
  obtain ⟨⟨w1, w4, hst, h1, hj⟩, hpwl, hwn, hm0, hk, hLE⟩ := byteOut_pin hP hpw hrun.toS
  obtain rfl : l = l' := by
    rw [hpwl] at hpw
    simp only [WeakMem.Val.loc.injEq, WeakMem.Address.mk.injEq] at hpw
    exact hpw.1.1
  have hk8 : k / 8 < m := by unfold printN at hk; omega
  obtain ⟨-, wv, hW⟩ := hB
  obtain ⟨-, jm, msg, hcell, hmsg, hv, -⟩ := hW (k / 8) hk8
  let mw : Word := ⟨msg.val, msg.view, jm⟩
  let b := laneN .w8 (wv (k / 8)) (k % 8)
  obtain ⟨c2, hr2, hΦ⟩ := hQ mw (wv (k / 8)) hv
  rw [nextCP_congr hLE] at hr2
  rw [hLE] at hrun
  have hh2 : c2.hold = none := localRunS_hold hr2.toS rfl
  refine ⟨b0, k, jm, wv (k / 8), c2, msg, hl, ha, hk8, hcell, hmsg, hv, hΦ, hh2, ?_, ?_, fun hc => ?_⟩
  · -- the print phase: at `nextCP`, then along the local run
    have hP' := printPh_nextCP (s1 := byteTh s1 s.pairs pw wn l m k jm msg b) (cw := cw) (mw := mw) hst hj hpwl h1
      hm0 hwn hk rfl rfl
    have := printPh_run hh2 hr2.toS (s1 := byteTh s1 s.pairs pw wn l m k jm msg b) rfl hP'
    exact this
  · exact pTermT_run hr2.toS pTermT_nextCP
  · -- the run: to the `idx`, the byte, after the `emit`
    let P := srcPo 2 arch helloSrc
    let thl : TTh := { s1 with term := (loadCP pw wn m k).term, env := (loadCP pw wn m k).env }
    let sl : Cfg := { s with ths := s.ths.set! 1 thl }
    have hil : sl.ths[1]? = some thl := getElem?_set!_self hi thl
    have hexl : mainExit sl = [] := (mainExit_eq (by simp only [sl, getElem?_set!_ne _ (by decide : 1 ≠ 0)])).trans hex
    let thb := byteTh thl sl.pairs pw wn l m k jm msg b
    let sb := outCfgI sl 1 thb b
    have hib : sb.ths[1]? = some thb := by
      show (sl.ths.set! 1 thb)[1]? = _
      exact getElem?_set!_self hil thb
    have hexb : mainExit sb = [] :=
      (mainExit_eq (by simp only [sb, outCfgI, getElem?_set!_ne _ (by decide : 1 ≠ 0)])).trans hexl
    have e2 : ({ sb with ths := sb.ths.set! 1 { thb with term := c2.term, env := c2.env } } : Cfg) =
        emitCfg s (emitTh s1 s.pairs l k jm msg c2) b := by
      simp only [sb, sl, outCfgI, emitCfg, set!_set!, thb, thl, byteTh, emitTh]
    rw [← e2] at hc
    have hcb : Certified helloSrc P.k P.arch sb 1 :=
      certified_of_solo (localRunS_solo hr2.toS hib rfl rfl hσ) hc
    obtain ⟨hcl, r2⟩ := loadCP_byte_vs (P := P) (p := helloSrc) rfl (by decide) hil rfl rfl hσ hpr hpwl hexl hx hcell
      hmsg hv hcb
    have r1 := localRunS_run_source_i (P := P) rfl (by decide) hrun.toS hi rfl rfl hσ hex hcl
    have r3 := localRunS_run_source_i (P := P) rfl (by decide) hr2.toS hib rfl rfl hσ hexb hc
    rw [← e2]
    exact r1.trans (r2.trans r3)

/-- info: 'Spike.Lib.HelloEmitSrc.emit_byte_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emit_byte_src

end Spike.Lib.HelloEmitSrc
