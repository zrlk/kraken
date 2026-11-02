/-
**hello.w on x86-64: the worker's print-phase steps, frame runs** (the
data in `Spike/Lib/X64HelloW1.lean`, the dispatch in
`Spike/Lib/X64HelloStep1.lean`): the frame-aware rows (`HelloSegThrS.OutTS`)
let the source worker take a frame run (local steps, `print`'s call and
return) where wake's took a local run.

- `FrameStep.det`: a frame step is determined by its pair.
- `frameRun_solo`, `frameRun_run_source_i`: a frame run of thread `i ≠ 0`
  is a solo run, and a source run with the empty trace once its end is
  certified (`WorkerSrcStep.localRunS_run_source_i` at any frames).
- `FrameStep.inv`: a frame step, inverted (local step, call, return).
- `storePh_popW`, `storePh_noFrame`, `printPh_frameStep`,
  `phase_frameRun`: from the print phase or the store phase,
  a frame run stays in them (local steps by `printPh_step`, the call by
  `printPh_call`, the return into the store phase), is in the print phase
  only from it, and is past the store point iff its start is.
- `post_instrKeepH`: an instruction keeping memory and promises, matched by
  a frame run, keeps `Post` (`X64WakeW1.post_instrKeep` at `PartsH`), by
  `post_frameRunH` (`X64HelloW1.post_setP` at the frame run's end).
- `post_silentH`, `post_choiceH`, `post_fncH`, `post_rtLoadH`: the rows
  keeping memory and promises (`X64WakeW1Instr`'s twins); `post_rtLoadH` takes
  `hms : ∀ w fs, D.ms w fs = D.ms w []` (`rfl` at
  `DH`, the twin of `HelloAssemblyI.DH`).
- `PromStepP`: the print phase's certified
  promise, `PrintStep1`'s promise branch.

x86-64 twin of `Spike/Lib/HelloStep1P.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the instruction steps are x86-64's (`stepOne Arch.tso` at
`isa`), the worker's owned words are read through `X64HelloOwn1.Own1H` (the worker may own its TCB word), and
the rows' lemmas are `X64WakeW1Instr`'s.
-/
import Spike.Lib.X64HelloStep1
import Spike.Lib.X64HelloW1Anchor
import Spike.Lib.Frames1
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloStep1P

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH PrintPh StorePh PAnchor BufV uFrame WCompatH)
open Spike.Lib.X64HelloSplit (envP wcP workerRestH workerCallH)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self getElem?_set!_ne certified_of_solo tstep_source_i mainExit_eq)
open Spike.Lib.X64WakeT1 (srcPo)

/-! ## Frame runs of a thread `i ≠ 0` -/

section Gen

variable {p : Prog}

/-- **A frame step is determined** by its pair. -/
theorem FrameStep.det {q q₁ q₂ : Ctl × List TermRun.Frame} (h₁ : FrameStep p q q₁) (h₂ : FrameStep p q q₂) :
    q₁ = q₂ := by
  let g : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }
  let th : TermRun.TTh := { term := q.1.term, env := q.1.env, stack := q.2 }
  have e₁ := h₁.tstep (g := g) (mem := #[]) (pairs := []) (th := th) rfl rfl rfl rfl rfl
  have e₂ := h₂.tstep (g := g) (mem := #[]) (pairs := []) (th := th) rfl rfl rfl rfl rfl
  rw [e₁] at e₂
  simp only [List.cons.injEq, Prod.mk.injEq, TermRun.TTh.mk.injEq, and_true, true_and] at e₂
  obtain ⟨ht, he, hs⟩ := e₂
  obtain ⟨⟨t₁, v₁, o₁⟩, f₁⟩ := q₁
  obtain ⟨⟨t₂, v₂, o₂⟩, f₂⟩ := q₂
  have o₁0 : o₁ = none := h₁.hold_none
  have o₂0 : o₂ = none := h₂.hold_none
  simp only at ht he hs
  subst ht he hs o₁0 o₂0
  rfl

/-- **A frame step, inverted** at any pair: a local step at the frames, a
call pushing the call's frame, or a return popping the top frame. -/
theorem FrameStep.inv {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') :
    (∃ c', LocalStepS p q.1 c' ∧ q' = (c', q.2)) ∨
    (∃ x f iss a e d t ws, q.1.term = .let_ x (.call f iss a []) e ∧ p.find? (·.name == f) = some d ∧
      TermRun.evalAt q.1.env a = some (t, ws) ∧
      q' = (⟨d.body, [(d.arg, d.argTy, ws)], none⟩, ⟨x, e, q.1.env, [], d.retTy⟩ :: q.2)) ∨
    (∃ (a : At) (fr : TermRun.Frame) (fs : List TermRun.Frame), ∃ t ws,
      q.1.term = .ret a ∧ q.2 = fr :: fs ∧ fr.σs = [] ∧
      TermRun.evalAt q.1.env a = some (t, ws) ∧ q' = (⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩, fs)) := by
  cases h with
  | loc hl => exact .inl ⟨_, hl, rfl⟩
  | call hc hd ha => exact .inr (.inl ⟨_, _, _, _, _, _, _, _, hc, hd, ha, rfl⟩)
  | ret hc hfr ha => exact .inr (.inr ⟨_, _, _, _, _, hc, rfl, hfr, ha, rfl⟩)

/-- **A frame run of thread `i` is a solo run** of `i`. -/
theorem frameRun_solo {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat} {q q' : Ctl × List TermRun.Frame}
    (h : FrameRun p q q') :
    ∀ {s : TermRun.Cfg} {th : TermRun.TTh}, s.ths[i]? = some th → th.term = q.1.term → th.env = q.1.env →
      th.σs = [] → th.stack = q.2 →
      TermRun.Solo p k arch i s
        { s with ths := s.ths.set! i { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  induction h with
  | refl q =>
    intro s th hi ht he _ hst
    have e1 : { th with term := q.1.term, env := q.1.env, stack := q.2 } = th := by rw [← ht, ← he, ← hst]
    have e2 : s.ths.set! i th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [e1, e2]
    exact .refl _
  | @step q q₁ q' hs _ ih =>
    intro s th hi ht he hσ hst
    let th₁ : TermRun.TTh := { th with term := q₁.1.term, env := q₁.1.env, stack := q₁.2 }
    have hm : { s with ths := s.ths.set! i th₁ } ∈ TermRun.threadSteps p k arch s i :=
      tstep_mem_threadSteps hi (hs.tstep rfl ht he hσ hst)
    have hi' := getElem?_set!_self hi th₁
    have h2 := ih (s := { s with ths := s.ths.set! i th₁ }) hi' rfl rfl hσ rfl
    simp only [th₁, set!_set!] at h2
    exact .thread hm h2

variable {P : SrcSem.SrcParams}

/-- **A frame run of thread `i ≠ 0`**, its end certified, before `main` has
returned, is a source run with the empty trace. -/
theorem frameRun_run_source_i (hP : SrcOutProto.UsesWc P p) {i : Nat} (hi0 : i ≠ 0)
    {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q') :
    ∀ {s : TermRun.Cfg} {th : TermRun.TTh}, s.ths[i]? = some th → th.term = q.1.term → th.env = q.1.env →
      th.σs = [] → th.stack = q.2 → SrcSem.mainExit s = [] →
      TermRun.Certified p P.k P.arch
        { s with ths := s.ths.set! i { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } i →
      (SrcSem.source P p).Run s []
        { s with ths := s.ths.set! i { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  induction h with
  | refl q =>
    intro s th hi ht he _ hst _ _
    have e1 : { th with term := q.1.term, env := q.1.env, stack := q.2 } = th := by rw [← ht, ← he, ← hst]
    have e2 : s.ths.set! i th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [e1, e2]
    exact .refl _
  | @step q q₁ q' hs hr ih =>
    intro s th hi ht he hσ hst hex hc
    let th₁ : TermRun.TTh := { th with term := q₁.1.term, env := q₁.1.env, stack := q₁.2 }
    have hi' : ({ s with ths := s.ths.set! i th₁ } : TermRun.Cfg).ths[i]? = some th₁ := getElem?_set!_self hi th₁
    have hsolo := frameRun_solo (k := P.k) (arch := P.arch) hr hi' rfl rfl hσ rfl
    simp only [th₁, set!_set!] at hsolo
    have hc₁ := certified_of_solo hsolo hc
    have h1 : (SrcSem.source P p).step i s [] { s with ths := s.ths.set! i th₁ } :=
      tstep_source_i (mem' := s.mem) (pairs' := s.pairs) hP hi0 hi
        (by rw [hs.tstep rfl ht he hσ hst]; exact List.mem_singleton.mpr rfl) hc₁ hex
    have hex₁ : SrcSem.mainExit { s with ths := s.ths.set! i th₁ } = [] :=
      (mainExit_eq (by simp only [getElem?_set!_ne _ hi0])).trans hex
    have h2 := ih hi' rfl rfl hσ rfl hex₁ (by simp only [th₁, set!_set!]; exact hc)
    simp only [th₁, set!_set!] at h2
    exact LRun.step ⟨i, h1⟩ h2

end Gen

/-! ## The phases under frame runs -/

section Phase

variable {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {cS : WeakMem.Address}

/-- The thread at a frame run's end. -/
abbrev atQ (s1 : TermRun.TTh) (q : Ctl × List TermRun.Frame) : TermRun.TTh :=
  { s1 with term := q.1.term, env := q.1.env, stack := q.2 }

/-- **The return out of `print`** (with any result words) lands at the store. -/
theorem storePh_popW {w0 w1 w2 w4 : TermRun.Word} (hj : w4.val = X64WakeW1.mainTidW) (th : TermRun.TTh)
    (ws : List TermRun.Word) : StorePh cw (SrcCalls.popTh th (uFrame w0 w1 w2 cw w4) [] ws) := by
  refine ⟨rfl, .inl rfl, ⟨.ptr .pub .int, .pub, .int, ?_, rfl, rfl⟩, .tid, w4, ?_, hj⟩
  · simp [SrcCalls.popTh, uFrame, envP, TermRun.evalAt, TermRun.lookupE]
  · simp [SrcCalls.popTh, uFrame, envP, TermRun.evalAt, TermRun.lookupE]

/-- **No frame step in the store phase.** -/
theorem storePh_noFrame {s1 : TermRun.TTh} (h : StorePh cw s1) (hcw : cw.val = .loc cS 0)
    {q' : Ctl × List TermRun.Frame} (hs : FrameStep helloSrc (Ctl.of s1, s1.stack) q') : False := by
  obtain ⟨hst, ht, -⟩ := id h
  rcases (FrameStep.inv hs) with ⟨c', hl, -⟩ | ⟨x, f, iss, a, e, d, t, ws, hc, -⟩ | ⟨a, fr, fs, t, ws, -, hfs, -⟩
  · exact X64HelloW1.storePh_noStep h hcw hl
  · simp only [Ctl.of] at hc
    rcases ht with ht | ht | ht <;> rw [ht] at hc <;> simp [wkStore, wkUnpark] at hc
  · simp only at hfs
    rw [hst] at hfs
    cases hfs

/-- **One frame step from the print phase** stays in it, or returns out of
`print` to the store. -/
theorem printPh_frameStep {s1 : TermRun.TTh} (h : PrintPh l n m cw s1) {q' : Ctl × List TermRun.Frame}
    (hs : FrameStep helloSrc (Ctl.of s1, s1.stack) q') :
    PrintPh l n m cw (atQ s1 q') ∨ (StorePh cw (atQ s1 q') ∧ q'.1.term = wkStore) := by
  have hloc : ∀ {c₁}, LocalStepS helloSrc (Ctl.of s1) c₁ →
      PrintPh l n m cw (atQ s1 q') ∨ (StorePh cw (atQ s1 q') ∧ q'.1.term = wkStore) := fun {c₁} hl => by
    obtain rfl := FrameStep.det hs (.loc hl)
    exact .inl (X64HelloW1.printPh_step h hl)
  have h' := h
  obtain ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, ⟨hst, hr⟩ | ⟨hst, a, hr, ha⟩⟩ := h'
  · rcases X64HelloW1.localRunS_cases hr with he | ⟨c₁, hl⟩
    · -- at `print`'s call
      have ht : s1.term = workerCallH := congrArg Ctl.term he
      obtain ⟨v0, v1, v2, hev, hP'⟩ := X64HelloW1.printPh_call h hst ht
      have hcall : FrameStep helloSrc (Ctl.of s1, s1.stack)
          (⟨PrintSrc.printBody, [("a", X64HelloRodataSrc.sliceTyP, [v0, v1, v2])], none⟩,
            ⟨"u", workerRestH, s1.env, [], .unit⟩ :: s1.stack) :=
        .call (by show s1.term = _; rw [ht]; rfl) X64HelloPrintSrcPub.printPD_find hev
      obtain rfl := FrameStep.det hs hcall
      exact .inl hP'
    · exact hloc hl
  · rcases X64HelloW1.localRunS_cases hr with he | ⟨c₁, hl⟩
    · subst he
      obtain ⟨⟨k, -, hk⟩ | ⟨k, mw, b, -, hk⟩ | ⟨ht, -⟩, hns⟩ := ha
      · rcases (FrameStep.inv hs) with ⟨c', hl, -⟩ | ⟨x, f, iss, a, e, d, t, ws, hc, -⟩ | ⟨a, fr, fs, t, ws, hc, -⟩
        · exact (hns _ hl).elim
        · simp only at hc; rw [hk] at hc; simp [X64HelloPrintSrcPub.ldCP] at hc
        · simp only at hc; rw [hk] at hc; simp [X64HelloPrintSrcPub.ldCP] at hc
      · rcases (FrameStep.inv hs) with ⟨c', hl, -⟩ | ⟨x, f, iss, a, e, d, t, ws, hc, -⟩ | ⟨a, fr, fs, t, ws, hc, -⟩
        · exact (hns _ hl).elim
        · simp only at hc; rw [hk] at hc; simp [X64HelloPrintSrcPub.emitCP, PrintSrc.printEmit] at hc
        · simp only at hc; rw [hk] at hc; simp [X64HelloPrintSrcPub.emitCP, PrintSrc.printEmit] at hc
      · rcases (FrameStep.inv hs) with ⟨c', hl, -⟩ | ⟨x, f, iss, a, e, d, t, ws, hc, -⟩ |
          ⟨a, fr, fs, t, ws, -, hfs, -, -, rfl⟩
        · exact (hns _ hl).elim
        · simp only at hc; rw [ht] at hc; cases hc
        · simp only at hfs
          rw [hst] at hfs
          simp only [List.cons.injEq] at hfs
          obtain ⟨rfl, rfl⟩ := hfs
          exact .inr ⟨storePh_popW hj s1 ws, rfl⟩
    · exact hloc hl

/-- **A frame run from a phase** stays in the phases, is in the print phase
only from it, and is past the store point iff its start is. -/
theorem phase_frameRun (hcw : cw.val = .loc cS 0) {q q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc q q') :
    ∀ {s1 : TermRun.TTh}, Ctl.of s1 = q.1 → s1.stack = q.2 → (PrintPh l n m cw s1 ∨ StorePh cw s1) →
      (PrintPh l n m cw (atQ s1 q') ∨ StorePh cw (atQ s1 q')) ∧
        (PrintPh l n m cw (atQ s1 q') → PrintPh l n m cw s1) ∧ (WPass (atQ s1 q') ↔ WPass s1) := by
  induction hr with
  | refl q =>
    intro s1 hc hst hph
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    exact ⟨hph, id, Iff.rfl⟩
  | @step q q₁ q' hs _ ih =>
    intro s1 hc hst hph
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    have hP : PrintPh l n m cw s1 := by
      rcases hph with hP | hS
      · exact hP
      · exact (storePh_noFrame hS hcw hs).elim
    have hnp : ¬ WPass s1 := X64HelloW1.printPh_not_pass hP
    have hh : q₁.1.hold = none := hs.hold_none
    have hc₁ : Ctl.of (atQ s1 q₁) = q₁.1 := by
      obtain ⟨⟨t, e, o⟩, f⟩ := q₁
      simp only at hh
      subst hh
      rfl
    have h1 := printPh_frameStep hP hs
    have hph₁ : PrintPh l n m cw (atQ s1 q₁) ∨ StorePh cw (atQ s1 q₁) := h1.imp_right And.left
    have hnp₁ : ¬ WPass (atQ s1 q₁) := by
      rcases h1 with hP₁ | ⟨-, ht⟩
      · exact X64HelloW1.printPh_not_pass hP₁
      · rintro ⟨-, ht' | ht'⟩ <;> simp only at ht' <;> rw [ht] at ht' <;> simp [wkStore, wkUnpark] at ht'
    obtain ⟨ihph, -, ihw⟩ := ih hc₁ rfl hph₁
    exact ⟨ihph, fun _ => hP, ⟨fun hw => absurd (ihw.mp hw) hnp₁, fun hw => absurd hw hnp⟩⟩

/-- **A frame step from the print phase keeps its terms** where it lands in
the print phase: a local step by `pTermT_step`, `print`'s call enters
`print`'s body, `print`'s return lands in the store phase. -/
theorem pTermH_frameStep (hcw : cw.val = .loc cS 0) {s1 : TermRun.TTh} (h : PrintPh l n m cw s1)
    (hT : X64HelloW1.PTermH s1) {q' : Ctl × List TermRun.Frame} (hs : FrameStep helloSrc (Ctl.of s1, s1.stack) q')
    (hP' : PrintPh l n m cw (atQ s1 q')) : X64HelloW1.PTermH (atQ s1 q') := by
  rcases (FrameStep.inv hs) with ⟨c', hl, rfl⟩ | ⟨x, f, iss, a, e, d, t, ws, hc, hd, -, rfl⟩ |
    ⟨a, fr, fs, t, ws, -, hfs, -, -, rfl⟩
  · exact X64HelloW1.pTermT_step hl hT
  · -- the only call at a print-phase term is `print`'s
    have hf : f = "print" := by
      have hT' : X64HelloW1.PTermT (.let_ x (.call f iss a []) e) := hc ▸ hT
      rcases hT' with h' | h' | h'
      · simp [X64HelloW1.preTermsH, workerCallH, X64HelloSplit.workerBodyH] at h'
        exact h'.2.1.1
      · simp [PrintSvc.printTerms, PrintSrc.printBody] at h'
      · simp [PrintSvc.printTerms, X64HelloPrintSrcPub.printLBodyP, X64HelloPrintSrcPub.printLoadP, PrintSrc.printAdv,
          PrintSrc.printLane, PrintSrc.printEmit, PrintSrc.printNext] at h'
    subst hf
    rw [X64HelloPrintSrcPub.printPD_find] at hd
    cases hd
    exact X64HelloW1.pTermT_printBody
  · -- `print`'s return lands in the store phase
    exfalso
    obtain ⟨w0, w1, w2, w4, hj, -, -, -, -, ⟨hst, -⟩ | ⟨hst, -⟩⟩ := h
    · simp only at hfs; rw [hst] at hfs; cases hfs
    · simp only at hfs
      rw [hst] at hfs
      simp only [List.cons.injEq] at hfs
      obtain ⟨rfl, rfl⟩ := hfs
      exact X64HelloW1.storePh_not_printPh (storePh_popW hj s1 ws) hcw hP'

/-- **A frame run from a phase keeps the print-phase terms** where it ends in
the print phase. -/
theorem pTermH_frameRun (hcw : cw.val = .loc cS 0) {q q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc q q') :
    ∀ {s1 : TermRun.TTh}, Ctl.of s1 = q.1 → s1.stack = q.2 →
      ((PrintPh l n m cw s1 ∧ X64HelloW1.PTermH s1) ∨ StorePh cw s1) →
      PrintPh l n m cw (atQ s1 q') → X64HelloW1.PTermH (atQ s1 q') := by
  induction hr with
  | refl q =>
    intro s1 hc hst hph hP'
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    rcases hph with ⟨-, hT⟩ | hS
    · exact hT
    · exact absurd hP' (X64HelloW1.storePh_not_printPh hS hcw)
  | @step q q₁ q' hs hr' ih =>
    intro s1 hc hst hph hP'
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    obtain ⟨hP, hT⟩ : PrintPh l n m cw s1 ∧ X64HelloW1.PTermH s1 := by
      rcases hph with hP | hS
      · exact hP
      · exact (storePh_noFrame hS hcw hs).elim
    have hh : q₁.1.hold = none := hs.hold_none
    have hc₁ : Ctl.of (atQ s1 q₁) = q₁.1 := by
      obtain ⟨⟨t, e, o⟩, f⟩ := q₁
      simp only at hh
      subst hh
      rfl
    rcases printPh_frameStep hP hs with hP₁ | ⟨hS₁, -⟩
    · exact ih (s1 := atQ s1 q₁) hc₁ rfl (.inl ⟨hP₁, pTermH_frameStep hcw hP hT hs hP₁⟩) hP'
    · exact ih (s1 := atQ s1 q₁) hc₁ rfl (.inr hS₁) hP'

end Phase

/-! ## The rows keeping memory and promises, at `PartsH` -/

section Rows

open Spike.Lib.X64HelloW1 (post_setP storePh_not_printPh KrW krW_of)
open Spike.Lib.Inv2Core (stepOne_cohL CohCoversL)
open Spike.Lib.X64HelloOwn1 (Own1H)
open Spike.Lib.X64HelloAssembly (HelloCompat)
open Spike.Lib.X64HelloW1Store (NoWrite relW)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : X64WakeM0.MSide Q.ι} {AbW : isa.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **A frame run of the worker keeps `Post`** (memory and promises kept):
from a phase, the run stays in the phases (`phase_frameRun`), and the source
runs it (`frameRun_run_source_i`). -/
theorem post_frameRunH (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hown : Own1H Q D Λ) (hex : SrcSem.mainExit s = []) {t1' : Thread isa} {k' : KState}
    {q' : Ctl × List TermRun.Frame} (hkr : KrW Q D w t s t1' t.1.mem (atQ s1 q') k') (hp : t1'.prom = t1.prom)
    (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = [])
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hwi : D.Wi w t1'.st q'.1 q'.2) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' t.1.mem, k') s' := by
  obtain ⟨hph, hPP, hpass⟩ := phase_frameRun (hC.cwv w) hr rfl rfl (h.pt1.2.2.1.imp_left And.left)
  have hh : q'.1.hold = none := hr.hold_none rfl
  have hc : Ctl.of (atQ s1 q') = q'.1 := by
    obtain ⟨⟨_, _, _⟩, _⟩ := q'
    simp only at hh
    subst hh
    rfl
  have hrun := fun hc => frameRun_run_source_i (P := srcPo 2 arch helloSrc) rfl (by decide) hr h.s1_get rfl rfl
    h.pt1.2.1 rfl hex hc
  refine post_setP (s1' := atQ s1 q') hC h hkr ?_
    (pTermH_frameRun (hC.cwv w) hr rfl rfl (h.pt1.2.2.1.imp_left fun x => ⟨x.1, x.2.2.1⟩)) ?_
    hrun hph h.pt1.2.1 rfl rfl hpass hp hb hcov ?_ hnp (by rw [hc]; exact hwi)
  · intro hP
    rcases h.pt1.2.2.1 with ⟨-, hB, -⟩ | hS
    · exact hB
    · exact absurd (hPP hP) (storePh_not_printPh hS (hC.cwv w))
  · intro hP
    rcases h.pt1.2.2.1 with ⟨-, -, -, hN⟩ | hS
    · exact X64HelloW1.clause_frameRun (hC.cwv w) hN hr hh hP
    · exact absurd (hPP hP) (storePh_not_printPh hS (hC.cwv w))
  · rw [hp]
    exact h.ownOk1 hown _ _

/-- **An instruction keeping memory and promises keeps `Post`**, its source
side a frame run (the twin of `X64WakeW1.post_instrKeep`). -/
theorem post_instrKeepH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Own1H Q D Λ) (hex : SrcSem.mainExit s = [])
    (hwr : t.2.wr 1 = 0) {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 o.thread o.mem)
    (hm : o.mem = t.1.mem) (hp : o.thread.prom = t1.prom) {q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hwi : D.Wi w o.thread.st q'.1 q'.2) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hb := (stepOne_bnd _ hso ho h.core.bnd1).1
  have hcov := stepOne_cohL _ hso ho h.core.cov1
  rw [hm] at hb hcov ⊢
  exact post_frameRunH hC.1 h hown hex (krW_of hC.1 h.kr hwr h.th) hp hb hcov
    (fun hn => hC.2.1.noProm w _ _ _ hn hco) hr hwi

/-- **The silent row keeps `Post`**, the source a frame run (`OutTS.frame`,
or `OutTS.pre` with `Out.silent`). -/
theorem post_silentH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Own1H Q D Λ) (hex : SrcSem.mainExit s = [])
    (hwr : t.2.wr 1 = 0) {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 o.thread o.mem)
    {s' : isa.State} {q' : Ctl × List TermRun.Frame} (he : isa.exec t1.st = some (.done s'))
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hX : D.Wi w s' q'.1 q'.2) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp, hst⟩ := X64WakeW1.stepOne_silent_keep he (Lower.silentTree_done s') hso ho
  exact post_instrKeepH hC h hown hex hwr hso ho hco hm hp hr (hst ▸ hX)

/-- **The choice row keeps `Post`** (`OutTS.pre` with `Out.choice`). -/
theorem post_choiceH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Own1H Q D Λ) (hex : SrcSem.mainExit s = [])
    (hwr : t.2.wr 1 = 0) {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 o.thread o.mem)
    {P : isa.State → Prop} {tree : EvTree isa.State}
    (he : isa.exec t1.st = some tree) (hs : Lower.SilentTree P tree)
    (hX : ∀ s', P s' → ∃ q', FrameRun helloSrc (Ctl.of s1, s1.stack) q' ∧ D.Wi w s' q'.1 q'.2) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp, hP⟩ := X64WakeW1.stepOne_silent_keep he hs hso ho
  obtain ⟨q', hr, hX'⟩ := hX _ hP
  exact post_instrKeepH hC h hown hex hwr hso ho hco hm hp hr hX'

/-- **The fence row keeps `Post`** (`OutTS.fnc`, or `OutTS.pre` with
`Out.fence` at a local run). -/
theorem post_fncH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Own1H Q D Λ) (hex : SrcSem.mainExit s = [])
    (hwr : t.2.wr 1 = 0) {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 o.thread o.mem)
    {k : Kraken.FenceKind} {s' : isa.State} {q' : Ctl × List TermRun.Frame}
    (he : isa.exec t1.st = some (.fence k fun _ => .done s'))
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hX : D.Wi w s' q'.1 q'.2) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.tso he hso ho
  exact post_instrKeepH hC h hown hex hwr hso ho hco hm hp hr (hst ▸ hX)

/-- **The runtime-load row keeps `Post`** (`OutTS.pre` with `Out.rtLoad`, at
the frames `fs₁` the run reaches): the value read is a `G` value (the
memory's invariant), the owned value if the worker owns the word (its latest write not promised, under its
cover). `hms` (`rfl` at
`DH`, the twin of `HelloAssemblyI.DH`): the worker's memory side is the same at every frame
stack, so its `G` and `own` at `fs₁` are `X64WakeW1.WCompat`'s (at `[]`). -/
theorem post_rtLoadH (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Own1H Q D Λ) (hex : SrcSem.mainExit s = [])
    (hwr : t.2.wr 1 = 0) {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 o.thread o.mem)
    {kl : Kraken.LoadKind} {L : Loc} {g : Val → isa.State} {c₁ c' : Ctl} {fs₁ : List TermRun.Frame}
    (he : isa.exec t1.st = some (.load kl false L fun v => .done (g v)))
    (hr₁ : FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, fs₁)) (hr : LocalRun helloSrc c₁ c')
    (hX : ∀ v, (D.ms w fs₁).G L v → (∀ u, (L, u) ∈ (D.ms w fs₁).own t1.st → v = u) → D.Wi w (g v) c' fs₁) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp⟩ := X64WakeW1.stepOne_load_keep he hso ho
  have hG : (D.ms w fs₁).G = Q.G w := by rw [hms w fs₁]; exact hC.2.1.G w
  have hO : ∀ s, (D.ms w fs₁).own s = Q.own w 1 s [] := fun s => by
    rw [hms w fs₁]
    exact hC.2.1.own w s
  have hwi : D.Wi w o.thread.st c' fs₁ := by
    by_cases hL : ∃ v0, (L, v0) ∈ Q.own w 1 t1.st []
    · -- an owned word: its latest write not promised, under the worker's cover
      obtain ⟨v0, hv0⟩ := hL
      have hown1 := h.ownOk1 hown t1.st []
      have hL8 := (hown1 L v0 hv0).1
      have hcL := h.ownCov1 hown t1.st [] L v0 hv0
      obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
      obtain ⟨-, ts1, v, hst, hl, hrd⟩ := Inv2Core.stepOne_load_tlatestL Arch.tso he hso ho h.core.cov1 hcL
      rw [hst]
      exact hX v (by rw [hG]; exact h.core.memInv.read? hrd) fun u hu => hown1.read hl hrd u (by rwa [hO] at hu)
    · obtain ⟨v, hst, hGv⟩ := stepOne_load_msgsExcept he hso ho (Scc.Sem.MemInv.msgsExcept h.core.memInv _)
        h.core.memInv.1
      rw [hst]
      exact hX v (by rw [hG]; exact hGv) fun u hu => absurd ⟨u, by rwa [hO] at hu⟩ hL
  exact post_instrKeepH hC h hown hex hwr hso ho hco hm hp (hr₁.trans (FrameRun.ofLocal hr fs₁)) hwi

end Rows

/-! ## The print phase's promise -/

/-- the print phase's certified promise. -/
def PromStepP (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc (m : Msg), PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc →
    PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 → SrcSem.mainExit s = [] → m.tid = 1 →
    CertOkC Arch.tso (certSem abi Arch.tso μ t.2 1) 1 (Live.Sem.promThread t1 t.1.mem m) (t.1.mem.append m).1 →
    ∃ s', (srcS helloSrc arch).Run s [] s' ∧
      Q.Post Λ (t.1.withThread 1 (Live.Sem.promThread t1 t.1.mem m) (t.1.mem.append m).1, t.2) s'

/-- info: 'Spike.Lib.X64HelloStep1P.post_rtLoadH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_rtLoadH

/-- info: 'Spike.Lib.X64HelloStep1P.post_choiceH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_choiceH

end Spike.Lib.X64HelloStep1P

/-- info: 'Spike.Lib.X64HelloStep1P.FrameStep.det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.FrameStep.det

/-- info: 'Spike.Lib.X64HelloStep1P.FrameStep.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.FrameStep.inv

/-- info: 'Spike.Lib.X64HelloStep1P.frameRun_solo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.frameRun_solo

/-- info: 'Spike.Lib.X64HelloStep1P.frameRun_run_source_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.frameRun_run_source_i

/-- info: 'Spike.Lib.X64HelloStep1P.storePh_popW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.storePh_popW

/-- info: 'Spike.Lib.X64HelloStep1P.storePh_noFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.storePh_noFrame

/-- info: 'Spike.Lib.X64HelloStep1P.printPh_frameStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.printPh_frameStep

/-- info: 'Spike.Lib.X64HelloStep1P.phase_frameRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.phase_frameRun

/-- info: 'Spike.Lib.X64HelloStep1P.pTermH_frameStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.pTermH_frameStep

/-- info: 'Spike.Lib.X64HelloStep1P.pTermH_frameRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.pTermH_frameRun

/-- info: 'Spike.Lib.X64HelloStep1P.post_frameRunH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.post_frameRunH

/-- info: 'Spike.Lib.X64HelloStep1P.post_instrKeepH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.post_instrKeepH

/-- info: 'Spike.Lib.X64HelloStep1P.post_silentH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.post_silentH

/-- info: 'Spike.Lib.X64HelloStep1P.post_fncH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloStep1P.post_fncH
