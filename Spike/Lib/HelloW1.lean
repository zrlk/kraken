/-
**hello.w on AArch64: the worker's relation after the spawn, with its print
phase** (C4, relation half; the twin of `Spike/Lib/WakeW1.lean`): hello's
worker runs its prelude (tail call, two `split`s, `unpack`), calls `print`
on the published slice, and after `print` returns runs wake's worker tail
(`store rel c 1`, `unpark j`, `ret ()`). The worker's per-thread relation
is the phase sum `PrintPh ∨ StorePh`; `StorePh` is `WakeW1.PT1`'s part past
the split, so the store-phase lemmas of `WakeW1*` apply there.

- `WSideH`: per ghost record `w`, the memory side `ms w fs` of the worker's
  rows at frames `fs` and an invariant `Wi w` of thread states, source
  controls and frames, closed under the frame-aware rows
  (`HelloSegThrS.OutTS` at `helloSrc`).
- `uFrame`: the frame `print`'s call pushes (`HelloPrintSrcPub.callTh`),
  returning into `u` and then `workerRestH` (`= WorkerSrc.wkStore`).
- `PAnchor`: the controls in `print` where the source does more than local
  steps (the buffer load `ldCP`, the byte's `emitCP`, `print`'s `ret ()`).
- `PrintPh`: the source worker before `print`'s call, on an empty stack, a
  local run from the call (`HelloSplit.wcP`); or inside `print`, on the
  stack `[uFrame …]`, a local run from an anchor. `StorePh`: on an empty
  stack at `wkStore`, `wkUnpark` or `ret ()`, `c` and `j` bound
  (`WakeW1.EnvCJ`). `NoEmit`: a frame run to `print`'s return (no `emit`
  ahead).
- `PT1h`: the per-thread relation: `Wi`, no type variables, a phase, and
  `WakeW1.PT1`'s promise facts.
- `printPh_step`, `printPh_run`: the print phase is closed under local runs
  (local steps are deterministic, `localStepS_det`); `storePh_pop`: the
  return out of `print` lands in the store phase; `printPh_spawn`: the
  spawned child is in the print phase.
- `preTermsH`, `PTermT`, `PTermH`: the print phase's terms (the prelude
  down to `print`'s call, `print`'s and `printL`'s bodies followed down);
  `pTermT_step`, `pTermT_run` (local steps keep them), `pTermT_printBody`,
  `pTermH_spawn`.
- `BufV`: the published buffer in the source memory (the print phase's
  conjunct of `PT1h`); `BufV.mono` (memory extension, no new message to the
  words), `bufV_spawn` (at the spawn).
- `PartsH`, `post_partsH`: `Post` unpacked at `PT1h` (`WakeW1.Parts`' twin).
-/
import Spike.Lib.HelloSegThrS
import Spike.Lib.HelloSplit
import Spike.Lib.HelloPrintSrcPub
import Spike.Lib.WakeW1Keep
import Spike.Lib.PrintSvcRun

namespace Spike.Lib.HelloW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloSplit (envP wcP wcR workerRestH workerCallH workerBodyH)
open Spike.Lib.HelloPrintSrcPub (ldCP emitCP elemW)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.WakeW1 (EnvCJ mainTidW)

/-! ## The worker's side -/

/-- **The worker's side of the relation**, per ghost record `w` of `ι`: the
memory side of its rows at each stack of frames, and an invariant over
thread states, source controls and frames closed under the frame-aware
rows at `helloSrc`. -/
structure WSideH (ι : Type) where
  lbl : ι → WeakMem.AllocLabel → Option Nat
  ms : ι → List TermRun.Frame → MemSide isaLSE2
  Wi : ι → FragS isaLSE2
  closed : ∀ w s c fs, Wi w s c fs → OutTS helloSrc (lbl w) (ms w) (Wi w) s c fs
  /-- The worker's pointer word for `c` (the packet's fourth word). -/
  cw : ι → TermRun.Word
  /-- The source memory's size at the spawn (`SpawnRec.S`). -/
  S : ι → Nat
  /-- The published buffer's label: the slice's first word is the locative
  of its start. -/
  bufL : ι → WeakMem.AllocLabel
  /-- The slice's byte count `n`. -/
  nB : ι → Nat
  /-- The slice's word count `m`. -/
  mB : ι → Nat

variable {ι : Type}

/-! ## The phases -/

/-- **The frame of `print`'s call**: returning into `u`, then
`workerRestH`, in the environment at the call (`HelloSplit.envP`). -/
def uFrame (w0 w1 w2 w3 w4 : TermRun.Word) : TermRun.Frame := ⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩

/-- `workerRestH` is wake's worker tail. -/
theorem workerRestH_eq : workerRestH = wkStore := rfl

/-- **The anchors in `print`**, on the slice `pw` (the buffer at the start
of label `l`), `wn` (holding `n`) of `m` words: the controls at which the
source does more than a local step: the load of byte `k`'s word, the
`emit` of byte `k` (`k` below `printN n m`), `print`'s return; none takes
a local step (`ldAnchor`, `emitAnchor`, `retAnchor`). -/
def PAnchor (pw wn : TermRun.Word) (l : WeakMem.AllocLabel) (n m : Nat) (a : Ctl) : Prop :=
  ((∃ k, k < printN n m ∧ a = ldCP pw wn m k (elemW pw l (k / 8))) ∨
    (∃ k mw b, k < printN n m ∧ a = emitCP pw wn m k (elemW pw l (k / 8)) mw b) ∨
    (a.term = .ret .unit ∧ a.hold = none)) ∧ ∀ a₁, ¬ LocalStepS helloSrc a a₁

/-- **The print phase** on the slice of label `l`, `n` bytes, `m` words:
on the packet's words `w0 w1 w2` (the slice: the buffer word at the start
of `l`, `m ≠ 0`, `n`), `cw` (`c`) and `w4` (`j`, main's thread id): before
`print`'s call, on an empty stack, a local run to the call; or inside
`print`, on the stack of its call's frame, a local run to an anchor. -/
def PrintPh (l : WeakMem.AllocLabel) (n m : Nat) (cw : TermRun.Word) (s1 : TermRun.TTh) : Prop :=
  ∃ w0 w1 w2 w4 : TermRun.Word, w4.val = mainTidW ∧
    w0.val = .loc ⟨l, 0⟩ 0 ∧ w1.val = .num m ∧ m ≠ 0 ∧ w2.val = .num n ∧
    ((s1.stack = [] ∧ LocalRunS helloSrc (Ctl.of s1) (wcP w0 w1 w2 cw w4)) ∨
      (s1.stack = [uFrame w0 w1 w2 cw w4] ∧ ∃ a, LocalRunS helloSrc (Ctl.of s1) a ∧ PAnchor w0 w2 l n m a))

/-- **The store phase**: `WakeW1.PT1`'s part past the split. -/
def StorePh (cw : TermRun.Word) (s1 : TermRun.TTh) : Prop :=
  s1.stack = [] ∧ (s1.term = wkStore ∨ s1.term = wkUnpark ∨ s1.term = .ret .unit) ∧ EnvCJ cw s1.env

/-- **No `emit` ahead**: a frame run (local steps, calls, returns; no load,
no `emit`) from the source worker's control and frames to `print`'s
`ret ()` on the stack of its call's frame (`uFrame`, `c` bound to `cw`, `j`
to main's thread id).
In the print phase past the last byte's `emit` (or before the call of a
`print` with no byte); certification of the flag's promise needs no more
(`HelloW1Cert.certified_printPh`): under WeakCore 621ec97a an extern step
needs no promise, so no promise is held across an `emit`. -/
def NoEmit (cw : TermRun.Word) (s1 : TermRun.TTh) : Prop :=
  ∃ w0 w1 w2 w4 : TermRun.Word, ∃ env : TermRun.Env, w4.val = mainTidW ∧
    FrameRun helloSrc (Ctl.of s1, s1.stack) (⟨.ret .unit, env, none⟩, [uFrame w0 w1 w2 cw w4])

/-- **The published buffer in the source memory** (the print phase's
memory fact): `S` (the spawn size) at most the memory's size, and the `m`
words at label `l` off the pointer word `cw`'s address, each with a latest
message of a known value `wv i`, below `S - 1` with its view.

Why it is in `PT1h`: while the source worker holds the flag's promise `kc`
in the print phase, `PartsH.certified_phase` certifies it by the run through
`print` (`certified_printPh`), which reads these words (`VBuf`); nothing else
in `Post` gives them. It reads only the source memory, is set at the spawn
(`bufV_spawn`) and is stable under memory extension with no new message to
the words (`BufV.mono`; the words are frozen, `Inv2Core.frzS`). -/
def BufV (l : WeakMem.AllocLabel) (m S : Nat) (cw : TermRun.Word) (sm : WeakMem.Memory) : Prop :=
  S ≤ sm.size ∧ ∃ wv : Nat → Nat, ∀ i < m, cw.val ≠ .loc ⟨l, i⟩ 0 ∧
    ∃ (j : Nat) (msg : WeakMem.Msg), Scc.Sem.MemRel.SLatest sm ⟨l, i⟩ j ∧ sm[j]? = some msg ∧
      msg.val = .num (wv i) ∧ j + 1 < S ∧ msg.view ≤ S - 1

/-- **The worker's prelude down to `print`'s call**: the spawned child's
tail call into `worker`, `worker`'s two `split`s and its `unpack`, the
call. -/
def preTermsH : List Expr :=
  [.tail "worker" [] (.var "a") [], workerBodyH,
    .split (.var "slc") "sl0" "c" (.unpack (.var "sl0") "q" "sl" workerCallH),
    .unpack (.var "sl0") "q" "sl" workerCallH, workerCallH]

/-- **A print-phase term** (on terms): one of the prelude's (`preTermsH`), or
`print`'s body or `printL`'s body followed down (`PrintSvc.printTerms`). -/
def PTermT (e : Expr) : Prop :=
  e ∈ preTermsH ∨ e ∈ PrintSvc.printTerms PrintSrc.printBody ∨
    e ∈ PrintSvc.printTerms HelloPrintSrcPub.printLBodyP

/-- **The print phase's terms** (wake's `WTerm` pattern): the
source worker's term is a print-phase term (`PTermT`). `PrintPh` alone
admits any term with a local run to an anchor; this pins the terms of
`helloSrc`, so the rows of other source terms (a store, an exchange, an
allocation, an `unpark`) are not at a print-phase control. -/
def PTermH (s1 : TermRun.TTh) : Prop := PTermT s1.term

/-- **The worker's per-thread relation** (`WakeRel.PT1` at hello): its state,
the source worker's control and frames in the invariant, no type
variables, a phase (in the print phase with the buffer's `BufV` and the
print-phase terms `PTermH`, and no promise or no `emit` ahead, `NoEmit`),
and `WakeW1.PT1`'s promise facts (at most one promise, a source message at
or after the spawn to `c`'s address; the target promises distinct). Frozen
(WeakCore 621ec97a: no promise spans an emit). -/
def PT1h (D : WSideH ι) (w : ι) (_tm : Memory) (sm : WeakMem.Memory) (t1 : Thread isaLSE2)
    (s1 : TermRun.TTh) : Prop :=
  D.Wi w t1.st (Ctl.of s1) s1.stack ∧ s1.σs = [] ∧
    ((PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 ∧ BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) sm ∧
        PTermH s1 ∧ (s1.promises = [] ∨ NoEmit (D.cw w) s1)) ∨
      StorePh (D.cw w) s1) ∧
    s1.promises.length ≤ 1 ∧
    (∀ k ∈ s1.promises, D.S w ≤ k ∧ ∃ m : WeakMem.Msg, sm[k]? = some m ∧ (D.cw w).val = .loc m.loc 0) ∧
    t1.prom.Nodup

/-! ## The buffer fact -/

/-- **A latest message is unique.** -/
theorem sLatest_unique {sm : WeakMem.Memory} {a : WeakMem.Address} {j j' : Nat}
    (h : Scc.Sem.MemRel.SLatest sm a j) (h' : Scc.Sem.MemRel.SLatest sm a j') : j = j' := by
  obtain ⟨⟨m, hm, hml⟩, hl⟩ := h
  obtain ⟨⟨m', hm', hml'⟩, hl'⟩ := h'
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd hml' (hl j' m' hlt hm')
  · exact heq
  · exact absurd hml (hl' j m hgt hm)

/-- **`BufV` is stable under memory extension** with no message at or after
`S` to the buffer's words (they are frozen: `Inv2Core.frzS` at the
instance's frozen buffer words). -/
theorem BufV.mono {l : WeakMem.AllocLabel} {m S : Nat} {cw : TermRun.Word} {sm sm' : WeakMem.Memory}
    (h : BufV l m S cw sm) (hext : TermCert.MemExt sm sm')
    (hnew : ∀ k (msg : WeakMem.Msg), sm'[k]? = some msg → S ≤ k → ∀ i < m, msg.loc ≠ ⟨l, i⟩) :
    BufV l m S cw sm' := by
  obtain ⟨hS, wv, hb⟩ := h
  refine ⟨Nat.le_trans hS (TermFul.memExt_size hext), wv, fun i hi => ?_⟩
  obtain ⟨hne, j, msg, ⟨⟨m0, hm0, hml⟩, hlast⟩, hj, hv, hjS, hvw⟩ := hb i hi
  refine ⟨hne, j, msg, ⟨⟨m0, hext _ _ hm0, hml⟩, fun k m' hk hm' hl' => ?_⟩, hext _ _ hj, hv, hjS, hvw⟩
  by_cases hks : k < sm.size
  · obtain ⟨m2, hm2⟩ : ∃ m2, sm[k]? = some m2 := ⟨_, Array.getElem?_eq_getElem hks⟩
    have h2 := hext _ _ hm2
    rw [hm'] at h2
    cases h2
    exact hlast k m' hk hm2 hl'
  · exact hnew k m' hm' (by omega) i hi hl'

/-- **`BufV` at the spawn**: `S` the memory's size, the words off `cw`'s
address with latest messages of known values below `S - 1` (as
`ClonePreH`'s rodata messages), their views by `MsgV`. -/
theorem bufV_spawn {l : WeakMem.AllocLabel} {m S : Nat} {cw : TermRun.Word} {sm : WeakMem.Memory}
    (wv : Nat → Nat) (hS : S = sm.size) (hmv : TermViewInv.MsgV sm) (hcw : ∀ i < m, cw.val ≠ .loc ⟨l, i⟩ 0)
    (hb : ∀ i < m, ∃ (j : Nat) (msg : WeakMem.Msg), Scc.Sem.MemRel.SLatest sm ⟨l, i⟩ j ∧ sm[j]? = some msg ∧
      msg.val = .num (wv i) ∧ j + 1 < sm.size) :
    BufV l m S cw sm := by
  subst hS
  refine ⟨Nat.le_refl _, wv, fun i hi => ?_⟩
  obtain ⟨j, msg, hl, hj, hv, hjS⟩ := hb i hi
  exact ⟨hcw i hi, j, msg, hl, hj, hv, hjS, Nat.le_trans (hmv j msg hj) (by omega)⟩

/-! ## Local steps are deterministic -/

/-- **A local step is determined** by its control. -/
theorem localStepS_det {p : Prog} {c c₁ c₂ : Ctl} (h₁ : LocalStepS p c c₁) (h₂ : LocalStepS p c c₂) :
    c₁ = c₂ := by
  let g : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }
  have e₁ := h₁.2 g #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl
  have e₂ := h₂.2 g #[] [] { term := c.term, env := c.env } rfl rfl rfl rfl
  rw [e₁] at e₂
  have ht := congrArg (fun l => l.head?.map (·.2.2.term)) e₂
  have he := congrArg (fun l => l.head?.map (·.2.2.env)) e₂
  simp only [List.head?_cons, Option.map_some, Option.some.injEq] at ht he
  obtain ⟨t₁, v₁, o₁⟩ := c₁
  obtain ⟨t₂, v₂, o₂⟩ := c₂
  have o₁0 : o₁ = none := h₁.1
  have o₂0 : o₂ = none := h₂.1
  simp only at ht he
  subst ht he o₁0 o₂0
  rfl

/-- **A local run to a control `a` continues from a local step**: either the
step's source is `a`, or the run goes on from the step's target. -/
theorem localRunS_after {p : Prog} {c c₁ a : Ctl} (hr : LocalRunS p c a) (hs : LocalStepS p c c₁) :
    c = a ∨ LocalRunS p c₁ a := by
  cases hr with
  | refl => exact .inl rfl
  | step h hr' => exact .inr (localStepS_det h hs ▸ hr')

/-- A local run is empty or starts with a local step. -/
theorem localRunS_cases {p : Prog} {c a : Ctl} (hr : LocalRunS p c a) : c = a ∨ ∃ c₁, LocalStepS p c c₁ := by
  cases hr with
  | refl => exact .inl rfl
  | step h _ => exact .inr ⟨_, h⟩

/-! ## Closure of the print phase -/

/-- No local step from a `ret` control (`localStep_not_ret`). -/
theorem localStepS_not_ret {p : Prog} {c c₁ : Ctl} (h : LocalStepS p c c₁) (a : At) : c.term ≠ .ret a :=
  localStep_not_ret h.toLocalStep a

/-- **An anchor takes no local step.** -/
theorem pAnchor_noStep {pw wn : TermRun.Word} {l : WeakMem.AllocLabel} {n m : Nat} {a a₁ : Ctl}
    (ha : PAnchor pw wn l n m a) (h : LocalStepS helloSrc a a₁) : False :=
  ha.2 a₁ h

/-- **No local step at `ret`** (with any frames). -/
theorem retAnchor {pw wn : TermRun.Word} {l : WeakMem.AllocLabel} {n m : Nat} {a : Ctl}
    (ht : a.term = .ret .unit) (hh : a.hold = none) : PAnchor pw wn l n m a :=
  ⟨.inr (.inr ⟨ht, hh⟩), fun _ h => localStepS_not_ret h .unit ht⟩

/-- **No local step at the byte's `emit`** (an extern). -/
theorem emitAnchor (pw wn : TermRun.Word) (l : WeakMem.AllocLabel) {n m k : Nat} (mw : TermRun.Word) (b : Nat)
    (hk : k < printN n m) : PAnchor pw wn l n m (emitCP pw wn m k (elemW pw l (k / 8)) mw b) := by
  refine ⟨.inr (.inl ⟨k, mw, b, hk, rfl⟩), fun a₁ h => ?_⟩
  have := h.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := (emitCP pw wn m k (elemW pw l (k / 8)) mw b).term,
      env := (emitCP pw wn m k (elemW pw l (k / 8)) mw b).env } rfl rfl rfl rfl
  simp [TermRun.tstep, emitCP, PrintSrc.printEmit, TermRun.evalOp] at this

/-- **The print phase is closed under a local step** of the source worker
(the stack and `σs` kept). -/
theorem printPh_step {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {s1 : TermRun.TTh} {c₁ : Ctl}
    (h : PrintPh l n m cw s1) (hs : LocalStepS helloSrc (Ctl.of s1) c₁) :
    PrintPh l n m cw { s1 with term := c₁.term, env := c₁.env } := by
  have hc₁ : Ctl.of { s1 with term := c₁.term, env := c₁.env } = c₁ := by
    obtain ⟨t, e, o⟩ := c₁
    have : o = none := hs.1
    subst this; rfl
  obtain ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, ⟨hst, hr⟩ | ⟨hst, a, hr, ha⟩⟩ := h
  · refine ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inl ⟨hst, ?_⟩⟩
    rw [hc₁]
    rcases localRunS_after hr hs with he | hr'
    · have := hs.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
        { term := (wcP w0 w1 w2 cw w4).term, env := (wcP w0 w1 w2 cw w4).env } rfl (by rw [he]) (by rw [he]) rfl
      simp [TermRun.tstep, wcP, HelloSplit.workerCallH, TermRun.callFrame, TermRun.enter, TermRun.ol,
        HelloPrintSrcPub.printPD_find, envP, TermRun.evalAt, TermRun.lookupE] at this
    · exact hr'
  · refine ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inr ⟨hst, a, ?_, ha⟩⟩
    rw [hc₁]
    rcases localRunS_after hr hs with he | hr'
    · exact absurd (he ▸ hs) (pAnchor_noStep ha)
    · exact hr'

/-- **The print phase is closed under a local run** (to a control with no
hold). -/
theorem printPh_run {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {c' : Ctl} (hh : c'.hold = none) :
    ∀ {c : Ctl}, LocalRunS helloSrc c c' → ∀ {s1 : TermRun.TTh}, Ctl.of s1 = c → PrintPh l n m cw s1 →
      PrintPh l n m cw { s1 with term := c'.term, env := c'.env } := by
  intro c hr
  induction hr with
  | refl c =>
    intro s1 hc h
    subst hc
    exact h
  | @step c c₁ c' hs _ ih =>
    intro s1 hc h
    subst hc
    have h1 := printPh_step h hs
    have hc₁ : Ctl.of { s1 with term := c₁.term, env := c₁.env } = c₁ := by
      obtain ⟨t, e, o⟩ := c₁
      have : o = none := hs.1
      subst this; rfl
    have hh' : c'.hold = none := by assumption
    exact @ih hh' { s1 with term := c₁.term, env := c₁.env } hc₁ h1

/-! ## The phase switches -/

/-- **The return out of `print` lands in the store phase**: popping the
call's frame `uFrame` with no result words, at `wcR` (`HelloSplit.wcR_pop`). -/
theorem storePh_pop {cw w0 w1 w2 w4 : TermRun.Word} (hj : w4.val = mainTidW) (th : TermRun.TTh) :
    StorePh cw (SrcCalls.popTh th (uFrame w0 w1 w2 cw w4) [] []) := by
  refine ⟨rfl, .inl rfl, ⟨.ptr .pub .int, .pub, .int, ?_, rfl, rfl⟩, .tid, w4, ?_, hj⟩
  · simp [SrcCalls.popTh, uFrame, envP, TermRun.evalAt, TermRun.lookupE]
  · simp [SrcCalls.popTh, uFrame, envP, TermRun.evalAt, TermRun.lookupE]

/-- **The spawned child is in the print phase**: at `tail worker [] a []`
on the packet's five words, on an empty stack (`HelloSplit.kid_splitH`). -/
theorem printPh_spawn {cw w0 w1 w2 w4 : TermRun.Word} {l : WeakMem.AllocLabel} {n m : Nat} {T : Ty}
    {s1 : TermRun.TTh} (hj : w4.val = mainTidW) (h0 : w0.val = .loc ⟨l, 0⟩ 0) (h1 : w1.val = .num m) (hm : m ≠ 0)
    (h2 : w2.val = .num n) (hst : s1.stack = []) (ht : s1.term = .tail "worker" [] (.var "a") [])
    (he : s1.env = [("a", T, [w0, w1, w2, cw, w4])]) : PrintPh l n m cw s1 := by
  refine ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inl ⟨hst, ?_⟩⟩
  have : Ctl.of s1 = ⟨.tail "worker" [] (.var "a") [], [("a", T, [w0, w1, w2, cw, w4])], none⟩ := by
    simp [Ctl.of, ht, he]
  rw [this]
  exact HelloSplit.kid_splitH HelloSplit.worker_find w0 w1 w2 cw w4

/-! ## The print phase's terms -/

/-- `print`'s body has `PrintSvc.PrintShape`. -/
theorem printShape_printBody : PrintSvc.PrintShape PrintSrc.printBody := by
  simp [PrintSvc.PrintShape, PrintSrc.printBody]

/-- hello's `printL` body has `PrintSvc.PrintShape`. -/
theorem printShape_printLBodyP : PrintSvc.PrintShape HelloPrintSrcPub.printLBodyP := by
  simp [PrintSvc.PrintShape, HelloPrintSrcPub.printLBodyP, HelloPrintSrcPub.printLoadP, PrintSrc.printAdv,
    PrintSrc.printLane, PrintSrc.printEmit, PrintSrc.printNext]

/-- **A local step from a term of `PrintSvc.PrintShape`** in `helloSrc`
moves to a term followed down from it, or (a tail call of `printL`) to
`printLBodyP` (`PrintSvc.localStepS_shape` at hello's `printL`). -/
theorem localStepS_shapeH {c c' : Ctl} (h : LocalStepS helloSrc c c') (hs : PrintSvc.PrintShape c.term) :
    c'.term ∈ PrintSvc.printTerms c.term ∨ c'.term = HelloPrintSrcPub.printLBodyP := by
  obtain ⟨t, env, o⟩ := c
  simp only at hs ⊢
  cases t
  case let_ x op b =>
    left
    cases op
    case call f is a ts => exact (h.not_call rfl).elim
    case callc f a => exact (hs.1 f a rfl).elim
    all_goals
      rw [Hello1Runs.localStepS_let h rfl (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)]
      exact List.mem_cons_of_mem _ (PrintSvc.self_mem_printTerms _)
  case split a x y b =>
    left
    rw [Hello1Runs.localStepS_split h rfl]
    exact List.mem_cons_of_mem _ (PrintSvc.self_mem_printTerms _)
  case ifeq a b y n =>
    left
    rcases Hello1oRuns.localStepS_ifeq_mem h rfl with e | e <;> rw [e]
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (PrintSvc.self_mem_printTerms _))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (PrintSvc.self_mem_printTerms _))
  case ret a => exact (h.not_ret a rfl).elim
  case tail f is a ts =>
    right
    obtain ⟨d, hf, e⟩ := Hello1Runs.localStepS_tail h rfl
    simp only [PrintSvc.PrintShape] at hs
    subst hs
    rw [HelloPrintSrcPub.printLPD_find] at hf
    cases hf
    exact e
  all_goals exact hs.elim

/-- **A local step keeps the print-phase terms**: the prelude steps down to
the call (the tail call enters `worker`'s body; the call takes no local
step); in `print`'s and `printL`'s bodies by `localStepS_shapeH`. -/
theorem pTermT_step {c c' : Ctl} (h : LocalStepS helloSrc c c') (ht : PTermT c.term) : PTermT c'.term := by
  rcases ht with ht | ht | ht
  · simp only [preTermsH, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht | ht | ht | ht
    · obtain ⟨d, hf, e⟩ := Hello1Runs.localStepS_tail h ht
      rw [HelloSplit.worker_find] at hf
      cases hf
      left; rw [e]; simp [preTermsH, HelloSplit.workerD]
    · left; rw [Hello1Runs.localStepS_split h (by rw [ht]; rfl)]; simp [preTermsH]
    · left; rw [Hello1Runs.localStepS_split h ht]; simp [preTermsH]
    · left; rw [Hello1Runs.localStepS_unpack h ht]; simp [preTermsH]
    · exact (h.not_call (by rw [ht]; rfl)).elim
  · rcases localStepS_shapeH h (printShape_printBody.mem ht) with h' | h'
    · exact .inr (.inl (PrintSvc.printTerms_trans ht h'))
    · exact .inr (.inr (by rw [h']; exact PrintSvc.self_mem_printTerms _))
  · rcases localStepS_shapeH h (printShape_printLBodyP.mem ht) with h' | h'
    · exact .inr (.inr (PrintSvc.printTerms_trans ht h'))
    · exact .inr (.inr (by rw [h']; exact PrintSvc.self_mem_printTerms _))

/-- **A local run keeps the print-phase terms.** -/
theorem pTermT_run {c c' : Ctl} (h : LocalRunS helloSrc c c') (ht : PTermT c.term) : PTermT c'.term := by
  induction h with
  | refl => exact ht
  | step hs _ ih => exact ih (pTermT_step hs ht)

/-- `print`'s body is a print-phase term (`print`'s call enters it). -/
theorem pTermT_printBody : PTermT PrintSrc.printBody := .inr (.inl (PrintSvc.self_mem_printTerms _))

/-- **The spawned child is at a print-phase term** (its tail call into
`worker`). -/
theorem pTermH_spawn {s1 : TermRun.TTh} (ht : s1.term = .tail "worker" [] (.var "a") []) : PTermH s1 :=
  .inl (by rw [ht]; simp [preTermsH])

/-! ## `Post`, unpacked -/

/-- **`Post` unpacked at `PT1h`** (the twin of `WakeW1.Parts`). -/
structure PartsH (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) (w : Q.ι) (t : Cfg) (s : TermRun.Cfg)
    (t0 t1 : Thread isaLSE2) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat)
    (oc : Option (Nat × Nat)) : Prop where
  th : t.1.threads = #[t0, t1]
  ths : s.ths = #[s0, s1]
  core : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
    (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) t.1.mem t0 t1 s.mem s0 s1 ts
    tp sp
  preC : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views
  pt0 : Q.PT0 w t.1.mem s.mem t0 s0
  pt1 : PT1h D w t.1.mem s.mem t1 s1
  prot : CProt (Q.SR w) (Q.C w) oc t.1.mem t1 s.mem s1 ts tp sp
  kr : Q.KR w t s

/-- **`Post` unpacks**, when the relation's worker data is `PT1h D`. -/
theorem post_partsH {Q : WakeRel} {D : WSideH Q.ι} {Λ : Scc.Sem.Layout} (hpt1 : Q.PT1 = PT1h D) {t : Cfg}
    {s : TermRun.Cfg} (h : Q.Post Λ t s) :
    ∃ w t0 t1 s0 s1 ts tp sp oc, PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hs, hcore, hp0, hp1, oc, hprot⟩, hkr⟩ := h
  simp only [WakeRel.PTw, ite_true] at hp0
  simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hpt1] at hp1
  exact ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hth, hs, hcore, hp0.1, hp0.2, hp1, hprot, hkr⟩

/-- info: 'Spike.Lib.HelloW1.printPh_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms printPh_run

/-- info: 'Spike.Lib.HelloW1.storePh_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms storePh_pop

/-- info: 'Spike.Lib.HelloW1.BufV.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BufV.mono

/-- info: 'Spike.Lib.HelloW1.bufV_spawn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bufV_spawn

end Spike.Lib.HelloW1
