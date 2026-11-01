/-
**The worker's steps in the print phase** (C4, relation half, check-in 2c;
data in `Spike/Lib/HelloW1.lean`; the twin of `Spike/Lib/WakeW1Keep.lean`
and `Spike/Lib/WakeW1Frame.lean` at `PT1h`).

- `WCompatH Q D μ Λ arch AbW`: the compatibility facts the print-phase steps
  need (`WakeW1.WCompat`'s fields, at frames where the worker has them);
  each field names its owner.
- `VBuf`: the published buffer's words have latest messages of known values
  with `pairTop`s and views below the spawn size, none at `c` (C3's `hM`,
  `hRd`, `hne` of a run through the buffer's loads; not read by
  `HelloW1Cert.certified_printPh` since WeakCore 621ec97a); `vbuf_of_bufV`:
  from `PT1h`'s `BufV`.
- `PartsH.src_prom`, `PartsH.past_noProm`: as `WakeW1.Parts`'.
- `printPh_not_pass`, `storePh_noStep`: the print phase is before the store
  point; the store phase takes no local step.
- `frameStep_det`, `frameRun_conf`, `retU_frameRun`, `noEmit_frameRun`,
  `clause_frameRun`: frame runs are deterministic, so no `emit` ahead
  (`NoEmit`) and `PT1h`'s print-phase promise clause are kept by a frame run
  to the print phase.
- `certified_phase`: the source worker replaced by a thread in a phase, with
  the same promises and views, is certified (no promise; in the print phase
  with no `emit` ahead `certified_printPh`; at the store `certified_store`; past the store no
  promise).
- `KrW`, `krW_of`: the kernel relation after a worker step (from
  `WCompatH.kr` at `wr 1 = 0`).
- `post_frameH`: `Post` after a worker step (`WakeW1.post_frame` at `PT1h`).
- `post_setP`: a worker step keeping memory and promises, matched by a
  source run replacing thread 1 in a phase, keeps `Post`.
- `post_keepP` (a local run at any depth), `post_callP` (`print`'s call),
  `post_retP` (`print`'s return, into the store phase).
-/
import Spike.Lib.HelloW1Cert
import Spike.Lib.HelloEmitPh
import Spike.Lib.Frames1

namespace Spike.Lib.HelloW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.WakeT1 (srcPo)
open Spike.Lib.HelloSplit (envP wcP workerRestH workerCallH)
open Spike.Lib.HelloPrintSrcPub (callTh)
open Spike.Lib.WakeW1 (EnvCJ W1Mem withThread1 preC_w1)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self certified_nil localRunS_run_source_i)
open Scc.Sem.MemRel (SLatest)

/-! ## The compatibility facts -/

/-- **The worker's compatibility facts in the print phase**, per ghost
record `w`; each field names its owner (as `WakeW1.WCompat`'s; the frame
facts at the worker's frames).

`AbW` is the abort-write phase that `sysOkH` admits `write(2, …)` and
`exit_group abortStatus` in (`print`'s refused `write` reaches
`scc_rt_abort(4)`, then `scc_rt_abort_write`). **Review guard**: the
instantiation must take exactly `Spike.Lib.A64.Flow.Worker.AbW exe`
(`Spike/Lib/A64HelloNN.lean`: the pc at `scc_rt_abort_write`'s two `svc`s,
by labels); `WCompatH` is never built at another `AbW` (`fun _ => True`
would make `sysOkH` admit any `write` and `exit_group`). -/
structure WCompatH (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch)
    (AbW : isaLSE2.State → Prop) : Prop where
  /-- `WakeRel`'s worker data is this file's, with the worker
  mid-`write` (`HelloEmitPh.PT1hE`). -/
  pt1 : Q.PT1 = HelloEmitPh.PT1hE D
  /-- The flag's record is hello's, at the worker's pointer
  word `D.cw w` for `c`. -/
  C : ∀ w, Q.C w = helloC (Q.C w).cT (Q.C w).cS (Q.C w).passT Promises.Knobs.all arch (D.cw w)
  /-- (the spawn rows) The pointer word is an untagged locative to `cS`. -/
  cwv : ∀ w, (D.cw w).val = .loc (Q.C w).cS 0
  /-- (`rfl` at `D.S w := (Q.SR w).S`) The worker side's
  spawn size is the spawn record's source size. -/
  S : ∀ w, D.S w = (Q.SR w).S
  /-- The target store point is the source one under the rows'
  invariant, in a phase: on an empty stack, at `unpark` or `ret ()`.
  (Restricted to `PrintPh ∨ StorePh`: `D.Wi` is closed only up to `Pend`,
  so it admits junk frame stacks outside the phases.) -/
  pass : ∀ w s (s1 : TermRun.TTh), D.Wi w s (Ctl.of s1) s1.stack →
    (PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 ∨ StorePh (D.cw w) s1) →
    ((Q.C w).passT s ↔ WPass s1)
  /-- (worker side) The worker's states are in the wide fragment. -/
  wide : ∀ w s c fs, D.Wi w s c fs → Scc.Cert.WideA64.WideSt s
  /-- (worker side) The worker is at no transfer site. -/
  noSite : ∀ w s c fs, D.Wi w s c fs → siteAt abi μ s = none
  /-- (worker side) At a system call the worker's instruction, if any,
  faults (`WakeW1.WCompat.sysExec`). -/
  sysExec : ∀ w s c fs t, D.Wi w s c fs → abi.atSys s = true → isaLSE2.exec s = some t → ∃ m, t = .fault m
  /-- (worker side) The worker's system calls are `exit`, a `write` to
  fd 1 (`print`'s), in the abort-write phase `AbW` a `write` to fd 2 or
  `exit_group abortStatus` (`scc_rt_abort_write`'s), or neither a `write`
  nor `exit_group` (`WakeW1.WCompat.sysOk`, weakened by `print`'s write and
  its abort path). -/
  sysOkH : ∀ w s c fs call, D.Wi w s c fs → abi.atSys s = true →
    decode abi.nrs (abi.nr s) (abi.arg s) = some call →
    call = .exit ∨ (∃ buf n, call = .write 1 buf n) ∨
      (AbW s ∧ ((∃ buf n, call = .write 2 buf n) ∨ call = .exitGroup abortStatus)) ∨
      ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)
  /-- The worker's owned words, at any frames, are in its cover set
  ... -/
  ownCov : ∀ w s fs L v, (L, v) ∈ Q.own w 1 s fs → (Q.P w).cov 1 L
  /-- ... and none of main's. -/
  ownDisj : ∀ w s0 fs0 s fs L v v', (L, v) ∈ Q.own w 0 s0 fs0 → (L, v') ∈ Q.own w 1 s fs → False
  /-- main's per-thread relation is stable under a worker step. -/
  pt0 : ∀ w tm sm t0 s0 tm' sm', Q.PT0 w tm sm t0 s0 → W1Mem (Q.P w) (Q.C w).cS tm sm tm' sm' →
    Q.PT0 w tm' sm' t0 s0
  /-- (`kr_frame1`) The kernel relation is stable under a step of the
  worker that keeps the kernel state, main's target and source threads and
  the source trace, with no byte of a worker `write` out (`wr 1 = 0`) and
  the worker after the step in its invariant (at `HelloKRE.KRHE` the link
  `Lk` reads thread 1, design (i′)). -/
  kr : ∀ w t t' s s', Q.KR w t s → t.2.wr 1 = 0 → t'.2 = t.2 → t'.1.threads[0]? = t.1.threads[0]? →
    s'.ths[0]? = s.ths[0]? → s'.trace = s.trace →
    (∀ t1 s1, t'.1.threads[1]? = some t1 → s'.ths[1]? = some s1 → D.Wi w t1.st (Ctl.of s1) s1.stack) →
    Q.KR w t' s'

/-- **`WCompatH.pass`'s shape** at a store-point predicate `passT` (the
instances' premise). -/
abbrev PassH {ι : Type} (D : WSideH ι) (passT : isaLSE2.State → Prop) : Prop :=
  ∀ w s (s1 : TermRun.TTh), D.Wi w s (Ctl.of s1) s1.stack →
    (PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 ∨ StorePh (D.cw w) s1) → (passT s ↔ WPass s1)

/-- **The published buffer, as the print phase reads it** (/C3,
`helloSrc_frzL`): the `m` words at label `l` have latest messages of values
`wv i`, with `pairTop`s and views at most `S - 1`, none at `cS`. -/
def VBuf (l : WeakMem.AllocLabel) (m S : Nat) (cS : WeakMem.Address) (s : TermRun.Cfg) : Prop :=
  ∃ wv : Nat → Nat,
    (∀ i < m, ∃ j msg, SLatest s.mem ⟨l, i⟩ j ∧ s.mem[j]? = some msg ∧ msg.val = .num (wv i)) ∧
    (∀ i < m, ∀ j msg, SLatest s.mem ⟨l, i⟩ j → s.mem[j]? = some msg →
      Promises.pairTop s.pairs j ≤ S - 1 ∧ msg.view ≤ S - 1) ∧
    ∀ i < m, (⟨l, i⟩ : WeakMem.Address) ≠ cS

/-- **`VBuf` from `PT1h`'s `BufV`**, at `c`'s address `cS` (the pointer word
`cw`'s): the latest messages are unique (`sLatest_unique`), their `pairTop`s
at most one past them (`pairTop_le'`). -/
theorem vbuf_of_bufV {l : WeakMem.AllocLabel} {m S : Nat} {cw : TermRun.Word} {cS : WeakMem.Address}
    {s : TermRun.Cfg} (h : BufV l m S cw s.mem) (hcw : cw.val = .loc cS 0) : VBuf l m S cS s := by
  obtain ⟨-, wv, hb⟩ := h
  refine ⟨wv, fun i hi => ?_, fun i hi j msg hl hj => ?_, fun i hi he => ?_⟩
  · obtain ⟨-, j, msg, hl, hj, hv, -⟩ := hb i hi
    exact ⟨j, msg, hl, hj, hv⟩
  · obtain ⟨-, j', msg', hl', hj', -, hjS, hvw⟩ := hb i hi
    obtain rfl := sLatest_unique hl hl'
    rw [hj] at hj'
    cases hj'
    exact ⟨Nat.le_trans (TermViewInv.pairTop_le' s.pairs j) (by omega), hvw⟩
  · obtain ⟨hne, -⟩ := hb i hi
    exact hne (by rw [hcw, he])

/-! ## Phase facts -/

/-- The source thread with a control `c` (no hold) has control `c`. -/
theorem ctl_of_set (s1 : TermRun.TTh) {c : Ctl} (hh : c.hold = none) :
    Ctl.of { s1 with term := c.term, env := c.env } = c := by
  obtain ⟨tm, en, hd⟩ := c
  simp only at hh
  subst hh
  rfl

/-- No local step at `unpark` (an extern). -/
theorem wkUnpark_noStep {c c₁ : Ctl} (h : LocalStepS helloSrc c c₁) (ht : c.term = wkUnpark) : False := by
  have := h.2 { p := helloSrc, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := c.term, env := c.env } rfl rfl rfl rfl
  simp [TermRun.tstep, ht, wkUnpark, TermRun.evalOp] at this

/-- **No local step at the store**: the store pushes a message (as
`WakeW1.localStep_wkStore_false`, at `helloSrc` and any depth). -/
theorem wkStore_noStep {cw : TermRun.Word} {cS : WeakMem.Address} {c c₁ : Ctl} (h : LocalStepS helloSrc c c₁)
    (ht : c.term = wkStore) (hc : EnvCJ cw c.env) (hcw : cw.val = .loc cS 0) : False := by
  obtain ⟨⟨t, μ, u, hev, hcell, hu⟩, -⟩ := hc
  let g : TermRun.G := { p := helloSrc, k := Promises.Knobs.all, arch := .arm, n := 2, i := 1, lbase := 0 }
  let th : TermRun.TTh := { term := c.term, env := c.env }
  have hA : AtStore cw cS th := ⟨ht, rfl, rfl, ⟨t, μ, u, hev, hcell, hu⟩, hcw⟩
  obtain ⟨th1, hs, -⟩ := stepStore_append_mem g.k g.arch #[] (TermRun.mth (TermRun.stOf #[] [] th) cw one one) cS
    (TermRun.dataE 1 one) [0] true
  have hm := atStore_tstep (g := g) (pairs := []) hA hs
  rw [h.2 g #[] [] th rfl rfl rfl rfl] at hm
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  have := congrArg Array.size hm.1
  simp at this

/-- **The store phase takes no local step.** -/
theorem storePh_noStep {cw : TermRun.Word} {cS : WeakMem.Address} {s1 : TermRun.TTh} {c₁ : Ctl}
    (h : StorePh cw s1) (hcw : cw.val = .loc cS 0) (hs : LocalStepS helloSrc (Ctl.of s1) c₁) : False := by
  obtain ⟨-, ht | ht | ht, hcj⟩ := h
  · exact wkStore_noStep hs ht hcj hcw
  · exact wkUnpark_noStep hs ht
  · exact localStepS_not_ret hs .unit ht

/-- **The print phase is before the store point.** -/
theorem printPh_not_pass {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {s1 : TermRun.TTh}
    (h : PrintPh l n m cw s1) : ¬ WPass s1 := by
  rintro ⟨hst, ht⟩
  obtain ⟨w0, w1, w2, w4, -, -, -, -, -, ⟨-, hr⟩ | ⟨hst', -⟩⟩ := h
  · rcases localRunS_cases hr with he | ⟨c₁, hs⟩
    · have : s1.term = workerCallH := congrArg Ctl.term he
      rw [this] at ht
      rcases ht with ht | ht <;> simp [workerCallH, wkUnpark] at ht
    · rcases ht with ht | ht
      · exact wkUnpark_noStep hs ht
      · exact localStepS_not_ret hs .unit ht
  · rw [hst] at hst'; cases hst'

/-- **The store phase is not the print phase** (it takes no local step, and
its control is not `print`'s call). -/
theorem storePh_not_printPh {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {cS : WeakMem.Address}
    {s1 : TermRun.TTh} (h : StorePh cw s1) (hcw : cw.val = .loc cS 0) : ¬ PrintPh l n m cw s1 := by
  intro hP
  obtain ⟨w0, w1, w2, w4, -, -, -, -, -, ⟨-, hr⟩ | ⟨hst', -⟩⟩ := hP
  · rcases localRunS_cases hr with he | ⟨c₁, hs⟩
    · have : s1.term = workerCallH := congrArg Ctl.term he
      obtain ⟨-, ht, -⟩ := h
      rw [this] at ht
      rcases ht with ht | ht | ht <;> simp [workerCallH, wkStore, wkUnpark] at ht
    · exact storePh_noStep h hcw hs
  · rw [h.1] at hst'; cases hst'

/-! ## No `emit` ahead under frame runs -/

/-- **A frame step is determined** by its pair (`HelloStep1P.FrameStep.det`'s
twin, above it in the imports). -/
theorem frameStep_det {p : Prog} {q q₁ q₂ : Ctl × List TermRun.Frame} (h₁ : FrameStep p q q₁)
    (h₂ : FrameStep p q q₂) : q₁ = q₂ := by
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

/-- **Two frame runs from one pair are ordered**: one's end is on the way to
the other's (frame steps are deterministic). -/
theorem frameRun_conf {p : Prog} {q r q' : Ctl × List TermRun.Frame} (hr : FrameRun p q r)
    (hq : FrameRun p q q') : FrameRun p q' r ∨ FrameRun p r q' := by
  induction hr generalizing q' with
  | refl q => exact .inr hq
  | @step q q₁ r hs hr ih =>
    cases hq with
    | refl => exact .inl (.step hs hr)
    | step hs' hq' =>
      obtain rfl := frameStep_det hs hs'
      exact ih hq'

/-- **Past `print`'s return** (on its call's frame, `j` bound to main's
thread id) a frame run is empty or the return itself, to the store, which
takes no step. -/
theorem retU_frameRun {cw w0 w1 w2 w4 : TermRun.Word} {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0)
    (hj : w4.val = WakeW1.mainTidW) {env : TermRun.Env} {q' : Ctl × List TermRun.Frame}
    (h : FrameRun helloSrc (⟨.ret .unit, env, none⟩, [uFrame w0 w1 w2 cw w4]) q') :
    q' = (⟨.ret .unit, env, none⟩, [uFrame w0 w1 w2 cw w4]) ∨
      (q'.2 = [] ∧ q'.1.term = wkStore ∧ EnvCJ cw q'.1.env) := by
  cases h with
  | refl => exact .inl rfl
  | step hs h2 =>
    right
    cases hs with
    | loc hl => exact (hl.not_ret .unit rfl).elim
    | call hc => cases hc
    | @ret _ _ _ a t ws hc hfr ha =>
      have hcj : EnvCJ cw (("u", Ty.unit, ws) :: envP w0 w1 w2 cw w4) :=
        ⟨⟨.ptr .pub .int, .pub, .int, by simp [envP, TermRun.evalAt, TermRun.lookupE], rfl, rfl⟩, .tid, w4,
          by simp [envP, TermRun.evalAt, TermRun.lookupE], hj⟩
      cases h2 with
      | refl => exact ⟨rfl, rfl, hcj⟩
      | step hs2 _ =>
        cases hs2 with
        | loc hl => exact (wkStore_noStep hl rfl hcj hcw).elim
        | call hc2 => simp [uFrame, workerRestH] at hc2

/-- **No `emit` ahead is kept by a frame run**, to the print phase (or the
run passes `print`'s return, into the store phase). -/
theorem noEmit_frameRun {cw : TermRun.Word} {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0) {s1 : TermRun.TTh}
    (hN : NoEmit cw s1) {q' : Ctl × List TermRun.Frame} (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q')
    (hh : q'.1.hold = none) :
    NoEmit cw { s1 with term := q'.1.term, env := q'.1.env, stack := q'.2 } ∨
      StorePh cw { s1 with term := q'.1.term, env := q'.1.env, stack := q'.2 } := by
  obtain ⟨w0, w1, w2, w4, env, hj, hN⟩ := hN
  have hc : Ctl.of { s1 with term := q'.1.term, env := q'.1.env, stack := q'.2 } = q'.1 := by
    obtain ⟨⟨_, _, _⟩, _⟩ := q'
    simp only at hh
    subst hh
    rfl
  rcases frameRun_conf hN hr with h | h
  · exact .inl ⟨w0, w1, w2, w4, env, hj, by rw [hc]; exact h⟩
  · rcases retU_frameRun hcw hj h with rfl | ⟨h2, h3, h4⟩
    · exact .inl ⟨w0, w1, w2, w4, env, hj, by rw [hc]; exact .refl _⟩
    · exact .inr ⟨h2, .inl h3, h4⟩

/-- **The print phase's promise clause is kept by a frame run** to the print
phase (`PT1h`'s `s1.promises = [] ∨ NoEmit`; the promises are kept). -/
theorem clause_frameRun {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {cS : WeakMem.Address}
    (hcw : cw.val = .loc cS 0) {s1 : TermRun.TTh} (hc : s1.promises = [] ∨ NoEmit cw s1)
    {q' : Ctl × List TermRun.Frame} (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hh : q'.1.hold = none)
    (hP : PrintPh l n m cw { s1 with term := q'.1.term, env := q'.1.env, stack := q'.2 }) :
    s1.promises = [] ∨ NoEmit cw { s1 with term := q'.1.term, env := q'.1.env, stack := q'.2 } :=
  hc.imp id fun hN => (noEmit_frameRun hcw hN hr hh).resolve_right fun hS => storePh_not_printPh hS hcw hP

/-! ## `Post`, unpacked: the promise -/

namespace PartsH

variable {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {AbW : isaLSE2.State → Prop}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

theorem s1_get (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : s.ths[1]? = some s1 := by
  rw [h.ths]; rfl

/-- `helloC`'s store point is `WPass`. -/
theorem passS_iff (hC : WCompatH Q D μ Λ arch AbW) (th : TermRun.TTh) : (Q.C w).passS th ↔ WPass th := by
  rw [hC.C w]; rfl

/-- **A source promise of the worker is the protocol's `kc`.** -/
theorem src_prom (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) {k : Nat}
    (hk : k ∈ s1.promises) : ∃ Tc, oc = some (Tc, k) := by
  obtain ⟨hS, m, hm, hl⟩ := h.pt1.2.2.2.2.1 k hk
  rw [hC.cwv w] at hl
  injection hl with hl1
  rw [hC.S w] at hS
  exact h.prot.smsg k m hm hS (by first | exact hl1 | exact hl1.symm)

/-- **Past its store the source worker has no promise** (as
`WakeW1.Parts.past_noProm`). -/
theorem past_noProm (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hpast : WPass s1) : s1.promises = [] := by
  cases hp : s1.promises with
  | nil => rfl
  | cons k ks =>
    have hk : k ∈ s1.promises := by rw [hp]; exact List.mem_cons_self
    obtain ⟨Tc, rfl⟩ := h.src_prom hC hk
    have hpS : (Q.C w).passS s1 := (passS_iff (w := w) hC s1).mpr hpast
    obtain ⟨Tc', kc', hoc, hn⟩ := h.prot.pass_done (h.prot.pass_iff.mpr hpS)
    simp only [Option.some.injEq, Prod.mk.injEq] at hoc
    obtain ⟨rfl, rfl⟩ := hoc
    obtain ⟨hT, -, hts, -, -⟩ := h.prot.some_msg Tc k rfl
    have := (h.core.mem.prom_corr k Tc hts (by omega)).mp ((h.core.sp_prom k).mpr (.inr hk))
    exact absurd this hn

/-- **The source worker in a phase is certified**: thread 1 replaced by
`s1'` in the print or the store phase, with `s1`'s promises and views, not
past the store unless `s1` is. With no promise, trivially; with the flag's
promise `kc` (G1–G3 from `CProtS`, `fulfil_ok`): in the print phase by the
run through `print` (`certified_printPh`, the buffer read by `hV`; `hSw`
from `prom_view`, `hSt` from `some_msg` with `0 < S` by `pre_lt`'s
`obS < S`), at the store by its
fulfilment (`certified_store`); past the store `s1` has no promise. -/
theorem certified_phase (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {s1' : TermRun.TTh} (hN : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1' →
      s1'.promises = [] ∨ NoEmit (D.cw w) s1')
    (hph : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1' ∨ StorePh (D.cw w) s1') (hσ : s1'.σs = [])
    (hsp : s1'.promises = s1.promises) (hvs : s1'.vs = s1.vs) (hpass : WPass s1' → WPass s1) :
    TermRun.Certified helloSrc Promises.Knobs.all arch { s with ths := s.ths.set! 1 s1' } 1 := by
  have hi' : ({ s with ths := s.ths.set! 1 s1' } : TermRun.Cfg).ths[1]? = some s1' :=
    getElem?_set!_self h.s1_get s1'
  have hcw := hC.cwv w
  obtain hp | ⟨k, ks, hp⟩ : s1.promises = [] ∨ ∃ k ks, s1.promises = k :: ks := by
    cases s1.promises <;> simp
  · exact certified_nil hi' (by rw [hsp, hp])
  · have hk : k ∈ s1.promises := by rw [hp]; exact List.mem_cons_self
    have hks : ks = [] := by
      have := h.pt1.2.2.2.1; rw [hp] at this; simpa using this
    subst hks
    obtain ⟨Tc, rfl⟩ := h.src_prom hC hk
    have hnp : ¬ WPass s1 := fun hpast => by rw [h.past_noProm hC hpast] at hp; cases hp
    have hnpS : ¬ (Q.C w).passS s1 := fun hps => hnp ((passS_iff (w := w) hC s1).mp hps)
    have hS := ((cProt_iff _ _ _).mp h.prot).2.1
    obtain ⟨-, m, hm, hml, hmv⟩ := hS.some_msg Tc k rfl
    have hksp : k ∈ sp := (h.core.sp_prom k).mpr (.inr hk)
    obtain ⟨hmv', hob⟩ := fulfil_ok hS hnpS hksp hm
    rw [hC.C w] at hmv' hob
    have hmv'' : Promises.storeMview (wTh s1'.vs (D.cw w)) (TermRun.dataE 1 one) [0] true ≤ m.view := by
      rw [hvs]; exact hmv'
    have hob'' : Promises.storeOb Promises.Knobs.all arch (wTh s1'.vs (D.cw w)) (Q.C w).cS (TermRun.dataE 1 one)
        [0] < k := by
      rw [hvs]; exact hob
    have hm' : ({ s with ths := s.ths.set! 1 s1' } : TermRun.Cfg).mem[k]? = some ⟨(Q.C w).cS, .num 1, m.view⟩ := by
      show s.mem[k]? = _
      rw [hm, ← hml, ← hmv]
    have hp' : s1'.promises = [k] := by rw [hsp, hp]
    rcases hph with hP | ⟨hst, ht | ht | ht, hcj⟩
    · exact certified_printPh ((hN hP).resolve_left (by rw [hp']; simp)) hi' hσ hp' hm' hcw hmv'' hob''
    · exact certified_store hi' ⟨ht, hst, hσ, hcj.1, hcw⟩ hp' hm' hmv'' hob''
    · exact absurd (hpass ⟨hst, .inl ht⟩) hnp
    · exact absurd (hpass ⟨hst, .inr ht⟩) hnp

end PartsH

/-! ## Reassembling `Post` -/

/-- **The kernel relation after a worker step** replacing thread 1 by `t1'`
and the memory by `mem'`, the kernel state `k'`, at every source
configuration keeping main's source thread and the trace, with the source
worker `s1'` in the worker's invariant `D.Wi`. From `WCompatH.kr` with no
byte out and the kernel state kept (`krW_of`); a kernel step
(`HelloStep1Sys`) or a promise proves it from the relation itself. -/
def KrW (Q : WakeRel) (D : WSideH Q.ι) (w : Q.ι) (t : Cfg) (s : TermRun.Cfg) (t1' : Thread isaLSE2)
    (mem' : Memory) (s1' : TermRun.TTh) (k' : KState) : Prop :=
  ∀ s' : TermRun.Cfg, s'.ths[0]? = s.ths[0]? → s'.ths[1]? = some s1' → s'.trace = s.trace →
    D.Wi w t1'.st (Ctl.of s1') s1'.stack → Q.KR w (t.1.withThread 1 t1' mem', k') s'

/-- **`KrW` from `WCompatH.kr`**, with no byte of a worker `write` out. -/
theorem krW_of {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
    {AbW : isaLSE2.State → Prop} (hC : WCompatH Q D μ Λ arch AbW) {w : Q.ι} {t : Cfg} {s : TermRun.Cfg}
    {t0 t1 t1' : Thread isaLSE2} {mem' : Memory} (hkr : Q.KR w t s) (hwr : t.2.wr 1 = 0)
    {s1' : TermRun.TTh} (hth : t.1.threads = #[t0, t1]) : KrW Q D w t s t1' mem' s1' t.2 := by
  intro s' hs0 hs1 htr hW
  refine hC.kr w t _ s s' hkr hwr rfl ?_ hs0 htr ?_
  · show (t.1.withThread 1 t1' mem').threads[0]? = t.1.threads[0]?
    rw [withThread1 hth, hth]; rfl
  · intro u1 v1 h1 h2
    have e1 : (t.1.withThread 1 t1' mem').threads[1]? = some t1' := by rw [withThread1 hth]; rfl
    obtain rfl : u1 = t1' := Option.some.inj (h1.symm.trans e1)
    obtain rfl : v1 = s1' := Option.some.inj (h2.symm.trans hs1)
    exact hW

/-- **`Post` after a worker step** (`WakeW1.post_frame` at `PT1h`). -/
theorem post_frameH {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
    {AbW : isaLSE2.State → Prop} (hC : WCompatH Q D μ Λ arch AbW) {w : Q.ι} {t : Cfg} {s s' : TermRun.Cfg}
    {t0 t1 t1' : Thread isaLSE2} {k' : KState}
    {s0 s1' : TermRun.TTh} {mem' : Memory} {ts' : Nat → Option Nat} {tp' sp' : List Nat}
    {s1 : TermRun.TTh} (hth : t.1.threads = #[t0, t1]) (hs : s.ths = #[s0, s1]) (hs' : s'.ths = #[s0, s1'])
    (hpre : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views) (hpt0 : Q.PT0 w t.1.mem s.mem t0 s0)
    (hkr : KrW Q D w t s t1' mem' s1' k') (hT : (Q.SR w).T ≤ t.1.mem.last)
    (hm : W1Mem (Q.P w) (Q.C w).cS t.1.mem s.mem mem' s'.mem)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1'.st s1'.stack)
      mem' t0 t1' s'.mem s0 s1' ts' tp' sp')
    (hpt1 : PT1h D w mem' s'.mem t1' s1')
    (hprot : HelloProt (Q.SR w) (Q.C w) (Q.pT w) mem' t0 t1' s'.mem s0 s1' ts' tp' sp')
    (htr : s'.trace = s.trace) :
    Q.Post Λ (t.1.withThread 1 t1' mem', k') s' := by
  have hth' := withThread1 (t1' := t1') (mem := mem') hth
  refine ⟨w, ⟨t0, t1', s0, s1', ts', tp', sp', hth', hs', hcore, ?_, ?_, hprot⟩, ?_⟩
  · simp only [WakeRel.PTw]
    exact ⟨preC_w1 hpre hT hm, hC.pt0 w _ _ t0 s0 _ _ hpt0 hm⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    exact .inl hpt1
  · exact hkr s' (by rw [hs', hs]; rfl) (by rw [hs']; rfl) htr hpt1.1

variable {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {AbW : isaLSE2.State → Prop}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **A worker step keeping memory and promises keeps `Post`**, matched by a
source run (given its end's certificate) replacing thread 1 by `s1'` in a
phase, with `s1`'s promises and views, on the same side of the store point;
thread 1 replaced by `t1'` (same promises, its bound, cover, owned words and
no-promise fact at the memory) with `Wi w t1'.st` at `s1'`. -/
theorem post_setP (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t1' : Thread isaLSE2} {s1' : TermRun.TTh} {k' : KState} (hkr : KrW Q D w t s t1' t.1.mem s1' k')
    (hB : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1' → BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem)
    (hT : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1' → PTermH s1')
    (hN : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1' → s1'.promises = [] ∨ NoEmit (D.cw w) s1')
    (hrun : TermRun.Certified helloSrc Promises.Knobs.all arch { s with ths := s.ths.set! 1 s1' } 1 →
      (helloS arch).Run s [] { s with ths := s.ths.set! 1 s1' })
    (hph : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1' ∨ StorePh (D.cw w) s1') (hσ : s1'.σs = [])
    (hsp : s1'.promises = s1.promises) (hvs : s1'.vs = s1.vs) (hpass : WPass s1' ↔ WPass s1)
    (hp : t1'.prom = t1.prom) (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    (hown : ExtRows.OwnOk (Q.own w 1 t1'.st s1'.stack) t.1.mem t1'.prom)
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = []) (hwi : D.Wi w t1'.st (Ctl.of s1') s1'.stack) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' t.1.mem, k') s' := by
  have hs' : ({ s with ths := s.ths.set! 1 s1' } : TermRun.Cfg).ths = #[s0, s1'] := by
    show s.ths.set! 1 s1' = _
    rw [h.ths]; rfl
  have hpT : (Q.C w).passT t1.st ↔ WPass s1 := hC.pass w _ s1 h.pt1.1 (h.pt1.2.2.1.imp_left And.left)
  have hpT' : (Q.C w).passT t1'.st ↔ WPass s1' := hC.pass w _ s1' hwi hph
  refine ⟨_, hrun (h.certified_phase hC hN hph hσ hsp hvs hpass.mp),
    post_frameH (ts' := ts) (tp' := tp) (sp' := sp) hC h.th h.ths hs' h.preC h.pt0 hkr h.core.T_le
      ⟨.inl rfl, .inl rfl⟩ ?_ ?_ ?_ rfl⟩
  · refine core1_same h.core (by simp) hp hsp hb hcov (by rw [hvs]; exact h.core.scov1) ?_ ?_ ?_ hnp
    · simpa only [Nat.one_ne_zero, ite_false] using hown
    · intro L v v' h0 h1
      simp only [ite_true] at h0
      simp only [Nat.one_ne_zero, ite_false] at h1
      exact hC.ownDisj w _ _ _ _ L v v' h0 h1
    · intro L v h1
      simp only [Nat.one_ne_zero, ite_false] at h1
      exact hC.ownCov w _ _ L v h1
  · exact ⟨hwi, hσ, hph.imp_left fun hP => ⟨hP, hB hP, hT hP, hN hP⟩, by rw [hsp]; exact h.pt1.2.2.2.1,
      by rw [hsp]; exact h.pt1.2.2.2.2.1,
      hp ▸ h.pt1.2.2.2.2.2⟩
  · obtain ⟨hT, hS, -⟩ := (cProt_iff _ _ _).mp h.prot
    have hpT'' : (Q.C w).passT t1'.st ↔ (Q.C w).passT t1.st := hpT'.trans (hpass.trans hpT.symm)
    refine ⟨oc, (cProt_iff _ _ _).mpr ⟨⟨hT.tmsg, hT.some_msg,
      fun Tc kc hoc htp => hp ▸ hT.prom_worker Tc kc hoc htp,
      fun hq => hT.pass_done (hpT''.mp hq), fun hq => hT.pass_prom (fun h' => hq (hpT''.mpr h'))⟩,
      cProtS_vs hS ?_ hsp ?_, ?_⟩⟩
    · rw [hC.C w]
      exact ⟨by simp only [helloC, hvs], by simp only [helloC, hvs]⟩
    · intro hn h'
      exact hn ((PartsH.passS_iff hC s1').mpr (hpass.mpr ((PartsH.passS_iff hC s1).mp h')))
    · rw [PartsH.passS_iff hC s1']; exact hpT'

/-- **A local run at any depth keeps `Post`**: in the print phase the run
stays in it (`printPh_run`); in the store phase it is empty
(`storePh_noStep`). The buffer premise is needed in the print phase only. -/
theorem post_keepP (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hwr : t.2.wr 1 = 0)
    (hex : SrcSem.mainExit s = []) {t1' : Thread isaLSE2} {c' : Ctl} (hp : t1'.prom = t1.prom)
    (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    (hown : ExtRows.OwnOk (Q.own w 1 t1'.st s1.stack) t.1.mem t1'.prom)
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = [])
    (hr : LocalRunS helloSrc (Ctl.of s1) c') (hh : c'.hold = none) (hwi : D.Wi w t1'.st c' s1.stack) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' t.1.mem, t.2) s' := by
  have hrun := fun hc => localRunS_run_source_i (P := srcPo 2 arch helloSrc) rfl (by decide) hr h.s1_get rfl rfl
    h.pt1.2.1 hex hc
  rcases h.pt1.2.2.1 with ⟨hP, hB, hT, hN⟩ | hS
  · have hP' := printPh_run hh hr rfl hP
    exact post_setP (s1' := { s1 with term := c'.term, env := c'.env }) hC h (krW_of hC h.kr hwr h.th)
      (fun _ => hB)
      (fun _ => pTermT_run hr hT) (clause_frameRun (q' := (c', s1.stack)) (hC.cwv w) hN (.ofLocalS hr _) hh)
      hrun (.inl hP')
      h.pt1.2.1 rfl rfl ⟨fun x => absurd x (printPh_not_pass hP'), fun x => absurd x (printPh_not_pass hP)⟩
      hp hb hcov hown hnp (by rw [ctl_of_set s1 hh]; exact hwi)
  · rcases localRunS_cases hr with he | ⟨c₁, hs1⟩
    · subst he
      exact post_setP (s1' := s1) hC h (krW_of hC h.kr hwr h.th)
        (fun hP => absurd hP (storePh_not_printPh hS (hC.cwv w)))
        (fun hP => absurd hP (storePh_not_printPh hS (hC.cwv w)))
        (fun hP => absurd hP (storePh_not_printPh hS (hC.cwv w))) hrun (.inr hS)
        h.pt1.2.1 rfl rfl Iff.rfl hp hb hcov hown hnp hwi
    · exact (storePh_noStep hS (hC.cwv w) hs1).elim

/-- **`print`'s call keeps `Post`**: at the call (in the print phase, on an
empty stack), the source pushes the call's frame and enters `print`'s body
on the slice's words (`call_printP_i`); still in the print phase
(`printPh_call`). -/
theorem post_callP (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hwr : t.2.wr 1 = 0)
    (hex : SrcSem.mainExit s = []) {t1' : Thread isaLSE2} {w0 w1 w2 : TermRun.Word} (ht : s1.term = workerCallH)
    (hst : s1.stack = [])
    (ha : TermRun.evalAt s1.env (.var "sl") = some (HelloRodataSrc.sliceTyP, [w0, w1, w2]))
    (hp : t1'.prom = t1.prom) (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    (hown : ExtRows.OwnOk (Q.own w 1 t1'.st (callTh s1 "u" workerRestH [w0, w1, w2]).stack) t.1.mem t1'.prom)
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = [])
    (hwi : D.Wi w t1'.st (Ctl.of (callTh s1 "u" workerRestH [w0, w1, w2]))
      (callTh s1 "u" workerRestH [w0, w1, w2]).stack) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' t.1.mem, t.2) s' := by
  have hPB : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 ∧
      BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem ∧ PTermH s1 ∧
      (s1.promises = [] ∨ NoEmit (D.cw w) s1) := by
    rcases h.pt1.2.2.1 with hP | ⟨-, hs, -⟩
    · exact hP
    · exfalso
      rw [ht] at hs
      rcases hs with hs | hs | hs <;> simp [workerCallH, wkStore, wkUnpark] at hs
  obtain ⟨hP, hB, -, hN⟩ := hPB
  obtain ⟨v0, v1, v2, hev, hP'⟩ := printPh_call hP hst ht
  rw [ha] at hev
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and] at hev
  obtain ⟨rfl, rfl, rfl, -⟩ := hev
  have hstep := fun hc => HelloPrintSrcPub.call_printP_i (P := srcPo 2 arch helloSrc) rfl
    HelloPrintSrcPub.printPD_find (by decide) h.s1_get ht h.pt1.2.1 ha hex hc
  have hcall : FrameStep helloSrc (Ctl.of s1, s1.stack)
      (⟨PrintSrc.printBody, [("a", HelloRodataSrc.sliceTyP, [w0, w1, w2])], none⟩,
        ⟨"u", workerRestH, s1.env, [], .unit⟩ :: s1.stack) :=
    .call (by show s1.term = _; rw [ht]; rfl) HelloPrintSrcPub.printPD_find ha
  refine post_setP (s1' := callTh s1 "u" workerRestH [w0, w1, w2]) hC h (krW_of hC h.kr hwr h.th)
    (fun _ => hB) (fun _ => pTermT_printBody) (clause_frameRun (hC.cwv w) hN (.single hcall) rfl)
    (fun hc => LRun.step (step := fun c es c' => ∃ i, (helloS arch).step i c es c') ⟨1, hstep hc⟩ (LRun.refl _))
    (.inl hP') h.pt1.2.1 rfl rfl ⟨fun x => absurd x (printPh_not_pass hP'), fun x => absurd x (printPh_not_pass hP)⟩
    hp hb hcov hown hnp hwi

/-- **`print`'s return keeps `Post`**: at `ret ()` inside `print` (the
print phase on the call's frame), the source pops the frame
(`HelloPrintSrcPub.ret_i`), landing at the store (`storePh_pop`); neither
side is past the store point. -/
theorem post_retP (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hwr : t.2.wr 1 = 0)
    (hex : SrcSem.mainExit s = []) {t1' : Thread isaLSE2} (ht : s1.term = .ret .unit) (hst : s1.stack ≠ [])
    (hp : t1'.prom = t1.prom) (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    (hown : ∀ fr rest, s1.stack = fr :: rest → ExtRows.OwnOk (Q.own w 1 t1'.st rest) t.1.mem t1'.prom)
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = [])
    (hwi : ∀ fr rest, s1.stack = fr :: rest → D.Wi w t1'.st (Ctl.of (SrcCalls.popTh s1 fr rest [])) rest) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 t1' t.1.mem, t.2) s' := by
  have hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 := by
    rcases h.pt1.2.2.1 with hP | ⟨hs, -, -⟩
    · exact hP.1
    · exact absurd hs hst
  obtain ⟨w0, w1, w2, w4, hj, -, -, -, -, ⟨hst', -⟩ | ⟨hst', -⟩⟩ := hP
  · exact absurd hst' hst
  have hstep := fun hc => HelloPrintSrcPub.ret_i (P := srcPo 2 arch helloSrc) (ws := []) rfl (by decide) h.s1_get ht
    hst' rfl hex hc
  refine post_setP hC h (krW_of hC h.kr hwr h.th)
    (fun hP => absurd hP (storePh_not_printPh (storePh_pop hj s1) (hC.cwv w)))
    (fun hP => absurd hP (storePh_not_printPh (storePh_pop hj s1) (hC.cwv w)))
    (fun hP => absurd hP (storePh_not_printPh (storePh_pop hj s1) (hC.cwv w)))
    (fun hc => LRun.step (step := fun c es c' => ∃ i, (helloS arch).step i c es c') ⟨1, hstep hc⟩ (LRun.refl _))
    (.inr (storePh_pop hj s1)) rfl rfl rfl ⟨fun ⟨_, hq⟩ => ?_, fun ⟨hq, _⟩ => absurd hq hst⟩
    hp hb hcov (hown _ _ hst') hnp (hwi _ _ hst')
  rcases hq with hq | hq <;> simp [SrcCalls.popTh, uFrame, workerRestH, wkUnpark] at hq

/-- info: 'Spike.Lib.HelloW1.PartsH.certified_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PartsH.certified_phase

/-- info: 'Spike.Lib.HelloW1.post_keepP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_keepP

/-- info: 'Spike.Lib.HelloW1.post_callP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_callP

/-- info: 'Spike.Lib.HelloW1.post_retP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_retP

end Spike.Lib.HelloW1
