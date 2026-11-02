/-
**hello.w on x86-64: `WCompatH.pass` at the worker side** (`X64HelloW1.PassH`, the
phase-restricted store point): the target store point `passT` is the source
one (`WPass`) at every invariant pair in a phase, given that the segment's
control fact `Z` pairs `passT` with the source store point (`PassZ`) and the
invariant lies in `Pend helloSrc Z` (`X64HelloWorkerRR.helloDR_inv`).

- `PrR`: the frame pairs reachable from the print phase: before `print`'s
  call (a local run to `wcP`, no frame), inside `print` (on `uFrame`, a local
  run to an anchor), or at `print`'s return point `wcR` (no frame);
  `prR_of`: the print phase is in `PrR`; `prR_step`, `prR_run`: `PrR` is
  closed under frame steps (local steps are deterministic, the anchors take
  none, `wcP`'s call enters `print` at `X64HelloW1.entry_anchor`, `ret ()` pops
  to `wcR`, `wcR` is at the store and takes none); `prR_not_pass`: no `PrR`
  pair is past the store point.
- `PassZ passT Z`: `Z` pairs `passT` with `fs = [] ∧ (unpark ∨ ret ())`.
- `passH_of_pend`: `PassH D passT` from `Pend Z` and `PassZ` (store phase by
  `X64HelloW1Store.frameRun_storeT_eq`, print phase by `prR_run`).

**Why restricted**: `D.Wi` is closed only up to
`Pend`, so it admits pairs whose frames are junk (a `ret ()` on a frame
returning into the store tail); at those `passT s ↔ WPass s1` fails. The
phases pin the frames: the examples at the end show both phase premises at
the pairs the run visits (the spawned child, `print`'s return).

x86-64 twin of `Spike/Lib/HelloPassH.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, nothing differs beyond the module names: the argument is on the source side.
Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only
live constants): `passH_DR`.
-/
import Spike.Lib.X64HelloWorkerRR
import Spike.Lib.X64HelloW1Store
import Spike.Lib.Frames1

namespace Spike.Lib.X64HelloPassH

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WorkerSrc Spike.Lib.Inv2Core
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (envP wcP wcR workerRestH workerCallH)
open Spike.Lib.X64HelloW1 (WSideH PrintPh StorePh PAnchor uFrame PassH)
open Spike.Lib.X64HelloW1Store (StoreT)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64.Flow.Worker (NNH)
open Spike.Lib.X64WakeW1 (EnvCJ mainTidW)

/-! ## The pairs reachable from the print phase -/

/-- **The frame pairs reachable from the print phase** on the slice of label
`l`, `n` bytes, `m` words, at `c`'s word `cw`: `PrintPh`'s two cases on
pairs, and `print`'s return point `wcR` on no frame. -/
def PrR (l : WeakMem.AllocLabel) (n m : Nat) (cw : TermRun.Word) (q : Ctl × List TermRun.Frame) : Prop :=
  ∃ w0 w1 w2 w4 : TermRun.Word, w4.val = mainTidW ∧
    w0.val = .loc ⟨l, 0⟩ 0 ∧ w1.val = .num m ∧ m ≠ 0 ∧ w2.val = .num n ∧
    ((q.2 = [] ∧ LocalRunS helloSrc q.1 (wcP w0 w1 w2 cw w4)) ∨
      (q.2 = [uFrame w0 w1 w2 cw w4] ∧ ∃ a, LocalRunS helloSrc q.1 a ∧ PAnchor w0 w2 l n m a) ∨
      (q.2 = [] ∧ q.1 = wcR w0 w1 w2 cw w4))

variable {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word}

/-- **The print phase is in `PrR`.** -/
theorem prR_of {s1 : TermRun.TTh} (h : PrintPh l n m cw s1) : PrR l n m cw (Ctl.of s1, s1.stack) := by
  obtain ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, ⟨hst, hr⟩ | ⟨hst, a, hr, ha⟩⟩ := h
  · exact ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inl ⟨hst, hr⟩⟩
  · exact ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inr (.inl ⟨hst, a, hr, ha⟩)⟩

/-- **`PrR` is closed under a frame step** (`c` an untagged locative). -/
theorem prR_step {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0) {q q' : Ctl × List TermRun.Frame}
    (h : PrR l n m cw q) (hs : FrameStep helloSrc q q') : PrR l n m cw q' := by
  obtain ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, ⟨hst, hr⟩ | ⟨hst, a, hr, ha⟩ | ⟨hst, hc⟩⟩ := h
  · cases hs with
    | loc hl =>
      refine ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inl ⟨hst, ?_⟩⟩
      rcases X64HelloW1.localRunS_after hr hl with he | hr'
      · exact (X64HelloW1.call_noStep (c := (wcP w0 w1 w2 cw w4)) rfl (by simp only at he; exact he ▸ hl)).elim
      · exact hr'
    | call hc hd ha =>
      rcases X64HelloW1.localRunS_cases hr with he | ⟨c₁, hl⟩
      · subst he
        simp only [wcP, workerCallH, Expr.let_.injEq, Op.call.injEq] at hc
        obtain ⟨rfl, ⟨rfl, rfl, rfl, -⟩, rfl⟩ := hc
        rw [X64HelloPrintSrcPub.printPD_find, Option.some.injEq] at hd
        subst hd
        have hsl : TermRun.evalAt (envP w0 w1 w2 cw w4) (.var "sl") =
            some (X64HelloRodataSrc.sliceTyP, [w0, w1, w2]) := rfl
        simp only [wcP] at ha
        rw [hsl, Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        obtain ⟨a, hr', ha'⟩ := X64HelloW1.entry_anchor h0 h1 hm h2
        simp only at hst
        subst hst
        exact ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inr (.inl ⟨rfl, a, hr', ha'⟩)⟩
      · exact (LocalStepS.not_call hl hc).elim
    | ret => simp at hst
  · cases hs with
    | loc hl =>
      refine ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inr (.inl ⟨hst, a, ?_, ha⟩)⟩
      rcases X64HelloW1.localRunS_after hr hl with he | hr'
      · exact (ha.2 _ (by simp only at he; exact he ▸ hl)).elim
      · exact hr'
    | call hc =>
      rcases X64HelloW1.localRunS_cases hr with he | ⟨c₁, hl⟩
      · subst he
        rcases ha.1 with ⟨k, -, rfl⟩ | ⟨k, mw, b, -, rfl⟩ | ⟨ht, -⟩
        · simp [X64HelloPrintSrcPub.ldCP] at hc
        · simp [X64HelloPrintSrcPub.emitCP, PrintSrc.printEmit] at hc
        · rw [ht] at hc; cases hc
      · exact (LocalStepS.not_call hl hc).elim
    | ret hc _ hev =>
      rcases X64HelloW1.localRunS_cases hr with he | ⟨c₁, hl⟩
      · subst he
        simp only [List.cons.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        rcases ha.1 with ⟨k, -, rfl⟩ | ⟨k, mw, b, -, rfl⟩ | ⟨ht, -⟩
        · simp [X64HelloPrintSrcPub.ldCP] at hc
        · simp [X64HelloPrintSrcPub.emitCP, PrintSrc.printEmit] at hc
        · rw [ht] at hc
          cases hc
          simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at hev
          obtain ⟨-, rfl⟩ := hev
          exact ⟨w0, w1, w2, w4, hj, h0, h1, hm, h2, .inr (.inr ⟨rfl, rfl⟩)⟩
      · exact (X64HelloW1.localStepS_not_ret hl _ hc).elim
  · have hE : EnvCJ cw (wcR w0 w1 w2 cw w4).env :=
      (X64HelloW1.storePh_pop (w0 := w0) (w1 := w1) (w2 := w2) hj ({ term := .ret .unit, env := [] } : TermRun.TTh)).2.2
    have hT : StoreT (wcR w0 w1 w2 cw w4).term := .inl rfl
    cases hs with
    | loc hl =>
      simp only at hc
      subst hc
      exact (X64HelloW1Store.localStep_storeT_false hl.toLocalStep hT hE hcw).elim
    | call hc' =>
      simp only at hc
      subst hc
      rcases X64HelloW1Store.storeT_let hT hc' with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | ret => simp at hst

/-- **`PrR` is closed under a frame run.** -/
theorem prR_run {cS : WeakMem.Address} (hcw : cw.val = .loc cS 0) :
    ∀ {q q' : Ctl × List TermRun.Frame}, FrameRun helloSrc q q' → PrR l n m cw q → PrR l n m cw q' := by
  intro q q' hr
  induction hr with
  | refl => exact id
  | step hs _ ih => exact fun h => ih (prR_step hcw h hs)

/-- **No `PrR` pair is past the store point.** -/
theorem prR_not_pass {q : Ctl × List TermRun.Frame} (h : PrR l n m cw q) :
    ¬ (q.2 = [] ∧ (q.1.term = wkUnpark ∨ q.1.term = .ret .unit)) := by
  rintro ⟨hfs, ht⟩
  obtain ⟨w0, w1, w2, w4, -, -, -, -, -, ⟨-, hr⟩ | ⟨hst, -⟩ | ⟨-, hc⟩⟩ := h
  · rcases X64HelloW1.localRunS_cases hr with he | ⟨c₁, hs⟩
    · rw [he] at ht
      rcases ht with ht | ht <;> simp [wcP, workerCallH, wkUnpark] at ht
    · rcases ht with ht | ht
      · exact X64HelloW1.wkUnpark_noStep hs ht
      · exact X64HelloW1.localStepS_not_ret hs .unit ht
  · rw [hfs] at hst; cases hst
  · rw [hc] at ht
    rcases ht with ht | ht <;> simp [wcR, workerRestH, wkUnpark] at ht

/-! ## The store point from `Pend Z` -/

/-- **The segment's control fact pairs the store points**: at every `Z` pair
the target store point `passT` is the source one on the pair's frames. -/
def PassZ (passT : isa.State → Prop) (Z : FragS isa) : Prop :=
  ∀ s c fs, Z s c fs → (passT s ↔ fs = [] ∧ (c.term = wkUnpark ∨ c.term = .ret .unit))

/-- **`PassH` from `Pend Z`**: a worker side whose invariant lies in
`Pend helloSrc (Z w)`, with `Z w` pairing the store points and `c`'s word an
untagged locative, has the phase-restricted store point. In the store phase
the pending frame run is empty (`frameRun_storeT_eq`); in the print phase
every pair it reaches is in `PrR`, before the store point (as `s1`,
`printPh_not_pass`). -/
theorem passH_of_pend {ι : Type} {D : WSideH ι} {passT : isa.State → Prop} {Z : ι → FragS isa}
    (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0)
    (hpend : ∀ w s c fs, D.Wi w s c fs → Pend helloSrc (Z w) s c fs) (hZ : ∀ w, PassZ passT (Z w)) :
    PassH D passT := by
  intro w s s1 hwi hph
  obtain ⟨cS, hcS⟩ := hcw w
  obtain ⟨c', fs', hr, hz⟩ := hpend w s _ _ hwi
  rw [hZ w s c' fs' hz]
  rcases hph with hP | hS
  · have hR := prR_run hcS hr (prR_of hP)
    exact ⟨fun h => (prR_not_pass hR h).elim, fun h => (X64HelloW1.printPh_not_pass hP h).elim⟩
  · obtain ⟨hst, ht, hE⟩ := hS
    rw [hst] at hr
    have he := X64HelloW1Store.frameRun_storeT_eq hr ht hE hcS
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun ⟨_, h⟩ => ⟨hst, h⟩, fun ⟨_, h⟩ => ⟨rfl, h⟩⟩

section DR

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isa)
  (P Z X : ι → FragS isa) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
    (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)

end DR

/-! ## Non-vacuity: the phase premises at the pairs the run visits -/

/-- The spawned child (`X64HelloSpawnR.spawn_RH`'s `hpass`) is in the print
phase, at hello's slice (13 bytes, 2 words). -/
example (l : WeakMem.AllocLabel) (cw : TermRun.Word) :
    PrintPh l 13 2 cw
      { term := .tail "worker" [] (.var "a") [],
        env := [("a", X64HelloSplit.workerTyH, [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.num 2),
          TermRun.cst (.num 13), cw, TermRun.cst mainTidW])] } :=
  X64HelloW1.printPh_spawn rfl rfl rfl (by decide) rfl rfl rfl rfl

/-- `print`'s return (`X64HelloW1.post_retP`) lands in the store phase. -/
example (cw w0 w1 w2 : TermRun.Word) (th : TermRun.TTh) :
    StorePh cw (SrcCalls.popTh th (uFrame w0 w1 w2 cw (TermRun.cst mainTidW)) [] []) :=
  X64HelloW1.storePh_pop rfl th

/-- At an invariant pair in the print phase, `PassH` puts the target before
its store point. -/
example {ι : Type} {D : WSideH ι} {passT : isa.State → Prop} (hp : PassH D passT) (w : ι)
    (s : isa.State) (s1 : TermRun.TTh) (hwi : D.Wi w s (Ctl.of s1) s1.stack)
    (hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1) : ¬ passT s :=
  fun h => X64HelloW1.printPh_not_pass hP ((hp w s s1 hwi (.inl hP)).mp h)

/-- info: 'Spike.Lib.X64HelloPassH.passH_of_pend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms passH_of_pend

end Spike.Lib.X64HelloPassH

/-- info: 'Spike.Lib.X64HelloPassH.prR_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPassH.prR_of

/-- info: 'Spike.Lib.X64HelloPassH.prR_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPassH.prR_step

/-- info: 'Spike.Lib.X64HelloPassH.prR_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPassH.prR_run

/-- info: 'Spike.Lib.X64HelloPassH.prR_not_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPassH.prR_not_pass
