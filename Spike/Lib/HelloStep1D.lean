/-
**hello.w on AArch64: a step of the worker in the print phase keeps `Post`**
(C4; `HelloStep1.PrintStep1`, the twin of
`WakeW1.post_step1_of` in the print phase): the dispatch over
`WakeW1.step1_cases` and the worker's frame-aware rows (`D.closed`, an
`HelloSegThrS.OutTS` row).

The rows' source runs start at the worker's print-phase control. A frame
run from it stays in the print phase, at a print-phase term
(`HelloStep1P.pTermH_frameRun`), or reaches the store (`wkStore`) through
`print`'s return (`storeT_frameRun`, `phase_end`). Print-phase terms bind
no acquire load, store, exchange, allocation, publication or `unpark`
(`okE_pTermT`), so those rows are not at the run's end except the store row
at `wkStore` (`HelloStep1St.post_storeH`). The other rows are
`HelloStep1P`'s and `HelloStep1Rt`'s; the system-call rows are not off a
system call; a `clone` is no row's (`noClone`); there is no transfer site
(`WCompatH.noSite`).

- `okOp`, `okE`, `okE_pTermT`: the operations print-phase terms bind.
- `storeT_frameRun`, `phase_end`, `excl`: where a frame run from the print
  phase ends, and the rows excluded there.
- `outL_noClone`, `noClone`: no row of the worker is at a `clone`.
- `post_outLH`: an `OutL` row after a frame run keeps `Post`.
- `SysStepP` (steps 4–5): the print phase's kernel
  system-call steps (`print`'s `write`, the abort path), with the machine step.
- `PrintWr0`, `printWr0_of`: no byte of a worker `write` out off a system
  call (at `HelloKRE.KRHE`).
- `printStep1_of`: `PrintStep1` from `SysStepP`, `PrintWr0` and
  `HelloStep1P.PromStepP`, with `hms` (`rfl` at
  `HelloAssemblyI.DH`), `hown` (`rfl` at `helloQ`) and `hml`
  (`HelloLive.mainLiveH`).
-/
import Spike.Lib.HelloStep1St

namespace Spike.Lib.HelloStep1D

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh StorePh WCompatH)
open Spike.Lib.HelloW1Store (NoWrite relW)
open Spike.Lib.HelloAssembly (HelloCompat)
open Spike.Lib.HelloStep1 (PrintStep1)
open Spike.Lib.HelloStep1P (atQ phase_frameRun pTermH_frameRun storePh_noFrame printPh_frameStep post_silentH
  post_choiceH post_fncH post_rtLoadH PromStepP)
open Spike.Lib.HelloStep1Rt (post_rtStoreH post_rtRmwH)
open Spike.Lib.HelloStep1St (post_storeH)
open Spike.Lib.WakeOwn (wakeOwn)

/-! ## The operations of the print phase's terms -/

/-- **An operation a print-phase term may bind**: none of an acquire load,
a store, an exchange, an allocation, a publication or an `unpark`. -/
def okOp : Op → Bool
  | .load true _ => false
  | .store _ _ _ _ => false
  | .xchg _ _ => false
  | .xchgAt _ _ _ => false
  | .newBuf _ _ => false
  | .new _ _ => false
  | .publish _ => false
  | .intoRgn _ _ => false
  | .ext .unpark _ => false
  | _ => true

/-- `okOp` at a `let`, every other term. -/
def okE : Expr → Bool
  | .let_ _ op _ => okOp op
  | _ => true

/-- **Print-phase terms bind only `okOp` operations.** -/
theorem okE_pTermT {e : Expr} (h : HelloW1.PTermT e) : okE e = true := by
  have h1 : HelloW1.preTermsH.all okE = true := by decide
  have h2 : (PrintSvc.printTerms PrintSrc.printBody).all okE = true := by decide
  have h3 : (PrintSvc.printTerms HelloPrintSrcPub.printLBodyP).all okE = true := by decide
  rcases h with h | h | h
  · exact List.all_eq_true.mp h1 e h
  · exact List.all_eq_true.mp h2 e h
  · exact List.all_eq_true.mp h3 e h

/-! ## Where a frame run from the print phase ends -/

section Phase

variable {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {cS : WeakMem.Address}

/-- **A frame run from the print phase reaches the store phase at the
store**: entering it is `print`'s return, at `wkStore`; in it there is no
frame step. -/
theorem storeT_frameRun (hcw : cw.val = .loc cS 0) {q q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc q q') :
    ∀ {s1 : TermRun.TTh}, Ctl.of s1 = q.1 → s1.stack = q.2 →
      (PrintPh l n m cw s1 ∨ (StorePh cw s1 ∧ s1.term = wkStore)) →
      StorePh cw (atQ s1 q') → q'.1.term = wkStore := by
  induction hr with
  | refl q =>
    intro s1 hc hst hph hS'
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    rcases hph with hP | ⟨-, ht⟩
    · exact absurd hP (HelloW1.storePh_not_printPh hS' hcw)
    · exact ht
  | @step q q₁ q' hs _ ih =>
    intro s1 hc hst hph hS'
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    have hP : PrintPh l n m cw s1 := by
      rcases hph with hP | ⟨hS, -⟩
      · exact hP
      · exact (storePh_noFrame hS hcw hs).elim
    have hh : q₁.1.hold = none := hs.hold_none
    have hc₁ : Ctl.of (atQ s1 q₁) = q₁.1 := by
      obtain ⟨⟨t, e, o⟩, f⟩ := q₁
      simp only at hh
      subst hh
      rfl
    rcases printPh_frameStep hP hs with hP₁ | ⟨hS₁, ht₁⟩
    · exact ih (s1 := atQ s1 q₁) hc₁ rfl (.inl hP₁) hS'
    · exact ih (s1 := atQ s1 q₁) hc₁ rfl (.inr ⟨hS₁, ht₁⟩) hS'

/-- **Where a frame run from the print phase ends**: in the print phase at
a print-phase term, or in the store phase at the store. -/
theorem phase_end (hcw : cw.val = .loc cS 0) {s1 : TermRun.TTh} (hP : PrintPh l n m cw s1)
    (hT : HelloW1.PTermH s1) {q' : Ctl × List TermRun.Frame} (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') :
    (PrintPh l n m cw (atQ s1 q') ∧ HelloW1.PTermH (atQ s1 q')) ∨
      (StorePh cw (atQ s1 q') ∧ q'.1.term = wkStore) := by
  obtain ⟨hph, -, -⟩ := phase_frameRun hcw hr rfl rfl (.inl hP)
  rcases hph with hP' | hS'
  · exact .inl ⟨hP', pTermH_frameRun hcw hr rfl rfl (.inl ⟨hP, hT⟩) hP'⟩
  · exact .inr ⟨hS', storeT_frameRun hcw hr rfl rfl (.inl hP) hS'⟩

/-- **The rows excluded where a frame run from the print phase ends**: a
`let` of an operation print-phase terms do not bind, other than a store. -/
theorem excl {s1 : TermRun.TTh} {c₁ : Ctl} {fs₁ : List TermRun.Frame}
    (hE : (PrintPh l n m cw (atQ s1 (c₁, fs₁)) ∧ HelloW1.PTermH (atQ s1 (c₁, fs₁))) ∨
      (StorePh cw (atQ s1 (c₁, fs₁)) ∧ c₁.term = wkStore))
    {x : String} {op : Op} {e : Expr} (ht : c₁.term = .let_ x op e) (hop : okOp op = false)
    (hns : ∀ a b o, op ≠ .store true a b o) : False := by
  rcases hE with ⟨-, hT⟩ | ⟨-, hw⟩
  · have h1 : okE c₁.term = true := okE_pTermT hT
    rw [ht] at h1
    simp [okE, hop] at h1
  · rw [hw] at ht
    simp only [wkStore, Expr.let_.injEq] at ht
    exact hns _ _ _ ht.2.1.symm

end Phase

/-! ## No `clone` -/

/-- **No `OutL` row is at a `clone`** (under the machine's kernel model),
at a state whose instruction faults: `Out.sys`'s `SysOk` excludes it, the
`emit` row is a `write`, every other row runs an instruction. -/
theorem outL_noClone {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {X : Frag isaLSE2} {t1 : Thread isaLSE2} {c : Ctl} (hK : ms.K = some abi) (hl : OutL p lbl ms X t1.st c)
    (hsx : ∀ tr, isaLSE2.exec t1.st = some tr → ∃ m, tr = .fault m) {st tl : Nat}
    (hd : callOf abi t1 = some (.clone st tl)) : False := by
  cases hl with
  | out r =>
    cases r with
    | sys K call hK' ha hd' hok hX =>
      rw [hK] at hK'; cases hK'
      exact hok.2.1 st tl (Option.some.inj (hd'.symm.trans hd))
    | emit K buf n Pw Qw hK' ha hd' =>
      rw [hK] at hK'; cases hK'
      cases hd'.symm.trans hd
    | choice P tree he hsil hX =>
      obtain ⟨m, rfl⟩ := hsx _ he
      cases hsil
    | _ =>
      obtain ⟨m, hm⟩ := hsx _ ‹isaLSE2.exec t1.st = some _›
      cases hm
  | ldSt _ _ _ _ _ _ _ _ _ he =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {AbW : isaLSE2.State → Prop} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : NoWrite D} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **No row of the worker is at a `clone`.** -/
theorem noClone (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w [])
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hat : abi.atSys t1.st = true) {st tl : Nat}
    (hd : callOf abi t1 = some (.clone st tl)) : False := by
  have hsx : ∀ tr, isaLSE2.exec t1.st = some tr → ∃ m, tr = .fault m := fun tr he =>
    hC.1.sysExec w _ _ _ _ h.pt1.1 hat he
  have hK : ∀ fs, (D.ms w fs).K = some abi := fun fs => by rw [hms w fs]; exact hC.2.1.K w
  cases D.closed w _ _ _ h.pt1.1 with
  | pre c₁ fs₁ _ hl => exact outL_noClone (hK fs₁) hl hsx hd
  | frame s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | fnc k s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | top c₁ _ hT =>
    cases hT with
    | outL hl => exact outL_noClone (hK []) hl hsx hd
    | unpk _ _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm
    | texit K a hK' ha hd' ht =>
      rw [hK []] at hK'; cases hK'
      cases hd'.symm.trans hd
    | fnc _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm

/-! ## The `OutL` rows -/

section Rows

variable (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hms : ∀ w fs, D.ms w fs = D.ms w []) (hwf : Λ.WF)
  (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hown : Q.own = wakeOwn) (hex : SrcSem.mainExit s = [])
  (hwr : t.2.wr 1 = 0)
  (hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1) (hns : abi.atSys t1.st = false)
  {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
  (hso : stepOne Arch.armv8 t1 1 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 o.thread o.mem)
include hC hms hwf h hown hex hwr hP hns hso ho hco

/-- **An `OutL` row after a frame run from the print phase keeps `Post`**:
by the row (`post_silentH`, `post_choiceH`, `post_fncH`, `post_rtLoadH`,
`post_rtStoreH`, `post_rtRmwH`, the store at `wkStore` by `post_storeH`);
the rows of other operations are not where the run ends (`excl`), the
system-call rows are not off a system call. -/
theorem post_outLH {c₁ : Ctl} {fs₁ : List TermRun.Frame} (hr₁ : FrameRun helloSrc (Ctl.of s1, s1.stack) (c₁, fs₁))
    (hE : (PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) (atQ s1 (c₁, fs₁)) ∧ HelloW1.PTermH (atQ s1 (c₁, fs₁))) ∨
      (StorePh (D.cw w) (atQ s1 (c₁, fs₁)) ∧ c₁.term = wkStore))
    (hl : OutL helloSrc (D.lbl w) (D.ms w fs₁) (fun s c => D.Wi w s c fs₁) t1.st c₁) :
    ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 1 o.thread o.mem, t.2) s' := by
  have hK : (D.ms w fs₁).K = some abi := by rw [hms w fs₁]; exact hC.2.1.K w
  have hno : ∀ {x : String} {op : Op} {e : Expr}, c₁.term = .let_ x op e → okOp op = false →
      (∀ a b o, op ≠ .store true a b o) → False := fun ht hop hst => excl hE ht hop hst
  cases hl with
  | out r =>
    cases r with
    | silent s' c' he hr hX =>
      exact post_silentH hC h hown hex hwr hso ho hco he (hr₁.trans (FrameRun.ofLocal hr fs₁)) hX
    | choice P tree he hsil hX =>
      exact post_choiceH hC h hown hex hwr hso ho hco he hsil fun s' hp =>
        let ⟨c', hr, hx⟩ := hX s' hp
        ⟨(c', fs₁), hr₁.trans (FrameRun.ofLocal hr fs₁), hx⟩
    | load kl A g x a e ty w' he ht =>
      exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
    | store kr A V s' x a b e ty tb wa wb he ht hea hva heb hvb hX =>
      rcases hE with ⟨-, hT⟩ | ⟨hS, hw⟩
      · have h1 : okE c₁.term = true := okE_pTermT hT
        rw [ht] at h1
        simp [okE, okOp] at h1
      · obtain rfl : fs₁ = [] := hS.1
        exact post_storeH hC hwf h hown hex hwr hP hso ho hco hr₁ hS hw he ht hea hva heb hvb hX
    | rtStore kr L V s' c' he hrt hmp hG hr hX =>
      exact post_rtStoreH hC hms hwf h hown hex hwr hso ho hco he hmp hG hr₁ hr hX
    | rtLoad kl L g c' he hrt hmp hr hX => exact post_rtLoadH hC hms h hown hex hwr hso ho hco he hr₁ hr hX
    | rtRmw k L op g c' he hrt hmp hr hX =>
      exact post_rtRmwH hC hms hwf h hown hex hwr hso ho hco he hmp hr₁ hr hX
    | sys K call hK' ha =>
      rw [hK] at hK'; cases hK'; rw [hns] at ha; cases ha
    | holdLoad kl A g x sa u v e he hxs =>
      obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs
      · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
      · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
    | xchgStore kr A V s' x sa u v e tv wv wold he hxs =>
      obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs
      · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
      · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
    | ctrRmw k op g x τ e n he hrt hm hs =>
      rcases hs with ⟨a, -, -, ht, -⟩ | ⟨-, a, -, ⟨_, ht⟩, -⟩
      · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
      · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
    | alloc s' A x a τ e ta ws k wold old us he ht =>
      exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
    | newStore kr A V s' x a t e w' wold old _ he hm ht =>
      obtain ⟨_, ht⟩ := ht
      exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
    | emit K buf n Pw Qw hK' ha =>
      rw [hK] at hK'; cases hK'; rw [hns] at ha; cases ha
    | fence k s' c' he hr hX =>
      cases hr with
      | loc hr => exact post_fncH hC h hown hex hwr hso ho hco he (hr₁.trans (FrameRun.ofLocal hr fs₁)) hX
      | pub _ hps _ =>
        obtain ⟨-, -, x', a, e, ta, ta', ws, hpt, -⟩ := hps
        rcases hpt with ⟨ht, -⟩ | ⟨r, ht, -⟩
        · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
        · exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim
  | ldSt kl A g x a e ty w' V he ht =>
    exact (hno ht rfl fun _ _ _ h' => Op.noConfusion h').elim

end Rows

/-! ## The obligation -/

/-- (steps 4–5) **The print phase's kernel system-call
steps**: `print`'s `write` to fd 1 and the abort path's (`WCompatH.sysOkH`). The
machine step itself is kept as a premise, for the kernel-state lemmas (`krh_write`). -/
def SysStepP (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t' (p : Pick), PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc →
    HelloStep1.PrivAt Λ t →
    PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 → ¬ Q.atTexit t s → SrcSem.mainExit s = [] →
    (machine (kernel 2)).Step μ 1 t es t' → sysStep abi Arch.armv8 1 t p = some (es, t') →
    CertAfter abi Arch.armv8 μ 1 t' →
    ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **`Post` from its parts** (`HelloW1.post_partsH`, reversed; at `PT1hE`'s
`PT1h`, `HelloEmitPh.PartsH.postE`). -/
theorem PartsH.post (hpt1 : Q.PT1 = HelloEmitPh.PT1hE D) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    Q.Post Λ t s := by
  refine ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, h.th, h.ths, h.core, ?_, ?_, oc, h.prot⟩, h.kr⟩
  · simp only [WakeRel.PTw, ite_true]
    exact ⟨h.preC, h.pt0⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hpt1]
    exact .inl h.pt1

/-- **No byte of a worker `write` out off a system call** (the print
phase's instruction rows' premise of `WCompatH.kr`, design (i′)). -/
def PrintWr0 (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc, PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → abi.atSys t1.st = false →
    t.2.wr 1 = 0

/-- **`PrintWr0` at `KRHE`**: mid-`write` the worker is at a system call
(`HelloKRE.wr1_zero`). -/
theorem printWr0_of {r0 r1 : Q.ι → Range} (hKR : Q.KR = HelloKRE.KRHE D r0 r1) : PrintWr0 Q D Λ := by
  intro w t s t0 t1 s0 s1 ts tp sp oc h hns
  have hk := h.kr
  rw [hKR] at hk
  exact HelloKRE.wr1_zero hk.2 (by rw [h.th]; rfl) (.inl hns)

/-- **`PrintStep1`**: a step of the worker in the print phase, off its
unpark and exit rows, keeps `Post`: an instruction by the worker's row
(`post_outLH` after the row's frame run; `post_silentH`, `post_fncH` for
`OutTS.frame`, `OutTS.fnc`), a promise by `PromStepP`, a kernel system call
by `SysStepP`; no `clone` (`noClone`), no transfer site. Off a system
call no byte of a worker `write` is out (`PrintWr0`). -/
theorem printStep1_of (hC : HelloCompat Q D M μ Λ arch AbW hcw hem) (hwf : Λ.WF)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : Q.own = wakeOwn)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = [])
    (hsy : SysStepP Q D μ Λ arch) (hpr : PromStepP Q D μ Λ arch) (hW0 : PrintWr0 Q D Λ) :
    PrintStep1 Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' h hpk hP _ hnt hs
  have hex : SrcSem.mainExit s = [] := hml t s (PartsH.post hC.1.pt1 h) hs.runs.2.1
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  have hT : HelloW1.PTermH s1 := by
    rcases h.pt1.2.2.1 with ⟨-, -, hT, -⟩ | hS
    · exact hT
    · exact (HelloW1.storePh_not_printPh hS (hC.1.cwv w) hP).elim
  rcases WakeW1.step1_cases ht1 hs with ⟨rfl, hns, outs, o, hso, ho, rfl, hco⟩ | ⟨rfl, m, hwt, rfl, hc⟩ |
    ⟨p, hsy', hca⟩ | ⟨rfl, j, r, hsp⟩ | ⟨rfl, k, hsite, -⟩
  · -- an instruction, by the worker's row
    have hwr := hW0 w t s t0 t1 s0 s1 ts tp sp oc h hns
    cases D.closed w _ _ _ h.pt1.1 with
    | pre c₁ fs₁ hr₁ hl =>
      exact post_outLH hC hms hwf h hown hex hwr hP hns hso ho hco hr₁ (phase_end (hC.1.cwv w) hP hT hr₁) hl
    | frame s' c' fs' he hr hx => exact post_silentH hC h hown hex hwr hso ho hco he hr hx
    | fnc k s' c' fs' he hr hx => exact post_fncH hC h hown hex hwr hso ho hco he hr hx
    | top c₁ hr₁ hT' =>
      have hE := phase_end (hC.1.cwv w) hP hT hr₁
      cases hT' with
      | outL hl => exact post_outLH hC hms hwf h hown hex hwr hP hns hso ho hco hr₁ hE hl
      | unpk k' A B op g x' a e ty jw he hrt hmp hop ht =>
        exact (excl hE ht rfl fun _ _ _ h' => Op.noConfusion h').elim
      | texit K a hK ha =>
        have hK0 : (D.ms w []).K = some abi := hC.2.1.K w
        rw [hK0] at hK; cases hK; rw [hns] at ha; cases ha
      | fnc k' s' c' he hr hX =>
        exact post_fncH hC h hown hex hwr hso ho hco he (hr₁.trans (FrameRun.ofLocal hr [])) hX
  · -- a certified promise
    exact hpr w t s t0 t1 s0 s1 ts tp sp oc m h hP hex hwt hc
  · -- a kernel system call
    exact hsy w t s t0 t1 s0 s1 ts tp sp oc es t' p h hpk hP hnt hex hs hsy' hca
  · -- no `clone`: no row is at one
    obtain ⟨hat, st, tl, hd⟩ := WakeW1.spawnStep_ready ht1 hsp
    exact (noClone hC hms h hat hd).elim
  · -- no range transfer: no site at the worker's states
    obtain ⟨a, ha, t1', ht1', hpc⟩ := hsite
    obtain rfl : t1' = t1 := Option.some.inj (ht1'.symm.trans ht1)
    have hn := siteAt_eq_none_iff.mp (hC.1.noSite w _ _ _ h.pt1.1)
    cases k with
    | take => exact absurd (ha.trans (congrArg some hpc.symm)) hn.1
    | release => exact absurd (ha.trans (congrArg some hpc.symm)) hn.2

/-- info: 'Spike.Lib.HelloStep1D.printStep1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printStep1_of

end Spike.Lib.HelloStep1D
