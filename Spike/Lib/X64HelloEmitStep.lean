/-
**hello.w on x86-64: a byte of `print`'s `write` keeps `Post`** (the twin
of `Spike/Lib/HelloEmitStep.lean`). The worker at its
`write(1, buf, n)` with `j` bytes out and the source worker at an emit-row
byte control (`ByteOutP` landing in `Pw (j + 1)`): a byte pick reads the
frozen buffer's byte `j` (`HelloFrz.readByte_frz`), the source runs one
byte of the published loop (`X64HelloEmitSrc.emit_byte_src`) emitting the same
byte, and both land at `X64HelloEmitPh.PartsE` with the link at `j + 1`
(`X64HelloKRE.EmitR`).

- `ByteFrz`: the instance's premise: the buffer's words
  in its label, their target words frozen.
- `byte_val`: the target's byte is the source's (`HelloFrz.readByte_frz` at
  the source's latest message, the worker's private keys clear of the
  buffer, `HelloWrite.hpriv_label`).
- `krhe_byte`: the kernel relation after the byte.
- `post_byte`: the step.

## Differences from the AArch64 version

- The target threads are over `X64.isa` and the kernel's architecture is `Arch.tso` (AArch64: `isaLSE2`,
  `Arch.armv8`); the runtime facts are `X64WakeA64`'s, and the source, worker side, phases, emit rows and kernel
  relation are the x86-64 twins (`X64HelloSrc`, `X64HelloW1`, `X64HelloEmitPh`, `X64HelloEmitSrc`,
  `X64HelloEmitPost`, `X64HelloKRE`, `X64HelloWriteK`). `HelloWrite`, `HelloFrz` and `Hello1Runs` are
  ISA-generic and shared. The statements and proofs are otherwise the AArch64 ones.
-/
import Spike.Lib.X64HelloEmitPost
import Spike.Lib.HelloWrite
import Spike.Lib.X64HelloEmitShapeF
import Spike.Lib.X64HelloStoreNB
import Spike.Lib.X64HelloStep1P
import Spike.Lib.X64HelloNoCert
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloEmitStep

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH PartsH PrintPh BufV PTermH WCompatH)
open Spike.Lib.X64HelloEmitPh (EmitPh PartsE PT1hE)
open Spike.Lib.X64HelloEmitShapeF (EmitShapeF)
open Spike.Lib.X64HelloStep1P (atQ phase_frameRun pTermH_frameRun frameRun_run_source_i)
open Spike.Lib.X64HelloEmitSrc (emitTh emitCfg emit_byte_src)
open Spike.Lib.X64HelloEmitPost (PartsC partsE_byte)
open Spike.Lib.X64HelloByteOutP (ByteOutP)
open Spike.Lib.X64HelloWriteK (KRH krh_set1_run krh_frame1)
open Spike.Lib.X64HelloKRE (KRHE EmitCl EmitR)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self getElem?_set!_ne)
open Scc.Sem.MemRel (SLatest)

/-! ## The instance's premise -/

/-- **The buffer's target words are frozen**: the layout
is well formed and, under the memory relation at the record's placement and
the buffer's label placed at `b0`, its `mB` words lie in the label with
their target words in `frz` (`HelloFrz.readByte_frz`'s premises but the
private keys; `X64HelloEmitFrzI.byteFrz_I` at the instance). -/
def ByteFrz (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) : Prop :=
  Λ.WF ∧ ∀ w b0 ts tm sm tp tq sp, MemRelP Λ (Q.SR w).lbl (Q.SR w).lsize ts tm sm tp tq sp →
    (Q.SR w).lbl (D.bufL w) = some b0 →
    D.mB w ≤ (Q.SR w).lsize (D.bufL w) ∧ ∀ i < D.mB w, (Q.P w).frz (wordLoc (b0 + 8 * i))

variable {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {AbW : isa.State → Prop}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)} {r0 r1 : Q.ι → Range}

/-! ## The byte -/

/-- **The target's byte is the source's**: the kernel's read at thread 1 of
byte `k` of the buffer (placed at `b0`) is lane `k % 8` of the value of the
word's latest source message `jm`; thread 1's promises and cover kept. -/
theorem byte_val (hfz : ByteFrz Q D Λ) (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) {Ent : Entry}
    (hpk : DmemPriv.PrivKeys abi Λ Ent t1.st) (hE : Ent.clear Λ = true)
    {b0 k jm v rd : Nat} {msg : WeakMem.Msg} {bt : Fin 256} {t1' : Thread isa}
    (hl : (Q.SR w).lbl (D.bufL w) = some b0) (hk8 : k / 8 < D.mB w)
    (hcell : SLatest s.mem ⟨D.bufL w, k / 8⟩ jm) (hm : s.mem[jm]? = some msg) (hv : msg.val = .num v)
    (hrb : readByte abi Arch.tso t1 t.1.mem (b0 + k) rd = some (bt, t1')) :
    bt.val = TermRun.laneN .w8 v (k % 8) ∧ t1'.prom = t1.prom ∧
      CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1) := by
  obtain ⟨hwf, hfz'⟩ := hfz
  obtain ⟨hmL, hfr⟩ := hfz' w b0 _ _ _ _ _ _ h.core.mem hl
  have hb8 : b0 % 8 = 0 := (h.core.mem.lbl_range _ b0 hl).1
  have ha : b0 + k - (b0 + k) % 8 = b0 + 8 * (k / 8) := by omega
  have hm8 : (b0 + k) % 8 = k % 8 := by omega
  have hwa : wordAddr (Q.SR w).lbl ⟨D.bufL w, k / 8⟩ = some (b0 + k - (b0 + k) % 8) := by
    rw [ha]; simp only [wordAddr, hl, Option.map_some]
  have hp := HelloWrite.hpriv_label hpk hwf hE h.core.mem hl (k := k) (by omega)
  have hf : (Q.P w).frz (wordLoc (b0 + k - (b0 + k) % 8)) := by rw [ha]; exact hfr _ hk8
  have := HelloFrz.readByte_frz h.core hwf hrb hp hf hwa hcell hm hv
  rwa [hm8] at this

/-! ## The kernel relation -/

/-- **The source worker after a byte is at its landing.** -/
theorem ctl_emitTh {s1 : TermRun.TTh} {pairs : List Nat} {l : WeakMem.AllocLabel} {k jm : Nat}
    {msg : WeakMem.Msg} {c2 : Ctl} (hh : c2.hold = none) : Ctl.of (emitTh s1 pairs l k jm msg c2) = c2 := by
  obtain ⟨_, _, _⟩ := c2
  simp only at hh
  subst hh
  rfl

/-- **`KRHE` after a byte** (from `KRH` before it): slot 1 running at `j + 1` (`krh_set1_run`), the
byte appended to the source trace (no `exit`, `krh_frame1`), the link at
`j + 1` mid-`write` (`EmitR`). -/
theorem krhe_byte (hk : KRH r0 r1 w t s) (ht1 : t.1.threads[1]? = some t1) (hs1 : s.ths[1]? = some s1)
    {t1' : Thread isa} {s1' : TermRun.TTh} {b : Nat} (hE : EmitR D w t1' s1' (t.2.wr 1 + 1)) :
    KRHE D r0 r1 w (t.1.withThread 1 t1' t.1.mem, t.2.set 1 (.run (t.2.wr 1 + 1))) (emitCfg s s1' b) := by
  have hs0 : (emitCfg s s1' b).ths[0]? = s.ths[0]? := getElem?_set!_ne _ (by decide : 1 ≠ 0) _
  have hx : ∀ c, Ev.exit c ∈ SrcSem.traceOf (emitCfg s s1' b) → Ev.exit c ∈ SrcSem.traceOf s := by
    intro c hc
    simpa [SrcSem.traceOf, emitCfg, List.filterMap_append, SrcSem.evOf] using hc
  have hf := krh_frame1 w t (t.1.withThread 1 t1' t.1.mem, t.2) s (emitCfg s s1' b) hk rfl hs0 hx
  have hwr : (t.2.set 1 (.run (t.2.wr 1 + 1))).wr 1 = t.2.wr 1 + 1 :=
    X64HelloKRE.wr_set_self _ _ (by rw [hk.1]; decide)
  have hg : (t.1.withThread 1 t1' t.1.mem).threads[1]? = some t1' := Live.Sem.withThread_get_self ht1
  have hs' : (emitCfg s s1' b).ths[1]? = some s1' := getElem?_set!_self hs1 s1'
  refine ⟨krh_set1_run _ hf _, fun _ => ⟨t1', s1', hg, hs', .inl (by rw [hwr]; exact hE)⟩, fun _ _ _ _ _ => ?_⟩
  show 0 < (t.2.set 1 (.run (t.2.wr 1 + 1))).wr 1
  rw [hwr]
  exact Nat.succ_pos _

/-! ## The source worker moved by a frame run -/

/-- **`Q` with no kernel relation**: the common parts at the source worker
moved by a frame run before the first byte, where `X64HelloKRE.Lk` need not
hold (the worker's invariant at the moved control is not known), and back
(`PartsE.ofQt`). -/
abbrev Qt (Q : WakeRel) : WakeRel := { Q with KR := fun _ _ _ => True }

/-- `WCompatH` at `Qt Q` (only `kr` reads the kernel relation). -/
theorem wcompatH_qt (hC : WCompatH Q D μ Λ arch AbW) : WCompatH (Qt Q) D μ Λ arch AbW :=
  { hC with kr := by intros; trivial }

/-- **The common parts at the source worker moved by a frame run** (to
`atQ s1 q'`, in the print phase at a print-phase term, with no source
promise), at `Qt Q`. -/
theorem _root_.Spike.Lib.X64HelloEmitPost.PartsC.atQt (hC : WCompatH Q D μ Λ arch AbW) (hown : X64HelloOwn1.Own1H Q D Λ)
    (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) {q' : Ctl × List TermRun.Frame}
    (hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) (atQ s1 q')) (hT : PTermH (atQ s1 q'))
    (hpr : s1.promises = []) :
    PartsC (Qt Q) D Λ w t { s with ths := s.ths.set! 1 (atQ s1 q') } t0 t1 s0 (atQ s1 q') ts tp sp oc := by
  have hnp1 : ¬ WPass s1 := X64HelloW1.printPh_not_pass h.ph
  have hnp1' : ¬ WPass (atQ s1 q') := X64HelloW1.printPh_not_pass hP
  obtain ⟨hT', hS, hl⟩ := (cProt_iff _ _ _).mp h.prot
  have hnpS : ¬ (Q.C w).passS s1 := fun hps => hnp1 ((X64HelloW1.PartsH.passS_iff (w := w) hC s1).mp hps)
  refine ⟨h.th, ?_, ?_, h.preC, h.pt0, ?_, trivial, h.σs, hP, h.bufV, hT, .inl hpr, h.plen, h.pprom,
    h.nodup⟩
  · show s.ths.set! 1 (atQ s1 q') = _
    rw [h.ths]; rfl
  · refine core1_same h.core (by simp) rfl rfl h.core.bnd1 h.core.cov1 h.core.scov1 ?_ ?_ ?_ h.core.noProm1
    · -- the worker's owned words do not depend on its source frames (`Own1H.const`)
      have h1 : ExtRows.OwnOk (Q.own w 1 t1.st s1.stack) t.1.mem t1.prom := by simpa using h.core.own1
      simp only [Nat.one_ne_zero, ite_false]
      rw [hown.const w t1.st s1.stack]; exact h1
    · intro L v v' h0 h1
      simp only [Nat.one_ne_zero, ite_false] at h1
      rw [hown.const w t1.st s1.stack] at h1
      exact h.core.own_disj L v v' h0 h1
    · intro L v h1
      simp only [Nat.one_ne_zero, ite_false] at h1
      rw [hown.const w t1.st s1.stack] at h1
      exact h.core.own_cov 1 L v (by decide) h1
  · have hmv : (Q.C w).mviewS (atQ s1 q') = (Q.C w).mviewS s1 := by
      rw [X64HelloEmitPost.mviewS_eq (w := w) hC, X64HelloEmitPost.mviewS_eq (w := w) hC]
    have hob : (Q.C w).obS (atQ s1 q') = (Q.C w).obS s1 := by
      rw [X64HelloEmitPost.obS_eq (w := w) hC, X64HelloEmitPost.obS_eq (w := w) hC]
    refine (cProt_iff _ _ _).mpr ⟨hT', ⟨hS.smsg, hS.some_msg, hS.prom_worker,
      fun _ => show (Q.C w).mviewS _ < _ ∧ (Q.C w).obS _ < _ by rw [hmv, hob]; exact hS.pre_lt hnpS,
      hS.prom_view⟩, ?_⟩
    rw [X64HelloW1.PartsH.passS_iff (w := w) hC (atQ s1 q'), hl, X64HelloW1.PartsH.passS_iff (w := w) hC s1]
    exact ⟨fun h' => absurd h' hnp1, fun h' => absurd h' hnp1'⟩

/-- **`PartsE` at `Qt Q` with `Q`'s kernel relation is `PartsE` at `Q`.** -/
theorem _root_.Spike.Lib.X64HelloEmitPh.PartsE.ofQt (h : PartsE (Qt Q) D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hkr : Q.KR w t s) :
    PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc :=
  ⟨h.th, h.ths, h.core, h.preC, h.pt0, h.pt1, h.prot, hkr⟩

/-- **No source promise with no target promise**: the source worker's
promise is `c`'s message after the spawn (`pprom`), paired by `oc` with the
worker's target message (`CProt`), which a mirrored promise makes a promise
of thread 1 (`Inv2Core`: `prom_corr`, `tp_prom`; thread 0's are its own,
`prom0`). -/
theorem _root_.Spike.Lib.X64HelloEmitPost.PartsC.promises_nil (hC : WCompatH Q D μ Λ arch AbW)
    (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (ht1 : t1.prom = []) : s1.promises = [] := by
  rcases hp : s1.promises with _ | ⟨k, rest⟩
  · rfl
  · exfalso
    have hk : k ∈ s1.promises := by rw [hp]; exact List.mem_cons_self ..
    obtain ⟨hS, m, hm, hcw⟩ := h.pprom k hk
    have hloc : m.loc = (Q.C w).cS := by
      have e := (hC.cwv w).symm.trans hcw
      simp only [WeakMem.Val.loc.injEq] at e
      exact e.1.symm
    obtain ⟨Tc, hoc⟩ := h.prot.smsg k m hm (by rw [← hC.S w]; exact hS) hloc
    obtain ⟨hT, -, hts, ⟨wm, hwm, -, htid, -⟩, -⟩ := h.prot.some_msg Tc k hoc
    have hsp : k ∈ sp := (h.core.sp_prom k).mpr (.inr hk)
    have htp : Tc ∈ tp := (h.core.mem.prom_corr k Tc hts (by omega)).mp hsp
    rcases h.core.tp_prom Tc htp with h0 | h1
    · obtain ⟨-, w', hw', htid0⟩ := h.core.prom0 Tc h0
      rw [hwm] at hw'
      cases hw'
      omega
    · rw [ht1] at h1
      cases h1

/-! ## The source frames and term at the landing -/

section FrS

open Spike.Lib.X64HelloEmitPh (EmitFrS PTermE)
open Spike.Lib.X64HelloSplit (workerCallH workerRestH)
open Spike.Lib.X64HelloW1 (StorePh preTermsH PTermT)
open Spike.Lib.X64HelloStep1P (FrameStep.inv printPh_frameStep pTermH_frameStep storePh_popW storePh_noFrame)

variable {l : WeakMem.AllocLabel} {n m : Nat} {cw : TermRun.Word} {cS : WeakMem.Address}

/-- **The prelude's terms are closed under a local step** (`pTermT_step`'s
first case). -/
theorem preTerms_step {c c' : Ctl} (h : LocalStepS helloSrc c c') (ht : c.term ∈ preTermsH) :
    c'.term ∈ preTermsH := by
  simp only [preTermsH, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht
  · obtain ⟨d, hf, e⟩ := Hello1Runs.localStepS_tail h ht
    rw [X64HelloSplit.worker_find] at hf
    cases hf
    rw [e]; simp [preTermsH, X64HelloSplit.workerD]
  · rw [Hello1Runs.localStepS_split h (by rw [ht]; rfl)]; simp [preTermsH]
  · rw [Hello1Runs.localStepS_split h ht]; simp [preTermsH]
  · rw [Hello1Runs.localStepS_unpack h ht]; simp [preTermsH]
  · exact (h.not_call (by rw [ht]; rfl)).elim

/-- **The prelude's terms are closed under a local run.** -/
theorem preTerms_run {c c' : Ctl} (h : LocalRunS helloSrc c c') (ht : c.term ∈ preTermsH) :
    c'.term ∈ preTermsH := by
  induction h with
  | refl => exact ht
  | step hs _ ih => exact ih (preTerms_step hs ht)

/-- **Inside `print`, a print-phase term is `print`'s or `printL`'s**: on a
non-empty stack the print phase runs locally to an anchor, and no prelude
term runs locally to one (`preTerms_run`). -/
theorem pTermE_of {s : TermRun.TTh} (hP : PrintPh l n m cw s) (hT : PTermH s) (hne : s.stack ≠ []) :
    PTermE s.term := by
  rcases hT with ht | ht | ht
  · exfalso
    obtain ⟨_, _, _, _, -, -, -, -, -, ⟨hst, -⟩ | ⟨-, a, hr, ha, hns⟩⟩ := hP
    · exact hne hst
    · have hp := preTerms_run hr ht
      rcases ha with ⟨k, -, rfl⟩ | ⟨k, mw, b, -, rfl⟩ | ⟨ha, -⟩
      · simp [preTermsH, X64HelloPrintSrcPub.ldCP, workerCallH, X64HelloSplit.workerBodyH] at hp
      · simp [preTermsH, X64HelloPrintSrcPub.emitCP, PrintSrc.printEmit, workerCallH, X64HelloSplit.workerBodyH] at hp
      · rw [ha] at hp
        simp [preTermsH, workerCallH, X64HelloSplit.workerBodyH] at hp
  · exact .inl ht
  · exact .inr ht

/-- **The frames of a frame run from a phase** (`EmitFrS`'s disjuncts): the
run ends on an empty stack, on its start's frames, or, from an empty stack,
on the frame of `print`'s call at the end of a local run to it (the only
call at a print-phase term; `print`'s return lands in the store phase,
which takes no frame step). -/
theorem emitFrS_run (hcw : cw.val = .loc cS 0) {q q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc q q') :
    ∀ {s1 : TermRun.TTh}, Ctl.of s1 = q.1 → s1.stack = q.2 →
      ((PrintPh l n m cw s1 ∧ PTermH s1) ∨ StorePh cw s1) →
      q'.2 = [] ∨ q'.2 = q.2 ∨ (q.2 = [] ∧ ∃ c', LocalRunS helloSrc q.1 c' ∧ c'.term = workerCallH ∧
        q'.2 = [⟨"u", workerRestH, c'.env, [], .unit⟩]) := by
  induction hr with
  | refl q => exact fun _ _ _ => .inr (.inl rfl)
  | @step q q₁ q' hs hr' ih =>
    intro s1 hc hst hph
    obtain ⟨c, fs⟩ := q
    simp only at hc hst
    subst hc hst
    obtain ⟨hP, hT⟩ : PrintPh l n m cw s1 ∧ PTermH s1 := by
      rcases hph with hP | hS
      · exact hP
      · exact (storePh_noFrame hS hcw hs).elim
    have hh : q₁.1.hold = none := hs.hold_none
    have hc₁ : Ctl.of (atQ s1 q₁) = q₁.1 := by
      obtain ⟨⟨t, e, o⟩, f⟩ := q₁
      simp only at hh
      subst hh
      rfl
    have hph₁ : (PrintPh l n m cw (atQ s1 q₁) ∧ PTermH (atQ s1 q₁)) ∨ StorePh cw (atQ s1 q₁) := by
      rcases printPh_frameStep hP hs with hP₁ | ⟨hS₁, -⟩
      · exact .inl ⟨hP₁, pTermH_frameStep hcw hP hT hs hP₁⟩
      · exact .inr hS₁
    have ih' := ih hc₁ rfl hph₁
    rcases (FrameStep.inv hs) with ⟨c', hl, rfl⟩ | ⟨x, f, iss, a, e, d, t, ws, hc, hd, -, rfl⟩ |
      ⟨a, fr, fs', t, ws, -, hfs, -, -, rfl⟩
    · rcases ih' with h' | h' | ⟨h0, c'', hr'', ht'', h'⟩
      · exact .inl h'
      · exact .inr (.inl h')
      · exact .inr (.inr ⟨h0, c'', .step hl hr'', ht'', h'⟩)
    · -- the only call at a print-phase term is `print`'s, on an empty stack
      have hT' : PTermT (.let_ x (.call f iss a []) e) := hc ▸ hT
      rcases hT' with h' | h' | h'
      · simp only [preTermsH, List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h' | h' | h' | h' | h'
        · cases h'
        · cases h'
        · cases h'
        · cases h'
        · unfold workerCallH at h'
          cases h'
          rw [X64HelloPrintSrcPub.printPD_find] at hd
          cases hd
          change s1.term = _ at hc
          have hst : s1.stack = [] := by
            obtain ⟨_, _, _, _, -, -, -, -, -, ⟨hst, -⟩ | ⟨-, a', hr, ha, hns⟩⟩ := hP
            · exact hst
            · exfalso
              rcases X64HelloW1.localRunS_cases hr with he | ⟨c₁, hl⟩
              · subst he
                rcases ha with ⟨k, -, hk⟩ | ⟨k, mw, b, -, hk⟩ | ⟨ha, -⟩
                · have e : s1.term = _ := congrArg Ctl.term hk
                  rw [hc] at e
                  simp [X64HelloPrintSrcPub.ldCP] at e
                · have e : s1.term = _ := congrArg Ctl.term hk
                  rw [hc] at e
                  simp [X64HelloPrintSrcPub.emitCP, PrintSrc.printEmit] at e
                · have e : s1.term = _ := ha
                  rw [hc] at e
                  cases e
              · exact hl.not_call hc
          rcases ih' with h' | h' | ⟨h0, -⟩
          · exact .inl h'
          · exact .inr (.inr ⟨hst, Ctl.of s1, .refl _, hc, by rw [h', hst]; rfl⟩)
          · exact absurd h0 (List.cons_ne_nil _ _)
      · simp [PrintSvc.printTerms, PrintSrc.printBody] at h'
      · simp [PrintSvc.printTerms, X64HelloPrintSrcPub.printLBodyP, X64HelloPrintSrcPub.printLoadP, PrintSrc.printAdv,
          PrintSrc.printLane, PrintSrc.printEmit, PrintSrc.printNext] at h'
    · -- `print`'s return lands in the store phase, which takes no frame step
      obtain ⟨w0, w1, w2, w4, hj, -, -, -, -, ⟨hst, -⟩ | ⟨hst, -⟩⟩ := hP
      · simp only at hfs; rw [hst] at hfs; cases hfs
      · simp only at hfs
        rw [hst] at hfs
        simp only [List.cons.injEq] at hfs
        obtain ⟨rfl, rfl⟩ := hfs
        rcases hph₁ with ⟨hP₁, -⟩ | hS₁
        · exact absurd hP₁ (X64HelloW1.storePh_not_printPh (storePh_popW hj s1 ws) hcw)
        · cases hr' with
          | refl => exact .inl rfl
          | step hs' _ => exact (storePh_noFrame hS₁ hcw (by rw [hc₁]; exact hs')).elim

end FrS

/-! ## The step -/

/-- **A byte of `print`'s `write` keeps `Post`**: at the common parts
with the worker at `write(1, buf, n)` in its invariant at some control, `j`
bytes out, a frame run of the source worker to `q'` (`EmitShapeF`'s with no
byte out, empty with bytes out), the emit row's clauses at `q'`'s frames,
and a byte control of byte `j` at `q'` landing in `Pw (j + 1)`
(`ByteOutP`): a byte pick emits `out bt`; the source runs the frame run
(`frameRun_run_source_i`; in the print phase, as `ByteOutP` starts no row in
the store phase, `X64HelloStoreNB.byteOutP_not_storePh`) and one byte of the
published loop emitting `bt` (`emit_byte_src`, the same byte by
`byte_val`), and both land at `PartsE` (`partsE_byte` at `Qt Q` after the
frame run, `PartsE.ofQt`) with the link at `j + 1` (`krhe_byte`). -/
theorem post_byte (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ) {Ent : Entry}
    (hpk : DmemPriv.DmemPriv abi Λ Ent t) (hE : Ent.clear Λ = true) (hown : X64HelloOwn1.Own1H Q D Λ)
    (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hex : SrcSem.mainExit s = []) (hW : ∃ c fs, D.Wi w t1.st c fs) (hat : abi.atSys t1.st = true)
    {buf n : Nat} (hd : decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n))
    {Pw : Nat → Ctl → Prop} {Qw : Ctl → Prop} {q' : Ctl × List TermRun.Frame}
    (hr : FrameRun helloSrc (Ctl.of s1, s1.stack) q') (hcl : EmitCl D w t1.st q'.2 buf n Pw Qw)
    (hF0 : X64HelloEmitPh.EmitFrS D w t1.st q'.2)
    (hbyte : ByteOutP helloSrc (D.lbl w) t1.st (buf + t.2.wr 1) q'.1 (Pw (t.2.wr 1 + 1)))
    {rd : Nat} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.tso 1 t (.byte rd) = some (es, t'))
    (hca : CertAfter abi Arch.tso μ 1 t') :
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  have hs1 : s.ths[1]? = some s1 := by rw [h.ths]; rfl
  have hk := h.kr
  rw [hKR] at hk
  -- no promise at the byte: the worker after it is certified at its `write`
  have hpr : s1.promises = [] := by
    obtain ⟨_, t1', -, hrb, -, rfl⟩ := HelloWrite.sysStep_write_byte ht1 hd hs
    obtain ⟨c, fs, hWi⟩ := hW
    have hc := hca t1' (by rw [X64WakeW1.withThread1 h.th]; rfl)
    have hst := readByte_st hrb
    have hp1 : t1'.prom = [] := X64HelloNoCert.prom_nil_of_certOkC_write (by rw [hst]; exact hC.noSite w _ c fs hWi)
      (by rw [hst]; exact hat) (by rw [hst]; exact hd) hc
    exact h.promises_nil hC (by rw [← Kernel.readByte_prom hrb]; exact hp1)
  -- the source worker moved by the frame run, in the print phase
  have hh : q'.1.hold = none := hr.hold_none rfl
  have hc : Ctl.of (atQ s1 q') = q'.1 := by
    obtain ⟨⟨_, _, _⟩, _⟩ := q'
    simp only at hh
    subst hh
    rfl
  have hbyte' : ByteOutP helloSrc (D.lbl w) t1.st (buf + t.2.wr 1) (Ctl.of (atQ s1 q')) (Pw (t.2.wr 1 + 1)) := by
    rw [hc]; exact hbyte
  obtain ⟨hph, -, -⟩ := phase_frameRun (hC.cwv w) hr rfl rfl (.inl h.ph)
  have hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) (atQ s1 q') :=
    hph.resolve_right fun hS => X64HelloStoreNB.byteOutP_not_storePh hS (hC.cwv w) hbyte'
  have hT := pTermH_frameRun (hC.cwv w) hr rfl rfl (.inl ⟨h.ph, h.term⟩) hP
  have hm := h.atQt hC hown hP hT hpr
  have hsm1 : ({ s with ths := s.ths.set! 1 (atQ s1 q') } : TermRun.Cfg).ths[1]? = some (atQ s1 q') :=
    getElem?_set!_self hs1 _
  have hsm0 : ({ s with ths := s.ths.set! 1 (atQ s1 q') } : TermRun.Cfg).ths[0]? = s.ths[0]? :=
    getElem?_set!_ne _ (by decide : 1 ≠ 0) _
  have hexm : SrcSem.mainExit { s with ths := s.ths.set! 1 (atQ s1 q') } = [] := by
    rw [WorkerSrcStep.mainExit_eq hsm0]; exact hex
  have hkm : KRH r0 r1 w t { s with ths := s.ths.set! 1 (atQ s1 q') } :=
    krh_frame1 w t t s _ hk.1 rfl hsm0 fun _ hx => hx
  -- the byte
  obtain ⟨b0, k, jm, v, c2, msg, hl, ha, hk8, hcell, hmm, hv, hΦ, hh2, hP', hT', hrun⟩ :=
    emit_byte_src (arch := arch) hsm1 hm.σs hpr hm.ph hm.bufV hbyte' hexm (X64HelloWriteK.krh_noexit hkm)
  rw [hlbl] at hl
  obtain ⟨bt, t1', hlt, hrb, he, rfl⟩ := HelloWrite.sysStep_write_byte ht1 hd hs
  rw [ha] at hrb
  have hTE : X64HelloEmitPh.PTermE c2.term := by
    obtain ⟨_, _, _, _, _, _, hpw', -, -, hrun', -⟩ := hbyte'
    obtain ⟨⟨_, _, hst', -⟩, -⟩ := X64HelloEmitSrc.byteOut_pin hP hpw' hrun'.toS
    exact pTermE_of hP' hT' (show (atQ s1 q').stack ≠ [] by rw [hst']; exact List.cons_ne_nil _ _)
  have hfz' : ByteFrz (Qt Q) D Λ := hfz
  obtain ⟨hbt, hp, hcov⟩ := byte_val hfz' hm (hpk 1 t1 ht1) hE hl hk8 hcell hmm hv hrb
  have hst : t1'.st = t1.st := readByte_st hrb
  have hb : t1'.Bnd t.1.mem.last := ExtThread.bnd_readByte abi h.core.bnd1 hrb
  have hER : EmitR D w t1' (emitTh (atQ s1 q') s.pairs (D.bufL w) k jm msg c2) (t.2.wr 1 + 1) :=
    ⟨buf, n, Pw, Qw, hst ▸ hat, hst ▸ hd, hst ▸ hcl, hlt, by rw [ctl_emitTh hh2]; exact hΦ⟩
  have hkr := krhe_byte (b := TermRun.laneN .w8 v (k % 8)) hkm ht1 hsm1 hER
  rw [← hKR] at hkr
  have hE' := (partsE_byte (wcompatH_qt hC) hm hW hat ⟨buf, n, hd⟩ hst hp hb hcov hk8 hcell hmm hP' hT' hpr
    hF0 hTE (k' := t.2.set 1 (.run (t.2.wr 1 + 1))) trivial).ofQt hkr
  refine ⟨_, ?_, hE'.post hpt1⟩
  have hr0 : (helloS arch).Run s [] { s with ths := s.ths.set! 1 (atQ s1 q') } :=
    frameRun_run_source_i (P := X64WakeT1.srcPo 2 arch helloSrc) rfl (by decide) hr hs1 rfl rfl h.σs rfl hex
      (hm.certified (wcompatH_qt hC))
  have hr1 := hrun ((X64HelloEmitPost.PartsE.toC hE').certified hC)
  have hbt' : bt = ⟨TermRun.laneN .w8 v (k % 8) % 256, Nat.mod_lt _ (by decide)⟩ :=
    Fin.ext (by show bt.val = _ % 256; rw [← hbt, Nat.mod_eq_of_lt bt.isLt])
  simp only [ite_true] at he
  subst he hbt'
  have := Scc.Sem.LRun.trans hr0 hr1
  rwa [List.nil_append] at this

/-! ## The byte picks -/

/-- **A byte pick at the worker's `write(1, buf, n)` keeps `Post`**, at the
common parts with the worker in its invariant at some control and, with no
byte out, at the source worker's control: with no byte out, the emit row
of the shape (`EmitShapeF`: a frame run to `(c', fs')` with `Pw 0 c'`, then
byte `0`'s `ByteOutP`); with `j > 0` bytes out, the link's emit row
(`EmitR`: the source worker at `Pw j`, an empty frame run; not `WrOth`, a
`write` to fd 1). -/
theorem post_byteC (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ) {Ent : Entry}
    (hpk : DmemPriv.DmemPriv abi Λ Ent t) (hE : Ent.clear Λ = true) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hex : SrcSem.mainExit s = [])
    (hW : ∃ c fs, D.Wi w t1.st c fs) (hat : abi.atSys t1.st = true)
    (hWi0 : t.2.wr 1 = 0 → D.Wi w t1.st (Ctl.of s1) s1.stack) (hF : X64HelloEmitPh.EmitFrS D w t1.st s1.stack)
    {buf n : Nat} (hd : decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n))
    {rd : Nat} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.tso 1 t (.byte rd) = some (es, t'))
    (hca : CertAfter abi Arch.tso μ 1 t') :
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  have hs1 : s.ths[1]? = some s1 := by rw [h.ths]; rfl
  obtain ⟨-, -, hlt, -⟩ := HelloWrite.sysStep_write_byte ht1 hd hs
  rcases Nat.eq_zero_or_pos (t.2.wr 1) with h0 | hp
  · obtain ⟨c', fs', Pw, Qw, hr, hP0, hcl⟩ := hES w t1.st s1 buf n (hWi0 h0) hat hd
    have hb := hcl.1 0 (by omega) c' hP0
    rw [hbo] at hb
    have hF0 : X64HelloEmitPh.EmitFrS D w t1.st fs' := by
      rcases emitFrS_run (hC.cwv w) hr (s1 := s1) rfl rfl (.inl ⟨h.ph, h.term⟩) with h' | h' | ⟨h0', h'⟩
      · exact .inl h'
      · exact .inr ⟨_, _, hWi0 h0, .inl h'⟩
      · exact .inr ⟨_, _, hWi0 h0, .inr ⟨h0', h'⟩⟩
    refine post_byte hC hKR hpt1 hlbl hfz hpk hE hown h hex hW hat hd (q' := (c', fs')) hr hcl hF0 ?_ hs hca
    rw [h0]
    exact hb
  · have hk := h.kr
    rw [hKR] at hk
    obtain ⟨u1, v1, h1, h2, hER⟩ := hk.2.1 hp
    obtain rfl : u1 = t1 := Option.some.inj (h1.symm.trans ht1)
    obtain rfl : v1 = s1 := Option.some.inj (h2.symm.trans hs1)
    rcases hER with ⟨buf', n', Pw, Qw, -, hd', hcl, -, hPj⟩ | ⟨fd, buf', n', hfd, -, hd', -⟩
    · have e := Option.some.inj (hd.symm.trans hd')
      cases e
      have hb := hcl.1 _ hlt _ hPj
      rw [hbo] at hb
      exact post_byte hC hKR hpt1 hlbl hfz hpk hE hown h hex hW hat hd (.refl _) hcl hF hb hs hca
    · have e := Option.some.inj (hd.symm.trans hd')
      cases e
      exact absurd rfl hfd

/-- **A byte pick from `PartsH` in the print phase** (`post_byteC`; the
worker's invariant at the source worker's control). -/
theorem post_byteH (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ) {Ent : Entry}
    (hpk : DmemPriv.DmemPriv abi Λ Ent t) (hE : Ent.clear Λ = true) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1)
    (hex : SrcSem.mainExit s = []) (hat : abi.atSys t1.st = true)
    {buf n : Nat} (hd : decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n))
    {rd : Nat} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.tso 1 t (.byte rd) = some (es, t'))
    (hca : CertAfter abi Arch.tso μ 1 t') :
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' :=
  post_byteC hC hKR hpt1 hlbl hfz hpk hE hown hbo hES (X64HelloEmitPost.PartsH.toC hC h hP) hex ⟨_, _, h.pt1.1⟩ hat
    (fun _ => h.pt1.1) (.inr ⟨_, _, h.pt1.1, .inl rfl⟩) hd hs hca

/-- **A byte pick from `PartsE` off the worker's invariant** (`post_byteC`;
bytes out by the link's converse). -/
theorem post_byteE (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ) {Ent : Entry}
    (hpk : DmemPriv.DmemPriv abi Λ Ent t) (hE : Ent.clear Λ = true) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w)) (hES : EmitShapeF D)
    (h : PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hn : ¬ D.Wi w t1.st (Ctl.of s1) s1.stack)
    (hex : SrcSem.mainExit s = []) {buf n : Nat}
    (hd : decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n))
    {rd : Nat} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.tso 1 t (.byte rd) = some (es, t'))
    (hca : CertAfter abi Arch.tso μ 1 t') :
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have hk := h.kr
  rw [hKR] at hk
  have hp := hk.2.2 t1 s1 h.t1_get h.s1_get hn
  exact post_byteC hC hKR hpt1 hlbl hfz hpk hE hown hbo hES (X64HelloEmitPost.PartsE.toC h) hex h.pt1.1 h.pt1.2.1
    (fun h0 => absurd hp (by rw [h0]; exact Nat.lt_irrefl 0)) h.pt1.frS hd hs hca

/-- info: 'Spike.Lib.X64HelloEmitStep.byte_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms byte_val

/-- info: 'Spike.Lib.X64HelloEmitStep.post_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_byte

/-- info: 'Spike.Lib.X64HelloEmitStep.post_byteE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_byteE

/-- info: 'Spike.Lib.X64HelloEmitStep.post_byteH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_byteH

end Spike.Lib.X64HelloEmitStep
