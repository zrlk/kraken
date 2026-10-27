/-
**The allocation-capable consumer at any source start** (AArch64):
`Spike/Lib/A64ConsumerACorrect.lean`'s load, step-wise simulation and
`Correct` with the source's start configuration a parameter, not
`s0 P.cap` (`main` entered on a unit argument). The start is one thread
`th0` with no frame, no type variable, no promise and no allocation yet, on
empty memory, its pair in the fragment at the loaded thread with no hold:
e.g. the start before a setup block (`setupStart`, `Scc/Sem/SrcOut.lean`;
`Spike/Test/SetupStartSrc.lean`), whose thread calls `rodata` and then
enters `main`.

- `StartOk`: those facts of a configuration and its thread.
- `StartOk.s0`: `s0 P.cap` at `c0` is such a start.
- `pre_loadA'`, `init_of_loadA'`, `stepSimA'`, `correctKOnA'`, `correctKA'`:
  `pre_loadA` … `correctKA` at a start with `StartOk`; only the load
  changes (the steps, progress and the abort clause are `RSA`'s).
- `correctKA_of'`: `correctKA` again, as `correctKA'` at `s0 P.cap`.
- `correctKAE'`: `correctKA'` at any entry state `E` (the target
  `target (kernel 1) E`, the loaded thread `threadAt E`); `correctKAE`:
  `CorrectE 1` from it at every admissible entry state.
-/
import Spike.Lib.A64ConsumerACorrect
import Scc.Sem.CorrectEA64

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry}

/-- **A source start**: one thread `th0`, no frame, no type variable, no
promise, no allocation yet, on empty memory. -/
structure StartOk (s : TermRun.Cfg) (th0 : TermRun.TTh) : Prop where
  ths : s.ths = #[th0]
  σs : th0.σs = []
  promises : th0.promises = []
  stack : th0.stack = []
  nalloc : th0.nalloc = 0
  mem : s.mem = #[]

/-- `s0 P.cap`, `main` entered on a unit argument, is a start. -/
theorem StartOk.s0 (cap : Nat) : StartOk (s0 cap) { term := c0.term, env := c0.env } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A start's heap use is 0. -/
theorem StartOk.heapUse {s : TermRun.Cfg} {th0 : TermRun.TTh} (h : StartOk s th0) : heapUse s = 0 := by
  unfold Scc.Sem.heapUse Scc.Sem.cellCount Scc.Sem.allocCount
  rw [h.mem, h.ths]; simp [h.nalloc]

/-! ## The load -/

open Scc.Cert.Link in
/-- **The start is related** (`pre_loadA` at a start `s` with `StartOk`,
its pair `⟨th0.term, th0.env, none⟩` in the fragment at no frame). -/
theorem pre_loadA' {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {prog : Program} {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize} {secs : DataSecs}
    {code : String → Option Nat} {name : WeakMem.AllocLabel → String} {s : TermRun.Cfg} {th0 : TermRun.TTh}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hinit : P.init s) (hs : StartOk s th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog syms) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s.lbase s.n 0 0)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64) {rS : Range} {Tk : State → Prop}
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog syms))
    (hown0 : OwnInit (own (threadAt E Λ.code.lo prog syms) [])
      (loadProg (kernel 1) E Λ prog syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ prog syms mem).1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc a) = 0)
    (hc0 : (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc ar.ctr) = 0) :
    PreSA Λ P p G own I rS Tk μ ar (loadProg (kernel 1) E Λ prog syms mem) s := by
  have hinv := Inv1.start_static (I := isaLSE2) (t := Thread.init (threadAt E Λ.code.lo prog syms))
    (tm := (loadProg (kernel 1) E Λ prog syms mem).1.mem) himg hss rfl rfl
  rw [← hs.mem] at hinv
  have hst' := hs.stack ▸ hst
  refine ⟨Thread.init (threadAt E Λ.code.lo prog syms), th0, 0, Λ.static, lsize, fun _ => none, [], ∅, none,
    rfl, ?_, fun _ => by simp [Kernel.byte],
    .inl ⟨rfl, htk0⟩, .inl rfl, certOkC_of_prom_nil rfl, hs.ths, hs.σs, hs.promises, hst', .inl trivial,
    wideSt_threadAt hw _ _ _,
    bnd_init _ _,
    hinv, ?_, ⟨?_, hmem⟩, ⟨fits_empty rfl, hmf⟩, hg,
    ownOk_init (by simp [loadProg, Config.init]) (hs.stack ▸ hown0) _, ?_, hs.nalloc ▸ hfr0, ?_,
    [], s, hinit, .refl _⟩
  · exact ⟨E, rfl⟩
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · intro k m hk; unfold Memory.get? at hk; split at hk
    · cases hk
    · simp [loadProg, Config.init] at hk
  · have hnm : ∀ k', (loadProg (kernel 1) E Λ prog syms mem).1.mem.get? k' = none := fun k' => by
      cases hk : (loadProg (kernel 1) E Λ prog syms mem).1.mem.get? k' with
      | none => rfl
      | some m =>
        unfold Memory.get? at hk; split at hk
        · cases hk
        · simp [loadProg, Config.init] at hk
    have har : AllocRow.ArenaOK Λ Λ.static lsize (Thread.init (threadAt E Λ.code.lo prog syms) : Thread isaLSE2)
        (loadProg (kernel 1) E Λ prog syms mem).1.mem ar.heap ar.cells 0 (fun _ => False) := by
      rw [hstat]; exact AllocRow.ArenaOK.init hsub hal hz0 hnm
    have hct := AllocInv.CtrAt.init (prom := (Thread.init (threadAt E Λ.code.lo prog syms) : Thread isaLSE2).prom)
      (ctr := ar.ctr) (fun k' _ => hnm k')
    rw [hc0] at hct
    rw [hs.heapUse]
    exact .inr ⟨(fun w h => by cases h), by simpa using hct, har⟩
  · intro l b hb
    simp [hstat] at hb

open Scc.Cert.Link in
/-- **The relation at the target's load** at a start with `StartOk`
(`init_of_loadA`, by `pre_loadA'`). -/
theorem init_of_loadA' {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String} {s0' : TermRun.Cfg}
    {th0 : TermRun.TTh} (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true)
    (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hinit : P.init s0') (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    {rS : Range} {Tk : State → Prop} (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    {t0 : T.M.Cfg} (hown0 : OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) [])
      t0.1.mem)
    (hg : MemInv G t0.1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : t0.1.mem.initVal (wordLoc ar.ctr) = 0) (h : loadParsed (kernel 1) E Λ prog secs = some t0) :
    ∃ s, (SrcSem.source P p).init s ∧ RSA Λ P p G own I rS Tk μ ar t0 s := by
  simp only [loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    refine ⟨s0', hinit, .inl (pre_loadA' himg hss hw hinit hs hst hfr0 (loadMem_in hwf hc.1.1.1.1) ?_ htk0
      hown0 hg hstat hsub hal hz0 hc0)⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

/-! ## The step-wise simulation and `Correct` -/

open Scc.Cert.Link in
/-- **The step-wise simulation** at a start with `StartOk` (`stepSimA`). -/
theorem stepSimA' {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hP : HookOK P p) (hinit : P.init s0')
    (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hrd : SrcRd P p rd)
    (hwf : Λ.WF) (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    StepSim (TOn A ld rs) (SrcSem.source P p) Λ asm
      (RSA Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) ar) where
  init _ h := init_of_loadA' hwf himg hss hw hinit hs hst hfr0 htk0 (hown0 _ h) (hG0 _ h) hstat hsub hal (hz0 _ h)
    (hc0 _ h) (hl.symm.trans h)
  step _ _ _ _ _ h hs := r_stepA hP hN hsafe hT (promSharedA hP hN hsafe hrd hwf hGpl hok hT)
    hrd hwf hGpl hok h hs

open Scc.Cert.Link in
/-- **`Correct` at a start with `StartOk`** on a target on the canonical
AArch64 machine (`correctKOnA`, the simulation `stepSimA'`). -/
theorem correctKOnA' {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p)
    (hinit : P.init s0')
    (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm := by
  have hsim := stepSimA' hl himg hss hw hs hst hfr0 hP hinit hN hsafe hT htk0 hown0 hrd hwf hG0 hGpl hok hstat hsub
    hal hz0 hc0
  have hps := promSharedA hP hN hsafe hrd hwf hGpl hok hT
  refine correct_of_stepSim hsim hwf hload (fun t0 tr t h0 hr => ?_)
    (fun t0 tr t tid es t' k s h0 hr _ hR hs hk => ?_)
    (fun t s hR => r_componentsA hN hwf hR)
  · obtain ⟨s, -, hR⟩ := hsim.reach h0 hr
    exact ⟨r_progressA hN hA hT hwf hsvc hR, inLayout_of_memIn (r_memInA hR)⟩
  · obtain ⟨s0', -, hR0⟩ := hsim.init t0 h0
    have hti := ti_runA hN hA hT
      (fun hR hs => let ⟨s', _, h'⟩ := r_stepA hP hN hsafe hT hps hrd hwf hGpl hok hR hs; ⟨s', h'⟩)
      hr hR0 (pre := []) (fun th h hab => absurd hab (ti_load hab0 (hl.symm.trans h0) th h))
    rw [List.nil_append] at hti
    exact r_abortA hN hwf hA hB hR hti hs hk

open Scc.Cert.Link in
/-- **`Correct` at a start with `StartOk`** on the canonical AArch64
target: `correctKOnA'` at `T`, the load by `load_of_parsed`. -/
theorem correctKA' {B : Budget} (hB : B.cells = ar.cells) {asm : String} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))
      ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init s0')
    (hN : NodesA Λ p (T.marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk (T.marks asm Λ) ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS (T.marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, T.load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, T.load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKOnA' (A := String) (ld := T.load) (rs := T.resolve) hB (load_of_parsed (kernel 1) Entry.linux Λ hpa hd)
    himg hss hw hs hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 hsvc hrd hwf hG0 hGpl hA hab0 hok hstat hsub hal
    hz0 hc0

open Scc.Cert.Link in
/-- **`correctKA` is `correctKA'` at `s0 P.cap`** (`StartOk.s0`; `c0` is the
start's pair with no hold). -/
theorem correctKA_of' {B : Budget} (hB : B.cells = ar.cells) {asm : String} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : NodesA Λ p (T.marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk (T.marks asm Λ) ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS (T.marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, T.load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, T.load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKA' hB hpa hd himg hss hw (StartOk.s0 P.cap) hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 hsvc hrd hwf
    hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0

-- The kernel's check that `target (kernel 1) E`'s machine is `T`'s (`canonical 1`) may recurse past the default depth.
set_option maxRecDepth 100000 in
open Scc.Cert.Link in
/-- **`Correct` at any entry state** on the kernel-model AArch64 target
`target (kernel 1) E`, at a start with `StartOk`: `correctKOnA'` at that
target, the load by `load_of_parsed` at `E`. `correctKA'` is it at
`Entry.linux`. The premises naming the loaded thread are at `threadAt E`. -/
theorem correctKAE' {B : Budget} (hB : B.cells = ar.cells) {asm : String} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, (target (kernel 1) E).load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init s0')
    (hN : NodesA Λ p ((target (kernel 1) E).marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((target (kernel 1) E).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk ((target (kernel 1) E).marks asm Λ) ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((target (kernel 1) E).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → ∀ a,
      (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct (target (kernel 1) E) (SrcSem.source P p) Λ B asm :=
  correctKOnA' (A := String) (ld := (target (kernel 1) E).load) (rs := (target (kernel 1) E).resolve) hB
    (load_of_parsed (kernel 1) E Λ hpa hd) himg hss hw hs hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 hsvc hrd
    hwf hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0

/-- **`CorrectE` from `correctKAE'` at every admissible entry state**: the
premises, given for each entry state `E` that `Entry.Ok` admits for `Λ`
(`h`), give `Correct` at `target (kernel 1) E` for each, which is
`Scc.Sem.A64.CorrectE 1`. -/
theorem correctKAE {B : Budget} {asm : String} {S : SrcSem}
    (h : ∀ E : Entry, E.Ok Λ → Correct (target (kernel 1) E) S Λ B asm) : CorrectE 1 S Λ B asm := h

/--
info: 'Spike.Lib.A64ConsumerA.correctKAE'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correctKAE'

end Spike.Lib.A64ConsumerA
