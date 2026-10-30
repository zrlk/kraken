/-
**Correctness of the allocation-capable consumer**
(`Spike/Lib/A64ConsumerA.lean`): `A64ConsumerS`'s load, step-wise
simulation, progress, abort clause and `Correct` over `RSA`.

The load relates the start with the allocation invariant idle at heap use 0
(`pre_loadA`: the arena zero and the counter 0 at the initial write, no
label placed); the step is `r_stepA` with `promSharedA`; a `heap` abort is
justified by `AllocInvAt.heapCtr`.

- `pre_loadA`, `init_of_loadA`, `stepSimA`, `r_componentsA`: the load and
  the simulation.
- `WriteNoPromA`, `pre_progressA`, `r_progressA`, `r_memInA`: progress.
- `ti_step_ofA`, `ti_stepA`, `ti_runA`, `r_abortA`: the abort clause.
- `correctKOnA`, `correctKA`: `Correct`.

The components, progress and abort lemmas hold for rows under any
`msOfAX … ab` (off the output `write`, `NodesA.rowX`, `NodesA.sysOkX`).
-/
import Spike.Lib.A64ConsumerACore
import Spike.Lib.HeapAbortBox

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry}

/-! ## The load -/

open Scc.Cert.Link in
/-- **The start is related** (`pre_load` with the frames): the loaded
thread at the start pair at no frames, thread 0's labels from 0 on unplaced
under the static placement (`hfr0`; at `main`'s start no buffer is
allocated: the allocation invariant idle at heap use 0, the arena
`ArenaOK.init`, the counter at its initial value 0, `CtrAt.init`; no label
placed, `hstat`). -/
theorem pre_loadA {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {prog : Program} {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize} {secs : DataSecs}
    {code : String → Option Nat} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hinit : P.init (s0 P.cap)) (hst : I Λ.static lsize (threadAt E Λ.code.lo prog syms) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64) {rS : Range} {Tk : State → Prop}
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog syms))
    (hown0 : OwnInit (own (threadAt E Λ.code.lo prog syms) [])
      (loadProg (kernel 1) E Λ prog syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ prog syms mem).1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc a) = 0)
    (hc0 : (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc ar.ctr) = 0) :
    PreSA Λ P p G own I rS Tk μ ar (loadProg (kernel 1) E Λ prog syms mem) (s0 P.cap) := by
  refine ⟨Thread.init (threadAt E Λ.code.lo prog syms), _, 0, Λ.static, lsize, fun _ => none, [], ∅, none,
    rfl, ?_, fun _ => by simp [Kernel.byte],
    .inl ⟨rfl, htk0⟩, .inl rfl, certOkC_of_prom_nil rfl, rfl, rfl, rfl, hst, .inl trivial,
    wideSt_threadAt hw _ _ _,
    bnd_init _ _,
    Inv1.start_static himg hss rfl rfl, ?_, ⟨?_, hmem⟩, ⟨fits_empty rfl, hmf⟩, hg,
    ownOk_init (by simp [loadProg, Config.init]) hown0 _, ?_, hfr0, ?_,
    [], s0 P.cap, hinit, .refl _⟩
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
    have h0 : heapUse (s0 P.cap) = 0 := rfl
    rw [h0]
    exact .inr ⟨(fun w h => by cases h), by simpa using hct, har⟩
  · intro l b hb
    simp [hstat] at hb

open Scc.Cert.Link in
/-- **The relation at the target's load** (`init_of_load` with the frames,
by `pre_loadA`). -/
theorem init_of_loadA {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true)
    (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hinit : P.init (s0 P.cap))
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
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
    refine ⟨s0 P.cap, hinit, .inl (pre_loadA himg hss hw hinit hst hfr0 (loadMem_in hwf hc.1.1.1.1) ?_ htk0
      hown0 hg hstat hsub hal hz0 hc0)⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

/-! ## The step-wise simulation -/

open Scc.Cert.Link in
/-- **The step-wise simulation** at any depth (`stepSim` with the frames;
`PromSharedS` discharged by `promSharedA`). -/
theorem stepSimA {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hP : HookOK P p) (hinit : P.init (s0 P.cap))
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
  init _ h := init_of_loadA hwf himg hss hw hinit hst hfr0 htk0 (hown0 _ h) (hG0 _ h) hstat hsub hal (hz0 _ h)
    (hc0 _ h) (hl.symm.trans h)
  step _ _ _ _ _ h hs := r_stepA hP hN hsafe hT (promSharedA hP hN hsafe hrd hwf hGpl hok hT)
    hrd hwf hGpl hok h hs

/-- **`RS` is explicit** (`r_components` with the frames). -/
theorem r_componentsA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    (hwf : Λ.WF) {rS : Range} {Tk : State → Prop} {t : T.M.Cfg}
    {s : TermRun.Cfg} (h : RSA Λ P p G own I rS Tk μ ar t s) :
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s) := by
  rcases h with ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, hk⟩, -, hh, -, -, hs0, -, -, hI, -, -, -, hinv,
      hown, hmi, -⟩ |
    ⟨th, th0, j, lbl, lsize, ts, hl, pm, o, hth, ⟨E, hk⟩, -, hh, hs0, -, -, hpl, hinv, hown, hmi, -⟩
  · exact (components_oneSX hwf hth (by rw [hk]; rfl) hh hmi hs0
      (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown).imp fun _ h => h.1
  · exact (components_oneSX hwf hth (by rw [hk]; rfl) hh hmi hs0 hpl hinv hown).imp fun _ h => h.1

/-! ## Progress -/

/-- **No promise at a `write`** at any depth (`WriteNoPromS` over `PreSA`). -/
def WriteNoPromA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s th, PreSA Λ P p G own I rS Tk μ ar t s → t.1.threads = #[th] → abi.atSys th.st = true →
    (∃ fd buf n, Kernel.callOf abi th = some (.write fd buf n)) → th.prom = []

/-- **The abort path with a `clone` refusal** (`AbortPathS` with the
`threads` abort): a pair at a resolved abort site may also be at the
`threads` site in the phase `Ac` (after a refused `clone`, `TIC`); `Ac` is
entered only at a state `Cl` marks (`sysC`: off `Cl`, a system call does not
enter it), not by an instruction (`instrC`) or the take (`takeC`). -/
structure AbortPathSC (μ : Marks) (I : InvS) (Cl Ab Ac : State → Prop) (cells ctr : Nat) : Prop where
  at_ : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortOblA cells ctr c) ∨ (k = .threads ∧ Ac s)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  instr : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')
  sys : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, Ab s' →
      ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r
  take : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ab s → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, ¬ Ab (abi.skip (abi.setDmem s m))
  instrC : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ac s → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ac s')
  sysC : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ac s → abi.atSys s = true → ¬ Cl s → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, ¬ Ac s'
  takeC : ∀ lbl lsize s c fs, I lbl lsize s c fs → ¬ Ac s → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, ¬ Ac (abi.skip (abi.setDmem s m))

/-- `AbortPathS` is `AbortPathSC` with no `threads` phase. -/
theorem _root_.Spike.Lib.A64ConsumerS.AbortPathS.toC {Cl Ab : State → Prop} {cells ctr : Nat}
    (h : AbortPathS μ I Ab cells ctr) :
    AbortPathSC μ I Cl Ab (fun _ => False) cells ctr where
  at_ lbl lsize s c fs hI k a ha hpc := by
    obtain ⟨h1, h2⟩ := h.at_ lbl lsize s c fs hI k a ha hpc
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr (.inl ⟨h1.1, HeapAbortObl.toA h1.2⟩))
  instr := h.instr
  sys := h.sys
  take := h.take
  instrC _ _ _ _ _ _ _ _ tree _ := (allInv_true tree).mono fun _ _ h => h
  sysC _ _ _ _ _ _ _ _ _ _ _ _ _ h := h
  takeC _ _ _ _ _ _ _ _ _ _ _ h := h

/-- **A row under `msOfA` off a system call has no error outcome**
(`ExtRows.out_no_error` with the box's rows: its store and the counter's
add, `Out.unnew`; the fence with the source's publication, `Out.unpubL`). -/
theorem outA_no_error {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {X : Frag isaLSE2} {c : Ctl}
    {th : Thread isaLSE2} {tid : Nat} {mem : Memory} (hns : abi.atSys th.st = false)
    (hout : Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs) X th.st c)
    {outs : List (Except String (Kraken.Promising.Outcome isaLSE2))}
    (hs : stepOne Arch.armv8 th tid mem = some outs) (m : String) :
    (.error m : Except String (Kraken.Promising.Outcome isaLSE2)) ∉ outs := by
  rcases hout.unnew with ⟨_, _, _, _, _, _, _, _, _, _, _, -, he, -⟩ | ⟨_, _, _, _, _, he, -⟩ | h
  · exact Spike.Bridge.stepOne_no_error _ he (Spike.Bridge.runTree_store_ok _ _ _ _ _ _ _ _) hs m
  · exact Spike.Bridge.stepOne_no_error _ he (RtRmw.runTree_rmw_ok _ _ _ _ _ _ _ _) hs m
  · -- the fence with the source's publication is a fence row with no publication (the landing dropped)
    rcases h.unpubL with ⟨k, s', -, -, he, -⟩ | h
    · exact ExtRows.out_no_error (X := fun _ _ => True) hns (show Out p lbl (msOfA0 Λ μ rd G own ar I lbl lsize fs)
        _ th.st c from .fence k s' c he (.loc (.refl _)) trivial) hs m
    · exact ExtRows.out_no_error hns (show Out p lbl (msOfA0 Λ μ rd G own ar I lbl lsize fs) X th.st c from h) hs m

/-- **A row under `msOfA` off a system call has an outcome** with no promise
for a thread with no promise and its values at most `|M|`
(`ExtRows.out_progress` with the box's rows, `Out.unnew`; the fence with
the source's publication, `Out.unpubL`). -/
theorem outA_progress {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {X : Frag isaLSE2} {c : Ctl}
    {th : Thread isaLSE2} {tid : Nat} {mem : Memory} (hp : th.prom = []) (hb : th.Bnd mem.last)
    (hns : abi.atSys th.st = false) (hout : Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs) X th.st c) :
    ∃ outs o, stepOne Arch.armv8 th tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  rcases hout.unnew with ⟨_, _, _, _, _, _, _, _, _, _, _, -, he, -⟩ | ⟨_, _, _, _, _, he, -⟩ | h
  · exact ExtRows.store_ok hp hb he
  · exact RtRmw.rmw_ok _ hp hb he
  · -- the fence with the source's publication is a fence row with no publication (the landing dropped)
    rcases h.unpubL with ⟨k, s', -, -, he, -⟩ | h
    · exact ExtRows.out_progress (X := fun _ _ => True) hp hb hns (show Out p lbl
        (msOfA0 Λ μ rd G own ar I lbl lsize fs) _ th.st c from .fence k s' c he (.loc (.refl _)) trivial)
    · exact ExtRows.out_progress hp hb hns (show Out p lbl (msOfA0 Λ μ rd G own ar I lbl lsize fs) X th.st c from h)

/-- **Before the exit there is progress** at any depth, for rows under any
`NodesA … ab Cl` with thread 0 off `Cl` (`hnc`; at a `Cl` state, a `clone`,
the one-slot configuration faults: `Spike.Lib.WakePre.Pre1.progressClone_of`
there). `pre_progressA`'s argument. -/
theorem pre_progressAC {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hwf : Λ.WF)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreSA Λ P p G own I rS Tk μ ar t s)
    (hnc : ∀ th, t.1.threads = #[th] → ¬ Cl th.st) : T.M.Progress μ t := by
  have hwnp := hsvc t s
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, hh, hwr, hcert, hs0, hσ, hp, hI, -, hw, hb,
    hinv, hown, hmi, -, -, -, -, -, -, hre⟩ := h
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hrk : t.2.runs 0 = true := by rw [hk]; rfl
  have hxk : t.2.exited = none := by rw [hk]; rfl
  have hruns : T.M.runs t 0 := ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs 0 = false); rw [hrk]; simp⟩
  have hnh : th.halted = false := by
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).2.1
      simp [Thread.halted, Kraken.Promising.Lower.A64.exec_nop hcn]
    cases hs : abi.atSys th.st
    · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowNS hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) hs
      have := Out.exec_isSome rfl hs hout
      simp only [Thread.halted]
      cases he : isaLSE2.exec th.st
      · rw [he] at this; cases this
      · simp
    · obtain ⟨imm, sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
      simp [Thread.halted, Kraken.Promising.Lower.A64.exec_svc hc]
  refine ⟨?_, .inr ⟨⟨0, hxk, hruns.2.2, th, ht, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.armv8 th 0 t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      cases hsy : abi.atSys th.st
      · by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
        · obtain ⟨a, ha, hpc⟩ := htk
          obtain ⟨sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).2.1
          exact Kraken.Promising.Lower.stepOne_silent_no_error Arch.armv8 0 (Kraken.Promising.Lower.A64.exec_nop hcn)
            (Kraken.Promising.Lower.silentTree_done _) hs' m hm
        · obtain ⟨c₁, fs₁, -, -, hout⟩ :=
            hN.rowNS hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) hsy
          exact outA_no_error hsy hout hs' m hm
      · exact hns ⟨th, ht1, hsy⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [hnh, Bool.or_false] at hf
        cases hsy : abi.atSys th.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXC hT hI hsy (hnc th hth)
          rw [show Kernel.callOf abi th = some call from hd] at hf
          cases call with
          | clone st tl => exact hcl st tl rfl
          | _ => simp at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      rw [hk] at htouch
      exact hN.mapped _ _ _ _ _ hI hns e hex (touches_mono (fun _ _ h => mapped_KS h) htouch)
  · obtain ⟨-, -, t1, ht1, -⟩ := hl
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · -- at the take site: the take
      obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨hntk, ⟨sz, hcn⟩, -, hsr, hsub, hpos, hrod, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
      obtain rfl : hl = [] := by
        rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h
        · exact absurd h hntk
      have hf : Kernel.fresh t (Kernel.siteRange abi th.st) = true := by
        rw [hsr]; exact fresh_of hwf hk hsub hpos hrod hmi
      exact ⟨[], _, .xfer .take hruns ⟨a, ha, th, ht, hpc⟩
        (Kernel.xfer_take (K := abi) Arch.armv8 1 ht hrk hxk (atNop_of_cellAt hcn) hf)⟩
    have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
    have hsite := no_siteA hN ht hI hnt
    cases hs : abi.atSys th.st
    · have hnsys : ¬ T.M.atSys t 0 := fun ⟨t2, ht2, h2⟩ => by
        cases (show some t2 = some th from ht2.symm.trans ht)
        have h3 : abi.atSys th.st = true := h2
        rw [hs] at h3; cases h3
      by_cases hpn : th.prom = []
      · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowNS hI hnt hs
        obtain ⟨outs, o, hso, ho, hpo⟩ :=
          outA_progress (tid := 0) (mem := t.1.mem) hpn hb hs hout
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
      · obtain ⟨t', mem', hr, hp'⟩ := hcert
        cases hr with
        | refl => exact absurd hp' hpn
        | step hs1 hrest =>
          obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
          replace hso : stepOne Arch.armv8 th 0 t.1.mem = some outs :=
            (Kernel.certSem_step_of_not_site (x := t.2) (siteAt_noneA hN hI hnt) hs).symm.trans hso
          exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
    · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
      obtain ⟨call, hd, hnx, hcl⟩ := hN.sysOkXC hT hI hs (hnc th hth)
      have hc : Kernel.callOf abi th = some call := hd
      have hsys : ∀ c', (kernel 1).sys μ 0 t [] c' → ∃ es c', T.M.Step μ 0 t es c' :=
        fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
      by_cases hpn : th.prom = []
      rotate_left
      · -- with promises: no `write` (`WriteNoPromA`), none at `exit_group`; elsewhere `Kernel.sys_progress`
        have hsn := siteAt_noneA hN hI hnt
        cases call with
        | write fd buf n => exact absurd (hwnp th hpre hth hs ⟨fd, buf, n, hc⟩) hpn
        | exitGroup v => exact absurd (Kernel.prom_nil_of_exit hsn hs hd (.inr ⟨v, rfl⟩) hcert) hpn
        | exit => exact absurd rfl hnx
        | clone st tl => exact absurd rfl (hcl st tl)
        | _ =>
          obtain ⟨r, es, c', h, hca⟩ := Kernel.sys_progress ht hr hsn hc (fun _ _ _ h => by cases h)
            (fun _ _ h => by cases h) hpn hcert
          obtain rfl := Kernel.sysStep_ret_nil ht hc (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun h => by cases h) (fun _ h => by cases h) h
          exact hsys c' ⟨.ret r, h, hca⟩
      cases call with
      | write fd buf n =>
        by_cases hj : t.2.wr 0 = 0
        · exact hsys _ (Kernel.sys_writeIntr (K := abi) Arch.armv8 1 ht hr hpn hc hj)
        · exact hsys _ (Kernel.sys_writeRet (K := abi) Arch.armv8 1 ht hr hpn hc (Nat.pos_of_ne_zero hj))
      | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.armv8 1 ht hr hpn hc)
      | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.armv8 1 ht hr hpn hc)
      | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.armv8 1 ht hr hpn hc)
      | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.armv8 1 ht hr hpn hc)
      | exitGroup v =>
        by_cases hab : ∃ k a, μ.abortAt k = some a ∧ pcOf th.st = a
        · -- at an abort site: the abort
          obtain ⟨k, a, ha, hpc⟩ := hab
          obtain ⟨-, hv⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroupAbort (K := abi) Arch.armv8 1 k ht hr hpn hc (hv v hd))
            (by simp) (fun k' hk => by obtain rfl : k' = k := by simpa using hk
                                       exact ⟨a, ha, th, ht, hpc⟩) (fun e he => by simp at he)⟩
        · have hnoab : ∀ k a, μ.abortAt k = some a → ¬ T.M.AtAddr a t 0 := fun k a ha ⟨t2, ht2, hpc⟩ => by
            cases (show some t2 = some th from ht2.symm.trans ht); exact hab ⟨k, a, ha, hpc⟩
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.armv8 1 ht hr hpn hc) (by simp)
            (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
      | exit => exact absurd rfl hnx
      | clone st tl => exact absurd rfl (hcl st tl)

/-- **Before the exit there is progress** at any depth (`pre_progress` with
the frames; off a system call by the row after the pair's frame run,
`NodesA.row`): `pre_progressAC` with no state marked. -/
theorem pre_progressA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    {Ab : State → Prop} (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hwf : Λ.WF)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreSA Λ P p G own I rS Tk μ ar t s) : T.M.Progress μ t :=
  pre_progressAC hN hA.toC hT hwf hsvc h fun _ _ h => h

/-- **There is progress from `RS`**, thread 0 off `Cl` (`pre_progressAC`). -/
theorem r_progressAC {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hwf : Λ.WF)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hnc : ∀ th, t.1.threads = #[th] → ¬ Cl th.st) : T.M.Progress μ t :=
  h.elim (fun h => pre_progressAC hN hA hT hwf hsvc h hnc) post_progressSA

/-- **There is progress from `RS`.** -/
theorem r_progressA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    {Ab : State → Prop} (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hwf : Λ.WF)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSA Λ P p G own I rS Tk μ ar t s) : T.M.Progress μ t :=
  h.elim (pre_progressA hN hA hT hwf hsvc) post_progressSA

/-! ## Correctness -/

/-- The memory of a configuration `RS` relates is in the layout. -/
theorem r_memInA {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : RSA Λ P p G own I rS Tk μ ar t s) : MemIn Λ t.1.mem := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ <;> exact hmi

/-! ## The abort clause -/

/-- **`TI` with the `clone` phase**: `TI` for the `writeErr` phase `Ab`,
and thread 0 in the `threads` phase `Ac` only after a refused `clone`. -/
def TIC (Ab Ac : State → Prop) (tr : List Ev) (t : T.M.Cfg) : Prop :=
  TI Ab tr t ∧ ∀ th, t.1.threads[0]? = some th → Ac th.st → Ev.cloneErr ∈ tr

/-- **`TIC` is kept by every step from thread 0 at a state of the fragment**
(`ti_step_ofA` with the `clone` phase): at a `Cl` state the step is a
refused `clone` (one slot, none dormant), which emits `cloneErr`; elsewhere
`Ac` is not entered (`AbortPathSC.instrC`, `sysC`, `takeC`). -/
theorem ti_step_ofAC {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {t t' : T.M.Cfg} {tid : Nat} {es pre : List Ev} {th : Thread isaLSE2} {j : Nat} {E : Entry}
    {hl : List (Nat × Range)} {pm : _root_.Mem 64} {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {sm : WeakMem.Memory} {c : Ctl} {fs : List TermRun.Frame}
    (hth : t.1.threads = #[th]) (hk : t.2 = KS E Λ j hl pm) (hwr : WrOk th j) (hI : I lbl lsize th.st c fs)
    (hw : WideSt th.st) (hinv : Inv1 Λ lbl lsize ts th t.1.mem sm)
    (hs : T.M.Step μ tid t es t') (hti : TIC Ab Ac pre t) : TIC Ab Ac (pre ++ es) t' := by
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have hget : ∀ {v : Thread isaLSE2} {mem : Memory} {u : Thread isaLSE2},
      (t.1.withThread 0 v mem).threads[0]? = some u → u = v :=
    fun h => by
      simp only [Config.withThread, hth] at h
      exact (Option.some.inj h).symm
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take enters neither phase (`AbortPathSC.take`, `takeC`)
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨-, rfl⟩ := step_takeA hN hT ht1 hI ha hpc hs
    refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · by_cases hab0 : Ab th.st
      · exact List.mem_append_left _ (hti.1 th ht1 hab0)
      obtain rfl := hget hu
      exact absurd hab (hA.take _ _ _ _ _ hI hab0 a ha hpc _)
    · by_cases hac0 : Ac th.st
      · exact List.mem_append_left _ (hti.2 th ht1 hac0)
      obtain rfl := hget hu
      exact absurd hac (hA.takeC _ _ _ _ _ hI hac0 a ha hpc _)
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  have hsite := no_siteA hN ht1 hI hnt
  by_cases hcl : Cl th.st
  · -- at a `clone`: its refusal, with `cloneErr`
    obtain ⟨hsys', st, tl, hdc⟩ := hC.svc _ _ _ _ _ hI hcl
    have h1 : t.2.slots.size = 1 := by rw [hk]; rfl
    have hr0 : t.2.runs 0 = true := by rw [hk]; rfl
    obtain ⟨rfl, r, hr, rfl⟩ := Spike.Lib.CloneOne.clone_step_nodormant (Spike.Lib.CloneOne.nodormant_one h1 hr0)
      ht1 hsys' hdc hsite hs
    refine ⟨fun u hu hab => ?_, fun _ _ _ => List.mem_append_right _ (List.mem_singleton_self _)⟩
    by_cases hab0 : Ab th.st
    · exact List.mem_append_left _ (hti.1 th ht1 hab0)
    obtain rfl := hget hu
    obtain ⟨fd, buf, n, he, -⟩ := hA.sys _ _ _ _ _ hI hab0 hsys' _ hdc _ (ret_mem_certSuccs_clone hr)
      (by rw [← Kernel.retThread_st (K := abi)]; exact hab)
    cases he
  rcases A64Ext.step_cases_site ht1 hw hinv hs (no_spawnAC hN hT ht1 hI hcl) hsite with
    ⟨rfl, hns, outs, o, hso, ho, rfl, -, -⟩ | ⟨rfl, w, rfl, -, -, -⟩ | ⟨pk, hsys, -, -⟩
  · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · by_cases hab0 : Ab th.st
      · exact List.mem_append_left _ (hti.1 th ht1 hab0)
      obtain rfl := hget hu
      exact absurd hab (stepOne_allInv Arch.armv8 hso ho (hA.instr _ _ _ _ _ hI hab0 hns)
        ⟨fun _ => trivial, fun _ _ => trivial⟩).1
    · by_cases hac0 : Ac th.st
      · exact List.mem_append_left _ (hti.2 th ht1 hac0)
      obtain rfl := hget hu
      exact absurd hac (stepOne_allInv Arch.armv8 hso ho (hA.instrC _ _ _ _ _ hI hac0 hns)
        ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · obtain rfl := hget hu
      exact List.mem_append_left _ (hti.1 _ ht1 hab)
    · obtain rfl := hget hu
      exact List.mem_append_left _ (hti.2 _ ht1 hac)
  · obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys (wr_le hk hwr)
    rcases hcases with ⟨fd, buf, n, rd', b, u', rfl, rfl, -, -, hust, -, rfl⟩ |
      ⟨r, rfl, -, -, -, -, u', hu', hsu, -⟩ | ⟨-, -, -, rfl⟩ | ⟨v, rfl, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · obtain rfl := hget hu
        exact List.mem_append_left _ (hti.1 _ ht1 (hust ▸ hab))
      · obtain rfl := hget hu
        exact List.mem_append_left _ (hti.2 _ ht1 (hust ▸ hac))
    · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · by_cases hab0 : Ab th.st
        · exact List.mem_append_left _ (hti.1 th ht1 hab0)
        refine List.mem_append_right _ ?_
        have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
        obtain ⟨fd, buf, n, rfl, hrf⟩ := hA.sys _ _ _ _ _ hI hab0 (atSys_of_ready hr) _ hcall _ hsu' hab
        obtain ⟨hc', hes⟩ := sysStep_write_ret ht1 hcall (wr_le hk hwr _ _ _ hcall) hsys
        have hu2 : u = Kernel.retThread abi th r := by rw [hc'] at hu; exact hget hu
        rw [hes (hrf r (by rw [hu2, Kernel.retThread_st]))]
        exact List.mem_singleton_self _
      · by_cases hac0 : Ac th.st
        · exact List.mem_append_left _ (hti.2 th ht1 hac0)
        have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
        exact absurd hac (hA.sysC _ _ _ _ _ hI hac0 (atSys_of_ready hr) hcl _ hcall _ hsu')
    all_goals
      refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
        exact List.mem_append_left _ (hti.1 _ ht1 hab)
      · obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
        exact List.mem_append_left _ (hti.2 _ ht1 hac)

/-- **`TI` is kept by every step from thread 0 at a state of the fragment**
(`ti_step` with the frames): the thread's facts `ti_stepA` takes from
`PreSA`, at any pair `(c, fs)` of the fragment at its state.
`ti_step_ofAC` with no state marked. -/
theorem ti_step_ofA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {t t' : T.M.Cfg} {tid : Nat} {es pre : List Ev} {th : Thread isaLSE2} {j : Nat} {E : Entry}
    {hl : List (Nat × Range)} {pm : _root_.Mem 64} {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {sm : WeakMem.Memory} {c : Ctl} {fs : List TermRun.Frame}
    (hth : t.1.threads = #[th]) (hk : t.2 = KS E Λ j hl pm) (hwr : WrOk th j) (hI : I lbl lsize th.st c fs)
    (hw : WideSt th.st) (hinv : Inv1 Λ lbl lsize ts th t.1.mem sm)
    (hs : T.M.Step μ tid t es t') (hti : TI Ab pre t) : TI Ab (pre ++ es) t' :=
  (ti_step_ofAC hN ClonePathS.none hA.toC hT hth hk hwr hI hw hinv hs ⟨hti, fun _ _ h => h.elim⟩).1

/-- **`TIC` is kept by every step from `RS`** (`ti_step_ofAC`). -/
theorem ti_stepAC {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hs : T.M.Step μ tid t es t') (hti : TIC Ab Ac pre t) : TIC Ab Ac (pre ++ es) t' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, hs0, hσ, hp, hI, -, hw, hb, hinv,
    hown, hmi, -⟩ := h
  exact ti_step_ofAC hN hC hA hT hth hk hwr hI hw hinv hs hti

/-- **`TI` is kept by every step from `RS`** (`ti_step` with the frames,
`ti_step_ofA`). -/
theorem ti_stepA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hs : T.M.Step μ tid t es t') (hti : TI Ab pre t) : TI Ab (pre ++ es) t' :=
  (ti_stepAC hN ClonePathS.none hA.toC hT h hs ⟨hti, fun _ _ h => h.elim⟩).1

/-- **`TIC` along every run from `RS`.** -/
theorem ti_runAC {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev},
      RSA Λ P p G own I rS Tk μ ar t s → T.M.Step μ tid t es t' → ∃ s', RSA Λ P p G own I rS Tk μ ar t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, RSA Λ P p G own I rS Tk μ ar t s → TIC Ab Ac pre t → TIC Ab Ac (pre ++ tr) t' := by
  induction hr with
  | refl => intro s pre _ h; rwa [List.append_nil]
  | step hs _ ih =>
    intro s pre hR h
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s', hR'⟩ := hstep hR hs
    rw [← List.append_assoc]
    exact ih hR' (ti_stepAC hN hC hA hT hR hs h)

/-- **`TI` along every run from `RS`.** -/
theorem ti_runA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    {Ab : State → Prop} (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev},
      RSA Λ P p G own I rS Tk μ ar t s → T.M.Step μ tid t es t' → ∃ s', RSA Λ P p G own I rS Tk μ ar t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, RSA Λ P p G own I rS Tk μ ar t s → TI Ab pre t → TI Ab (pre ++ tr) t' :=
  fun hR h => (ti_runAC hN ClonePathS.none hA.toC hT hstep hr hR ⟨h, fun _ _ h => h.elim⟩).1

/-- **An abort from `RS` is justified**, with the `clone` phase
(`r_abortA`; a `threads` abort in the phase `Ac` by `TIC`, after a refused
`clone`: `AbortJustified.of_cloneErr`). -/
theorem r_abortAC {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hwf : Λ.WF) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {B : Budget} (hB : B.cells = ar.cells) {rS : Range} {Tk : State → Prop} {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hti : TIC Ab Ac tr t) (hs : T.M.Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    ∃ w i, Components T.M Λ w t ((SrcSem.source P p).core s) ∧ w.thr i = some tid ∧
      AbortJustified B (SrcSem.source P p) tr s i k := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hx⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hx]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk'⟩, -, hh, -, -, hs0, hσ, hp, hI, -, -, -, hinv,
    hown, hmi, -, -, -, hai, hfr, -, tr', hre⟩ := h
  obtain ⟨a, ha, t2, ht2, hpc⟩ := hs.abort_at hk
  obtain ⟨rfl, rfl⟩ := get_one hth ht2
  obtain ⟨w, hw, hw0⟩ := components_oneSX hwf hth (by rw [hk']; rfl) hh hmi hs0
    (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown
  refine ⟨w, 0, hw, hw0, ?_⟩
  have hi : s.ths[0]? = some th0 := by rw [hs0]; rfl
  obtain ⟨⟨rfl, hab⟩ | ⟨rfl, hc, he⟩ | ⟨rfl, hheap⟩ | ⟨rfl, hac⟩, -⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
  · exact hti.1 th ht2 hab
  · exact abortJustified_overflow_sourceS hi hc hσ hp (noBigNumT_of_envSmallS hi he)
  · have hr := hheap.at_heapCtr hai.heapCtrA
    exact abortJustified_heap_sourceA hi (by rw [hB]; exact hr) hσ hp
      (Spike.Lib.fresh_of_placed (fun m hmem => (hinv.mem.lbl_mem m hmem).imp fun _ h => h.1) hfr.fresh)
      (hsafe.box _ _ hre)
  · exact AbortJustified.of_cloneErr (hti.2 th ht2 hac)

/-- **An abort from `RS` is justified** (`r_abort` with the frames): the
`writeErr` one by `TI`; the `overflow` one at any depth with every frame's
environment small (`abortJustified_overflow_sourceS`); the `heap` one with
the heap use within the budget's `cells` (`AllocInvAt.heapCtr`, `hB`) and the next
label fresh (`FreshInv`) and the boxes counted (`SrcSafeS.box`,
`abortJustified_heap_source`). `r_abortAC` with no `threads` phase. -/
theorem r_abortA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) (hsafe : SrcSafeS P p I)
    (hwf : Λ.WF) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {B : Budget} (hB : B.cells = ar.cells) {rS : Range} {Tk : State → Prop} {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hti : TI Ab tr t) (hs : T.M.Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    ∃ w i, Components T.M Λ w t ((SrcSem.source P p).core s) ∧ w.thr i = some tid ∧
      AbortJustified B (SrcSem.source P p) tr s i k :=
  r_abortAC hN hsafe hwf hA.toC hB h ⟨hti, fun _ _ h => h.elim⟩ hs hk

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program at any call depth on a target on
the canonical AArch64 machine** (`correctKOn` with the frames: `stepSimA`,
`r_progressA`, `r_memInA`, `r_abortA` with `ti_runA` from `ti_load`,
`r_componentsA`); the budget's heap `cells` are the arena's (`hB`). -/
theorem correctKOnA {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p)
    (hinit : P.init (s0 P.cap))
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
  have hsim := stepSimA hl himg hss hw hst hfr0 hP hinit hN hsafe hT htk0 hown0 hrd hwf hG0 hGpl hok hstat hsub hal
    hz0 hc0
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
    exact r_abortA hN hsafe hwf hA hB hR hti hs hk

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program at any call depth on the canonical
AArch64 target**: `correctKOnA` at `T`, the load by `load_of_parsed`. -/
theorem correctKA {B : Budget} (hB : B.cells = ar.cells) {asm : String} {prog : Program} {secs : DataSecs}
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
  correctKOnA (A := String) (ld := T.load) (rs := T.resolve) hB (load_of_parsed (kernel 1) Entry.linux Λ hpa hd)
    himg hss hw hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 hsvc hrd hwf hG0 hGpl hA hab0 hok hstat hsub hal hz0
    hc0

/-- info: 'Spike.Lib.A64ConsumerA.r_abortAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms r_abortAC

/-- info: 'Spike.Lib.A64ConsumerA.ti_runAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ti_runAC

/-- info: 'Spike.Lib.A64ConsumerA.r_progressAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms r_progressAC

/-- info: 'Spike.Lib.A64ConsumerA.pre_stepAXC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre_stepAXC

/-- info: 'Spike.Lib.A64ConsumerA.promSharedAXC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms promSharedAXC

/-! ## Over a held predicate (`HeldPathS`) -/

open Scc.Cert.Link in
/-- **The start is related at any source start, over a held predicate**
(`pre_loadA` with the source start `s₀` a parameter, one thread `th₀` at
the start pair `⟨th₀.term, th₀.env, none⟩` and its frames, empty memory,
heap use 0 (`hhu`), its allocation count `th₀.nalloc` fresh from the static
placement (`hfr0`); and `H` holding at the loaded state with no range held,
`hH0`, in place of `HeldOk`'s phase). -/
theorem pre_loadAH {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS} {I : InvS} {μ : Marks}
    {H : State → List (Nat × Range) → Prop}
    {prog : Program} {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize} {secs : DataSecs}
    {code : String → Option Nat} {name : WeakMem.AllocLabel → String} {s₀ : TermRun.Cfg} {th₀ : TermRun.TTh}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hinit : P.init s₀) (hs0 : s₀.ths = #[th₀]) (hσ : th₀.σs = []) (hp : th₀.promises = [])
    (hsm : s₀.mem = #[]) (hhu : heapUse s₀ = 0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog syms) ⟨th₀.term, th₀.env, none⟩ th₀.stack)
    (hfr0 : AllocInv.FreshInv Λ.static s₀.lbase s₀.n 0 th₀.nalloc)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64)
    (hH0 : H (threadAt E Λ.code.lo prog syms) [])
    (hown0 : OwnInit (own (threadAt E Λ.code.lo prog syms) th₀.stack)
      (loadProg (kernel 1) E Λ prog syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ prog syms mem).1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc a) = 0)
    (hc0 : (loadProg (kernel 1) E Λ prog syms mem).1.mem.initVal (wordLoc ar.ctr) = 0) :
    PreSAH Λ P p G own I H μ ar (loadProg (kernel 1) E Λ prog syms mem) s₀ := by
  have hinv : Inv1 Λ Λ.static lsize (fun _ => none) (Thread.init (threadAt E Λ.code.lo prog syms) : Thread isaLSE2)
      (loadProg (kernel 1) E Λ prog syms mem).1.mem s₀.mem := by
    rw [hsm]; exact Inv1.start_static himg hss rfl rfl
  refine ⟨Thread.init (threadAt E Λ.code.lo prog syms), th₀, 0, Λ.static, lsize, fun _ => none, [], ∅, none,
    rfl, ?_, fun _ => by simp [Kernel.byte],
    hH0, .inl rfl, certOkC_of_prom_nil rfl, hs0, hσ, hp, hst, .inl trivial,
    wideSt_threadAt hw _ _ _,
    bnd_init _ _,
    hinv, ?_, ⟨?_, hmem⟩, ⟨fits_empty rfl, hmf⟩, hg,
    ownOk_init (by simp [loadProg, Config.init]) hown0 _, ?_, hfr0, ?_,
    [], s₀, hinit, .refl _⟩
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
    rw [hhu]
    exact .inr ⟨(fun w h => by cases h), by simpa using hct, har⟩
  · intro l b hb
    simp [hstat] at hb

/-- **The site's range is fresh** at the take (`fresh_of` with the held
ranges `hl`, each off the range, `HeldPathS.held`). -/
theorem fresh_ofH (hwf : Λ.WF) {r : Range} {t : T.M.Cfg} {j : Nat} {hl : List (Nat × Range)}
    {pm : _root_.Mem 64} (hk : t.2 = KS E Λ j hl pm) (hsub : r.Sub Λ.stackPool) (hpos : 0 < r.size)
    (hrod : Λ.rodata.Disjoint Λ.stackPool) (hdj : ∀ h ∈ hl, r.Disjoint h.2) (hmi : MemIn Λ t.1.mem) :
    Kernel.fresh t r = true := by
  have hall : hl.all (fun h => !Kernel.overlaps r h.2.lo h.2.size) = true := by
    rw [List.all_eq_true]
    intro x hx
    rcases hdj x hx with h | h <;> simp [Kernel.overlaps] <;> omega
  have h0 := fresh_of (E := E) (t := (t.1, KS E Λ j [] pm)) hwf rfl hsub hpos hrod hmi
  unfold Kernel.fresh at h0 ⊢
  rw [hk]
  have e : (KS E Λ j hl pm).held = hl := rfl
  have e0 : (KS E Λ j [] pm).held = [] := rfl
  have ep : (KS E Λ j hl pm).pool = (KS E Λ j [] pm).pool := rfl
  rw [e, ep, hall]
  rw [e0] at h0
  simpa using h0

/-- **No promise at a `write`** at any depth (`WriteNoPromS` over `PreSA`). Over `HeldPathS`. -/
def WriteNoPromAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s th, PreSAH Λ P p G own I H μ ar t s → t.1.threads = #[th] → abi.atSys th.st = true →
    (∃ fd buf n, Kernel.callOf abi th = some (.write fd buf n)) → th.prom = []

/-- **`RS` is explicit** (`r_components` with the frames). Over `HeldPathS`. -/
theorem r_componentsAH {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    (hwf : Λ.WF) {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) {t : T.M.Cfg}
    {s : TermRun.Cfg} (h : RSAH Λ P p G own I H μ ar t s) :
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s) := by
  rcases h with ⟨th, th0, j, lbl, lsize, ts, hl, pm, _, hth, ⟨E, hk⟩, -, hh, -, -, hs0, -, -, hI, -, -, -, hinv,
      hown, hmi, -⟩ |
    ⟨th, th0, j, lbl, lsize, ts, hl, pm, o, hth, ⟨E, hk⟩, -, hh, hs0, -, -, hpl, hinv, hown, hmi, -⟩
  · exact (components_oneSXH hwf hth (by rw [hk]; rfl) (hT.own _ _ hh) hmi hs0
      (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown).imp fun _ h => h.1
  · exact (components_oneSXH hwf hth (by rw [hk]; rfl) (hT.own _ _ hh) hmi hs0 hpl hinv hown).imp fun _ h => h.1

/-- **Before the exit there is progress** at any depth, for rows under any
`NodesA … ab Cl` with thread 0 off `Cl` (`hnc`; at a `Cl` state, a `clone`,
the one-slot configuration faults: `Spike.Lib.WakePre.Pre1.progressClone_of`
there). `pre_progressA`'s argument. Over `HeldPathS`. -/
theorem pre_progressACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) (hwf : Λ.WF)
    (hsvc : WriteNoPromAH Λ P p G own I H μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreSAH Λ P p G own I H μ ar t s)
    (hnc : ∀ th, t.1.threads = #[th] → ¬ Cl th.st) : T.M.Progress μ t := by
  have hwnp := hsvc t s
  have hpre := h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, hh, hwr, hcert, hs0, hσ, hp, hI, -, hw, hb,
    hinv, hown, hmi, -, -, -, -, -, -, hre⟩ := h
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hrk : t.2.runs 0 = true := by rw [hk]; rfl
  have hxk : t.2.exited = none := by rw [hk]; rfl
  have hruns : T.M.runs t 0 := ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs 0 = false); rw [hrk]; simp⟩
  have hnh : th.halted = false := by
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).1
      simp [Thread.halted, Kraken.Promising.Lower.A64.exec_nop hcn]
    cases hs : abi.atSys th.st
    · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowNS hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) hs
      have := Out.exec_isSome rfl hs hout
      simp only [Thread.halted]
      cases he : isaLSE2.exec th.st
      · rw [he] at this; cases this
      · simp
    · obtain ⟨imm, sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
      simp [Thread.halted, Kraken.Promising.Lower.A64.exec_svc hc]
  refine ⟨?_, .inr ⟨⟨0, hxk, hruns.2.2, th, ht, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.armv8 th 0 t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      cases hsy : abi.atSys th.st
      · by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
        · obtain ⟨a, ha, hpc⟩ := htk
          obtain ⟨sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).1
          exact Kraken.Promising.Lower.stepOne_silent_no_error Arch.armv8 0 (Kraken.Promising.Lower.A64.exec_nop hcn)
            (Kraken.Promising.Lower.silentTree_done _) hs' m hm
        · obtain ⟨c₁, fs₁, -, -, hout⟩ :=
            hN.rowNS hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) hsy
          exact outA_no_error hsy hout hs' m hm
      · exact hns ⟨th, ht1, hsy⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [hnh, Bool.or_false] at hf
        cases hsy : abi.atSys th.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXCT hT.toTakeSiteS hI hsy (hnc th hth)
          rw [show Kernel.callOf abi th = some call from hd] at hf
          cases call with
          | clone st tl => exact hcl st tl rfl
          | _ => simp at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      rw [hk] at htouch
      exact hN.mapped _ _ _ _ _ hI hns e hex (touches_mono (fun _ _ h => mapped_KS h) htouch)
  · obtain ⟨-, -, t1, ht1, -⟩ := hl
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
    · -- at the take site: the take
      obtain ⟨a, ha, hpc⟩ := htk
      obtain ⟨⟨sz, hcn⟩, -, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
      obtain ⟨hsub, hpos, hrod, hdj, -⟩ := hT.held _ _ _ _ _ _ hI hh a ha hpc
      have hf : Kernel.fresh t (Kernel.siteRange abi th.st) = true := fresh_ofH hwf hk hsub hpos hrod hdj hmi
      exact ⟨[], _, .xfer .take hruns ⟨a, ha, th, ht, hpc⟩
        (Kernel.xfer_take (K := abi) Arch.armv8 1 ht hrk hxk (atNop_of_cellAt hcn) hf)⟩
    have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
    have hsite := no_siteA hN ht hI hnt
    cases hs : abi.atSys th.st
    · have hnsys : ¬ T.M.atSys t 0 := fun ⟨t2, ht2, h2⟩ => by
        cases (show some t2 = some th from ht2.symm.trans ht)
        have h3 : abi.atSys th.st = true := h2
        rw [hs] at h3; cases h3
      by_cases hpn : th.prom = []
      · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowNS hI hnt hs
        obtain ⟨outs, o, hso, ho, hpo⟩ :=
          outA_progress (tid := 0) (mem := t.1.mem) hpn hb hs hout
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
      · obtain ⟨t', mem', hr, hp'⟩ := hcert
        cases hr with
        | refl => exact absurd hp' hpn
        | step hs1 hrest =>
          obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
          replace hso : stepOne Arch.armv8 th 0 t.1.mem = some outs :=
            (Kernel.certSem_step_of_not_site (x := t.2) (siteAt_noneA hN hI hnt) hs).symm.trans hso
          exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
    · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
      obtain ⟨call, hd, hnx, hcl⟩ := hN.sysOkXCT hT.toTakeSiteS hI hs (hnc th hth)
      have hc : Kernel.callOf abi th = some call := hd
      have hsys : ∀ c', (kernel 1).sys μ 0 t [] c' → ∃ es c', T.M.Step μ 0 t es c' :=
        fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
      by_cases hpn : th.prom = []
      rotate_left
      · -- with promises: no `write` (`WriteNoPromA`), none at `exit_group`; elsewhere `Kernel.sys_progress`
        have hsn := siteAt_noneA hN hI hnt
        cases call with
        | write fd buf n => exact absurd (hwnp th hpre hth hs ⟨fd, buf, n, hc⟩) hpn
        | exitGroup v => exact absurd (Kernel.prom_nil_of_exit hsn hs hd (.inr ⟨v, rfl⟩) hcert) hpn
        | exit => exact absurd rfl hnx
        | clone st tl => exact absurd rfl (hcl st tl)
        | _ =>
          obtain ⟨r, es, c', h, hca⟩ := Kernel.sys_progress ht hr hsn hc (fun _ _ _ h => by cases h)
            (fun _ _ h => by cases h) hpn hcert
          obtain rfl := Kernel.sysStep_ret_nil ht hc (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
            (fun h => by cases h) (fun _ h => by cases h) h
          exact hsys c' ⟨.ret r, h, hca⟩
      cases call with
      | write fd buf n =>
        by_cases hj : t.2.wr 0 = 0
        · exact hsys _ (Kernel.sys_writeIntr (K := abi) Arch.armv8 1 ht hr hpn hc hj)
        · exact hsys _ (Kernel.sys_writeRet (K := abi) Arch.armv8 1 ht hr hpn hc (Nat.pos_of_ne_zero hj))
      | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.armv8 1 ht hr hpn hc)
      | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.armv8 1 ht hr hpn hc)
      | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.armv8 1 ht hr hpn hc)
      | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.armv8 1 ht hr hpn hc)
      | exitGroup v =>
        by_cases hab : ∃ k a, μ.abortAt k = some a ∧ pcOf th.st = a
        · -- at an abort site: the abort
          obtain ⟨k, a, ha, hpc⟩ := hab
          obtain ⟨-, hv⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroupAbort (K := abi) Arch.armv8 1 k ht hr hpn hc (hv v hd))
            (by simp) (fun k' hk => by obtain rfl : k' = k := by simpa using hk
                                       exact ⟨a, ha, th, ht, hpc⟩) (fun e he => by simp at he)⟩
        · have hnoab : ∀ k a, μ.abortAt k = some a → ¬ T.M.AtAddr a t 0 := fun k a ha ⟨t2, ht2, hpc⟩ => by
            cases (show some t2 = some th from ht2.symm.trans ht); exact hab ⟨k, a, ha, hpc⟩
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.armv8 1 ht hr hpn hc) (by simp)
            (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
      | exit => exact absurd rfl hnx
      | clone st tl => exact absurd rfl (hcl st tl)

/-- **There is progress from `RS`**, thread 0 off `Cl` (`pre_progressAC`). Over `HeldPathS`. -/
theorem r_progressACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) (hwf : Λ.WF)
    (hsvc : WriteNoPromAH Λ P p G own I H μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSAH Λ P p G own I H μ ar t s)
    (hnc : ∀ th, t.1.threads = #[th] → ¬ Cl th.st) : T.M.Progress μ t :=
  h.elim (fun h => pre_progressACH hN hA hT hwf hsvc h hnc) post_progressSAH

/-- The memory of a configuration `RS` relates is in the layout. Over `HeldPathS`. -/
theorem r_memInAH {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : RSAH Λ P p G own I H μ ar t s) : MemIn Λ t.1.mem := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ <;> exact hmi

/-- **`TIC` is kept by every step from thread 0 at a state of the fragment**
(`ti_step_ofA` with the `clone` phase): at a `Cl` state the step is a
refused `clone` (one slot, none dormant), which emits `cloneErr`; elsewhere
`Ac` is not entered (`AbortPathSC.instrC`, `sysC`, `takeC`). Over `HeldPathS`. -/
theorem ti_step_ofACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop}
    (hT : HeldPathS Λ p μ I H)
    {t t' : T.M.Cfg} {tid : Nat} {es pre : List Ev} {th : Thread isaLSE2} {j : Nat} {E : Entry}
    {hl : List (Nat × Range)} {pm : _root_.Mem 64} {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {sm : WeakMem.Memory} {c : Ctl} {fs : List TermRun.Frame}
    (hth : t.1.threads = #[th]) (hk : t.2 = KS E Λ j hl pm) (hwr : WrOk th j) (hI : I lbl lsize th.st c fs)
    (hw : WideSt th.st) (hinv : Inv1 Λ lbl lsize ts th t.1.mem sm)
    (hs : T.M.Step μ tid t es t') (hti : TIC Ab Ac pre t) : TIC Ab Ac (pre ++ es) t' := by
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have hget : ∀ {v : Thread isaLSE2} {mem : Memory} {u : Thread isaLSE2},
      (t.1.withThread 0 v mem).threads[0]? = some u → u = v :=
    fun h => by
      simp only [Config.withThread, hth] at h
      exact (Option.some.inj h).symm
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take enters neither phase (`AbortPathSC.take`, `takeC`)
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨-, rfl⟩ := step_takeAT hN hT.toTakeSiteS ht1 hI ha hpc hs
    refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · by_cases hab0 : Ab th.st
      · exact List.mem_append_left _ (hti.1 th ht1 hab0)
      obtain rfl := hget hu
      exact absurd hab (hA.take _ _ _ _ _ hI hab0 a ha hpc _)
    · by_cases hac0 : Ac th.st
      · exact List.mem_append_left _ (hti.2 th ht1 hac0)
      obtain rfl := hget hu
      exact absurd hac (hA.takeC _ _ _ _ _ hI hac0 a ha hpc _)
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  have hsite := no_siteA hN ht1 hI hnt
  by_cases hcl : Cl th.st
  · -- at a `clone`: its refusal, with `cloneErr`
    obtain ⟨hsys', st, tl, hdc⟩ := hC.svc _ _ _ _ _ hI hcl
    have h1 : t.2.slots.size = 1 := by rw [hk]; rfl
    have hr0 : t.2.runs 0 = true := by rw [hk]; rfl
    obtain ⟨rfl, r, hr, rfl⟩ := Spike.Lib.CloneOne.clone_step_nodormant (Spike.Lib.CloneOne.nodormant_one h1 hr0)
      ht1 hsys' hdc hsite hs
    refine ⟨fun u hu hab => ?_, fun _ _ _ => List.mem_append_right _ (List.mem_singleton_self _)⟩
    by_cases hab0 : Ab th.st
    · exact List.mem_append_left _ (hti.1 th ht1 hab0)
    obtain rfl := hget hu
    obtain ⟨fd, buf, n, he, -⟩ := hA.sys _ _ _ _ _ hI hab0 hsys' _ hdc _ (ret_mem_certSuccs_clone hr)
      (by rw [← Kernel.retThread_st (K := abi)]; exact hab)
    cases he
  rcases A64Ext.step_cases_site ht1 hw hinv hs (no_spawnACT hN hT.toTakeSiteS ht1 hI hcl) hsite with
    ⟨rfl, hns, outs, o, hso, ho, rfl, -, -⟩ | ⟨rfl, w, rfl, -, -, -⟩ | ⟨pk, hsys, -, -⟩
  · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · by_cases hab0 : Ab th.st
      · exact List.mem_append_left _ (hti.1 th ht1 hab0)
      obtain rfl := hget hu
      exact absurd hab (stepOne_allInv Arch.armv8 hso ho (hA.instr _ _ _ _ _ hI hab0 hns)
        ⟨fun _ => trivial, fun _ _ => trivial⟩).1
    · by_cases hac0 : Ac th.st
      · exact List.mem_append_left _ (hti.2 th ht1 hac0)
      obtain rfl := hget hu
      exact absurd hac (stepOne_allInv Arch.armv8 hso ho (hA.instrC _ _ _ _ _ hI hac0 hns)
        ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
    · obtain rfl := hget hu
      exact List.mem_append_left _ (hti.1 _ ht1 hab)
    · obtain rfl := hget hu
      exact List.mem_append_left _ (hti.2 _ ht1 hac)
  · obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys (wr_le hk hwr)
    rcases hcases with ⟨fd, buf, n, rd', b, u', rfl, rfl, -, -, hust, -, rfl⟩ |
      ⟨r, rfl, -, -, -, -, u', hu', hsu, -⟩ | ⟨-, -, -, rfl⟩ | ⟨v, rfl, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · obtain rfl := hget hu
        exact List.mem_append_left _ (hti.1 _ ht1 (hust ▸ hab))
      · obtain rfl := hget hu
        exact List.mem_append_left _ (hti.2 _ ht1 (hust ▸ hac))
    · refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · by_cases hab0 : Ab th.st
        · exact List.mem_append_left _ (hti.1 th ht1 hab0)
        refine List.mem_append_right _ ?_
        have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
        obtain ⟨fd, buf, n, rfl, hrf⟩ := hA.sys _ _ _ _ _ hI hab0 (atSys_of_ready hr) _ hcall _ hsu' hab
        obtain ⟨hc', hes⟩ := sysStep_write_ret ht1 hcall (wr_le hk hwr _ _ _ hcall) hsys
        have hu2 : u = Kernel.retThread abi th r := by rw [hc'] at hu; exact hget hu
        rw [hes (hrf r (by rw [hu2, Kernel.retThread_st]))]
        exact List.mem_singleton_self _
      · by_cases hac0 : Ac th.st
        · exact List.mem_append_left _ (hti.2 th ht1 hac0)
        have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
        exact absurd hac (hA.sysC _ _ _ _ _ hI hac0 (atSys_of_ready hr) hcl _ hcall _ hsu')
    all_goals
      refine ⟨fun u hu hab => ?_, fun u hu hac => ?_⟩
      · obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
        exact List.mem_append_left _ (hti.1 _ ht1 hab)
      · obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
        exact List.mem_append_left _ (hti.2 _ ht1 hac)

/-- **`TIC` is kept by every step from `RS`** (`ti_step_ofAC`). Over `HeldPathS`. -/
theorem ti_stepACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev} (h : RSAH Λ P p G own I H μ ar t s)
    (hs : T.M.Step μ tid t es t') (hti : TIC Ab Ac pre t) : TIC Ab Ac (pre ++ es) t' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, hs0, hσ, hp, hI, -, hw, hb, hinv,
    hown, hmi, -⟩ := h
  exact ti_step_ofACH hN hC hA hT hth hk hwr hI hw hinv hs hti

/-- **`TIC` along every run from `RS`.** Over `HeldPathS`. -/
theorem ti_runACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hC : ClonePathS p I Cl) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev},
      RSAH Λ P p G own I H μ ar t s → T.M.Step μ tid t es t' → ∃ s', RSAH Λ P p G own I H μ ar t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, RSAH Λ P p G own I H μ ar t s → TIC Ab Ac pre t → TIC Ab Ac (pre ++ tr) t' := by
  induction hr with
  | refl => intro s pre _ h; rwa [List.append_nil]
  | step hs _ ih =>
    intro s pre hR h
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s', hR'⟩ := hstep hR hs
    rw [← List.append_assoc]
    exact ih hR' (ti_stepACH hN hC hA hT hR hs h)

/-- **An abort from `RS` is justified**, with the `clone` phase
(`r_abortA`; a `threads` abort in the phase `Ac` by `TIC`, after a refused
`clone`: `AbortJustified.of_cloneErr`). Over `HeldPathS`. -/
theorem r_abortACH {ab : Option (State → Prop)} {Cl : State → Prop} (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hwf : Λ.WF) {Ab Ac : State → Prop} (hA : AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr)
    {B : Budget} (hB : B.cells = ar.cells) {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind} (h : RSAH Λ P p G own I H μ ar t s)
    (hti : TIC Ab Ac tr t) (hs : T.M.Step μ tid t es t') (hk : Ev.abort k ∈ es) :
    ∃ w i, Components T.M Λ w t ((SrcSem.source P p).core s) ∧ w.thr i = some tid ∧
      AbortJustified B (SrcSem.source P p) tr s i k := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hx⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hx]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk'⟩, -, hh, -, -, hs0, hσ, hp, hI, -, -, -, hinv,
    hown, hmi, -, -, -, hai, hfr, -, tr', hre⟩ := h
  obtain ⟨a, ha, t2, ht2, hpc⟩ := hs.abort_at hk
  obtain ⟨rfl, rfl⟩ := get_one hth ht2
  obtain ⟨w, hw, hw0⟩ := components_oneSXH hwf hth (by rw [hk']; rfl) (hT.own _ _ hh) hmi hs0
    (by have hpl := hN.place _ _ _ _ _ hI; exact hpl) hinv hown
  refine ⟨w, 0, hw, hw0, ?_⟩
  have hi : s.ths[0]? = some th0 := by rw [hs0]; rfl
  obtain ⟨⟨rfl, hab⟩ | ⟨rfl, hc, he⟩ | ⟨rfl, hheap⟩ | ⟨rfl, hac⟩, -⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
  · exact hti.1 th ht2 hab
  · exact abortJustified_overflow_sourceS hi hc hσ hp (noBigNumT_of_envSmallS hi he)
  · have hr := hheap.at_heapCtr hai.heapCtrA
    exact abortJustified_heap_sourceA hi (by rw [hB]; exact hr) hσ hp
      (Spike.Lib.fresh_of_placed (fun m hmem => (hinv.mem.lbl_mem m hmem).imp fun _ h => h.1) hfr.fresh)
      (hsafe.box _ _ hre)
  · exact AbortJustified.of_cloneErr (hti.2 th ht2 hac)

/-- info: 'Spike.Lib.A64ConsumerA.r_abortACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms r_abortACH

/-- info: 'Spike.Lib.A64ConsumerA.ti_runACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ti_runACH

/-- info: 'Spike.Lib.A64ConsumerA.r_progressACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms r_progressACH

/-- info: 'Spike.Lib.A64ConsumerA.pre_stepAXCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre_stepAXCH

/-- info: 'Spike.Lib.A64ConsumerA.promSharedAXCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms promSharedAXCH

/-- info: 'Spike.Lib.A64ConsumerA.r_componentsAH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms r_componentsAH

/-- info: 'Spike.Lib.A64ConsumerA.ti_stepACH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ti_stepACH

/-- info: 'Spike.Lib.A64ConsumerS.TakePathS.toH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TakePathS.toH

end Spike.Lib.A64ConsumerA
