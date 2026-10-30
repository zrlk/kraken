/-
**Correctness of the allocation-capable consumer**
(`Spike/Lib/X64ConsumerA.lean`): `X64ConsumerS`'s load, step-wise
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
import Spike.Lib.X64ConsumerACore

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

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
    {tcells : List (Directive × Nat)} {syms : List (String × Nat)} {mem : List (Loc × Val)} {lsize : Lsize}
    {secs : DataSecs}
    {code : String → Option Nat} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name)
    (hw : wideIn (tcells.map (·.1)) = true)
    (hinit : P.init (s0 P.cap)) (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells syms) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hmem : ∀ q ∈ mem, InitIn Λ q.1) (hmf : ∀ q ∈ mem, q.2.toNat < 2 ^ 64) {rS : Range} {Tk : State → Prop}
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells syms))
    (hown0 : OwnInit (own (threadAt E Λ.code.lo tcells syms) [])
      (loadProg (kernel 1) E Λ tcells syms mem).1.mem)
    (hg : MemInv G (loadProg (kernel 1) E Λ tcells syms mem).1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      (loadProg (kernel 1) E Λ tcells syms mem).1.mem.initVal (wordLoc a) = 0)
    (hc0 : (loadProg (kernel 1) E Λ tcells syms mem).1.mem.initVal (wordLoc ar.ctr) = 0) :
    PreSA Λ P p G own I rS Tk μ ar (loadProg (kernel 1) E Λ tcells syms mem) (s0 P.cap) := by
  refine ⟨Thread.init (threadAt E Λ.code.lo tcells syms), _, 0, Λ.static, lsize, fun _ => none, [], ∅, none,
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
  · have hnm : ∀ k', (loadProg (kernel 1) E Λ tcells syms mem).1.mem.get? k' = none := fun k' => by
      cases hk : (loadProg (kernel 1) E Λ tcells syms mem).1.mem.get? k' with
      | none => rfl
      | some m =>
        unfold Memory.get? at hk; split at hk
        · cases hk
        · simp [loadProg, Config.init] at hk
    have har : AllocRow.ArenaOK Λ Λ.static lsize (Thread.init (threadAt E Λ.code.lo tcells syms) : Thread isa)
        (loadProg (kernel 1) E Λ tcells syms mem).1.mem ar.heap ar.cells 0 (fun _ => False) := by
      rw [hstat]; exact AllocRow.ArenaOK.init hsub hal hz0 hnm
    have hct := AllocInv.CtrAt.init (prom := (Thread.init (threadAt E Λ.code.lo tcells syms) : Thread isa).prom)
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
    {tcells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hwf : Λ.WF)
    (himg : imageOk Λ secs code = true)
    (hss : StaticSyms Λ secs code lsize name) (hw : wideIn (tcells.map (·.1)) = true) (hinit : P.init (s0 P.cap))
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    {rS : Range} {Tk : State → Prop} (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    {t0 : T.M.Cfg} (hown0 : OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) [])
      t0.1.mem)
    (hg : MemInv G t0.1.mem) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : t0.1.mem.initVal (wordLoc ar.ctr) = 0) (h : loadParsed (kernel 1) E Λ tcells secs offs = some t0) :
    ∃ s, (SrcSem.source P p).init s ∧ RSA Λ P p G own I rS Tk μ ar t0 s := by
  simp only [loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    refine ⟨s0 P.cap, hinit, .inl (pre_loadA himg hss hw hinit hst hfr0 (loadMem_in hwf hc.1.1.1.1.2) ?_ htk0
      hown0 hg hstat hsub hal hz0 hc0)⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

/-! ## The step-wise simulation -/

open Scc.Cert.Link in
/-- **The step-wise simulation** at any depth (`stepSim` with the frames;
`PromSharedS` discharged by `promSharedA`). -/
theorem stepSimA {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {tcells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ tcells secs offs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (tcells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hrd : ∀ w, rd w)
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
  step _ _ _ _ _ h hs :=
    r_stepA hP hN hsafe hT (promSharedA hP hN hsafe (.of_all hrd) hwf hGpl hok hT) (.of_all hrd) hwf hGpl hok h hs

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

/-- **Before the exit there is progress** at any depth (`pre_progress` with
the frames; off a system call by the row after the pair's frame run,
`NodesA.row`). -/
theorem pre_progressA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    {Ab : State → Prop} (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hwf : Λ.WF)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk μ ar)
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreSA Λ P p G own I rS Tk μ ar t s) : T.M.Progress μ t := by
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
      obtain ⟨n, sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).2.1
      simp [Thread.halted, Kraken.Promising.Lower.X64.exec_nop hcn]
    cases hs : abi.atSys th.st
    · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowX hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) (fun h => by rw [hs] at h; cases h)
      have := ExtRows.out_exec hs hout
      simp only [Thread.halted]
      cases he : isa.exec th.st
      · rw [he] at this; cases this
      · simp
    · obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
      simp [Thread.halted, Kraken.Promising.Lower.X64.exec_syscall hc]
  refine ⟨?_, .inr ⟨⟨0, hxk, hruns.2.2, th, ht, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.tso th 0 t.1.mem = some outs := by simp only [stepThread, ht1] at hs; exact hs
      cases hsy : abi.atSys th.st
      · by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
        · obtain ⟨a, ha, hpc⟩ := htk
          obtain ⟨n, sz, hcn⟩ := (hT.site _ _ _ _ _ hI a ha hpc).2.1
          exact Kraken.Promising.Lower.stepOne_silent_no_error Arch.tso 0 (Kraken.Promising.Lower.X64.exec_nop hcn)
            (Kraken.Promising.Lower.silentTree_done _) hs' m hm
        · obtain ⟨c₁, fs₁, -, -, hout⟩ :=
            hN.rowX hI (fun a ha hpc => htk ⟨a, ha, hpc⟩) (fun h => by rw [hsy] at h; cases h)
          exact ExtRows.out_no_error hsy hout hs' m hm
      · exact hns ⟨th, ht1, hsy⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [hnh, Bool.or_false] at hf
        cases hsy : abi.atSys th.st
        · simp [hsy] at hf
        · obtain ⟨call, hd, -, hcl⟩ := hN.sysOkX hT hI hsy
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
      obtain ⟨hntk, ⟨n, sz, hcn⟩, -, hsr, hsub, hpos, hrod, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
      obtain rfl : hl = [] := by
        rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h
        · exact absurd h hntk
      have hf : Kernel.fresh t (Kernel.siteRange abi th.st) = true := by
        rw [hsr]; exact fresh_of hwf hk hsub hpos hrod hmi
      exact ⟨[], _, .xfer .take hruns ⟨a, ha, th, ht, hpc⟩
        (Kernel.xfer_take (K := abi) Arch.tso 1 ht hrk hxk (atNop_of_cellAt hcn) hf)⟩
    have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
    have hsite := no_siteA hN ht hI hnt
    cases hs : abi.atSys th.st
    · have hnsys : ¬ T.M.atSys t 0 := fun ⟨t2, ht2, h2⟩ => by
        cases (show some t2 = some th from ht2.symm.trans ht)
        have h3 : abi.atSys th.st = true := h2
        rw [hs] at h3; cases h3
      by_cases hpn : th.prom = []
      · obtain ⟨c₁, fs₁, -, -, hout⟩ := hN.rowX hI hnt (fun h => by rw [hs] at h; cases h)
        obtain ⟨outs, o, hso, ho, hpo⟩ :=
          ExtRows.out_progress (A := Arch.tso) (tid := 0) (mem := t.1.mem) hpn hb hs hout
        exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, certOkC_of_prom_nil hpo, rfl⟩)⟩
      · obtain ⟨t', mem', hr, hp'⟩ := hcert
        cases hr with
        | refl => exact absurd hp' hpn
        | step hs1 hrest =>
          obtain ⟨outs, o, hso, ho, rfl⟩ := hs1
          replace hso : stepOne Arch.tso th 0 t.1.mem = some outs :=
            (Kernel.certSem_step_of_not_site (x := t.2) (siteAt_noneA hN hI hnt) hs).symm.trans hso
          exact ⟨[], _, .instr hruns hnsys hsite (.inl ⟨th, outs, o, ht, hso, ho, ⟨t', mem', hrest, hp'⟩, rfl⟩)⟩
    · have hr := Kernel.ready_of abi (t := th) (c := t) hs hrk hxk
      obtain ⟨call, hd, hnx, hcl⟩ := hN.sysOkX hT hI hs
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
        · exact hsys _ (Kernel.sys_writeIntr (K := abi) Arch.tso 1 ht hr hpn hc hj)
        · exact hsys _ (Kernel.sys_writeRet (K := abi) Arch.tso 1 ht hr hpn hc (Nat.pos_of_ne_zero hj))
      | futexWait => exact hsys _ (Kernel.sys_futexWait (K := abi) Arch.tso 1 ht hr hpn hc)
      | futexWake k => exact hsys _ (Kernel.sys_futexWake (K := abi) Arch.tso 1 ht hr hpn hc)
      | rtSigaction => exact hsys _ (Kernel.sys_rtSigaction (K := abi) Arch.tso 1 ht hr hpn hc)
      | archSetFs a => exact hsys _ (Kernel.sys_archSetFs (K := abi) Arch.tso 1 ht hr hpn hc)
      | exitGroup v =>
        by_cases hab : ∃ k a, μ.abortAt k = some a ∧ pcOf th.st = a
        · -- at an abort site: the abort
          obtain ⟨k, a, ha, hpc⟩ := hab
          obtain ⟨-, hv⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroupAbort (K := abi) Arch.tso 1 k ht hr hpn hc (hv v hd))
            (by simp) (fun k' hk => by obtain rfl : k' = k := by simpa using hk
                                       exact ⟨a, ha, th, ht, hpc⟩) (fun e he => by simp at he)⟩
        · have hnoab : ∀ k a, μ.abortAt k = some a → ¬ T.M.AtAddr a t 0 := fun k a ha ⟨t2, ht2, hpc⟩ => by
            cases (show some t2 = some th from ht2.symm.trans ht); exact hab ⟨k, a, ha, hpc⟩
          exact ⟨_, _, .sys hruns (Kernel.sys_exitGroup (K := abi) Arch.tso 1 ht hr hpn hc) (by simp)
            (fun k hk => by simp at hk) (fun _ _ => hnoab)⟩
      | exit => exact absurd rfl hnx
      | clone st tl => exact absurd rfl (hcl st tl)

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

/-- **`TI` is kept by every step from thread 0 at a state of the fragment**
(`ti_step` with the frames): the thread's facts `ti_stepA` takes from
`PreSA`, at any pair `(c, fs)` of the fragment at its state. -/
theorem ti_step_ofA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {t t' : T.M.Cfg} {tid : Nat} {es pre : List Ev} {th : Thread isa} {j : Nat} {E : Entry}
    {hl : List (Nat × Range)} {pm : _root_.Mem 64} {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat}
    {sm : WeakMem.Memory} {c : Ctl} {fs : List TermRun.Frame}
    (hth : t.1.threads = #[th]) (hk : t.2 = KS E Λ j hl pm) (hwr : WrOk th j) (hI : I lbl lsize th.st c fs)
    (hw : WideSt th.st) (hinv : Inv1 Λ lbl lsize ts th t.1.mem sm)
    (hs : T.M.Step μ tid t es t') (hti : TI Ab pre t) : TI Ab (pre ++ es) t' := by
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  intro u hu hab
  by_cases hab0 : Ab th.st
  · exact List.mem_append_left _ (hti th ht1 hab0)
  refine List.mem_append_right _ ?_
  have hget : ∀ {v : Thread isa} {mem : Memory}, (t.1.withThread 0 v mem).threads[0]? = some u → u = v :=
    fun h => by
      simp only [Config.withThread, hth] at h
      exact (Option.some.inj h).symm
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · -- the take does not enter the phase (`AbortPathS.take`)
    obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨-, rfl⟩ := step_takeA hN hT ht1 hI ha hpc hs
    obtain rfl := hget hu
    exact absurd hab (hA.take _ _ _ _ _ hI hab0 a ha hpc _)
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  rcases X64Ext.step_cases_site ht1 hw hinv hs (no_spawnA hN hT ht1 hI) (no_siteA hN ht1 hI hnt) with
    ⟨rfl, hns, outs, o, hso, ho, rfl, -, -⟩ | ⟨rfl, w, rfl, -, -, -⟩ | ⟨pk, hsys, -, -⟩
  · obtain rfl := hget hu
    exact absurd hab (stepOne_allInv Arch.tso hso ho (hA.instr _ _ _ _ _ hI hab0 hns)
      ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  · obtain rfl := hget hu
    exact absurd hab hab0
  · obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsys (wr_le hk hwr)
    rcases hcases with ⟨fd, buf, n, rd', b, u', rfl, rfl, -, -, hust, -, rfl⟩ |
      ⟨r, rfl, -, -, -, -, u', hu', hsu, -⟩ | ⟨-, -, -, rfl⟩ | ⟨v, rfl, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · obtain rfl := hget hu
      exact absurd (hust ▸ hab) hab0
    · have hsu' : u.st ∈ Kernel.certSuccs abi th.st call := Option.some.inj (hu'.symm.trans hu) ▸ hsu
      obtain ⟨fd, buf, n, rfl, hrf⟩ := hA.sys _ _ _ _ _ hI hab0 (atSys_of_ready hr) _ hcall _ hsu' hab
      obtain ⟨hc', hes⟩ := sysStep_write_ret ht1 hcall (wr_le hk hwr _ _ _ hcall) hsys
      have hu2 : u = Kernel.retThread abi th r := by rw [hc'] at hu; exact hget hu
      rw [hes (hrf r (by rw [hu2, Kernel.retThread_st]))]
      exact List.mem_singleton_self _
    all_goals
      obtain rfl : th = u := Option.some.inj (ht1.symm.trans hu)
      exact absurd hab hab0

/-- **`TI` is kept by every step from `RS`** (`ti_step` with the frames,
`ti_step_ofA`). -/
theorem ti_stepA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hs : T.M.Step μ tid t es t') (hti : TI Ab pre t) : TI Ab (pre ++ es) t' := by
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  rotate_left
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, hs0, hσ, hp, hI, -, hw, hb, hinv,
    hown, hmi, -⟩ := h
  exact ti_step_ofA hN hA hT hth hk hwr hI hw hinv hs hti

/-- **`TI` along every run from `RS`.** -/
theorem ti_runA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab)
    {Ab : State → Prop} (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev},
      RSA Λ P p G own I rS Tk μ ar t s → T.M.Step μ tid t es t' → ∃ s', RSA Λ P p G own I rS Tk μ ar t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, RSA Λ P p G own I rS Tk μ ar t s → TI Ab pre t → TI Ab (pre ++ tr) t' := by
  induction hr with
  | refl => intro s pre _ h; rwa [List.append_nil]
  | step hs _ ih =>
    intro s pre hR h
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s', hR'⟩ := hstep hR hs
    rw [← List.append_assoc]
    exact ih hR' (ti_stepA hN hA hT hR hs h)

/-- **An abort from `RS` is justified** (`r_abort` with the frames): the
`writeErr` one by `TI`; the `overflow` one at any depth with every frame's
environment small (`abortJustified_overflow_sourceS`); the `heap` one with
the heap use within the budget's `cells` (`AllocInvAt.heapCtr`, `hB`) and the next
label fresh (`FreshInv`) and the boxes counted (`SrcSafeS.box`,
`abortJustified_heap_source`). -/
theorem r_abortA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) (hsafe : SrcSafeS P p I)
    (hwf : Λ.WF) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr)
    {B : Budget} (hB : B.cells = ar.cells) {rS : Range} {Tk : State → Prop} {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind} (h : RSA Λ P p G own I rS Tk μ ar t s)
    (hti : TI Ab tr t) (hs : T.M.Step μ tid t es t') (hk : Ev.abort k ∈ es) :
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
  obtain ⟨⟨rfl, hab⟩ | ⟨rfl, hc, he⟩ | ⟨rfl, hheap⟩, -⟩ := hA.at_ _ _ _ _ _ hI k a ha hpc
  · exact hti th ht2 hab
  · exact abortJustified_overflow_sourceS hi hc hσ hp (noBigNumT_of_envSmallS hi he)
  · have hr := hheap (heapUse s) hai.heapCtr
    exact abortJustified_heap_source hi (by rw [hB]; exact hr) hσ hp
      (Spike.Lib.fresh_of_placed (fun m hmem => (hinv.mem.lbl_mem m hmem).imp fun _ h => h.1) hfr.fresh)
      (hsafe.box _ _ hre)

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program at any call depth on a target on
the canonical x86-64 machine** (`correctKOn` with the frames: `stepSimA`,
`r_progressA`, `r_memInA`, `r_abortA` with `ti_runA` from `ti_load`,
`r_componentsA`); the budget's heap `cells` are the arena's (`hB`). -/
theorem correctKOnA {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {tcells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)}
    {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ tcells secs offs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (tcells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p)
    (hinit : P.init (s0 P.cap))
    (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm := by
  have hsim := stepSimA hl himg hss hw hst hfr0 hP hinit hN hsafe hT htk0 hown0 hrd hwf hG0 hGpl hok hstat hsub hal
    hz0 hc0
  have hps := promSharedA hP hN hsafe (.of_all hrd) hwf hGpl hok hT
  refine correct_of_stepSim hsim hwf hload (fun t0 tr t h0 hr => ?_)
    (fun t0 tr t tid es t' k s h0 hr _ hR hs hk => ?_)
    (fun t s hR => r_componentsA hN hwf hR)
  · obtain ⟨s, -, hR⟩ := hsim.reach h0 hr
    exact ⟨r_progressA hN hA hT hwf hsvc hR, inLayout_of_memIn (r_memInA hR)⟩
  · obtain ⟨s0', -, hR0⟩ := hsim.init t0 h0
    have hti := ti_runA hN hA hT
      (fun hR hs => let ⟨s', _, h'⟩ := r_stepA hP hN hsafe hT hps (.of_all hrd) hwf hGpl hok hR hs; ⟨s', h'⟩)
      hr hR0 (pre := []) (fun th h hab => absurd hab (ti_load hab0 (hl.symm.trans h0) th h))
    rw [List.nil_append] at hti
    exact r_abortA hN hsafe hwf hA hB hR hti hs hk

open Scc.Cert.Link in
/-- **`Correct` for a one-thread program at any call depth on the canonical
X64 target**: `correctKOnA` at `T`, the load by `load_of_parsed`. -/
theorem correctKA {B : Budget} (hB : B.cells = ar.cells) {asm : Asm} {tcells : List (Directive × Nat)}
    {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : cellsOf asm = some tcells)
    (hd : dataSections asm.text = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (tcells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : NodesA Λ p (T.marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk (T.marks asm Λ) ar)
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS (T.marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, T.load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, T.load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKOnA (A := Asm) (ld := T.load) (rs := T.resolve) hB (load_of_parsed (kernel 1) Entry.linux Λ hpa hd)
    himg hss hw hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 hsvc hrd hwf hG0 hGpl hA hab0 hok hstat hsub hal hz0
    hc0

end Spike.Lib.X64ConsumerA
