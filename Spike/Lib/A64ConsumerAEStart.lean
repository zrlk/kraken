/-
**`Correct` through `print`'s `write`** on the canonical AArch64 target:
`Spike/Lib/A64ConsumerAStart.lean`'s load, simulation and `Correct` over
`RSAE` (`Spike/Lib/A64ConsumerAE.lean`), the rows under `msOfAB`
(`NodesA … (some Ab)`) with the emit rows `EmitA`, the source's reads
`SrcRd`.

Facts about the middle of the output `write` (`EmitSA`) that are
certification facts are premises: promises there are to shared regions
(`PromSharedAE`) or absent (`WriteNoPromAE`), and so is `PromSharedA` at a
`write(1, …)`'s pairs (`promSharedA` covers the rows under `msOfA` only).
All three hold vacuously with `write` a certification dead end. The
components at `EmitSA` (the source inside `print`, `Top`) are a premise
too (`CompAE`).

- `pre_loadAE`, `init_of_loadAE`, `stepSimAE`: the load (`PreSA`,
  `Wr1Zero`, `PrivInv`) and the simulation (`r_stepAE`).
- `WriteNoPromAE`, `emit_progressA`, `r_progressAE`, `PreJA.memIn`,
  `r_memInAE`: progress.
- `emit_noAbort`, `ti_stepAE`, `ti_runAE`, `r_abortAE`: the abort clause
  (no abort in the middle of the output `write`).
- `CompAE`, `r_componentsAE'`: the components from `CompAE`.
- `correctKOnAE`, `correctKAEmitE'`: `Correct` at a start with `StartOk`
  (`correctKOnA'`, `correctKAE'`).
-/
import Spike.Lib.A64ConsumerAEStep
import Spike.Lib.A64ConsumerAStart

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.DmemPriv (PrivInv)
open Spike.Lib.LowerNode (SrcNumSP PrintLd)

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry} {Top : Ctl → Prop}

/-! ## The load -/

open Scc.Cert.Link in
/-- **The relation at the target's load** (`init_of_loadA'`): `PreSA` with
no byte out (the count 0) and the private-memory invariant from the entry
state (`privInv_load`). -/
theorem init_of_loadAE {prog : Program} {secs : DataSecs}
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
    (hc0 : t0.1.mem.initVal (wordLoc ar.ctr) = 0) (hEnt : E.clear Λ = true)
    (h : loadParsed (kernel 1) E Λ prog secs = some t0) :
    ∃ s, (SrcSem.source P p).init s ∧ RSAE Λ P p G own I Top rS Tk μ ar E t0 s := by
  simp only [loadParsed] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    cases h
    refine ⟨s0', hinit, .inl ⟨.inl ⟨pre_loadA' himg hss hw hinit hs hst hfr0 (loadMem_in hwf hc.1.1.1.1) ?_ htk0
      hown0 hg hstat hsub hal hz0 hc0, fun _ _ _ _ _ => rfl⟩,
      Spike.Lib.A64DmemPriv.privInv_load (wideSt_threadAt hw _ _ _) hEnt⟩⟩
    rw [imageMem, wordsMem, wordsMem, ← List.map_append]
    exact initFits_words fun q hq => (List.mem_append.mp hq).elim (image_fit hwf q) (rodataWords_fit _ _ _ q)
  · cases h

/-! ## Progress -/

/-- **No promise in the middle of the output `write`** (`WriteNoPromA`
over `EmitSA`). -/
def WriteNoPromAE (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (Top : Ctl → Prop) (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s th, EmitSA Λ P p G own I Top rS Tk μ ar t s → t.1.threads = #[th] → th.prom = []

/-- **In the middle of the output `write` there is progress**: the thread
is at the `svc` (not halted, no fault, no instruction), with no promise
(`WriteNoPromAE`) the kernel's `write` steps (`sys_writeIntr`,
`sys_writeRet`). -/
theorem emit_progressA {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range}
    {Tk : State → Prop} (hsvcE : WriteNoPromAE Λ P p G own I Top rS Tk μ ar) {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : EmitSA Λ P p G own I Top rS Tk μ ar t s) : T.M.Progress μ t := by
  have hpn := fun th => hsvcE t s th h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, -, -, -, -, -, hJ, -⟩ := h
  obtain ⟨-, -, -, -, hsys, c₀, fs₀, c₁, buf, n, Pw, hI, -, hdc, -⟩ := hJ
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  have hrk : t.2.runs 0 = true := by rw [hk]; rfl
  have hxk : t.2.exited = none := by rw [hk]; rfl
  have hruns : T.M.runs t 0 := ⟨⟨th, ht⟩, hxk, by show ¬ (t.2.runs 0 = false); rw [hrk]; simp⟩
  obtain ⟨imm, sz, hcs⟩ := hN.svc _ _ _ _ _ hI hsys
  have hnh : th.halted = false := by simp [Thread.halted, Kraken.Promising.Lower.A64.exec_svc hcs]
  have hc : Kernel.callOf abi th = some (.write 1 buf n) := hdc
  refine ⟨?_, .inr ⟨⟨0, hxk, hruns.2.2, th, ht, fun h => by rw [hnh] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, -⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, -⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      exact hns ⟨th, ht1, hsys⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [hnh, Bool.or_false, hc] at hf
        simp at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      rw [hsys] at hns; cases hns
  · obtain ⟨-, -, t1, ht1, -⟩ := hl
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    have hr := Kernel.ready_of abi (t := th) (c := t) hsys hrk hxk
    have hp0 := hpn th hth
    have hstep : ∀ c', (kernel 1).sys μ 0 t [] c' → ∃ es c', T.M.Step μ 0 t es c' :=
      fun c' h => ⟨[], c', .sys hruns h (by simp) (by simp) (by simp)⟩
    by_cases hj : t.2.wr 0 = 0
    · exact hstep _ (Kernel.sys_writeIntr (K := abi) Arch.armv8 1 ht hr hp0 hc hj)
    · exact hstep _ (Kernel.sys_writeRet (K := abi) Arch.armv8 1 ht hr hp0 hc (Nat.pos_of_ne_zero hj))

/-- **There is progress from `RSAE`.** -/
theorem r_progressAE {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hwf : Λ.WF) (hsvc : WriteNoPromA Λ P p G own I rS Tk μ ar) (hsvcE : WriteNoPromAE Λ P p G own I Top rS Tk μ ar)
    {Ent : Entry} {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSAE Λ P p G own I Top rS Tk μ ar Ent t s) :
    T.M.Progress μ t := by
  rcases h with ⟨⟨hpre, -⟩ | hem, -⟩ | hpost
  · exact pre_progressA hN hA hT hwf hsvc hpre
  · exact emit_progressA hN hsvcE hem
  · exact post_progressSA hpost

/-- `PreJA`'s memory is in the layout. -/
theorem PreJA.memIn {J : InvS} {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : PreJA Λ P p G own J rS Tk μ ar t s) : MemIn Λ t.1.mem := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ := h
  exact hmi

/-- The memory of a configuration `RSAE` relates is in the layout. -/
theorem r_memInAE {rS : Range} {Tk : State → Prop} {Ent : Entry} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : RSAE Λ P p G own I Top rS Tk μ ar Ent t s) : MemIn Λ t.1.mem := by
  rcases h with ⟨⟨hpre, -⟩ | hem, -⟩ | hpost
  · exact PreJA.memIn hpre
  · exact PreJA.memIn hem
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmi, _⟩ := hpost
    exact hmi

/-! ## The abort clause -/

/-- **No abort in the middle of the output `write`**: every step from
`EmitSA` is a promise (no event) or a kernel step of the `write` (a byte,
or a return with `writeErr` at most). -/
theorem emit_noAbort {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat}
    {es : List Ev} {k : AbortKind} (h : EmitSA Λ P p G own I Top rS Tk μ ar t s) (hs : T.M.Step μ tid t es t')
    (hk : Ev.abort k ∈ es) : False := by
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk'⟩, -, -, hwr, -, -, -, -, hJ, -, hw, -, hinv, -⟩ := h
  obtain ⟨-, -, -, -, hsys, c₀, fs₀, c₁, buf, n, Pw, hI, -, hdc, -⟩ := hJ
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => by
    obtain ⟨-, -, hsys', -⟩ := hT.site _ _ _ _ _ hI a ha hpc
    rw [hsys] at hsys'; cases hsys'
  rcases A64Ext.step_cases_site ht1 hw hinv hs (no_spawnA hN hT ht1 hI) (no_siteA hN ht1 hI hnt) with
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨pk, hsy, -, -⟩
  · cases hk
  · cases hk
  · obtain ⟨-, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsy (wr_le hk' hwr)
    obtain rfl : call = .write 1 buf n := Option.some.inj (hcall.symm.trans hdc)
    rcases hcases with ⟨fd, -, -, -, b, -, -, -, -, -, -, rfl, -⟩ | ⟨r, -, -, -, hev, -⟩ | ⟨hex, -⟩ | ⟨v, hex, -⟩
    · split at hk <;> simp at hk
    · rcases hev with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp at hk
    · cases hex
    · cases hex

/-- **`TI` is kept by every step from `RSAE`**: from `PreSA` by
`ti_stepA`, from `EmitSA` by `ti_step_ofA` at the emit row's pair of the
fragment. -/
theorem ti_stepAE {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {Ent : Entry} {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es pre : List Ev}
    (h : RSAE Λ P p G own I Top rS Tk μ ar Ent t s) (hs : T.M.Step μ tid t es t') (hti : TI Ab pre t) :
    TI Ab (pre ++ es) t' := by
  rcases h with ⟨⟨hpre, -⟩ | hem, -⟩ | hpost
  · exact ti_stepA hN hA hT (.inl hpre) hs hti
  · obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, -, -, -, hJ, -, hw, -, hinv, -⟩ :=
      hem
    obtain ⟨-, -, -, -, -, c₀, fs₀, -, -, -, -, hI, -⟩ := hJ
    exact ti_step_ofA hN hA hT hth hk hwr hI hw hinv hs hti
  · exact ti_stepA hN hA hT (.inr hpost) hs hti

/-- **`TI` along every run from `RSAE`.** -/
theorem ti_runAE {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {Ab : State → Prop}
    (hA : AbortPathS μ I Ab ar.cells ar.ctr) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    {Ent : Entry}
    (hstep : ∀ {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev},
      RSAE Λ P p G own I Top rS Tk μ ar Ent t s → T.M.Step μ tid t es t' →
        ∃ s', RSAE Λ P p G own I Top rS Tk μ ar Ent t' s')
    {t t' : T.M.Cfg} {tr : List Ev} (hr : T.M.Run μ t tr t') :
    ∀ {s pre}, RSAE Λ P p G own I Top rS Tk μ ar Ent t s → TI Ab pre t → TI Ab (pre ++ tr) t' := by
  induction hr with
  | refl => intro s pre _ h; rwa [List.append_nil]
  | step hs _ ih =>
    intro s pre hR h
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s', hR'⟩ := hstep hR hs
    rw [← List.append_assoc]
    exact ih hR' (ti_stepAE hN hA hT hR hs h)

/-- **An abort from `RSAE` is justified**: from `PreSA` by `r_abortA`; there
is none from `EmitSA` (`emit_noAbort`). -/
theorem r_abortAE {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) (hsafe : SrcSafeS P p I)
    (hwf : Λ.WF)
    {Ab : State → Prop} (hA : AbortPathS μ I Ab ar.cells ar.ctr) {B : Budget} (hB : B.cells = ar.cells)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {Ent : Entry} {t t' : T.M.Cfg}
    {s : TermRun.Cfg} {tid : Nat} {es tr : List Ev} {k : AbortKind}
    (h : RSAE Λ P p G own I Top rS Tk μ ar Ent t s) (hti : TI Ab tr t) (hs : T.M.Step μ tid t es t')
    (hk : Ev.abort k ∈ es) :
    ∃ w i, Components T.M Λ w t ((SrcSem.source P p).core s) ∧ w.thr i = some tid ∧
      AbortJustified B (SrcSem.source P p) tr s i k := by
  rcases h with ⟨⟨hpre, -⟩ | hem, -⟩ | hpost
  · exact r_abortA hN hsafe hwf hA hB (.inl hpre) hti hs hk
  · exact (emit_noAbort hN hT hem hs hk).elim
  · exact r_abortA hN hsafe hwf hA hB (.inr hpost) hti hs hk

/-! ## The components -/

/-- **The components in the middle of the output `write`** (the source
inside `print`). -/
def CompAE (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (Top : Ctl → Prop) (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s, EmitSA Λ P p G own I Top rS Tk μ ar t s →
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s)

/-- **`RSAE` is explicit**: `r_componentsA` off the output `write`, `CompAE`
in its middle. -/
theorem r_componentsAE' {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) (hwf : Λ.WF)
    {rS : Range} {Tk : State → Prop} (hcompE : CompAE Λ P p G own I Top rS Tk μ ar) {Ent : Entry} {t : T.M.Cfg}
    {s : TermRun.Cfg} (h : RSAE Λ P p G own I Top rS Tk μ ar Ent t s) :
    ∃ w : Witness T.M, Components T.M Λ w t ((SrcSem.source P p).core s) := by
  rcases h with ⟨⟨hpre, -⟩ | hem, -⟩ | hpost
  · exact r_componentsA hN hwf (.inl hpre)
  · exact hcompE t s hem
  · exact r_componentsA hN hwf (.inr hpost)

/-! ## The step-wise simulation and `Correct` -/

open Scc.Cert.Link in
/-- **The step-wise simulation through `print`'s `write`** at a start with
`StartOk` (`stepSimA'` over `RSAE`, the step `r_stepAE`). -/
theorem stepSimAE {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p) (hnum : SrcNumSP P p PrintLd) (hinit : P.init s0')
    {ab : Option (State → Prop)} (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I ab)
    (hE : EmitA Λ p I Top) (hsafe : SrcSafeS P p I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hps : PromSharedA Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hpsE : PromSharedAE Λ P p G own I Top rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF) (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hEnt : E.clear Λ = true) :
    StepSim (TOn A ld rs) (SrcSem.source P p) Λ asm
      (RSAE Λ P p G own I Top rS Tk ((TOn A ld rs).marks asm Λ) ar E) where
  init _ h := init_of_loadAE hwf himg hss hw hinit hs hst hfr0 htk0 (hown0 _ h) (hG0 _ h) hstat hsub hal (hz0 _ h)
    (hc0 _ h) hEnt (hl.symm.trans h)
  step _ _ _ _ _ h hs := r_stepAE hP hW hnum hN hsafe hE hT hps hpsE hrd hwf hGpl hok hEnt h hs

open Scc.Cert.Link in
/-- **`Correct` through `print`'s `write`** at a start with `StartOk` on a
target on the canonical AArch64 machine (`correctKOnA'` over `RSAE`: the
simulation `stepSimAE`, `r_progressAE`, `r_memInAE`, `r_abortAE` with
`ti_runAE` from `ti_load`, `r_componentsAE'`). The rows are under any
`msOfAX … ab` (`msOfAB` at `ab = some Ab`, the emit rows `EmitA`); the
certification facts in the middle of the output `write` (`PromSharedA` at
its pairs, `PromSharedAE`, `WriteNoPromAE`) and its components (`CompAE`)
are premises. -/
theorem correctKOnAE {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p)
    (hnum : SrcNumSP P p PrintLd) (hinit : P.init s0')
    {ab : Option (State → Prop)} (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I ab)
    (hE : EmitA Λ p I Top) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hps : PromSharedA Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hpsE : PromSharedAE Λ P p G own I Top rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hsvcE : WriteNoPromAE Λ P p G own I Top rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hcompE : CompAE Λ P p G own I Top rS Tk ((TOn A ld rs).marks asm Λ) ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hEnt : E.clear Λ = true) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm := by
  have hsim := stepSimAE hl himg hss hw hs hst hfr0 hP hW hnum hinit hN hE hsafe hT htk0 hown0 hps hpsE hrd hwf
    hG0 hGpl hok hstat hsub hal hz0 hc0 hEnt
  refine correct_of_stepSim hsim hwf hload (fun t0 tr t h0 hr => ?_)
    (fun t0 tr t tid es t' k s h0 hr _ hR hs hk => ?_)
    (fun t s hR => r_componentsAE' hN hwf hcompE hR)
  · obtain ⟨s, -, hR⟩ := hsim.reach h0 hr
    exact ⟨r_progressAE hN hA hT hwf hsvc hsvcE hR, inLayout_of_memIn (r_memInAE hR)⟩
  · obtain ⟨s0', -, hR0⟩ := hsim.init t0 h0
    have hti := ti_runAE hN hA hT
      (fun hR hs => let ⟨s', _, h'⟩ := r_stepAE hP hW hnum hN hsafe hE hT hps hpsE hrd hwf hGpl hok hEnt hR hs
        ⟨s', h'⟩)
      hr hR0 (pre := []) (fun th h hab => absurd hab (ti_load hab0 (hl.symm.trans h0) th h))
    rw [List.nil_append] at hti
    exact r_abortAE hN hsafe hwf hA hB hT hR hti hs hk

-- The kernel's check that `target (kernel 1) E`'s machine is `T`'s (`canonical 1`) may recurse past the default depth.
set_option maxRecDepth 100000 in
open Scc.Cert.Link in
/-- **`correctKOnAE` at any entry state `E`** on the target
`target (kernel 1) E`, the load by `load_of_parsed` (`correctKAE'` through
`print`'s `write`). -/
theorem correctKAEmitE' {B : Budget} (hB : B.cells = ar.cells) {asm : String} {prog : Program}
    {secs : DataSecs} {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, (target (kernel 1) E).load asm Λ = some t0) (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p)
    (hnum : SrcNumSP P p PrintLd) (hinit : P.init s0')
    {ab : Option (State → Prop)} (hN : NodesA Λ p ((target (kernel 1) E).marks asm Λ) rd G own ar I ab)
    (hE : EmitA Λ p I Top) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((target (kernel 1) E).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hps : PromSharedA Λ P p G own I rS Tk ((target (kernel 1) E).marks asm Λ) ar)
    (hpsE : PromSharedAE Λ P p G own I Top rS Tk ((target (kernel 1) E).marks asm Λ) ar)
    (hsvc : WriteNoPromA Λ P p G own I rS Tk ((target (kernel 1) E).marks asm Λ) ar)
    (hsvcE : WriteNoPromAE Λ P p G own I Top rS Tk ((target (kernel 1) E).marks asm Λ) ar)
    (hcompE : CompAE Λ P p G own I Top rS Tk ((target (kernel 1) E).marks asm Λ) ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((target (kernel 1) E).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → ∀ a,
      (AllocRow.freeR ar.heap ar.cells 0).contains a → t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hEnt : E.clear Λ = true) :
    Correct (target (kernel 1) E) (SrcSem.source P p) Λ B asm :=
  correctKOnAE (A := String) (ld := (target (kernel 1) E).load) (rs := (target (kernel 1) E).resolve) hB
    (load_of_parsed (kernel 1) E Λ hpa hd) himg hss hw hs hst hfr0 hload hP hW hnum hinit hN hE hsafe hT htk0 hown0
    hps hpsE hsvc hsvcE hcompE hrd hwf hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0 hEnt

/--
info: 'Spike.Lib.A64ConsumerA.correctKAEmitE'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correctKAEmitE'

end Spike.Lib.A64ConsumerA
