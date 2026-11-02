/-
**hello.w on x86-64: the source-side premises of `OPremH`** (ISA-neutral in the memory
model `arch`): the source facts `hP` (`HookOK`) and `hsafe` (`SrcSafeS`) at
`srcPo 2 arch helloSrc` (`Spike.Lib.X64WakeSrcOPrem`'s twins for `wakeSrc`).

**Hooks** (`hello_hookOK`). hello's source runs under WeakCore's output hook
(`UsesWc`, by definition of `srcPo`). Its externs are `emit`, `park` and
`unpark`, never `exitEv`, so no reachable configuration's event trace has an
exit (`X64WakeSrcOPrem.wake_noExit`'s invariant, `CfgNoS ExitEvOp`, from hello's
start before the setup block, `hello_start`).

- `hello_noExitEv`, `hello_start_noS`: no block and no start has the exit
  extern.
- `hello_noExit`, `hello_hookOK`: no exit at any reachable configuration;
  `HookOK (srcPo 2 arch helloSrc) helloSrc`.

**Source safety** (`hello_srcSafeS`, at any fragment `I`: the `IRun`
premise is not used). Every reachable configuration has `HInv`: before the
spawn one thread, main, at a stage of `X64HelloPreTerm.HAt` with the buffer's
`Lanes` (`X64HelloVBuf.VBufR`) and the box's flag cell past its `new`
(`X64HelloVFlag.VFlagH`); after it two threads, main with
`X64WakeSrcOPrem.BTh` (at an `MTerm` with no stack, `c` bound to the box's
word, a message there: `VFlagH`'s `FlagMem` at the spawn, kept as memory
only grows). No stage is at a load or store (`hat_not_ld`); the stages' one
exchange sites are rodata's lane exchanges (stages 5 and 7, at the buffer's
words 0 and 1, `hat_xchgSite`), whose words have `Lanes`' message
(`LaneU`). Past the spawn the argument is wake's: at an `MTerm` the one
load is `wlBody`'s of `c`, and there is no store or exchange.

- `hat_not_ld`, `hat_xchgSite`, `hat_spawn_k`: the stages' loads, stores,
  exchanges and spawn.
- `waitLoop_declH`, `bthH_tstep`: hello's `waitLoop` is wake's
  (`X64WakeM0.wlBody`), so a thread step of main keeps `BTh`.
- `HInv`, `hinv_init`, `hinv_step`, `hinv_run`: the invariant.
- `hello_srcSafeS`: `SrcSafeS (srcPo 2 arch helloSrc) helloSrc I`.

x86-64 twin of `Spike/Lib/HelloSrcOPrem.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, nothing differs beyond the module names: the source is ISA-neutral.
-/
import Spike.Lib.X64WakeSrcOPrem
import Spike.Lib.X64HelloVFlag

namespace Spike.Lib.X64HelloSrcOPrem

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem
open Spike.Lib.X64WakeT1 (srcPo progInitT setupStartT)
open Spike.Lib.X64HelloSrc (helloSrc helloS hello_start)
open Spike.Lib.X64WakeSrcOPrem (ExitEvOp cfgNoS_spawnCfg BTh lookupE_cons)

/-! ## Hooks -/

/-- **No block of hello has the exit extern.** -/
theorem hello_noExitEv : ProgNoS ExitEvOp helloSrc := by
  intro d hd
  simp only [helloSrc, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [NoS, ExitEvOp]

/-- **hello's start has no exit extern and no exit.** -/
theorem hello_start_noS {c : Cfg} (h : progInitT helloSrc 2 c) :
    CfgNoS ExitEvOp c ∧ ∀ x, Event.exit x ∉ c.trace := by
  rw [hello_start] at h
  subst h
  refine ⟨fun j th hj => ?_, fun x hx => by simp [setupStartT] at hx⟩
  rcases j with _ | j
  · simp only [setupStartT, List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    exact ⟨by simp [NoS, ExitEvOp, Scc.Sem.SrcSem.setupTerm], by simp⟩
  · simp [setupStartT] at hj

/-- **No reachable configuration of hello has an exit in its trace.** -/
theorem hello_noExit {arch : WeakMem.Arch} {tr : List Ev} {s : Cfg}
    (h : (SrcSem.source (srcPo 2 arch helloSrc) helloSrc).Reach tr s) : ∀ x, Event.exit x ∉ s.trace := by
  obtain ⟨s0, h0, hr⟩ := h
  have H : CfgNoS ExitEvOp s0 ∧ ∀ x, Event.exit x ∉ s0.trace := hello_start_noS h0
  clear h0
  suffices CfgNoS ExitEvOp s ∧ ∀ x, Event.exit x ∉ s.trace from this.2
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact ⟨LowerNode.cfgNoS_threadB hello_noExitEv H.1 hs, by erw [TermArchE.threadSteps_trace hs]; exact H.2⟩
      · exact ⟨LowerNode.cfgNoS_promB H.1, by erw [TermArchE.promise_trace]; exact H.2⟩
    · obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, hterm, -, -, -, rfl⟩ := hs
      exact ⟨cfgNoS_spawnCfg H.1 hth hterm, H.2⟩
    · obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, hterm, -, -, -, -, rfl⟩ := hs
      have hn : n ≠ .exitEv := by
        rintro rfl
        have := (H.1 _ _ h1).1
        rw [hterm] at this
        exact this.1 trivial
      refine ⟨LowerNode.cfgNoS_wakeB _ _ _ _ (LowerNode.cfgNoS_extB h1 hterm H.1 ws rs), fun y hy => ?_⟩
      erw [TermExtStep.wake_trace, TermExtStep.extCfg_trace] at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact H.2 y hy
      · exact LowerNode.events_noExit hn ws rs y hy

/-- **hello's hook is accepted** (`OPremH.hP`). -/
theorem hello_hookOK (arch : WeakMem.Arch) : HookOK (srcPo 2 arch helloSrc) helloSrc :=
  .wc rfl fun _ _ h => Spike.Lib.PrintSrc.noExit_hook (P := srcPo 2 arch helloSrc) (p := helloSrc) rfl (hello_noExit h)

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hello_hookOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello_hookOK

/-! ## Source safety -/

open WeakMem (Ts)
open Scc.Sem.SrcSem (stepBy_size spawnBy_size)
open Promises.Sim (MemExt)
open Spike.Lib.X64WakeM0 (MTerm mTail wlBody wlIf wlPark)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self getElem?_set!_ne)
open Spike.Lib.Hello1RodataSrc (env0 envN bBind envA env1 env2 env3)
open Spike.Lib.X64HelloRodataSrc
open Spike.Lib.X64HelloMainPreSrc
open Spike.Lib.X64HelloPreTerm
open Spike.Lib.X64HelloVBuf (VBufR vbufR_init vbufR_step hat_not_ext LaneU)
open Spike.Lib.X64HelloVFlag (VFlagH vflagH_init vflagH_step)

section Stages

variable {th : TTh} {k : Nat} {wo0 wo1 : Word}

/-- No stage is at a load or a store. -/
theorem hat_not_ld (h : HAt th k wo0 wo1) {x : String} {a : At} {e : Expr}
    (hop : th.term = .let_ x (.load true a) e ∨ ∃ b, th.term = .let_ x (.store true a b none) e) : False := by
  obtain ⟨hk, hterm, -⟩ := h
  rw [hterm] at hop
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _
  | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ =>
    simp [hc, Scc.Sem.SrcSem.setupTerm, rdC0, rdBody, eM, rdCN, eB, rdCA, eW0, rdC1, eO0, rdC2, eW1, rdC3, eO1,
      rdC4, eS, rdC5, eN, eSm, eSl0, ePack, rdRet, eRet, SrcCalls.setupCont, mainC, mainBodyH, zTerm, c0H,
      newTerm, boxTermH, p0Term, pTerm, spawnTermH] at hop
  | _ + 23, hk => omega

/-- Only stage 22 is at a `spawn`. -/
theorem hat_spawn_k (h : HAt th k wo0 wo1) {x f : String} {a : At} {T : Ty} {ts : List Ty} {e : Expr}
    (ht : th.term = .let_ x (.spawn f a T ts) e) : k = 22 := by
  obtain ⟨hk, hterm, -⟩ := h
  rw [hterm] at ht
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _
  | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ =>
    simp [hc, Scc.Sem.SrcSem.setupTerm, rdC0, rdBody, eM, rdCN, eB, rdCA, eW0, rdC1, eO0, rdC2, eW1, rdC3, eO1,
      rdC4, eS, rdC5, eN, eSm, eSl0, ePack, rdRet, eRet, SrcCalls.setupCont, mainC, mainBodyH, zTerm, c0H,
      newTerm, boxTermH, p0Term, pTerm, spawnTermH] at ht
  | 22, _ => rfl
  | _ + 23, hk => omega

/-- **The stages' exchange sites**: rodata's lane exchanges, stage 5 at the
buffer's word 0 and stage 7 at its word 1. -/
theorem hat_xchgSite (h : HAt th k wo0 wo1) {hd : Option (Nat × Word)} {x : String} {sa : WeakMem.Address} {u : Ty}
    {v : At} {e : Expr} (hx : XchgSite ⟨th.term, th.env, hd⟩ x sa u v e) :
    k = 5 ∧ sa = ⟨lbB, 0⟩ ∨ k = 7 ∧ sa = ⟨lbB, 1⟩ := by
  obtain ⟨hk, hterm, henv, -⟩ := h
  rcases hx.2 with ⟨a, -, -, -, he, -⟩ | ⟨b, i, t, pw, ti, iws, μ, sb, n, he, hb, hpw, -, hi, hn, rfl⟩
  · simp only at he
    rw [hterm] at he
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _
    | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ =>
      simp [hc, Scc.Sem.SrcSem.setupTerm, rdC0, rdBody, eM, rdCN, eB, rdCA, eW0, rdC1, eO0, rdC2, eW1, rdC3, eO1,
        rdC4, eS, rdC5, eN, eSm, eSl0, ePack, rdRet, eRet, SrcCalls.setupCont, mainC, mainBodyH, zTerm, c0H,
        newTerm, boxTermH, p0Term, pTerm, spawnTermH] at he
    | _ + 23, hk => omega
  · simp only at he hb hi
    rw [hterm] at he
    rw [henv] at hb hi
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 6, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _
    | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ =>
      simp [hc, Scc.Sem.SrcSem.setupTerm, rdC0, rdBody, eM, rdCN, eB, rdCA, eW0, eO0, rdC2, eW1, eO1,
        rdC4, eS, rdC5, eN, eSm, eSl0, ePack, rdRet, eRet, SrcCalls.setupCont, mainC, mainBodyH, zTerm, c0H,
        newTerm, boxTermH, p0Term, pTerm, spawnTermH] at he
    | 5, _ =>
      simp only [hc, rdC1, eO0, Expr.let_.injEq, Op.xchgAt.injEq] at he
      obtain ⟨-, ⟨rfl, rfl, -⟩, -⟩ := he
      simp [hc, rdC1, env1, envA, bBind, evalAt, lookupE, cst, Promises.TVal.mk0] at hb hi
      obtain ⟨-, rfl⟩ := hb
      obtain ⟨-, rfl⟩ := hi
      simp at hpw
      subst hpw
      simp [numOf] at hn
      subst hn
      exact .inl ⟨rfl, by simp [offs]⟩
    | 7, _ =>
      simp only [hc, rdC3, eO1, Expr.let_.injEq, Op.xchgAt.injEq] at he
      obtain ⟨-, ⟨rfl, rfl, -⟩, -⟩ := he
      simp [hc, rdC3, env3, env2, env1, envA, bBind, evalAt, lookupE, cst, Promises.TVal.mk0] at hb hi
      obtain ⟨-, rfl⟩ := hb
      obtain ⟨-, rfl⟩ := hi
      simp at hpw
      subst hpw
      simp [numOf] at hn
      subst hn
      exact .inr ⟨rfl, by simp [offs]⟩
    | _ + 23, hk => omega

end Stages

theorem waitLoop_declH :
    ∃ d, helloSrc.find? (·.name == "waitLoop") = some d ∧ d.body = wlBody ∧ d.arg = "c" :=
  ⟨_, rfl, rfl, rfl⟩

/-- **One thread step of main past the spawn keeps `BTh`** (`X64WakeSrcOPrem.bth_tstep` at `helloSrc`). -/
theorem bthH_tstep {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List Ts} {th th' : TTh}
    (hg : g.p = helloSrc) (hb : BTh mem th) (h : (mem', pairs', th') ∈ tstep g mem pairs th) : BTh mem' th' := by
  have hext : MemExt mem mem' := (TermLiveProps.tstep_ext _ _ _ _ _ h).mem
  obtain ⟨hm, hst, l, t, hc, k, m, hk, hkl⟩ := hb
  have hk' := TermLiveProps.get_ext hext hk
  rcases hm with ht | ht | ht | ht | ht
  · obtain ⟨d, hd, hbd, hda⟩ := waitLoop_declH
    rw [← hg] at hd
    simp [tstep, ht, mTail, enter, hd, evalAt, hc, ol] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨by rw [hbd]; exact Or.inr (Or.inl rfl), hst, l, _, by simp [lookupE, hda]; rfl, k, m, hk', hkl⟩
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "d" (.load true (.var "c")) wlIf) rfl] at h
    obtain ⟨⟨s', t', ws⟩, -, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨Or.inr (Or.inr (Or.inl rfl)), hst, l, t, by simp only [withS]; rw [lookupE_cons (by decide)]; exact hc,
      k, m, hk', hkl⟩
  · simp only [tstep, ht, wlIf] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [List.mem_singleton, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         refine ⟨?_, hst, l, t, hc, k, m, hk, hkl⟩
         first | exact Or.inr (Or.inr (Or.inr (Or.inr rfl))) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · rw [TermExtStep.tstep_ext (ht.trans rfl : th.term = .let_ "p" (.ext .park .unit) mTail)] at h
    simp at h
  · simp [tstep, ht, WakeMLive.wlRet, hst] at h

/-- **The source invariant of hello**: before the spawn, one thread with
`VBufR` and `VFlagH`; after it, two threads, main with `BTh`. -/
def HInv (s : Cfg) : Prop :=
  (s.ths.size = 1 ∧ VBufR s ∧ VFlagH s) ∨ (s.ths.size = 2 ∧ ∃ th0, s.ths[0]? = some th0 ∧ BTh s.mem th0)

/-- **hello's start has `HInv`.** -/
theorem hinv_init {arch : WeakMem.Arch} {s : Cfg} (h : (helloS arch).init s) : HInv s := by
  have hb := vbufR_init h
  have hf := vflagH_init h
  have h' : s = setupStartT 2 := by
    change progInitT helloSrc 2 s at h
    rw [hello_start] at h
    exact h
  subst h'
  exact Or.inl ⟨rfl, hb, hf⟩

/-- **One source step keeps `HInv`.** -/
theorem hinv_step {arch : WeakMem.Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (helloS arch).step i s es s')
    (hw : HInv s) : HInv s' := by
  rcases hw with ⟨h1, hb, hf⟩ | ⟨h2, th0, h0, hB⟩
  · have hb' := vbufR_step h hb
    have hf' := vflagH_step h hf
    obtain ⟨-, hs, -⟩ := h
    rcases hs with hs | hs | hs
    · exact Or.inl ⟨(stepBy_size hs).trans h1, hb', hf'⟩
    · have hsz := (spawnBy_size hs).1
      obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, hterm, -, -, -, rfl⟩ := hs
      obtain ⟨th0, k, wo0, wo1, h0, -, -, hat, hfl⟩ := hf h1
      obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
      rw [h0] at hth; cases hth
      obtain rfl := hat_spawn_k hat hterm
      rw [hat.2.1] at hterm
      simp only [hc, spawnTermH, Expr.let_.injEq] at hterm
      obtain ⟨rfl, -, rfl⟩ := hterm
      obtain ⟨i0, j, -, ⟨m, hm, hml⟩, -⟩ := hfl (by decide)
      refine Or.inr ⟨by rw [hsz, h1], _, TermSpawnMid.spawnT_get_par (TermSpawn.lt_of_get h0),
        Or.inl rfl, by simp only [TermSpawnStep.spawnPar, withS]; rw [hat.2.2.2.2.1]; rfl, lbX, .ptr .pub .int, ?_,
        i0, m, hm, hml⟩
      simp only [TermSpawnStep.spawnPar]
      rw [lookupE_cons (by decide), hat.2.2.1]
      simp [hc, envP0, envC, lookupE]
    · obtain ⟨x, n, a, e, th, rt, ws, rs, hth, hterm, -⟩ := hs
      obtain ⟨th0, k, wo0, wo1, h0, -, -, hat, -⟩ := hb h1
      obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
      rw [h0] at hth; cases hth
      exact (hat_not_ext hat hterm).elim
  · obtain ⟨-, hs, -⟩ := h
    rcases hs with hs | hs | hs
    · have h2' := (stepBy_size hs).trans h2
      rcases hs with ⟨hm, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · unfold TermRun.threadSteps at hm
        split at hm
        · simp at hm
        · rename_i th hth
          obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
          refine Or.inr ⟨h2', ?_⟩
          by_cases hi0 : i = 0
          · subst hi0
            rw [h0] at hth; cases hth
            exact ⟨th', getElem?_set!_self h0 _, bthH_tstep rfl hB hr⟩
          · exact ⟨th0, by dsimp only; rw [getElem?_set!_ne _ hi0]; exact h0,
              hB.mono (TermLiveProps.tstep_ext _ _ _ _ _ hr).mem rfl rfl rfl⟩
      · refine Or.inr ⟨h2', ?_⟩
        unfold TermRun.promise
        split
        · exact ⟨th0, h0, hB⟩
        · rename_i th hth
          by_cases hi0 : i = 0
          · subst hi0
            rw [h0] at hth; cases hth
            exact ⟨_, getElem?_set!_self h0 _, hB.mono (Promises.Sim.MemExt.push _ _) rfl rfl rfl⟩
          · exact ⟨th0, by dsimp only; rw [getElem?_set!_ne _ hi0]; exact h0,
              hB.mono (Promises.Sim.MemExt.push _ _) rfl rfl rfl⟩
    · have : s.ths.size < 2 := (spawnBy_size hs).2
      omega
    · obtain ⟨x, n, a, e, th, rt, ws, rs, hth, hterm, -, -, -, -, rfl⟩ := hs
      refine Or.inr ⟨by rw [TermExtStep.wake_size, TermExtStep.extCfg_size]; exact h2, ?_⟩
      have hmem : (wake (extCfg s i th x n e ws rs) i (relView th.vs) n ws).mem = s.mem := by
        rw [TermExtStep.wake_mem, TermExtStep.extCfg_mem]
      have hE : ∃ th1, (extCfg s i th x n e ws rs).ths[0]? = some th1 ∧ BTh s.mem th1 := by
        by_cases hi0 : i = 0
        · subst hi0
          rw [h0] at hth; cases hth
          rcases X64WakeM0.mterm_let hB.1 hterm with ⟨-, h, -⟩ | ⟨rfl, h, rfl⟩
          · cases h
          · injection h with hn
            subst hn
            rw [TermExtStep.extCfg_ths_self h0 _ _ _ _ _ (by decide)]
            obtain ⟨-, hst, l, t, hc, hmsg⟩ := hB
            exact ⟨_, rfl, Or.inl rfl, hst, l, t, by simp only; rw [lookupE_cons (by decide)]; exact hc, hmsg⟩
        · exact ⟨th0, by rw [TermExtStep.extCfg_ths_ne _ _ _ _ _ _ _ (Ne.symm hi0)]; exact h0, hB⟩
      obtain ⟨th1, h1, hB1⟩ := hE
      rw [hmem]
      rcases TermExtStep.wake_get (extCfg s i th x n e ws rs) i (relView th.vs) n ws 0 with h | ⟨th2, u, h2, h3⟩
      · exact ⟨th1, h.trans h1, hB1⟩
      · rw [h1] at h2; cases h2
        exact ⟨_, h3, hB1.mono (Promises.Sim.MemExt.refl _) rfl rfl rfl⟩

/-- **`HInv` along source runs.** -/
theorem hinv_run {arch : WeakMem.Arch} {s s' : Cfg} {tr : List Ev} (h : (helloS arch).Run s tr s') (hw : HInv s) :
    HInv s' := by
  induction h with
  | refl => exact hw
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (hinv_step hs hw)

/-- **hello's source safety** (`OPremH.hsafe`), at any fragment `I`. -/
theorem hello_srcSafeS (arch : WeakMem.Arch) (I : X64ConsumerS.InvS) :
    X64ConsumerS.SrcSafeS (srcPo 2 arch helloSrc) helloSrc I where
  cell := by
    intro tr s th hr h0 _ _ _ _ _ x a e ty w sa hop hev hw
    obtain ⟨s0, hs0, hrun⟩ := hr
    rcases hinv_run hrun (hinv_init hs0) with ⟨h1, hb, -⟩ | ⟨-, th0, h0', hB⟩
    · obtain ⟨th', k, wo0, wo1, h0', -, -, hat, -⟩ := hb h1
      rw [h0] at h0'; cases h0'
      exact (hat_not_ld hat hop).elim
    · rw [h0] at h0'; cases h0'
      obtain ⟨hm, -, l, t, hc, k, m, hk, hkl⟩ := hB
      rcases hop with hop | ⟨b, hop⟩
      · obtain ⟨-, -, -, rfl, -⟩ := X64WakeM0.mterm_load hm hop
        simp only [evalAt, hc, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hev
        obtain ⟨-, rfl, -⟩ := hev
        simp [cst, Promises.TVal.mk0] at hw
        subst hw
        exact ⟨k, m, hk, hkl⟩
      · exact (X64WakeM0.mterm_not_store hm hop).elim
  xchg := by
    intro tr s th hr h0 _ _ _ hd _ x sa u v e hx
    obtain ⟨s0, hs0, hrun⟩ := hr
    rcases hinv_run hrun (hinv_init hs0) with ⟨h1, hb, -⟩ | ⟨-, th0, h0', hB⟩
    · obtain ⟨th', k, wo0, wo1, h0', -, -, hat, hl⟩ := hb h1
      rw [h0] at h0'; cases h0'
      rcases hat_xchgSite hat hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨n, m, hm, hml, -⟩ := hl.1 (by decide) (by decide)
        exact ⟨n, m, hm, hml⟩
      · obtain ⟨n, m, hm, hml, -⟩ := hl.2.1 (by decide) (by decide)
        exact ⟨n, m, hm, hml⟩
    · rw [h0] at h0'; cases h0'
      exact (X64WakeM0.mterm_not_xchgSite (c := ⟨th.term, th.env, hd⟩) hB.1 hx).elim
  box := fun _ _ hr => Spike.Lib.BoxCount.reach_boxLe (P := srcPo 2 arch helloSrc)
    (.inr (show SrcOutProto.UsesWc _ _ from rfl)) (fun c hc => by
      rw [show (srcPo 2 arch helloSrc).init = progInitT helloSrc 2 from rfl, hello_start] at hc
      subst hc; decide) hr

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hello_srcSafeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello_srcSafeS

end Spike.Lib.X64HelloSrcOPrem

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hello_noExitEv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hello_noExitEv

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hello_start_noS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hello_start_noS

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hello_noExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hello_noExit

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hat_not_ld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hat_not_ld

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hat_spawn_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hat_spawn_k

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hat_xchgSite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hat_xchgSite

/-- info: 'Spike.Lib.X64HelloSrcOPrem.waitLoop_declH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.waitLoop_declH

/-- info: 'Spike.Lib.X64HelloSrcOPrem.bthH_tstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.bthH_tstep

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hinv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hinv_init

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hinv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hinv_step

/-- info: 'Spike.Lib.X64HelloSrcOPrem.hinv_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSrcOPrem.hinv_run
