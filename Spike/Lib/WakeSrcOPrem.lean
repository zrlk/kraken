/-
**wake's source-side premises of `WakeO.OPrem`** (ISA-neutral in the
memory model `arch`): the source facts `hP` (`HookOK`), `hsafe`
(`SrcSafeS`) and `hrd` (`SrcRd`) at `srcPo 2 arch wakeSrc`.

**Hooks** (`wake_hookOK`). wake's source runs under WeakCore's output hook
(`UsesWc`, by definition of `srcPo`). Its externs are `park`/`unpark`, never
`exitEv`, so no reachable configuration's event trace has an exit. Unlike
`Accepted2Out.noExit_of_progNoS`, the invariant only excludes the exit
extern (`ExitEvOp`), not the spawn: main spawns the worker, whose start
term (a tail call) has none, and the parent keeps its stack.

- `ExitEvOp`: the exit extern.
- `cfgNoS_spawnCfg`: a spawn keeps `CfgNoS` (parent's continuation, kid's
  tail call).
- `wake_noExitEv`, `wake_start_noS`: no block and no start has one.
- `wake_noExit`, `wake_hookOK`: no exit at any reachable configuration;
  `HookOK (srcPo 2 arch wakeSrc) wakeSrc`.

**Source safety** (`wake_srcSafeS`, at any fragment `I`: the `IRun`
premise is not used). Every reachable configuration has `WInv`: before the
spawn one thread, main, at a `MainPre` term (`VPre`, `VFlag`), with `o` and
then `c` bound to a pointer word `cst (.loc ⟨l, 0⟩ 0)` (`CBind`, from
`new`'s result and `publish`); after it two threads, main at an `MTerm`
with no stack, `c` so bound and a message at `⟨l, 0⟩` (`BTh`; the message is
`VFlag`'s `FlagMem` at the spawn, kept as memory only grows). `MainPre`
terms have no load, store or exchange; at an `MTerm` the one load is
`wlBody`'s of `c`, whose cell has that message.

- `CBind`, `BTh`, `WInv`: the invariant; `cbind_tstep`, `bth_tstep`: one
  thread step of main keeps it.
- `winv_init`, `winv_step`, `winv_run`: along source runs.
- `wake_srcSafeS`: `SrcSafeS (srcPo 2 arch wakeSrc) wakeSrc I`.
-/
import Spike.Lib.SpawnFlag
import Spike.Lib.Src.Accepted2Out
import Spike.Lib.WakeM0Rows
import Spike.Lib.A64ConsumerS
import Spike.Lib.Src.BoxCount

namespace Spike.Lib.WakeSrcOPrem

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem
open Spike.Lib.WakeT1 (wakeSrc srcPo progInitT)

/-! ## Hooks -/

/-- **The exit extern**: the one operation that puts an exit in the trace. -/
def ExitEvOp : Op → Prop
  | .ext .exitEv _ => True
  | _ => False

/-- **A spawn keeps `CfgNoS`**: the parent continues at its `let`'s body
with its stack, the kid starts at a tail call with no stack. -/
theorem cfgNoS_spawnCfg {bad : Op → Prop} {c : Cfg} {i : Nat} {th : TTh} {x f : String} {a : At} {T : Ty}
    {ts : List Ty} {e : Expr} {ws : List Word} (hc : CfgNoS bad c) (hth : c.ths[i]? = some th)
    (hterm : th.term = .let_ x (.spawn f a T ts) e) :
    CfgNoS bad (TermSpawnStep.spawnCfg c i th x e f ts T ws) := by
  obtain ⟨hT1, hT2⟩ := hc i th hth
  rw [hterm] at hT1
  intro j t hj
  rcases TermSpawnMid.spawnT_get_cases (TermSpawn.lt_of_get hth) hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hj'⟩
  · exact ⟨hT1.2, hT2⟩
  · exact ⟨trivial, fun fr hfr => by simp [TermSpawnStep.spawnKid] at hfr⟩
  · exact hc j t hj'

/-- **No block of wake has the exit extern.** -/
theorem wake_noExitEv : ProgNoS ExitEvOp wakeSrc := by
  intro d hd
  simp only [wakeSrc, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> simp [NoS, ExitEvOp]

/-- **wake's start has no exit extern and no exit.** -/
theorem wake_start_noS {c : Cfg} (h : progInitT wakeSrc 2 c) :
    CfgNoS ExitEvOp c ∧ ∀ x, Event.exit x ∉ c.trace := by
  rw [WakeT1.wake_start] at h
  subst h
  refine ⟨fun j th hj => ?_, fun x hx => by simp [WakeT1.tidStartT] at hx⟩
  rcases j with _ | j
  · simp only [WakeT1.tidStartT, List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    exact ⟨trivial, by simp⟩
  · simp [WakeT1.tidStartT] at hj

/-- **No reachable configuration of wake has an exit in its trace.** -/
theorem wake_noExit {arch : WeakMem.Arch} {tr : List Ev} {s : Cfg}
    (h : (SrcSem.source (srcPo 2 arch wakeSrc) wakeSrc).Reach tr s) : ∀ x, Event.exit x ∉ s.trace := by
  obtain ⟨s0, h0, hr⟩ := h
  have H : CfgNoS ExitEvOp s0 ∧ ∀ x, Event.exit x ∉ s0.trace := wake_start_noS h0
  clear h0
  suffices CfgNoS ExitEvOp s ∧ ∀ x, Event.exit x ∉ s.trace from this.2
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact ⟨LowerNode.cfgNoS_threadB wake_noExitEv H.1 hs, by erw [TermArchE.threadSteps_trace hs]; exact H.2⟩
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

/-- **wake's hook is accepted** (`WakeO.OPrem.hP`). -/
theorem wake_hookOK (arch : WeakMem.Arch) : HookOK (srcPo 2 arch wakeSrc) wakeSrc :=
  .wc rfl fun _ _ h => Spike.Lib.PrintSrc.noExit_hook (P := srcPo 2 arch wakeSrc) (p := wakeSrc) rfl (wake_noExit h)

/-- info: 'Spike.Lib.WakeSrcOPrem.wake_hookOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_hookOK

/-! ## Source safety -/

open WeakMem (Ts)
open Scc.Sem.SrcSem (stepBy_size spawnBy_size)
open Promises.Sim (MemExt)
open Spike.Lib.WakeA64 (wakeS)
open Spike.Lib.WakeM0 (MTerm mTail wlBody wlIf wlPark)
open Spike.Lib.SpawnViewLtSteps
open Spike.Lib.SpawnFlag (FlagC VFlag alloc_flag vflag_init vflag_step)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self getElem?_set!_ne)

/-- **main's pointer bindings before the spawn**: `o` at `publish`, and `c`
from then on, are bound to a pointer word `cst (.loc ⟨l, 0⟩ 0)`. -/
def CBind (th : TTh) : Prop :=
  (th.term = mO → ∃ l t, lookupE th.env "o" = some (t, [cst (.loc ⟨l, 0⟩ 0)])) ∧
    (th.term = mC ∨ th.term = spawnTerm → ∃ l t, lookupE th.env "c" = some (t, [cst (.loc ⟨l, 0⟩ 0)]))

/-- **main past the spawn, at memory `mem`**: at an `MTerm` with no stack,
`c` bound to a pointer word `cst (.loc ⟨l, 0⟩ 0)` with a message at
`⟨l, 0⟩`. -/
def BTh (mem : WeakMem.Memory) (th : TTh) : Prop :=
  MTerm th.term ∧ th.stack = [] ∧ ∃ l t, lookupE th.env "c" = some (t, [cst (.loc ⟨l, 0⟩ 0)]) ∧
    ∃ (k : Nat) (m : WeakMem.Msg), mem[k]? = some m ∧ m.loc = ⟨l, 0⟩

/-- **The source invariant of wake**: before the spawn, one thread with
`VPre`, `VFlag` and `CBind`; after it, two threads, main with `BTh`. -/
def WInv (s : Cfg) : Prop :=
  (s.ths.size = 1 ∧ VPre s ∧ VFlag s ∧ ∃ th0, s.ths[0]? = some th0 ∧ CBind th0) ∨
    (s.ths.size = 2 ∧ ∃ th0, s.ths[0]? = some th0 ∧ BTh s.mem th0)

/-- A binding of another variable does not shadow `x`. -/
theorem lookupE_cons {env : Env} {y x : String} (h : y ≠ x) (p : Ty × List Word) :
    lookupE ((y, p) :: env) x = lookupE env x := by
  simp [lookupE, h]

/-- `BTh` under memory growth, at the same term, stack and environment. -/
theorem BTh.mono {mem mem' : WeakMem.Memory} {th th' : TTh} (h : BTh mem th) (he : MemExt mem mem')
    (ht : th'.term = th.term) (hs : th'.stack = th.stack) (hv : th'.env = th.env) : BTh mem' th' := by
  obtain ⟨hm, hst, l, t, hc, k, m, hk, hkl⟩ := h
  exact ⟨ht ▸ hm, hs.trans hst, l, t, hv ▸ hc, k, m, TermLiveProps.get_ext he hk, hkl⟩

theorem waitLoop_decl : ∃ d, wakeSrc.find? (·.name == "waitLoop") = some d ∧ d.body = wlBody ∧ d.arg = "c" :=
  ⟨_, rfl, rfl, rfl⟩

/-- **One thread step of main before the spawn keeps `CBind`.** -/
theorem cbind_tstep {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List Ts} {th th' : TTh}
    (hg : g.p = wakeSrc) (hi : TInv mem.size th) (hf : FlagC mem th) (hb : CBind th)
    (h : (mem', pairs', th') ∈ tstep g mem pairs th) : CBind th' := by
  obtain ⟨hm, -, -, -, hz, -⟩ := hi
  rcases hm with ht | ht | ht | ht | ht | ht
  · obtain ⟨d, hd, hb'⟩ := main_decl
    rw [← hg] at hd
    simp [tstep, ht, mStart, enter, hd] at h
    cases hme : evalAt th.env (.var "me") with
    | none => simp [hme, ol] at h
    | some r =>
      obtain ⟨t, ws⟩ := r
      simp only [hme, ol, Option.bind_some, Function.comp, Option.map_some, Option.toList_some,
        List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [hb', mBody, mZ, mO] at h
      · simp [hb', mBody, mZ, mC, spawnTerm, WakePreA.spawnTerm] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "z" (.zero .int) mZ) rfl] at h
    obtain ⟨⟨s', t, ws⟩, -, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [withS, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "o" (.new (.var "z")) mO) rfl] at h
    have hzt := hz ht
    obtain ⟨t0, hz0⟩ := hf.1 ht
    rw [hz0] at hzt
    simp only [Option.map_some, Option.some.injEq] at hzt
    subst hzt
    simp only [evalOp, evalAt, hz0, accs, List.map_map, List.mem_map, Function.comp] at h
    obtain ⟨⟨s', pw⟩, ha, he'⟩ := h
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    obtain ⟨-, rfl⟩ := alloc_flag ha
    refine ⟨fun _ => ⟨_, _, by simp [withS, lookupE]; exact ⟨rfl, rfl⟩⟩, fun h => ?_⟩
    simp [withS, mO, mC, spawnTerm, WakePreA.spawnTerm] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "c" (.publish (.var "o")) mC) rfl] at h
    obtain ⟨⟨s', t, ws⟩, hr, rfl, rfl, rfl⟩ := List.mem_map.mp h
    obtain ⟨rfl, t0, ho⟩ := publish_res hr
    obtain ⟨l, t1, ho'⟩ := hb.1 ht
    simp only [evalAt, ho', Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨-, rfl⟩ := ho
    refine ⟨fun h => ?_, fun _ => ⟨l, t, by simp [withS, lookupE]⟩⟩
    simp [withS, mC, mO] at h
  · rw [TermLocal.tstep_let_gen (ht.trans rfl : th.term = .let_ "p" (.pair (.var "c") (.var "me")) spawnTerm) rfl] at h
    obtain ⟨⟨s', t, ws⟩, -, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨l, t1, hc⟩ := hb.2 (Or.inl ht)
    refine ⟨fun h => ?_, fun _ => ⟨l, t1, ?_⟩⟩
    · simp [withS, spawnTerm, WakePreA.spawnTerm, mO] at h
    · simp only [withS]; rw [lookupE_cons (by decide)]; exact hc
  · rw [TermLocal.tstep_let_gen
      (ht.trans rfl : th.term = .let_ "t" (.spawn "worker" (.var "p") (.prod (.ptr .pub .int) .tid) []) mTail) rfl] at h
    simp [evalOp] at h

/-- **One thread step of main past the spawn keeps `BTh`.** -/
theorem bth_tstep {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List Ts} {th th' : TTh}
    (hg : g.p = wakeSrc) (hb : BTh mem th) (h : (mem', pairs', th') ∈ tstep g mem pairs th) : BTh mem' th' := by
  have hext : MemExt mem mem' := (TermLiveProps.tstep_ext _ _ _ _ _ h).mem
  obtain ⟨hm, hst, l, t, hc, k, m, hk, hkl⟩ := hb
  have hk' := TermLiveProps.get_ext hext hk
  rcases hm with ht | ht | ht | ht | ht
  · obtain ⟨d, hd, hbd, hda⟩ := waitLoop_decl
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

/-- No load or store at a `MainPre` term. -/
theorem mainPre_not_ld {e : Expr} (hm : MainPre e) {x : String} {a : At} {e' : Expr}
    (h : e = .let_ x (.load true a) e' ∨ ∃ b, e = .let_ x (.store true a b none) e') : False := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mStart, mBody, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at h

/-- No exchange site at a `MainPre` term. -/
theorem mainPre_not_xchgSite {c : Ctl} (hm : MainPre c.term) {x : String} {sa : WeakMem.Address} {u : Ty} {v : At}
    {e : Expr} (h : XchgSite c x sa u v e) : False := by
  rcases h.2 with ⟨a, -, -, -, he, -⟩ | ⟨b, i, -, -, -, -, -, -, -, he, -⟩ <;>
    rcases hm with h | h | h | h | h | h <;> rw [h] at he <;>
    simp [mStart, mBody, mZ, mO, mC, spawnTerm, WakePreA.spawnTerm] at he

/-- **wake's start has `WInv`.** -/
theorem winv_init {arch : WeakMem.Arch} {s : Cfg} (h : (wakeS arch).init s) : WInv s := by
  have hv := vpre_init h
  have hf := vflag_init h
  have h' : s = WakeT1.tidStartT 2 := by
    change WakeT1.progInitT wakeSrc 2 s at h
    rw [WakeT1.wake_start] at h
    exact h
  subst h'
  refine Or.inl ⟨rfl, hv, hf, _, rfl, fun h => ?_, fun h => ?_⟩
  · simp [WakeT1.tidStartT, mO] at h
  · simp [WakeT1.tidStartT, mC, spawnTerm, WakePreA.spawnTerm] at h

/-- **One source step keeps `WInv`.** -/
theorem winv_step {arch : WeakMem.Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (wakeS arch).step i s es s')
    (hw : WInv s) : WInv s' := by
  rcases hw with ⟨h1, hv, hf, th0, h0, hb⟩ | ⟨h2, th0, h0, hB⟩
  · have hv' := vpre_step h hv
    have hf' := vflag_step h hv hf
    obtain ⟨th', h0', hi⟩ := hv h1
    obtain ⟨th'', h0'', hfi⟩ := hf h1
    rw [h0] at h0' h0''; cases h0'; cases h0''
    obtain ⟨-, hs, -⟩ := h
    rcases hs with hs | hs | hs
    · have h1' : s'.ths.size = 1 := (stepBy_size hs).trans h1
      refine Or.inl ⟨h1', hv', hf', ?_⟩
      rcases hs with ⟨hm, -⟩ | ⟨a, v, w, hi', -, -, rfl⟩
      · unfold TermRun.threadSteps at hm
        split at hm
        · simp at hm
        · rename_i th hth
          obtain rfl := idx0 h1 hth
          rw [h0] at hth; cases hth
          obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
          exact ⟨th', getElem?_set!_self h0 _, cbind_tstep rfl hi hfi hb hr⟩
      · obtain rfl : i = 0 := by omega
        unfold TermRun.promise
        rw [h0]
        exact ⟨_, getElem?_set!_self h0 _, hb⟩
    · have hsz := (spawnBy_size hs).1
      obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, hterm, -, -, -, rfl⟩ := hs
      obtain rfl := idx0 h1 hth
      rw [h0] at hth; cases hth
      have ht : th0.term = spawnTerm := by
        rcases hi.1 with h | h | h | h | h | h <;> rw [h] at hterm ⊢ <;>
          simp [mStart, mBody, mZ, mO, mC] at hterm
      rw [ht, spawnTerm_eq] at hterm
      simp only [Expr.let_.injEq] at hterm
      obtain ⟨rfl, -, rfl⟩ := hterm
      obtain ⟨l, t, hc⟩ := hb.2 (Or.inr ht)
      obtain ⟨i0, j, -, ⟨m, hm, hml⟩, -⟩ := hfi.2 l (Or.inr ⟨Or.inr ht, t, hc⟩)
      refine Or.inr ⟨by rw [hsz, h1], _, TermSpawnMid.spawnT_get_par (TermSpawn.lt_of_get h0),
        Or.inl rfl, hi.2.1, l, t, ?_, i0, m, hm, hml⟩
      simp only [TermSpawnStep.spawnPar]
      rw [lookupE_cons (by decide)]
      exact hc
    · obtain ⟨x, n, a, e, th, rt, ws, rs, hth, hterm, -⟩ := hs
      obtain rfl := idx0 h1 hth
      rw [h0] at hth; cases hth
      exact (not_ext hi.1 hterm).elim
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
            exact ⟨th', getElem?_set!_self h0 _, bth_tstep rfl hB hr⟩
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
          rcases WakeM0.mterm_let hB.1 hterm with ⟨-, h, -⟩ | ⟨rfl, h, rfl⟩
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

/-- **`WInv` along source runs.** -/
theorem winv_run {arch : WeakMem.Arch} {s s' : Cfg} {tr : List Ev} (h : (wakeS arch).Run s tr s') (hw : WInv s) :
    WInv s' := by
  induction h with
  | refl => exact hw
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (winv_step hs hw)

/-- **wake's source safety** (`WakeO.OPrem.hsafe`), at any fragment `I`. -/
theorem wake_srcSafeS (arch : WeakMem.Arch) (I : A64ConsumerS.InvS) :
    A64ConsumerS.SrcSafeS (srcPo 2 arch wakeSrc) wakeSrc I where
  cell := by
    intro tr s th hr h0 _ _ _ _ _ x a e ty w sa hop hev hw
    obtain ⟨s0, hs0, hrun⟩ := hr
    rcases winv_run hrun (winv_init hs0) with ⟨h1, hv, -, -⟩ | ⟨-, th0, h0', hB⟩
    · obtain ⟨th', h0', hi⟩ := hv h1
      rw [h0] at h0'; cases h0'
      exact (mainPre_not_ld hi.1 hop).elim
    · rw [h0] at h0'; cases h0'
      obtain ⟨hm, -, l, t, hc, k, m, hk, hkl⟩ := hB
      rcases hop with hop | ⟨b, hop⟩
      · obtain ⟨-, -, -, rfl, -⟩ := WakeM0.mterm_load hm hop
        simp only [evalAt, hc, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hev
        obtain ⟨-, rfl, -⟩ := hev
        simp [cst, Promises.TVal.mk0] at hw
        subst hw
        exact ⟨k, m, hk, hkl⟩
      · exact (WakeM0.mterm_not_store hm hop).elim
  xchg := by
    intro tr s th hr h0 _ _ _ hd _ x sa u v e hx
    obtain ⟨s0, hs0, hrun⟩ := hr
    rcases winv_run hrun (winv_init hs0) with ⟨h1, hv, -, -⟩ | ⟨-, th0, h0', hB⟩
    · obtain ⟨th', h0', hi⟩ := hv h1
      rw [h0] at h0'; cases h0'
      exact (mainPre_not_xchgSite (c := ⟨th.term, th.env, hd⟩) hi.1 hx).elim
    · rw [h0] at h0'; cases h0'
      exact (WakeM0.mterm_not_xchgSite (c := ⟨th.term, th.env, hd⟩) hB.1 hx).elim
  box := fun _ _ hr => Spike.Lib.BoxCount.reach_boxLe (P := srcPo 2 arch wakeSrc) (.inr (show SrcOutProto.UsesWc _ _ from rfl)) (fun c hc => by
    rw [show (srcPo 2 arch wakeSrc).init = progInitT wakeSrc 2 from rfl, Spike.Lib.WakeT1.wake_start] at hc
    subst hc; decide) hr

/-- info: 'Spike.Lib.WakeSrcOPrem.wake_srcSafeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_srcSafeS

end Spike.Lib.WakeSrcOPrem
