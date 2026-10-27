import Spike.Lib.Src.NoAcq
import WeakCore.TermArchE
import Spike.Test.Hello1MainSrc

/-!
**`hello1o` never exits through an extern** (ISA-neutral). Under WeakCore's
output hook (`UsesWc`), no reachable configuration's event trace has an exit,
and so neither does its hook trace (`hello1o_noExit`, `hello1o_noExit_hook`:
`HookOK.wc`'s premise). `main`'s exit is the source's `mainExit`, not a
trace event.

- `stdout`: the output bytes of a source trace;
- `ExitOp`: the operations that could put an exit in the trace or add a
  thread, an `exitEv` extern and a spawn;
- `cfgNoS_threadB`, `cfgNoS_promB`: a thread step and a promise keep any
  `NoS` (as `NoAcq`'s, for any `bad`);
- `hello1o_noExitOp`: no block of `hello1o` has one;
- `hello1o_noExit`, `hello1o_noExit_hook`: every reachable configuration.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem

/-- **The output bytes of a source trace.** -/
def stdout (tr : List Ev) : List (Fin 256) := tr.filterMap (fun | .out b => some b | _ => none)

/-- **An exit extern or a spawn**: the operations that could put an exit in
the trace or add a thread. -/
def ExitOp : Op → Prop
  | .ext .exitEv _ | .spawn .. => True
  | _ => False

theorem cfgNoS_threadB {bad : Op → Prop} {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg}
    {i : Nat} (hp : ProgNoS bad p) (hc : CfgNoS bad c) (h : c' ∈ threadSteps p k arch c i) : CfgNoS bad c' := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; cases h
  | some th =>
    rw [hth] at h
    simp only [List.mem_map] at h
    obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := h
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact tstep_noS (g := gOf p k arch c i) hp (hc i th hth) hr
    · exact hc j th0 hj

theorem cfgNoS_promB {bad : Op → Prop} {c : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val}
    {w : WeakMem.Ts} (hc : CfgNoS bad c) : CfgNoS bad (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact hc
  | some th =>
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact hc i th hth
    · exact hc j th0 hj

/-- **No block of `hello1o` has an exit extern or a spawn.** -/
theorem hello1o_noExitOp : ProgNoS ExitOp Spike.Test.Hello1MainSrc.hello1o := by
  intro d hd
  simp only [Spike.Test.Hello1MainSrc.hello1o, Spike.Lib.Hello1Src.hello1Src, List.tail_cons, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [NoS, ExitOp, Spike.Lib.PrintSrc.printLD, Spike.Lib.PrintSrc.printD, Spike.Lib.PrintSrc.printLBody,
      Spike.Lib.PrintSrc.printBody, Spike.Lib.PrintSrc.printLoad, Spike.Lib.PrintSrc.printLane,
      Spike.Lib.PrintSrc.printEmit, Spike.Lib.PrintSrc.printNext, Spike.Lib.PrintSrc.printAdv]

/-- The extern events of any extern but `exitEv` have no exit. -/
theorem events_noExit {n : ExtName} (hn : n ≠ .exitEv) (ws rs : List Word) (x : Nat) :
    Event.exit x ∉ n.events ws rs := by
  intro h
  unfold ExtName.events at h
  split at h <;> (try split at h) <;> simp_all

/-- **No reachable configuration of `hello1o` has an exit in its trace**, under
WeakCore's output hook, from the starts before the setup block. -/
theorem hello1o_noExit {P : SrcSem.SrcParams} (hU : SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o)
    (hinit : ∀ c, P.init c → ∃ meW, c = SrcSem.setupStart P.cap meW) {tr : List Ev} {s : Cfg}
    (h : (SrcSem.source P Spike.Test.Hello1MainSrc.hello1o).Reach tr s) : ∀ x, Event.exit x ∉ s.trace := by
  obtain ⟨s0, h0, hr⟩ := h
  have H : CfgNoS ExitOp s0 ∧ ∀ x, Event.exit x ∉ s0.trace := by
    obtain ⟨meW, rfl⟩ := hinit s0 h0
    refine ⟨fun j th hj => ?_, fun x hx => by simp [SrcSem.setupStart] at hx⟩
    have : j = 0 := by
      rcases j with _ | j
      · rfl
      · simp [SrcSem.setupStart] at hj
    subst this
    simp only [SrcSem.setupStart, List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    exact ⟨by simp [SrcSem.setupTerm, NoS, ExitOp], by simp⟩
  clear h0
  suffices CfgNoS ExitOp s ∧ ∀ x, Event.exit x ∉ s.trace from this.2
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact ⟨cfgNoS_threadB hello1o_noExitOp H.1 hs, by erw [TermArchE.threadSteps_trace hs]; exact H.2⟩
      · exact ⟨cfgNoS_promB H.1, by erw [TermArchE.promise_trace]; exact H.2⟩
    · exfalso
      obtain ⟨x, f, a, T, ts, e, th, -, -, hth, hterm, -⟩ := hs
      have := (H.1 _ _ hth).1
      rw [hterm] at this
      exact this.1 trivial
    · rw [hU] at hs
      obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, hterm, -, -, -, -, rfl⟩ := hs
      have hn : n ≠ .exitEv := by
        rintro rfl
        have := (H.1 _ _ h1).1
        rw [hterm] at this
        exact this.1 trivial
      refine ⟨cfgNoS_wakeB _ _ _ _ (cfgNoS_extB h1 hterm H.1 ws rs), fun y hy => ?_⟩
      erw [TermExtStep.wake_trace, TermExtStep.extCfg_trace] at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact H.2 y hy
      · exact events_noExit hn ws rs y hy

/-- **`hello1o`'s hook trace has no exit** (`HookOK.wc`'s premise). -/
theorem hello1o_noExit_hook {P : SrcSem.SrcParams} (hU : SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o)
    (hinit : ∀ c, P.init c → ∃ meW, c = SrcSem.setupStart P.cap meW) :
    ∀ tr s, (SrcSem.source P Spike.Test.Hello1MainSrc.hello1o).Reach tr s → ∀ x, Ev.exit x ∉ P.hooks.trace s :=
  fun _ _ h => Spike.Lib.PrintSrc.noExit_hook hU (hello1o_noExit hU hinit h)

end Spike.Lib.LowerNode
