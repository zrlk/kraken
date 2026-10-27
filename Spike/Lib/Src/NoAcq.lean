import Spike.Lib.Ret0Src
import Spike.Test.SetupStartSrc
import Scc.Sem.SrcOutProto
import WeakCore.TermExtStep

/-!
**No acquire load nor release store in the source** (ISA-neutral): the
`cell` side of the source safety (`SrcSafeS.cell`) is vacuous for a program
whose blocks have no `load true`, `store true` nor `spawn`, from starts that
have none either (`reach_noAcq`, as `Ret0Src.reach_noMem`).

- `AcqOp`: the operations concerned;
- `cfgNoS_extB`, `cfgNoS_wakeB`: an extern step and a wake keep any `NoS`;
- `reach_noAcq`: every reachable configuration is free of them, with no hook
  or WeakCore's (`UsesWc`);
- `setupInit_noAcq`: the starts before the setup block;
- `noAcq_cell`: the `cell` trigger of thread 0 is unreachable.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem

/-- **The operations the `cell` side of the source safety concerns**, with
`spawn`: an acquire load, a release store, a spawn. -/
def AcqOp : Op → Prop
  | .load true _ | .store true _ _ _ | .spawn .. => True
  | _ => False

theorem cfgNoS_thread_acq {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg} {i : Nat}
    (hp : ProgNoS AcqOp p) (hc : CfgNoS AcqOp c) (h : c' ∈ threadSteps p k arch c i) : CfgNoS AcqOp c' := by
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

theorem cfgNoS_prom_acq {c : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : WeakMem.Ts}
    (hc : CfgNoS AcqOp c) : CfgNoS AcqOp (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact hc
  | some th =>
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact hc i th hth
    · exact hc j th0 hj

theorem no_spawnBy_acq {cap i : Nat} {c c' : Cfg} (hc : CfgNoS AcqOp c) (h : SrcSem.SpawnBy cap i c c') :
    False := by
  obtain ⟨x, f, a, T, ts, e, th, -, -, hth, hterm, -⟩ := h
  have := (hc _ _ hth).1
  rw [hterm] at this
  exact this.1 trivial

/-- **An extern step keeps a configuration free of `bad`** (as
`TermArchENS.cfgNoS_ext`, for any `bad`). -/
theorem cfgNoS_extB {bad : Op → Prop} {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) {x : String}
    {n : ExtName} {a : At} {e : Expr} (hterm : th.term = .let_ x (.ext n a) e) (hc : CfgNoS bad c)
    (ws rs : List Word) : CfgNoS bad (extCfg c i th x n e ws rs) := by
  have hT := hc i th hth
  have he : NoS bad e := by
    have h1 := hT.1
    rw [hterm] at h1
    exact h1.2
  have key : ∀ {th' : TTh} (j : Nat) (th0 : TTh), (c.ths.set! i th')[j]? = some th0 →
      th'.term = e → th'.stack = th.stack → ThNoS bad th0 := by
    intro th' j th0 hj ht hs
    rcases getElem?_set!_or hj with rfl | hj
    · exact ⟨ht ▸ he, hs ▸ hT.2⟩
    · exact hc j th0 hj
  intro j th0 hj
  cases n with
  | current =>
      cases hl : th.tidLbl with
      | some l => simp only [extCfg, curCfg, hl] at hj; exact key j th0 hj rfl rfl
      | none => simp only [extCfg, curCfg, hl] at hj; exact key j th0 hj rfl rfl
  | _ => exact key j th0 hj rfl rfl

/-- **A wake keeps a configuration free of `bad`** (it changes only permits). -/
theorem cfgNoS_wakeB {bad : Op → Prop} {c : Cfg} (i : Nat) (v : WeakMem.Ts) (n : ExtName) (ws : List Word)
    (hc : CfgNoS bad c) : CfgNoS bad (wake c i v n ws) := fun j th0 hj => by
  rcases TermExtStep.wake_get c i v n ws j with h | ⟨th, u, h1, h2⟩
  · rw [h] at hj; exact hc j th0 hj
  · rw [h2] at hj; cases hj; exact hc j th h1

/-- **Every reachable source configuration is free of `AcqOp`**, with no hook
or WeakCore's (`UsesWc`). -/
theorem reach_noAcq {P : SrcSem.SrcParams} {p : Prog} (hp : ProgNoS AcqOp p)
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ SrcOutProto.UsesWc P p) (hinit : ∀ c, P.init c → CfgNoS AcqOp c)
    {tr : List Ev}
    {s : Cfg} (h : (SrcSem.source P p).Reach tr s) : CfgNoS AcqOp s := by
  obtain ⟨s0, h0, hr⟩ := h
  have H := hinit s0 h0
  clear h0
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact cfgNoS_thread_acq hp H hs
      · exact cfgNoS_prom_acq H
    · exact (no_spawnBy_acq H hs).elim
    · rcases hH with hH | hH <;> rw [hH] at hs
      · exact hs.elim
      obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, hterm, -, -, -, -, rfl⟩ := hs
      exact cfgNoS_wakeB _ _ _ _ (cfgNoS_extB h1 hterm H ws rs)

/-- **The starts before the setup block** are free of `AcqOp`. -/
theorem setupInit_noAcq {cap : Nat} {c : Cfg} (h : ∃ meW, c = Scc.Sem.SrcSem.setupStart cap meW) :
    CfgNoS AcqOp c := by
  obtain ⟨meW, rfl⟩ := h
  intro j th hj
  have : j = 0 := by
    rcases j with _ | j
    · rfl
    · simp [Scc.Sem.SrcSem.setupStart] at hj
  subst this
  simp only [Scc.Sem.SrcSem.setupStart, List.getElem?_toArray, List.getElem?_cons_zero,
    Option.some.injEq] at hj
  subst hj
  exact ⟨by simp [Scc.Sem.SrcSem.setupTerm, NoS, AcqOp], by simp⟩

/-- **The `cell` trigger is unreachable**: no reachable thread 0 is at an
acquire load or a release store. -/
theorem noAcq_cell {P : SrcSem.SrcParams} {p : Prog} (hp : ProgNoS AcqOp p)
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ SrcOutProto.UsesWc P p) (hinit : ∀ c, P.init c → CfgNoS AcqOp c)
    {tr : List Ev}
    {s : Cfg} (hr : (SrcSem.source P p).Reach tr s) {th : TTh} (h0 : s.ths[0]? = some th) {x : String}
    {a : At} {e : Expr} (ht : th.term = .let_ x (.load true a) e ∨ ∃ b, th.term = .let_ x (.store true a b none) e) :
    False := by
  have hn := (reach_noAcq hp hH hinit hr 0 th h0).1
  rcases ht with ht | ⟨b, ht⟩ <;> rw [ht] at hn <;> exact hn.1 trivial

end Spike.Lib.LowerNode
