import WeakCore.TermViewInvG
import WeakCore.TermStep

/-!
# TermViewInvH: the view invariant along every run

`ViewInv c`: every message's view is at most its timestamp, and every thread's words
(environment and saved frames) have view at most their read timestamp, which is below
the memory size, as are its scalar views.  It is preserved by every machine step
(`viewInv_step`), hence along every run (`viewInv_run`), and gives `EnvVR`
(`envVR_of_run`, stated unfolded so that this module need not import `TermSeenHid`).
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The run invariant. -/
def ViewInv (c : Cfg) : Prop :=
  MsgV c.mem ∧ ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ThV c.mem.size th

theorem getElem?_set!_cases {ths : Array TTh} {i j : Nat} {th' th : TTh}
    (h : (ths.set! i th')[j]? = some th) : th = th' ∨ ths[j]? = some th := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
  split at h
  · split at h
    · left; exact (Option.some.inj h).symm
    · simp at h
  · right; exact h

theorem viewInv_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (hv : ViewInv c) (h : c' ∈ threadSteps p k arch c i) : ViewInv c' := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; cases h
  | some th =>
    rw [hth] at h
    simp only [List.mem_map] at h
    obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := tstep_V evalOp_V hr hv.1 (hv.2 i th hth)
    refine ⟨h1, fun j th0 hj => ?_⟩
    rcases getElem?_set!_cases hj with rfl | hj
    · exact h3
    · exact (hv.2 j th0 hj).mono h2

theorem viewInv_prom {c : Cfg} {i : Nat} {a : Address} {v : Val} {w : Ts}
    (hv : ViewInv c) (hw : w < c.mem.size) : ViewInv (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact hv
  | some th =>
    have hle : c.mem.size ≤ (c.mem.push ⟨a, v, w⟩).size := by simp
    refine ⟨MsgV_push hv.1 (Nat.le_of_lt hw), fun j th0 hj => ?_⟩
    rcases getElem?_set!_cases hj with rfl | hj
    · have := hv.2 i th hth
      exact ⟨this.1.mono hle, fun fr hf => (this.2.1 fr hf).mono hle, this.2.2.mono hle⟩
    · exact (hv.2 j th0 hj).mono hle

theorem viewInv_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (hv : ViewInv c) (h : Step p k arch c c') : ViewInv c' := by
  cases h with
  | thread i hc _ => exact viewInv_thread hv hc
  | prom i a v w _ hw _ => exact viewInv_prom hv hw

/-- (spawn, run-closed) **`ViewInv` at every configuration reachable from `cs`** by machine steps and
`Sp` steps. -/
def ViewInvR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (cs : Cfg) : Prop :=
  ∀ {c : Cfg}, TermSpawnStep.StepsG p k arch Sp cs c → ViewInv c

/-- **`ViewInv` along every run** (the generic induction; the `Sp` arm is the caller's). -/
theorem viewInvR_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {cs : Cfg}
    (hSp : ∀ c c', Sp c c' → ViewInv c → ViewInv c') (h : ViewInv cs) : ViewInvR p k arch Sp cs :=
  fun hr => TermSpawnStep.stepsG_pres (fun _ _ hs hv => viewInv_step hv hs) hSp hr h

/-- `ViewInvR` at `Sp := ⊥` from `ViewInv` at the start (no premise beyond it). -/
theorem viewInvR_bot {p : Prog} {k : Promises.Knobs} {arch : Arch} {cs : Cfg} (h : ViewInv cs) :
    ViewInvR p k arch (fun _ _ => False) cs :=
  viewInvR_of (fun _ _ hf _ => hf.elim) h

#print axioms viewInvR_of
#print axioms viewInvR_bot

/-- **`ViewInv` along every run.** -/
theorem viewInv_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c0 c : Cfg}
    (h0 : ViewInvR p k arch Sp c0) (hr : TermSpawnStep.StepsG p k arch Sp c0 c) : ViewInv c := h0 hr

/-- `EnvVR` (unfolded) of every thread of every configuration reachable from a `ViewInv` one. -/
theorem envVR_of_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c0 c : Cfg}
    (h0 : ViewInvR p k arch Sp c0)
    (hr : TermSpawnStep.StepsG p k arch Sp c0 c) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) :
    ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws →
      w.view ≤ w.rts :=
  fun _ _ _ w hev hw => (evalAt_V ((viewInv_run h0 hr).2 i th hth).1 hev w hw).1

/-- `ViewInv` along a solo run. -/
theorem viewInv_solo {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (hv : ViewInv c) (h : Solo p k arch i c c') : ViewInv c' := by
  induction h with
  | refl => exact hv
  | thread hs _ ih => exact ih (viewInv_thread hv hs)
  | prom a v w hw _ ih => exact ih (viewInv_prom hv hw)

/-- `EnvVR` (unfolded) of thread `i` along a solo run from a `ViewInv` configuration. -/
theorem envVR_solo {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (hv : ViewInv c) (h : Solo p k arch i c c') {th : TTh} (hth : c'.ths[i]? = some th) :
    ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws →
      w.view ≤ w.rts :=
  envVR_of_run (p := p) (k := k) (arch := arch) (viewInvR_bot (viewInv_solo hv h)) (.refl _) hth

/-- `ViewInv` at an initial configuration of the `TermInit.InitShape` kind: empty memory, empty
stacks, zero scalar views, and argument words with zero view and read timestamp (e.g. `cst`). -/
theorem viewInv_init {c0 : Cfg} (hm : c0.mem = #[])
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th →
      th.stack = [] ∧ VSB 0 th.vs ∧ ∀ e ∈ th.env, ∀ w ∈ e.2.2, w.view = 0 ∧ w.rts = 0) :
    ViewInv c0 := by
  refine ⟨fun t m ht => by rw [hm] at ht; simp at ht, fun i th hth => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h i th hth
  rw [hm]; unfold ThV
  refine ⟨fun e he w hw => ?_, fun fr hf => (by rw [h1] at hf; cases hf), h2⟩
  obtain ⟨a, b⟩ := h3 e he w hw
  exact ⟨by rw [a, b]; exact Nat.le_refl _, by rw [b]; exact Nat.le_refl _⟩

end TermViewInv

#print axioms TermViewInv.viewInv_step
#print axioms TermViewInv.viewInv_run
#print axioms TermViewInv.envVR_of_run
#print axioms TermViewInv.viewInv_init
