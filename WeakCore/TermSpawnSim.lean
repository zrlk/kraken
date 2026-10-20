import WeakCore.TermStep
/-! # TermSpawnSim — a phantom bottom frame does not change a thread's steps -/
namespace TermSpawnSim
open CoreLang CoreTerm TermRun
open WeakMem (Memory Ts Arch)

/-- Append frame `f0` at the bottom of the stack. -/
def app (f0 : Frame) (th : TTh) : TTh := { th with stack := th.stack ++ [f0] }

set_option maxHeartbeats 1000000 in
theorem tstep_app_eq (f0 : Frame) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh)
    (hr : ∀ a, th.term = .ret a → th.stack ≠ []) :
    tstep g mem pairs (app f0 th) = (tstep g mem pairs th).map (fun x => (x.1, x.2.1, app f0 x.2.2)) := by
  obtain ⟨term, env, σs, stack, vs, promises, nalloc, undefs⟩ := th
  cases term
  case let_ x op e =>
    cases op
    case call f is a ts =>
      simp only [tstep, app, ol, enter, callFrame]
      cases List.find? (fun x => x.name == f) g.p <;> cases evalAt env a <;> simp
    case callc f a =>
      simp only [tstep, app, ol, enter, callFrame]
      rcases hf : evalAt env f with _ | ⟨tf, _ | ⟨w, _ | ⟨w2, ws⟩⟩⟩ <;> simp
      cases hw : w.val <;> simp
      rename_i i
      cases hd : g.p[i]? <;> simp
      rename_i d
      cases List.find? (fun x => x.name == d.name) g.p <;> cases evalAt env a <;> simp
    all_goals (simp only [tstep, app, withS, stOf]; (repeat' split) <;> (try simp_all [List.map_map, Function.comp_def]) <;> (repeat' split) <;> (try simp_all) <;> (try (intros; split <;> simp_all)))
  case ret a =>
    cases stack with
    | nil => exact absurd rfl (hr a rfl)
    | cons f rest => simp only [tstep, app]; cases evalAt env a <;> simp
  case tail f is a ts =>
    simp only [tstep, app, ol, enter]
    cases List.find? (fun x => x.name == f) g.p <;> cases evalAt env a <;> simp
  all_goals (simp only [tstep, app, withS, stOf]; (repeat' split) <;> (try simp_all [List.map_map, Function.comp_def, List.map_flatMap]) <;> (repeat' split) <;> (try simp_all) <;> (try (intros; split <;> simp_all)))

theorem tstep_app {f0 : Frame} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    (hr : ∀ a, th.term = .ret a → th.stack ≠ [])
    {m : Memory} {ps : List Ts} {th' : TTh} (h : (m, ps, th') ∈ tstep g mem pairs th) :
    (m, ps, app f0 th') ∈ tstep g mem pairs (app f0 th) := by
  rw [tstep_app_eq f0 g mem pairs th hr]
  exact List.mem_map.2 ⟨_, h, rfl⟩

theorem hr_of_mem {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : Memory × List Ts × TTh}
    (h : x ∈ tstep g mem pairs th) : ∀ a, th.term = .ret a → th.stack ≠ [] := by
  intro a ht hs
  obtain ⟨term, env, σs, stack, vs, promises, nalloc, undefs⟩ := th
  simp only at ht hs; subst ht hs
  simp [tstep] at h

theorem tstep_app' {f0 : Frame} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {m : Memory} {ps : List Ts} {th' : TTh} (h : (m, ps, th') ∈ tstep g mem pairs th) :
    (m, ps, app f0 th') ∈ tstep g mem pairs (app f0 th) := tstep_app (hr_of_mem h) h

/-- The phantom configuration: thread `0` gets `f0` at the bottom of its stack. -/
def phantC (f0 : Frame) (c : Cfg) : Cfg := { c with ths := c.ths.modify 0 (app f0) }

theorem phantC_get (f0 : Frame) (c : Cfg) (j : Nat) :
    (phantC f0 c).ths[j]? = if j = 0 then (c.ths[j]?).map (app f0) else c.ths[j]? := by
  simp only [phantC]
  split
  · subst_vars; simp [Array.getElem?_modify]
  · rename_i hj; simp [Array.getElem?_modify, Ne.symm hj]

theorem phantC_size (f0 : Frame) (c : Cfg) : (phantC f0 c).ths.size = c.ths.size := by
  simp [phantC]

theorem gOf_phantC (p : Prog) (k : Promises.Knobs) (arch : Arch) (f0 : Frame) (c : Cfg) (i : Nat) :
    gOf p k arch (phantC f0 c) i = gOf p k arch c i := by
  simp [gOf, phantC, Cfg.n]

theorem cfg_ext {c d : Cfg} (hm : c.mem = d.mem) (hp : c.pairs = d.pairs) (hl : c.lbase = d.lbase)
    (hb : c.boxFence = d.boxFence) (hc : c.cap = d.cap) (hs : c.ths.size = d.ths.size)
    (ht : ∀ j : Nat, c.ths[j]? = d.ths[j]?) : c = d := by
  obtain ⟨_, _, ths, _, _, _⟩ := c; obtain ⟨_, _, ths', _, _, _⟩ := d
  simp only at *; subst_vars
  have : ths = ths' := Array.ext_getElem? ht
  subst this; rfl

theorem threadSteps_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {f0 : Frame} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) : phantC f0 c' ∈ threadSteps p k arch (phantC f0 c) i := by
  unfold threadSteps at h ⊢
  rw [gOf_phantC]
  cases hc : c.ths[i]? with
  | none => simp [hc] at h
  | some th =>
    simp only [hc, List.mem_map] at h
    obtain ⟨⟨m, ps, th'⟩, hm, rfl⟩ := h
    by_cases hi : i = 0
    · subst hi
      have : (phantC f0 c).ths[0]? = some (app f0 th) := by rw [phantC_get]; simp [hc]
      rw [this]; simp only [List.mem_map]
      refine ⟨(m, ps, app f0 th'), tstep_app' hm, ?_⟩
      apply cfg_ext <;> simp [phantC]
      intro j; rw [Array.getElem?_setIfInBounds, Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_setIfInBounds]
      by_cases hj : 0 = j <;> simp [hj]
    · have : (phantC f0 c).ths[i]? = some th := by rw [phantC_get]; simp [hc, hi]
      rw [this]; simp only [List.mem_map]
      refine ⟨(m, ps, th'), hm, ?_⟩
      apply cfg_ext <;> simp [phantC]
      intro j; rw [Array.getElem?_setIfInBounds, Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_setIfInBounds]
      by_cases hj : 0 = j
      · subst hj; simp [hi]
      · by_cases hij : i = j <;> simp [hj, hij]

theorem promise_phantC (f0 : Frame) (c : Cfg) (i : Nat) (a : WeakMem.Address) (v : WeakMem.Val) (w : Ts) :
    phantC f0 (promise c i a v w) = promise (phantC f0 c) i a v w := by
  unfold promise
  cases hc : c.ths[i]? with
  | none =>
    have : (phantC f0 c).ths[i]? = none := by rw [phantC_get]; split <;> simp [hc]
    simp [this]
  | some th =>
    have : (phantC f0 c).ths[i]? = some (if i = 0 then app f0 th else th) := by
      rw [phantC_get]; split <;> simp [hc]
    simp only [this]
    apply cfg_ext <;> simp [phantC]
    intro j; rw [Array.getElem?_setIfInBounds, Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_setIfInBounds]
    by_cases hj : 0 = j
    · subst hj; by_cases hi : i = 0 <;> simp [hi, app]
    · by_cases hij : i = j <;> simp [hj, hij]
      subst hij; simp [Ne.symm hj]

theorem noPromises_phantC (f0 : Frame) (c : Cfg) (i : Nat) : noPromises (phantC f0 c) i = noPromises c i := by
  unfold noPromises; rw [phantC_get]; split <;> (try cases c.ths[i]?) <;> rfl

theorem solo_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {f0 : Frame} {i : Nat} {c c'' : Cfg}
    (h : Solo p k arch i c c'') : Solo p k arch i (phantC f0 c) (phantC f0 c'') := by
  induction h with
  | refl c => exact .refl _
  | thread hc _ ih => exact .thread (threadSteps_phantC hc) ih
  | prom a v w hw _ ih =>
    rw [promise_phantC] at ih
    exact .prom a v w (by simpa [phantC] using hw) ih

theorem certified_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {f0 : Frame} {c : Cfg} {i : Nat}
    (h : Certified p k arch c i) : Certified p k arch (phantC f0 c) i := by
  obtain ⟨c', hs, hn⟩ := h
  exact ⟨phantC f0 c', solo_phantC hs, by rw [noPromises_phantC]; exact hn⟩

theorem step_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {f0 : Frame} {c c' : Cfg}
    (h : Step p k arch c c') : Step p k arch (phantC f0 c) (phantC f0 c') := by
  cases h with
  | thread i hc hcert => exact .thread i (threadSteps_phantC hc) (certified_phantC hcert)
  | prom i a v w hi hw hcert =>
    rw [promise_phantC]
    refine .prom i a v w (by simpa [phantC] using hi) (by simpa [phantC] using hw) ?_
    rw [← promise_phantC]; exact certified_phantC hcert

theorem steps_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {f0 : Frame} {c c' : Cfg}
    (h : TermStep.Steps p k arch c c') : TermStep.Steps p k arch (phantC f0 c) (phantC f0 c') := by
  induction h with
  | refl c => exact .refl _
  | step hs _ ih => exact .step (step_phantC hs) ih
end TermSpawnSim
