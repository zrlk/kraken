/-
**Source steps of a thread other than `main`** (the
worker's source half). ISA-generic. The one-thread source lemmas
(`Spike.Lib.SrcFrames`, `Spike.Lib.PrintSrc`) step thread 0 and use its
nonempty stack to know that `main` has not returned. A thread `i ≠ 0`
leaves thread 0 alone, so `mainExit` is unchanged by its steps and the
caller supplies `mainExit s = []` (the source machine's gate). A thread
with an outstanding promise also needs a certificate after each step
(`Certified`), which the lemmas take as a hypothesis; with no promise it
is the empty run (`certified_nil`).

- `getElem?_set!_ne`, `getElem?_set!_self`, `mainExit_congr`: thread 0
  is untouched, hence so is `mainExit`.
- `source_step_nil`: a step of thread `i` under WeakCore's hook that
  keeps thread 0's control and the event list is a source step with the
  empty trace.
- `tstep_source_i`: a `tstep` successor of thread `i ≠ 0` (memory and
  pairs may change), certified afterwards.
- `prom_source_i`: a promise step of thread `i ≠ 0`, certified
  afterwards.
- `certified_nil`, `certified_of_solo`, `localRunS_solo`: certificates.
- `localRunS_run_source_i`: a local run of thread `i ≠ 0`, with a
  certificate at its end.
- `emit_src_i`: `let x = emit a in e` of thread `i ≠ 0`, its trace the
  byte.
- `unpark_src_i`, `thrOfTid_extCfg`, `wake_unpark_get`: `let x = unpark a
  in e` of thread `i ≠ 0`, with the empty trace; when `a` names thread `j`,
  `j` gets a permit carrying the caller's release view.
-/
import Spike.Lib.PrintSrc

namespace Spike.Lib.WorkerSrcStep

open CoreLang CoreTerm TermRun TermExtStep
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib

variable {P : SrcParams} {p : Prog}

/-! ## Thread 0 and the trace -/

/-- Writing slot `i` keeps slot `j ≠ i`. -/
theorem getElem?_set!_ne {α : Type} (a : Array α) {i j : Nat} (h : i ≠ j) (x : α) : (a.set! i x)[j]? = a[j]? := by
  simp [Array.set!_eq_setIfInBounds, h]

/-- Writing an existing slot `i` reads back the new value. -/
theorem getElem?_set!_self {α : Type} {a : Array α} {i : Nat} {y : α} (h : a[i]? = some y) (x : α) :
    (a.set! i x)[i]? = some x := by
  have hi : i < a.size := (Array.getElem?_eq_some_iff.mp h).1
  simp [Array.set!_eq_setIfInBounds, hi]

/-- `mainExit` reads thread 0's term, stack and environment only. -/
theorem mainExit_congr {c c' : Cfg}
    (h : c'.ths[0]?.map (fun t => (t.term, t.stack, t.env)) = c.ths[0]?.map (fun t => (t.term, t.stack, t.env))) :
    mainExit c' = mainExit c := by
  unfold mainExit
  cases h1 : c'.ths[0]? <;> cases h2 : c.ths[0]? <;>
    simp only [h1, h2, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h ⊢
  obtain ⟨e1, e2, e3⟩ := h
  rw [e1, e2, e3]

/-- `mainExit_congr` when thread 0 is the same. -/
theorem mainExit_eq {c c' : Cfg} (h : c'.ths[0]? = c.ths[0]?) : mainExit c' = mainExit c :=
  mainExit_congr (by rw [h])

/-- **A silent step of thread `i`** under WeakCore's hook: a machine step or an
extern step of `i` that keeps thread 0's control and the event list, before
`main` has returned, is a source step with the empty trace. -/
theorem source_step_nil (hP : UsesWc P p) {s s' : Cfg} {i : Nat}
    (hst : StepBy p P.k P.arch i s s' ∨ P.hooks.ext i s s') (hex : mainExit s = [])
    (h0 : s'.ths[0]?.map (fun t => (t.term, t.stack, t.env)) = s.ths[0]?.map (fun t => (t.term, t.stack, t.env)))
    (htr : s'.trace = s.trace) :
    (source P p).step i s [] s' := by
  refine ⟨hex, hst.imp_right Or.inr, ?_⟩
  have e1 : mainExit s' = [] := (mainExit_congr h0).trans hex
  have e2 : P.hooks.trace s' = P.hooks.trace s := by rw [hP]; simp only [wcHooks, traceOf, htr]
  simp only [srcObs, hex, e1, List.append_nil, e2, List.drop_length]

/-! ## Certificates -/

/-- With no promise, the certificate is the empty run. -/
theorem certified_nil {k : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th : TTh}
    (hi : c.ths[i]? = some th) (hp : th.promises = []) : Certified p k arch c i :=
  ⟨c, .refl _, by simp [noPromises, hi, hp]⟩

/-- Solo runs compose. -/
theorem solo_trans {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat} {c c₁ c₂ : Cfg}
    (h₁ : Solo p k arch i c c₁) (h₂ : Solo p k arch i c₁ c₂) : Solo p k arch i c c₂ := by
  induction h₁ with
  | refl => exact h₂
  | thread hm _ ih => exact .thread hm (ih h₂)
  | prom a v w hw _ ih => exact .prom a v w hw (ih h₂)
  | ext hm _ ih => exact .ext hm (ih h₂)

/-- A solo run into a certified configuration certifies its start. -/
theorem certified_of_solo {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat} {c c₁ : Cfg}
    (h : Solo p k arch i c c₁) (hc : Certified p k arch c₁ i) : Certified p k arch c i := by
  obtain ⟨c₂, h₂, hn⟩ := hc
  exact ⟨c₂, solo_trans h h₂, hn⟩

/-- **A local run of thread `i` is a solo run** of `i`. -/
theorem localRunS_solo {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat} {c c' : Ctl}
    (h : LocalRunS p c c') :
    ∀ {s : Cfg} {th : TTh}, s.ths[i]? = some th → th.term = c.term → th.env = c.env → th.σs = [] →
      Solo p k arch i s { s with ths := s.ths.set! i { th with term := c'.term, env := c'.env } } := by
  induction h with
  | refl c =>
    intro s th hi ht he _
    have e1 : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    have e2 : s.ths.set! i th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [e1, e2]
    exact .refl _
  | @step c c₁ c' hs _ ih =>
    intro s th hi ht he hσ
    have hm := hs.mem_threadSteps (k := k) (arch := arch) hi ht he hσ
    have hi' := getElem?_set!_self hi { th with term := c₁.term, env := c₁.env }
    have h2 := ih (s := { s with ths := s.ths.set! i { th with term := c₁.term, env := c₁.env } }) hi' rfl rfl hσ
    simp only [set!_set!] at h2
    exact .thread hm h2

/-! ## Thread and promise steps of thread `i ≠ 0` -/

/-- **A `tstep` successor of thread `i ≠ 0`**, certified afterwards, before
`main` has returned, is a source step with the empty trace (memory and pairs
may change). -/
theorem tstep_source_i (hP : UsesWc P p) {s : Cfg} {i : Nat} {th th' : TTh} {mem' : WeakMem.Memory}
    {pairs' : List Nat} (hi0 : i ≠ 0) (hi : s.ths[i]? = some th)
    (h : (mem', pairs', th') ∈ tstep (gOf p P.k P.arch s i) s.mem s.pairs th)
    (hc : Certified p P.k P.arch { s with mem := mem', pairs := pairs', ths := s.ths.set! i th' } i)
    (hex : mainExit s = []) :
    (source P p).step i s [] { s with mem := mem', pairs := pairs', ths := s.ths.set! i th' } :=
  source_step_nil hP (.inl (.inl ⟨SrcMem.mem_threadSteps hi h, hc⟩)) hex
    (by simp only [getElem?_set!_ne _ hi0]) rfl

/-- `tstep_source_i` with no promise left. -/
theorem tstep_source_i_nil (hP : UsesWc P p) {s : Cfg} {i : Nat} {th th' : TTh} {mem' : WeakMem.Memory}
    {pairs' : List Nat} (hi0 : i ≠ 0) (hi : s.ths[i]? = some th)
    (h : (mem', pairs', th') ∈ tstep (gOf p P.k P.arch s i) s.mem s.pairs th) (hp : th'.promises = [])
    (hex : mainExit s = []) :
    (source P p).step i s [] { s with mem := mem', pairs := pairs', ths := s.ths.set! i th' } :=
  tstep_source_i hP hi0 hi h (certified_nil (getElem?_set!_self hi th') hp) hex

/-- `promise` leaves thread `j ≠ i` alone. -/
theorem promise_ths_ne (c : Cfg) {i j : Nat} (h : i ≠ j) (a : WeakMem.Address) (v : WeakMem.Val) (w : Nat) :
    (promise c i a v w).ths[j]? = c.ths[j]? := by
  unfold promise; split
  · rfl
  · simp only [getElem?_set!_ne _ h]

/-- **A promise step of thread `i ≠ 0`**, certified afterwards, before `main`
has returned, is a source step with the empty trace. -/
theorem prom_source_i (hP : UsesWc P p) {s : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : Nat}
    (hi0 : i ≠ 0) (hlt : i < s.ths.size) (hw : w < s.mem.size)
    (hc : Certified p P.k P.arch (promise s i a v w) i) (hex : mainExit s = []) :
    (source P p).step i s [] (promise s i a v w) :=
  source_step_nil hP (.inl (.inr ⟨a, v, w, hlt, hw, hc, rfl⟩)) hex
    (by rw [promise_ths_ne _ hi0]) (by unfold promise; split <;> rfl)

/-- **A local run of thread `i ≠ 0`**, certified at its end, before `main`
has returned, is a source run with the empty trace. -/
theorem localRunS_run_source_i (hP : UsesWc P p) {i : Nat} (hi0 : i ≠ 0) {c c' : Ctl} (h : LocalRunS p c c') :
    ∀ {s : Cfg} {th : TTh}, s.ths[i]? = some th → th.term = c.term → th.env = c.env → th.σs = [] →
      mainExit s = [] →
      Certified p P.k P.arch { s with ths := s.ths.set! i { th with term := c'.term, env := c'.env } } i →
      (source P p).Run s [] { s with ths := s.ths.set! i { th with term := c'.term, env := c'.env } } := by
  induction h with
  | refl c =>
    intro s th hi ht he _ _ _
    have e1 : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    have e2 : s.ths.set! i th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [e1, e2]
    exact .refl _
  | @step c c₁ c' hs hr ih =>
    intro s th hi ht he hσ hex hc
    let th₁ : TTh := { th with term := c₁.term, env := c₁.env }
    have hi' : ({ s with ths := s.ths.set! i th₁ } : Cfg).ths[i]? = some th₁ := getElem?_set!_self hi th₁
    have hsolo := localRunS_solo (k := P.k) (arch := P.arch) hr hi' rfl rfl hσ
    simp only [th₁, set!_set!] at hsolo
    have hc₁ := certified_of_solo hsolo hc
    have h1 : (source P p).step i s [] { s with ths := s.ths.set! i th₁ } :=
      tstep_source_i (mem' := s.mem) (pairs' := s.pairs) hP hi0 hi (by rw [hs.2 _ _ _ _ rfl ht he hσ]; exact List.mem_singleton.mpr rfl) hc₁
        hex
    have hex₁ : mainExit { s with ths := s.ths.set! i th₁ } = [] :=
      (mainExit_eq (by simp only [getElem?_set!_ne _ hi0])).trans hex
    have h2 := ih hi' rfl rfl hσ hex₁ (by simp only [th₁, set!_set!]; exact hc)
    simp only [th₁, set!_set!] at h2
    exact LRun.step ⟨i, h1⟩ h2

/-! ## Extern steps of thread `i ≠ 0` -/

/-- **`emit` of thread `i ≠ 0`** under WeakCore's hook, certified afterwards,
before `main` has returned and before any exit event: a source step whose
trace is the byte. -/
theorem emit_src_i (hP : UsesWc P p) {s : Cfg} {i : Nat} {th : TTh} {x : String} {a : At} {e : Expr} {rt : Ty}
    {w : Word} {b : Nat} (hi0 : i ≠ 0) (hi : s.ths[i]? = some th) (ht : th.term = .let_ x (.ext .emit a) e)
    (hp : th.promises = []) (ha : evalAt th.env a = some (rt, [w])) (hw : w.val = .num b)
    (hc : Certified p P.k P.arch (extCfg s i th x .emit e [w] []) i) (hex : mainExit s = [])
    (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s) :
    (source P p).step i s [.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩] (extCfg s i th x .emit e [w] []) := by
  refine ⟨hex, .inr (.inr ?_), ?_⟩
  · rw [hP]
    exact ⟨x, .emit, a, e, th, rt, [w], [], hi, ht, fun _ => hp, ha, rfl, hc, rfl⟩
  · have hex' : mainExit (extCfg s i th x .emit e [w] []) = [] :=
      (mainExit_eq (extCfg_ths_ne s th x .emit e [w] [] (Ne.symm hi0))).trans hex
    have htr : P.hooks.trace (extCfg s i th x .emit e [w] []) =
        P.hooks.trace s ++ [.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩] := by
      rw [hP]; simp [wcHooks, traceOf, extCfg, ExtName.events, hw, evOf]
    have hx' : ∀ c, Ev.exit c ∉ P.hooks.trace (extCfg s i th x .emit e [w] []) := by
      intro c hc; rw [htr] at hc; simp at hc; exact hx c hc
    simp only [srcObs, hex, hex', List.append_nil]
    rw [PrintSrc.cutAtExit_noExit hx', PrintSrc.cutAtExit_noExit hx, htr]
    simp

/-- `extCfg` keeps the thread a `ThreadId` word names (a non-`current` extern
keeps every thread's box and the thread count). -/
theorem thrOfTid_extCfg {c : Cfg} {i : Nat} {th : TTh} (hi : c.ths[i]? = some th) (x : String) {n : ExtName}
    (hn : n ≠ .current) (e : Expr) (ws rs : List Word) (w : Word) :
    thrOfTid (extCfg c i th x n e ws rs) w = thrOfTid c w := by
  have hsz : (extCfg c i th x n e ws rs).ths.size = c.ths.size := by
    unfold extCfg; split
    · exact absurd rfl hn
    · simp
  have hb : ∀ j : Nat, ((extCfg c i th x n e ws rs).ths[j]?.bind (fun t : TTh => t.tidLbl)) =
      (c.ths[j]?.bind (fun t : TTh => t.tidLbl)) := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [extCfg_ths_self hi x n e ws rs hn, hi]
      rfl
    · rw [extCfg_ths_ne c th x n e ws rs hj]
  unfold thrOfTid
  split
  · rw [hsz]; simp only [hb]
  · rfl

/-- **`unpark` of thread `i ≠ 0`** under WeakCore's hook, certified afterwards,
before `main` has returned: a source step with the empty trace (the wake
changes only a permit). -/
theorem unpark_src_i (hP : UsesWc P p) {s : Cfg} {i : Nat} {th : TTh} {x : String} {a : At} {e : Expr} {rt : Ty}
    {w : Word} (hi0 : i ≠ 0) (hi : s.ths[i]? = some th) (ht : th.term = .let_ x (.ext .unpark a) e)
    (ha : evalAt th.env a = some (rt, [w]))
    (hc : Certified p P.k P.arch (extCfg s i th x .unpark e [w] []) i) (hex : mainExit s = []) :
    (source P p).step i s [] (wake (extCfg s i th x .unpark e [w] []) i (relView th.vs) .unpark [w]) := by
  refine source_step_nil hP (.inr ?_) hex ?_ ?_
  · rw [hP]
    exact ⟨x, .unpark, a, e, th, rt, [w], [], hi, ht,
      fun h => by simp [ExtNeedsNoProm, CoreTerm.ExtName.isChoice] at h, ha, rfl, hc, rfl⟩
  · rcases wake_get (extCfg s i th x .unpark e [w] []) i (relView th.vs) .unpark [w] 0 with h | ⟨t, u, h1, h2⟩
    · rw [h, extCfg_ths_ne s th x .unpark e [w] [] (Ne.symm hi0)]
    · rw [h2]
      rw [extCfg_ths_ne s th x .unpark e [w] [] (Ne.symm hi0)] at h1
      rw [h1]
      rfl
  · rw [wake_trace]; simp [extCfg, ExtName.events]

/-- **The wake of `unpark`** when its word names thread `j ≠ i`: thread `j`
gets a permit carrying the caller's release view (joined with any permit
it had), and thread `i` moves to `e` binding `x` to ``. -/
theorem wake_unpark_get {s : Cfg} {i j : Nat} {th th0 : TTh} {x : String} {e : Expr} {w : Word}
    (hij : j ≠ i) (hi : s.ths[i]? = some th) (hj : s.ths[j]? = some th0) (hw : thrOfTid s w = some j) :
    (wake (extCfg s i th x .unpark e [w] []) i (relView th.vs) .unpark [w]).ths[j]? =
        some { th0 with permit := some (max (th0.permit.getD 0) (relView th.vs)) } ∧
      (wake (extCfg s i th x .unpark e [w] []) i (relView th.vs) .unpark [w]).ths[i]? =
        some { th with term := e, env := (x, ExtName.unpark.sig.2, []) :: th.env } := by
  have hw' : thrOfTid (extCfg s i th x .unpark e [w] []) w = some j := by
    rw [thrOfTid_extCfg hi x (by decide) e [w] [] w, hw]
  have hj' : (extCfg s i th x .unpark e [w] []).ths[j]? = some th0 := by
    rw [extCfg_ths_ne s th x .unpark e [w] [] hij, hj]
  have hi' := extCfg_ths_self hi x .unpark e [w] [] (by decide)
  simp only [wake, hw', hij, ite_false, setPermit, hj']
  refine ⟨getElem?_set!_self hj' _, ?_⟩
  rw [getElem?_set!_ne _ hij, hi']
  simp

end Spike.Lib.WorkerSrcStep
