/-
**Source runs across calls** under WeakCore's hook (`SrcSem.source P p`): the
top-level runs of `main` (an empty stack), the return out of a setup block into
`main`, and a whole call of the `print` extern, each for any program that
contains the declarations involved.

- `cutAtExit_append`: `cutAtExit` passes an exit-free prefix through.
- `tstep_source_exit`: a one-successor `tstep` of thread 0 before `main` has
  returned, with an exit-free hook trace, is a source step whose trace is
  `main`'s exit at the configuration it lands in.
- `ret_src`: `ret a` inside a call pops the top frame, as such a step.
- `LocalRunS.run_source_top`: a local run of thread 0 with an empty stack,
  from a control not at `ret`, is a source run whose trace is `main`'s exit at
  the configuration it lands in (`run_source_top_nil`: empty when the run does
  not end at `ret`).
- `setupCont`, `setup_ret_src`: the setup block's `ret` returns into the
  wrapper (`SrcSem.setupTerm`), which pairs the result with `me` and enters
  `main`'s body on the pair.
- `printBytes`, `outEvs`, `PrintMem`: the bytes of a slice read word by word,
  their observable events, and the memory premise (each word's latest message).
- `print_loop`: `r` bytes of the `print` loop.
- `call_print_src`: `let x = call print … a in e` runs to `e` with `x` bound,
  emitting the slice's `printN n m` bytes, then `main`'s exit if `e` is
  `main`'s `ret`; only thread 0 and the trace change.
-/
import Spike.Lib.PrintSrc

namespace Spike.Lib.SrcCalls

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.PrintSrc
open Scc.Sem.MemRel (SLatest)

/-- **`cutAtExit` passes an exit-free prefix through.** -/
theorem cutAtExit_append {l : List Ev} (m : List Ev) (hl : ∀ c, Ev.exit c ∉ l) :
    cutAtExit (l ++ m) = l ++ cutAtExit m := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have ih' := ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    cases e with
    | exit c => exact absurd (List.mem_cons_self ..) (hl c)
    | _ => simp [cutAtExit, ih']

variable {P : SrcParams} {p : Prog}

/-- One source step of thread 0 is a run. -/
theorem run_one {s s' : Cfg} {es : List Ev} (h : (source P p).step 0 s es s') : (source P p).Run s es s' := by
  have R := Scc.Sem.LRun.step (step := fun c es c' => ∃ i, (source P p).step i c es c') (tr := []) ⟨0, h⟩
    (.refl _)
  rwa [List.append_nil] at R

/-- **A one-successor `tstep` of thread 0** that keeps memory and pairs and
leaves no promise, before `main` has returned and with an exit-free hook
trace, is a source step whose trace is `main`'s exit at the configuration it
lands in (empty unless thread 0 lands at `ret` with an empty stack). -/
theorem tstep_source_exit (hT : TraceThs P) {s : Cfg} {th th' : TTh} (hi : s.ths[0]? = some th)
    (h : tstep (gOf p P.k P.arch s 0) s.mem s.pairs th = [(s.mem, s.pairs, th')])
    (hp : th'.promises = []) (hex : mainExit s = []) (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s) :
    (source P p).step 0 s (mainExit { s with ths := s.ths.set! 0 th' }) { s with ths := s.ths.set! 0 th' } := by
  have h1 := tstep_source_obs hi h hp hex
  have e : ((srcObs P.hooks.trace { s with ths := s.ths.set! 0 th' }).drop (srcObs P.hooks.trace s).length :
      List Ev) = mainExit { s with ths := s.ths.set! 0 th' } := by
    simp only [srcObs, hex, List.append_nil]
    rw [hT s (s.ths.set! 0 th'), cutAtExit_append _ hx, cutAtExit_noExit hx, cutAtExit_mainExit, List.drop_left]
  rwa [e] at h1

/-- Thread `th` after popping frame `fr` (frames `rest` below) with result words `ws`. -/
def popTh (th : TTh) (fr : Frame) (rest : List Frame) (ws : List Word) : TTh :=
  { th with term := fr.body, env := (fr.x, fr.ty, ws) :: fr.env, σs := fr.σs, stack := rest }

/-- **`ret a` inside a call**, with an exit-free hook trace: thread 0 pops the
top frame `fr` and continues with its body, `fr.x` bound to `a`'s words; the
trace is `main`'s exit at the landing configuration. -/
theorem ret_src (hT : TraceThs P) {s : Cfg} {th : TTh} {a : At} {fr : Frame} {rest : List Frame} {t : Ty}
    {ws : List Word} (hi : s.ths[0]? = some th) (ht : th.term = .ret a) (hst : th.stack = fr :: rest)
    (hp : th.promises = []) (ha : evalAt th.env a = some (t, ws)) (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s) :
    (source P p).step 0 s
      (mainExit { s with ths := s.ths.set! 0 (popTh th fr rest ws) })
      { s with ths := s.ths.set! 0 (popTh th fr rest ws) } :=
  tstep_source_exit hT hi (tstep_ret ht hst ha) hp (mainExit_of_stack hi (by rw [hst]; exact List.cons_ne_nil _ _))
    hx

/-- **A local run of thread 0 with an empty stack** (no type variables, no
promises, an exit-free hook trace), from a control not at `ret`, is a source
run whose trace is `main`'s exit at the configuration it lands in: `main`
returns at most at the last step, a thread at `ret` taking no local step. -/
theorem _root_.Spike.Lib.LocalRunS.run_source_top (hT : TraceThs P) {c c' : Ctl} (h : LocalRunS p c c') :
    ∀ {s : Cfg} {th : TTh}, s.ths[0]? = some th → th.term = c.term → th.env = c.env →
      th.σs = [] → th.stack = [] → th.promises = [] → (∀ a, c.term ≠ .ret a) →
      (∀ e, Ev.exit e ∉ P.hooks.trace s) →
      (source P p).Run s (mainExit { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } })
        { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } := by
  induction h with
  | refl c =>
    intro s th hi ht he _ _ _ hr _
    have : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    rw [this]
    have hs : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [hs, show ({ s with ths := s.ths } : Cfg) = s from rfl, mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h))]
    exact .refl _
  | @step c c₁ c' hs hrun ih =>
    intro s th hi ht he hσ hst hp hr hx
    have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hi' : ({ s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } : Cfg).ths[0]? =
        some { th with term := c₁.term, env := c₁.env } := by simp [hlt]
    have hex0 := mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h))
    have h1 := tstep_source_exit hT hi (hs.2 _ _ _ _ rfl ht he hσ) hp hex0 hx
    by_cases hr₁ : ∀ a, c₁.term ≠ .ret a
    · have hx' : ∀ e, Ev.exit e ∉
          P.hooks.trace { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } := by
        rw [hT]; exact hx
      have h2 := ih hi' rfl rfl hσ hst hp hr₁ hx'
      simp only [set!_set!] at h2
      rw [mainExit_of_not_ret hi' hr₁] at h1
      exact (run_one h1).trans h2
    · have hc' : c' = c₁ := by
        cases hrun with
        | refl => rfl
        | step hs' _ => exact absurd (localStep_not_ret hs'.toLocalStep) hr₁
      subst hc'
      exact run_one h1

/-- **A top-level local run that does not end at `ret`** is a source run with
the empty trace. -/
theorem _root_.Spike.Lib.LocalRunS.run_source_top_nil (hT : TraceThs P)
    {c c' : Ctl} (h : LocalRunS p c c') {s : Cfg} {th : TTh}
    (hi : s.ths[0]? = some th) (ht : th.term = c.term) (he : th.env = c.env) (hσ : th.σs = [])
    (hst : th.stack = []) (hp : th.promises = []) (hr : ∀ a, c.term ≠ .ret a) (hr' : ∀ a, c'.term ≠ .ret a)
    (hx : ∀ e, Ev.exit e ∉ P.hooks.trace s) :
    (source P p).Run s [] { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } := by
  have h1 := h.run_source_top hT hi ht he hσ hst hp hr hx
  rwa [mainExit_of_not_ret (th := { th with term := c'.term, env := c'.env }) (set0 hi) hr'] at h1

/-! ## The setup block's return -/

/-- The wrapper's continuation after the setup block returns into `r`: pair
`r` with `me` and enter `main` on the pair. -/
def setupCont : Expr := .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))

theorem setupTerm_eq : setupTerm = .let_ "r" (.call "rodata" [] (.var "u")) setupCont := rfl

/-- Thread `th` entering `d`'s body on the words `ws` with an empty stack. -/
def enterTop (th : TTh) (d : Decl) (ws : List Word) : TTh :=
  { th with term := d.body, env := [(d.arg, d.argTy, ws)], σs := [], stack := [] }

/-- **The setup block returns into `main`**: thread 0 at `ret a` on the
wrapper's frame alone (environment `fe` binding `me`, return type `rty`) pops
the frame, pairs `a`'s words with `me`'s and enters `main`'s body on the pair;
the trace is `main`'s exit at the landing configuration (empty unless `main`'s
body is a `ret`). -/
theorem setup_ret_src (hT : TraceThs P) {s : Cfg} {th : TTh} {a : At} {fe : Env} {rty t tm : Ty}
    {ws mws : List Word} {d : Decl} (hi : s.ths[0]? = some th) (ht : th.term = .ret a)
    (hst : th.stack = [⟨"r", setupCont, fe, [], rty⟩]) (hp : th.promises = [])
    (ha : evalAt th.env a = some (t, ws)) (hme : evalAt fe (.var "me") = some (tm, mws))
    (hd : p.find? (·.name == "main") = some d) (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s) :
    (source P p).Run s
      (mainExit { s with ths := s.ths.set! 0 (enterTop th d (ws ++ mws)) })
      { s with ths := s.ths.set! 0 (enterTop th d (ws ++ mws)) } := by
  have h0 := ret_src (p := p) hT hi ht hst hp ha hx
  have hnr : ∀ a', setupCont ≠ .ret a' := fun _ h => by cases h
  rw [mainExit_of_not_ret (set0 hi) hnr] at h0
  have hme' : evalAt (("r", rty, ws) :: fe) (.var "me") = some (tm, mws) := by
    simpa [evalAt, lookupE] using hme
  have r2 : LocalRunS p ⟨setupCont, ("r", rty, ws) :: fe, none⟩
      ⟨d.body, [(d.arg, d.argTy, ws ++ mws)], none⟩ :=
    .step (localStepS_pair rfl rfl hme') (.single (localStepS_tail rfl hd rfl))
  have hx' : ∀ c, Ev.exit c ∉ P.hooks.trace
      { s with ths := s.ths.set! 0 (popTh th ⟨"r", setupCont, fe, [], rty⟩ [] ws) } := by
    rw [hT]; exact hx
  have R := r2.run_source_top hT (set0 (th' := popTh th ⟨"r", setupCont, fe, [], rty⟩ [] ws) hi) rfl rfl rfl rfl
    hp hnr hx'
  have R' := (run_one h0).trans R
  simp only [set!_set!, List.nil_append] at R'
  exact R'

/-! ## A call of `print` -/

/-- The `r` bytes from byte `k` of a slice whose word `i` holds `w i`: lane
`k % 8` of word `k / 8`. -/
def printBytes (w : Nat → Nat) (k r : Nat) : List Nat :=
  (List.range' k r).map fun k => laneN .w8 (w (k / 8)) (k % 8)

/-- The observable output events of the bytes `bs`. -/
def outEvs (bs : List Nat) : List Ev := bs.map fun b => .out ⟨b % 256, Nat.mod_lt _ (by decide)⟩

/-- **The memory premise of `print`** on location `l`: for each of the first
`N` bytes, the cell of its word has a latest message `j`, whose value is the
number `w (k / 8)`. -/
def PrintMem (M : WeakMem.Memory) (l N : Nat) (w : Nat → Nat) : Prop :=
  ∀ k < N, ∃ j msg, SLatest M ⟨l, k / 8⟩ j ∧ M[j]? = some msg ∧ msg.val = .num (w (k / 8))

theorem printBytes_succ (w : Nat → Nat) (k r : Nat) :
    printBytes w k (r + 1) = laneN .w8 (w (k / 8)) (k % 8) :: printBytes w (k + 1) r := by
  simp [printBytes, List.range'_succ]

/-- **`r` bytes of the loop**: from the invariant at `k`, with `k + r` bytes
at most and the memory premise, the source emits the bytes `k … k + r - 1`
and reaches the invariant at `k + r`; only thread 0 and the trace change. -/
theorem print_loop (hP : UsesWc P p) (hd : p.find? (·.name == "printL") = some printLD)
    {fs : List Frame} {pw wn : Word} {l n m : Nat} {w : Nat → Nat} {M : WeakMem.Memory} (hfs : fs ≠ [])
    (hM : PrintMem M l (printN n m) w) :
    ∀ r k (s : Cfg), s.mem = M → k + r ≤ printN n m → PrintAt fs pw wn l n m k s →
      ∃ th', (source P p).Run s (outEvs (printBytes w k r))
          { s with ths := s.ths.set! 0 th', trace := s.trace ++ (printBytes w k r).map Event.out } ∧
        PrintAt fs pw wn l n m (k + r)
          { s with ths := s.ths.set! 0 th', trace := s.trace ++ (printBytes w k r).map Event.out } := by
  intro r
  induction r with
  | zero =>
    intro k s _ _ h
    obtain ⟨th, hi⟩ : ∃ th, s.ths[0]? = some th := by obtain ⟨th, -, -, hi, -⟩ := h; exact ⟨th, hi⟩
    have hs : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    have e : printBytes w k 0 = [] := rfl
    refine ⟨th, ?_, ?_⟩
    · rw [e, hs]; simp only [outEvs, List.map_nil, List.append_nil]; exact .refl _
    · rw [e, hs]; simpa using h
  | succ r ih =>
    intro k s hs hkr h
    obtain ⟨j, msg, hc, hm, hv⟩ := hM k (by omega)
    obtain ⟨th1, R1, h1⟩ := print_byte hP hd hfs h (by omega) (hs ▸ hc) (hs ▸ hm) hv
    obtain ⟨th2, R2, h2⟩ := ih (k + 1)
      { s with ths := s.ths.set! 0 th1, trace := s.trace ++ [.out (laneN .w8 (w (k / 8)) (k % 8))] } hs
      (by omega) h1
    refine ⟨th2, ?_, ?_⟩
    · have R := R1.trans R2
      simp only [printBytes_succ, outEvs, List.map_cons, set!_set!, List.append_assoc, List.singleton_append]
        at R ⊢
      exact R
    · rw [show k + (r + 1) = k + 1 + r by omega]
      simp only [set!_set!, List.append_assoc, List.singleton_append] at h2
      simp only [printBytes_succ, List.map_cons]
      exact h2

/-- Configuration `s` with thread 0 replaced by `th` and the bytes `bs` appended to its trace. -/
def outCfg (s : Cfg) (th : TTh) (bs : List Nat) : Cfg :=
  { s with ths := s.ths.set! 0 th, trace := s.trace ++ bs.map Event.out }

/-- **A call of `print`**: thread 0 at `let x = call print is a in e` (no type
variables, no promises, any frames below), `a` a slice `(b, m, n)` with `b`
the start of location `l`, the memory premise for its `printN n m` bytes and
an exit-free trace, runs to `e` with `x` bound to `()`, emitting those bytes,
then `main`'s exit if `e` is `main`'s `ret` (an empty stack). Memory and pairs
are kept; the trace grows by the bytes. -/
theorem call_print_src (hP : UsesWc P p) (hdp : p.find? (·.name == "print") = some printD)
    (hd : p.find? (·.name == "printL") = some printLD)
    {s : Cfg} {th : TTh} {x : String} {is : List String} {a : At} {e : Expr} {t : Ty} {pw wm wn : Word}
    {l n m : Nat} {w : Nat → Nat}
    (hi : s.ths[0]? = some th) (ht : th.term = .let_ x (.call "print" is a []) e) (hσ : th.σs = [])
    (hp : th.promises = []) (ha : evalAt th.env a = some (t, [pw, wm, wn]))
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hwm : wm.val = .num m) (hwn : wn.val = .num n)
    (hM : PrintMem s.mem l (printN n m) w) (hx : ∀ c, Event.exit c ∉ s.trace) :
    ∃ th', th'.term = e ∧ th'.env = (x, .unit, []) :: th.env ∧ th'.σs = [] ∧ th'.stack = th.stack ∧
      th'.promises = [] ∧
      (source P p).Run s (outEvs (printBytes w 0 (printN n m)) ++ mainExit (outCfg s th' (printBytes w 0 (printN n m))))
        (outCfg s th' (printBytes w 0 (printN n m))) := by
  have hT := traceThs_wc hP
  have h0 := tstep_call_nil (g := gOf p P.k P.arch s 0) (mem := s.mem) (pairs := s.pairs) ht hσ hdp ha
  have step0 := tstep_source hT hi h0 hp (mainExit_of_not_ret hi (fun a h => by rw [ht] at h; cases h))
    (mainExit_of_stack (set0 hi) (List.cons_ne_nil _ _))
  have hi1 := set0 (th' := { th with term := printD.body, env := [(printD.arg, printD.argTy, [pw, wm, wn])],
                                     stack := ⟨x, e, th.env, [], printD.retTy⟩ :: th.stack }) hi
  have hfs : (⟨x, e, th.env, [], printD.retTy⟩ :: th.stack : List Frame) ≠ [] := List.cons_ne_nil _ _
  by_cases hm0 : m = 0
  · subst hm0
    have hN : printN n 0 = 0 := by simp [printN]
    obtain ⟨env, R1⟩ := print_empty (p := p) hT hi1 rfl rfl hσ hfs hp hwm
    simp only [set!_set!] at R1
    have h5 := ret_src (p := p) (a := .unit) (ws := []) (t := .unit) (fr := ⟨x, e, th.env, [], printD.retTy⟩)
      (rest := th.stack) hT
      (set0 (th' := { th with term := .ret .unit, env := env, stack := ⟨x, e, th.env, [], printD.retTy⟩ :: th.stack })
        hi) rfl rfl hp rfl (noExit_hook hP hx)
    refine ⟨popTh { th with term := .ret .unit, env := env, stack := ⟨x, e, th.env, [], printD.retTy⟩ :: th.stack }
      ⟨x, e, th.env, [], printD.retTy⟩ th.stack [], rfl, rfl, rfl, rfl, hp, ?_⟩
    have R := ((run_one step0).trans R1).trans (run_one h5)
    rw [hN]
    simp only [set!_set!, List.nil_append, List.append_nil] at R
    simp only [printBytes, List.range'_zero, List.map_nil, outEvs, List.append_nil, List.nil_append, outCfg]
    exact R
  · obtain ⟨th2, R1, hst2, hAt⟩ := print_entry hT hd hi1 rfl rfl hσ hfs hp hpw hwm hm0 hwn hx
    simp only [set!_set!] at R1 hAt
    obtain ⟨th3, R2, hAt3⟩ := print_loop (P := P) hP hd hfs hM (printN n m) 0
      { s with ths := s.ths.set! 0 th2 } rfl (by omega) hAt
    simp only [set!_set!, Nat.zero_add] at R2 hAt3
    have hx3 : ∀ c, Event.exit c ∉ s.trace ++ (printBytes w 0 (printN n m)).map Event.out := by
      intro c hc
      simp only [List.mem_append, List.mem_map] at hc
      rcases hc with hc | ⟨_, _, hc⟩
      · exact hx c hc
      · cases hc
    obtain ⟨th4, env4, hi4, hst4, hp4, -, R3⟩ := print_done hT hfs hAt3
    simp only [set!_set!] at R3
    have h5 := ret_src (p := p) (a := .unit) (ws := []) (t := .unit) hT
      (set0 (s := { s with trace := s.trace ++ (printBytes w 0 (printN n m)).map Event.out })
        (th' := { th4 with term := .ret .unit, env := env4 }) hi) rfl hst4 hp4 rfl (noExit_hook hP hx3)
    refine ⟨popTh { th4 with term := .ret .unit, env := env4 } ⟨x, e, th.env, [], printD.retTy⟩ th.stack [],
      rfl, rfl, rfl, rfl, hp4, ?_⟩
    have R := (run_one step0).trans (R1.trans (R2.trans (R3.trans (run_one h5))))
    simp only [set!_set!, List.nil_append] at R
    simp only [outCfg]
    exact R

end Spike.Lib.SrcCalls
