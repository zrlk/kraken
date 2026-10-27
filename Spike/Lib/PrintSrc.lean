/-
**Source steps of the `print` loop** (`Spike.Test.PrintEmitLoop`): the
WeakCore model of hello1's `print` that loads each word of the slice, takes
its lanes and `emit`s them one byte at a time.

- `src_loadAt_step`: `let x = loadAt b i in e` on a one-word element can
  read the latest message of the element and bind its word.
- `localStepS_lane`: `let x = lane a j in e` is a local step.
- `tstep_source_mem`: a `tstep` successor of thread 0 that keeps memory and
  pairs and leaves no promise, inside a call, is a source step with the
  empty trace.
- `cutAtExit_noExit`: `cutAtExit` keeps an exit-free list.
- `emit_src_stack`: `let x = emit a in e` inside a call, before any exit
  event, is a source step whose trace is the byte.
- `printLD`, `printD`: the loop's declarations as terms; their agreement
  with the parsed `prog` is checked by `#guard`.
- `PrintAt`, `printN`: the loop invariant at `k` emitted bytes and the byte
  count `min n (8 * m)`.
- `print_entry`, `print_empty`: `print` enters the invariant at `k = 0`, or
  returns on an empty slice.
- `print_byte`: one byte of the loop, reading the latest message of the
  word, emits its lane and moves the invariant to `k + 1`.
- `print_done`: at `k = printN n m` the loop returns.
- `PrintC`, `print_entry_run`, `printC_entry`, `printC_load`, `printC_lane`,
  `printC_next`, `print_done_run`: the same loop between controls (`Ctl`,
  `LocalRunS`), for relating it to target code; `loadC`, `laneC`, `emitC`,
  `nextC` are the controls of one byte.
- `loadC_byte`: from the element load (`loadC`), reading the latest message
  of the byte's word (the premise `PrintMem` asks), the source emits the
  byte and lands at `nextC`: the source half of the output row's byte step.
-/
import Spike.Lib.SrcFrames
import Spike.Lib.SrcMem
import Spike.Test.PrintEmitLoop
import Spike.Lib.SrcEmit
import Spike.Lib.Hello1Src

namespace Spike.Lib.PrintSrc

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Scc.Sem.MemRel (SLatest)

/-! ## Steps -/

/-- **The source load of a one-word element**: at `let x = loadAt b i in
e` with the buffer word an untagged locative and the element one word, the
thread can read the latest message `j` of the element, binding its word;
memory and pairs stay. -/
theorem src_loadAt_step (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts) (th : TTh)
    {x : String} {b i : At} {e : Expr} {t ti : Ty} {pw : Word} {iws : List Word}
    {μ : Mode} {u : Ty} {sa : WeakMem.Address} {k j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.loadAt b i) e) (heb : evalAt th.env b = some (t, [pw]))
    (hei : evalAt th.env i = some (ti, iws)) (hpw : pw.val = .loc sa 0) (hbuf : bufElem t = some (μ, u))
    (hu : accs u = some [.one]) (hk : numOf iws = some k)
    (hj : SLatest mem (offs sa k) j) (hm : mem[j]? = some m) :
    ∃ th', (mem, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = th.promises ∧ th'.σs = th.σs ∧
      th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  have hk1 : offs sa (k * nWords [.one]) = offs sa k := by simp [nWords, Acc.size]
  obtain ⟨vs, hl⟩ := Spike.Lib.SrcMem.loadUnits_one g.arch pw false (stOf mem pairs th) hj hm
  refine ⟨⟨e, (x, u, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs, th.promises, th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, ?mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, heb, hei, hbuf, hk, addrOf, hpw, hu, hk1, List.mem_map]
    exact ⟨_, ⟨_, hl, rfl⟩, rfl⟩
  all_goals rfl

/-- **`lane` is a local step**: lane `jj mod 64/w` of the word. -/
theorem localStepS_lane {p : Prog} {c : Ctl} {x : String} {a j : At} {e : Expr} {sg : Bool} {w : Wd}
    {ws js : List Word} {tj : Ty} {n jj : Nat}
    (ht : c.term = .let_ x (.lane a j) e) (ha : evalAt c.env a = some (.lanes sg w, ws))
    (hn : numOf ws = some n) (hj : evalAt c.env j = some (tj, js)) (hjj : numOf js = some jj) :
    LocalStepS p c ⟨e, (x, .fix sg w, [cst (.num (laneN w n (jj % w.lanes)))]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [tstep, ht', ht, evalOp, he, ha, hn, hj, hjj, ol, withS, stOf, lanesOf]

/-! ## Source steps inside a call -/

variable {P : SrcParams} {p : Prog}

/-- **A `tstep` successor of thread 0 inside a call** that keeps memory and
pairs and leaves no promise is a source step with the empty trace, for every
hook that ignores the threads. -/
theorem tstep_source_mem (hT : TraceThs P) {s : Cfg} {th th' : TTh} (hi : s.ths[0]? = some th)
    (h : (s.mem, s.pairs, th') ∈ tstep (gOf p P.k P.arch s 0) s.mem s.pairs th)
    (hp : th'.promises = []) (hst : th.stack ≠ []) (hst' : th'.stack ≠ []) :
    (source P p).step 0 s [] { s with ths := s.ths.set! 0 th' } := by
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hi' : ({ s with ths := s.ths.set! 0 th' } : Cfg).ths[0]? = some th' := by simp [hlt]
  have hex := mainExit_of_stack hi hst
  have hex' := mainExit_of_stack hi' hst'
  have h1 : (source P p).step 0 s
      ((srcObs P.hooks.trace { s with ths := s.ths.set! 0 th' }).drop (srcObs P.hooks.trace s).length)
      { s with ths := s.ths.set! 0 th' } := by
    refine ⟨hex, .inl (.inl ⟨Spike.Lib.SrcMem.mem_threadSteps hi h, ⟨_, .refl _, ?_⟩⟩), rfl⟩
    simp [noPromises, hlt, hp]
  have e : ((srcObs P.hooks.trace { s with ths := s.ths.set! 0 th' }).drop
      (srcObs P.hooks.trace s).length : List Ev) = [] := by
    simp only [srcObs, hex, hex', List.append_nil]
    rw [hT s (s.ths.set! 0 th'), List.drop_length]
  rwa [e] at h1

/-- **`cutAtExit` keeps an exit-free list.** -/
theorem cutAtExit_noExit : ∀ {l : List Ev}, (∀ c, Ev.exit c ∉ l) → cutAtExit l = l
  | [], _ => rfl
  | e :: l, h => by
    have ih := cutAtExit_noExit (l := l) (fun c hc => h c (List.mem_cons_of_mem _ hc))
    cases e with
    | exit c => exact absurd (List.mem_cons_self ..) (h c)
    | _ => simp [cutAtExit, ih]

/-- **The extern step `emit` of thread 0 inside a call**, before any exit
event, under WeakCore's hook: a source step whose trace is the byte. -/
theorem emit_src_stack (hP : UsesWc P p) {s : Cfg} {th : TTh} {x : String} {a : At} {e : Expr} {rt : Ty}
    {w : Word} {b : Nat} (hi : s.ths[0]? = some th) (ht : th.term = .let_ x (.ext .emit a) e)
    (hp : th.promises = []) (hst : th.stack ≠ []) (ha : evalAt th.env a = some (rt, [w]))
    (hw : w.val = .num b) (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s) :
    (source P p).step 0 s [.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩] (extCfg s 0 th x .emit e [w] []) := by
  have h := Spike.Lib.SrcEmit.emit_src hP hi ht hp ha
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hi' : (extCfg s 0 th x .emit e [w] []).ths[0]? =
      some { th with term := e, env := (x, ExtName.emit.sig.2, []) :: th.env } := by
    simp [extCfg, hlt]
  have hex := mainExit_of_stack hi hst
  have hex' := mainExit_of_stack hi' hst
  have htr : P.hooks.trace (extCfg s 0 th x .emit e [w] []) =
      P.hooks.trace s ++ [.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩] := by
    rw [hP]; simp [wcHooks, traceOf, extCfg, ExtName.events, hw, evOf]
  have hx' : ∀ c, Ev.exit c ∉ P.hooks.trace (extCfg s 0 th x .emit e [w] []) := by
    intro c hc; rw [htr] at hc; simp at hc; exact hx c hc
  have e : ((srcObs P.hooks.trace (extCfg s 0 th x .emit e [w] [])).drop (srcObs P.hooks.trace s).length :
      List Ev) = [.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩] := by
    simp only [srcObs, hex, hex', List.append_nil]
    rw [cutAtExit_noExit hx', cutAtExit_noExit hx, htr]
    simp
  rwa [e] at h

/-! ## The loop -/

/-- The buffer type of `printL`'s argument: an owned, initialised byte-lane array of
`(i + 1) + d` words. -/
def bufTy : Ty :=
  .refine (.loc .own (.array (.add (.add (.var 1) (.lit 1)) (.var 0)) (.lanes false .w8)))
    (.ini (.add (.add (.var 1) (.lit 1)) (.var 0)))

/-- The argument type of `printL`: `(((buffer, i), d), ((c, n), j))`. -/
def printLTy : Ty :=
  .prod (.prod (.prod bufTy (.intS (.var 1))) (.intS (.var 0))) (.prod (.prod .int .int) .int)

/-- The word advance of `printL` (`j = 8`, `d ≠ 0`): step to the next word with `j = 0`. -/
def printAdv : Expr :=
  .let_ "d1" (.sub (.var "dv") (.lit 1)) <| .let_ "un" (.nameI (.var "d1")) <|
  .let_ "i1" (.add (.var "iv") (.lit 1)) <| .let_ "jn" (.nameI (.var "i1")) <|
  .let_ "bi1" (.pair (.var "b") (.var "jn")) <| .let_ "w1" (.pair (.var "bi1") (.var "un")) <|
  .let_ "z" (.atom (.lit 0)) <| .let_ "q1" (.pair (.var "cn") (.var "z")) <|
  .let_ "a1" (.pair (.var "w1") (.var "q1")) <| .tail "printL" ["jn", "un"] (.var "a1") []

/-- The byte advance of `printL`: bump `c` and `j` and call `printL` again. -/
def printNext : Expr :=
  .let_ "c1" (.add (.var "c") (.lit 1)) <| .let_ "j1" (.add (.var "j") (.lit 1)) <|
  .let_ "cn1" (.pair (.var "c1") (.var "n")) <| .let_ "q1" (.pair (.var "cn1") (.var "j1")) <|
  .let_ "bi2" (.pair (.var "b") (.var "iv")) <| .let_ "w2" (.pair (.var "bi2") (.var "dv")) <|
  .let_ "a1" (.pair (.var "w2") (.var "q1")) <| .tail "printL" ["i", "d"] (.var "a1") []

/-- `let r = emit x in printNext`. -/
def printEmit : Expr := .let_ "r" (.ext .emit (.var "x")) printNext
/-- `let x = lane wd j in printEmit`. -/
def printLane : Expr := .let_ "x" (.lane (.var "wd") (.var "j")) printEmit
/-- `let wd = loadAt b iv in printLane`. -/
def printLoad : Expr := .let_ "wd" (.loadAt (.var "b") (.var "iv")) printLane

/-- The body of `printL`: stop at `c = n`; at `j = 8` stop on the last word or advance a word;
otherwise load the word and emit lane `j`. -/
def printLBody : Expr :=
  .split (.var "a") "w" "q" <| .split (.var "w") "bi" "dv" <| .split (.var "bi") "b" "iv" <|
  .split (.var "q") "cn" "j" <| .split (.var "cn") "c" "n" <|
  .ifeq (.var "c") (.var "n") (.ret .unit) <|
  .ifeq (.var "j") (.lit 8) (.ifeq (.var "dv") (.lit 0) (.ret .unit) printAdv) printLoad

/-- The `printL` declaration of `Spike.Test.PrintEmitLoop.prog` (checked by the `#guard` below). -/
def printLD : Decl :=
  { name := "printL", idx := ["i", "d"], arg := "a", argTy := printLTy, retTy := .unit, body := printLBody }

/-- The body of `print`: stop on an empty slice, otherwise call `printL` at word 0, byte 0. -/
def printBody : Expr :=
  .split (.var "a") "bm" "n" <| .split (.var "bm") "b" "mv" <|
  .ifeq (.var "mv") (.lit 0) (.ret .unit) <|
  .let_ "m1" (.sub (.var "mv") (.lit 1)) <| .let_ "mn" (.nameI (.var "m1")) <|
  .let_ "z" (.nameI (.lit 0)) <| .let_ "bi" (.pair (.var "b") (.var "z")) <|
  .let_ "w" (.pair (.var "bi") (.var "mn")) <| .let_ "c0" (.atom (.lit 0)) <|
  .let_ "j0" (.atom (.lit 0)) <| .let_ "cn" (.pair (.var "c0") (.var "n")) <|
  .let_ "q" (.pair (.var "cn") (.var "j0")) <| .let_ "a1" (.pair (.var "w") (.var "q")) <|
  .tail "printL" ["z", "mn"] (.var "a1") []

/-- The `print` declaration of `Spike.Test.PrintEmitLoop.prog` (checked by the `#guard` below). -/
def printD : Decl :=
  { name := "print", idx := ["m"], arg := "a", argTy := Hello1Src.sliceTy, retTy := .unit, body := printBody }

#guard reprStr [printLD, printD] == reprStr Spike.Test.PrintEmitLoop.prog

/-- The environment of `printL`'s body on entry: the argument words `ws`. -/
def topEnv (ws : List Word) : Env := [("a", printLTy, ws)]

/-- **Word advance**: from the top of `printL` at `c ≠ n`, `j = 8`, `d ≠ 0`, the thread runs
locally back to the top with `i + 1`, `d - 1`, `j = 0`. -/
theorem adv_run (hd : p.find? (·.name == "printL") = some printLD)
    {pw wiv wdv wc wn wj : Word} {k n dv : Nat}
    (hc : wc.val = .num k) (hn : wn.val = .num n) (hkn : k ≠ n) (hj : wj.val = .num 8)
    (hdv : wdv.val = .num dv) (hdv0 : dv ≠ 0) :
    LocalRunS p ⟨printLBody, topEnv [pw, wiv, wdv, wc, wn, wj], none⟩
      ⟨printLBody, topEnv [pw, addW wiv (cst (.num 1)), subW wdv (cst (.num 1)), wc, wn, cst (.num 0)], none⟩ := by
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_ifeq_ne rfl rfl rfl hc hn hkn) ?_
  refine .step (localStepS_ifeq_eq rfl rfl rfl hj rfl) ?_
  refine .step (localStepS_ifeq_ne rfl rfl rfl hdv rfl hdv0) ?_
  refine .step (localStepS_sub rfl rfl rfl) ?_
  refine .step (localStepS_nameI rfl rfl) ?_
  refine .step (localStepS_add rfl rfl rfl) ?_
  refine .step (localStepS_nameI rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  refine .step (localStepS_atom rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  exact .single (localStepS_tail rfl hd rfl)

/-- The environment of `printL`'s body after its five `split`s. -/
def loadEnv (w0 w1 w2 w3 w4 w5 : Word) : Env :=
  [("n", .int, [w4]), ("c", .int, [w3]), ("j", .int, [w5]), ("cn", .prod .int .int, [w3, w4]),
   ("iv", .intS (.var 1), [w1]), ("b", bufTy, [w0]), ("dv", .intS (.var 0), [w2]),
   ("bi", .prod bufTy (.intS (.var 1)), [w0, w1]), ("q", .prod (.prod .int .int) .int, [w3, w4, w5]),
   ("w", .prod (.prod bufTy (.intS (.var 1))) (.intS (.var 0)), [w0, w1, w2]),
   ("a", printLTy, [w0, w1, w2, w3, w4, w5])]

/-- **To the load**: from the top of `printL` at `c ≠ n`, `j ≠ 8`, the thread runs locally to
the `loadAt`. -/
theorem body_load {w0 w1 w2 w3 w4 w5 : Word} {k n j : Nat}
    (hc : w3.val = .num k) (hn : w4.val = .num n) (hkn : k ≠ n) (hj : w5.val = .num j) (hj8 : j ≠ 8) :
    LocalRunS p ⟨printLBody, topEnv [w0, w1, w2, w3, w4, w5], none⟩ ⟨printLoad, loadEnv w0 w1 w2 w3 w4 w5, none⟩ := by
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_ifeq_ne rfl rfl rfl hc hn hkn) ?_
  exact .single (localStepS_ifeq_ne rfl rfl rfl hj rfl hj8)

/-- **Byte advance**: after the `emit`, the thread runs locally back to the top of `printL`
with `c + 1`, `j + 1`. -/
theorem next_run (hd : p.find? (·.name == "printL") = some printLD) {w0 w1 w2 w3 w4 w5 mw xw : Word} :
    LocalRunS p ⟨printNext, ("r", .unit, []) :: ("x", .fix false .w8, [xw]) :: ("wd", .lanes false .w8, [mw]) ::
        loadEnv w0 w1 w2 w3 w4 w5, none⟩
      ⟨printLBody, topEnv [w0, w1, w2, addW w3 (cst (.num 1)), w4, addW w5 (cst (.num 1))], none⟩ := by
  refine .step (localStepS_add rfl rfl rfl) ?_
  refine .step (localStepS_add rfl rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  refine .step (localStepS_pair rfl rfl rfl) ?_
  exact .single (localStepS_tail rfl hd rfl)

/-- `printL`'s argument words at word `i`, `dv` words left, byte count `c` and lane `j`. -/
def printArgs (pw wn : Word) (i dv c j : Nat) : List Word :=
  [pw, cst (.num i), cst (.num dv), cst (.num c), wn, cst (.num j)]

/-- Writing thread 0 of a configuration whose thread 0 exists. -/
theorem set0 {s : Cfg} {th th' : TTh} (hi : s.ths[0]? = some th) :
    ({ s with ths := s.ths.set! 0 th' } : Cfg).ths[0]? = some th' := by
  simp [(Array.getElem?_eq_some_iff.mp hi).1]

/-- An exit-free trace gives an exit-free hook trace under the write-cell hooks. -/
theorem noExit_hook (hP : UsesWc P p) {s : Cfg} (hx : ∀ x, Event.exit x ∉ s.trace) :
    ∀ c, Ev.exit c ∉ P.hooks.trace s := by
  rw [hP]
  simp only [wcHooks, traceOf, List.mem_filterMap, not_exists, not_and]
  intro c e he hev
  cases e <;> simp [evOf] at hev
  exact hx _ he

/-- **One byte inside a word** (`j ≠ 8`): from the top of `printL`, reading the latest
message of word `i`, the source emits lane `j` of its value and returns to the top with
`c + 1`, `j + 1`; only thread 0 and the trace change. -/
theorem print_byte_lt (hP : UsesWc P p) (hd : p.find? (·.name == "printL") = some printLD)
    {s : Cfg} {th : TTh} {pw wn : Word} {l n i dv c j jm v : Nat} {msg : WeakMem.Msg}
    (hi : s.ths[0]? = some th) (ht : th.term = printLBody)
    (he : th.env = topEnv (printArgs pw wn i dv c j)) (hσ : th.σs = []) (hst : th.stack ≠ [])
    (hp : th.promises = []) (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hwn : wn.val = .num n) (hcn : c ≠ n)
    (hj : j ≠ 8) (hx : ∀ x, Event.exit x ∉ s.trace)
    (hcell : SLatest s.mem ⟨l, i⟩ jm) (hm : s.mem[jm]? = some msg) (hv : msg.val = .num v) :
    ∃ th', (source P p).Run s [.out ⟨laneN .w8 v (j % 8) % 256, Nat.mod_lt _ (by decide)⟩]
        { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out (laneN .w8 v (j % 8))] } ∧
      th'.term = printLBody ∧ th'.env = topEnv (printArgs pw wn i dv (c + 1) (j + 1)) ∧ th'.σs = [] ∧
      th'.stack = th.stack ∧ th'.promises = [] := by
  have hT := traceThs_wc hP
  have r1 := (body_load (p := p) (w0 := pw) (w1 := cst (.num i)) (w2 := cst (.num dv)) (w3 := cst (.num c))
    (w5 := cst (.num j)) rfl hwn hcn rfl hj).run_source hT hi ht he hσ hst hp
  have hi1 := set0 (th' := { th with term := printLoad, env := (loadEnv pw (cst (.num i)) (cst (.num dv))
    (cst (.num c)) wn (cst (.num j))) }) hi
  have hc' : SLatest s.mem (offs ⟨l, 0⟩ i) jm := by simpa [offs] using hcell
  obtain ⟨th2, h2, ht2, he2, hp2, hσ2, hst2, hn2⟩ := src_loadAt_step (gOf p P.k P.arch _ 0) s.mem s.pairs
    { th with term := printLoad, env := (loadEnv pw (cst (.num i)) (cst (.num dv)) (cst (.num c)) wn (cst (.num j))) }
    (x := "wd") (b := .var "b") (i := .var "iv") (e := printLane) (t := bufTy) (pw := pw)
    (iws := [cst (.num i)]) (μ := .own) (u := .lanes false .w8) (sa := ⟨l, 0⟩) (k := i)
    rfl rfl rfl hpw rfl rfl rfl hc' hm
  have step2 := tstep_source_mem hT hi1 h2 (hp2.trans hp) hst (hst2 ▸ hst)
  have hi2 := set0 (th' := th2) hi1
  have l3 := localStepS_lane (p := p) (c := ⟨printLane, th2.env, none⟩) (n := v) (jj := j) rfl
    (by rw [he2]; rfl) (by simp [numOf, hv]) (by rw [he2]; rfl) rfl
  have r3 := (LocalRunS.single l3).run_source hT hi2 ht2 rfl (hσ2.trans hσ) (hst2 ▸ hst) (hp2.trans hp)
  have hi3 := set0 (th' := { th2 with term := printEmit, env := (("x", .fix false .w8,
    [cst (.num (laneN .w8 v (j % Wd.lanes .w8)))]) :: th2.env) }) hi2
  have step4 := emit_src_stack hP hi3 rfl (hp2.trans hp) (hst2 ▸ hst) rfl rfl (noExit_hook hP hx)
  have hi4 := TermExtStep.extCfg_ths_self hi3 "r" .emit printNext [cst (.num (laneN .w8 v (j % Wd.lanes .w8)))] []
    (by decide)
  have r5 := (next_run (p := p) hd (w0 := pw) (w1 := cst (.num i)) (w2 := cst (.num dv)) (w3 := cst (.num c))
    (w4 := wn) (w5 := cst (.num j)) (mw := ⟨msg.val, msg.view, jm⟩)
    (xw := cst (.num (laneN .w8 v (j % Wd.lanes .w8))))).run_source hT hi4 rfl
    (by show ("r", ExtName.emit.sig.2, []) :: _ :: th2.env = _; rw [he2]; rfl)
    (hσ2.trans hσ) (hst2 ▸ hst) (hp2.trans hp)
  have R := r1.trans (LRun.step ⟨0, step2⟩ (r3.trans (LRun.step ⟨0, step4⟩ r5)))
  simp only [List.nil_append, List.append_nil] at R
  refine ⟨{ th2 with term := printLBody, env := topEnv (printArgs pw wn i dv (c + 1) (j + 1)) }, ?_, rfl, rfl,
    hσ2.trans hσ, hst2, hp2.trans hp⟩
  simp only [extCfg, set!_set!, ExtName.events] at R
  exact R

/-- The number of bytes `print` emits: `n`, capped by the `8 * m` bytes of the slice. -/
def printN (n m : Nat) : Nat := min n (8 * m)

/-- **The loop invariant**: thread 0 is at the top of `printL` on frames `fs` with `k` bytes
emitted (`k = 8 * i + j`, `j ≤ 8`, `i < m`), the buffer word `pw` points at the start of
location `l`, `wn` holds `n`, and the trace has no exit. -/
def PrintAt (fs : List Frame) (pw wn : Word) (l n m k : Nat) (s : Cfg) : Prop :=
  ∃ th i j, s.ths[0]? = some th ∧ th.term = printLBody ∧ th.env = topEnv (printArgs pw wn i (m - 1 - i) k j) ∧
    th.σs = [] ∧ th.stack = fs ∧ th.promises = [] ∧ k = 8 * i + j ∧ j ≤ 8 ∧ i < m ∧
    pw.val = .loc ⟨l, 0⟩ 0 ∧ wn.val = .num n ∧ ∀ x, Event.exit x ∉ s.trace

/-- **One byte of the loop**: below `printN n m`, reading the latest message of cell
`⟨l, k / 8⟩`, the source emits lane `k % 8` of its value and the invariant moves to
`k + 1`; the configuration changes only in thread 0 and the trace (memory is kept). A
pending word advance (`j = 8`) is taken first. -/
theorem print_byte (hP : UsesWc P p) (hd : p.find? (·.name == "printL") = some printLD)
    {fs : List Frame} {pw wn : Word} {l n m k jm v : Nat} {msg : WeakMem.Msg} {s : Cfg} (hfs : fs ≠ [])
    (h : PrintAt fs pw wn l n m k s) (hk : k < printN n m)
    (hcell : SLatest s.mem ⟨l, k / 8⟩ jm) (hm : s.mem[jm]? = some msg) (hv : msg.val = .num v) :
    ∃ th', (source P p).Run s [.out ⟨laneN .w8 v (k % 8) % 256, Nat.mod_lt _ (by decide)⟩]
        { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out (laneN .w8 v (k % 8))] } ∧
      PrintAt fs pw wn l n m (k + 1)
        { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out (laneN .w8 v (k % 8))] } := by
  obtain ⟨th, i, j, hi, ht, he, hσ, hst, hp, rfl, hj8, him, hpw, hwn, hx⟩ := h
  have hT := traceThs_wc hP
  have hkn : 8 * i + j ≠ n := by unfold printN at hk; omega
  have hx' : ∀ b, ∀ x, Event.exit x ∉ s.trace ++ [Event.out b] := by
    intro b x hx1; simp at hx1; exact hx x hx1
  by_cases hj : j = 8
  · subst hj
    have hdv : m - 1 - i ≠ 0 := by unfold printN at hk; omega
    have r0 := (adv_run (p := p) hd (pw := pw) (wiv := cst (.num i)) (wdv := cst (.num (m - 1 - i)))
      (wc := cst (.num (8 * i + 8))) (wn := wn) (wj := cst (.num 8)) rfl hwn hkn rfl rfl hdv).run_source
      hT hi ht he hσ (hst ▸ hfs) hp
    have hi1 := set0 (th' := { th with term := printLBody, env := (topEnv [pw, addW (cst (.num i)) (cst (.num 1)),
      subW (cst (.num (m - 1 - i))) (cst (.num 1)), cst (.num (8 * i + 8)), wn, cst (.num 0)]) }) hi
    have he1 : topEnv [pw, addW (cst (.num i)) (cst (.num 1)), subW (cst (.num (m - 1 - i))) (cst (.num 1)),
        cst (.num (8 * i + 8)), wn, cst (.num 0)] =
        topEnv (printArgs pw wn (i + 1) (m - 1 - (i + 1)) (8 * i + 8) 0) := by
      have : m - 1 - i - 1 = m - 1 - (i + 1) := by omega
      simp only [topEnv, printArgs, addW, subW, cst, Promises.TVal.mk0, this]
    have hc1 : SLatest s.mem ⟨l, i + 1⟩ jm := by
      have : (8 * i + 8) / 8 = i + 1 := by omega
      rwa [this] at hcell
    obtain ⟨th', R1, ht', he', hσ', hst', hp'⟩ := print_byte_lt (P := P) (c := 8 * i + 8) (j := 0) hP hd hi1 rfl he1
      hσ (hst ▸ hfs) hp hpw hwn hkn (by decide) hx hc1 hm hv
    have R := r0.trans R1
    simp only [set!_set!, List.nil_append] at R
    have e8 : (8 * i + 8) % 8 = 0 % 8 := by omega
    rw [e8]
    refine ⟨th', R, th', i + 1, 1, set0 hi, ht', he', hσ', hst' ▸ hst, hp', by omega, by omega, ?_, hpw, hwn, hx' _⟩
    unfold printN at hk; omega
  · have hj' : j < 8 := by omega
    have hc1 : SLatest s.mem ⟨l, i⟩ jm := by
      have : (8 * i + j) / 8 = i := by omega
      rwa [this] at hcell
    obtain ⟨th', R, ht', he', hσ', hst', hp'⟩ := print_byte_lt (P := P) hP hd hi ht he hσ (hst ▸ hfs) hp hpw hwn
      hkn hj hx hc1 hm hv
    have ej : (8 * i + j) % 8 = j % 8 := by omega
    rw [ej]
    exact ⟨th', R, th', i, j + 1, set0 hi, ht', he', hσ', hst' ▸ hst, hp', by omega, by omega, him, hpw, hwn,
      hx' _⟩

/-- **Entry of `print`** on a nonempty slice: the source runs silently into the invariant at
`k = 0`, keeping the frames. -/
theorem print_entry (hT : TraceThs P) (hd : p.find? (·.name == "printL") = some printLD)
    {s : Cfg} {th : TTh} {pw wm wn : Word} {l n m : Nat}
    (hi : s.ths[0]? = some th) (ht : th.term = printBody) (he : th.env = [("a", Hello1Src.sliceTy, [pw, wm, wn])])
    (hσ : th.σs = []) (hst : th.stack ≠ []) (hp : th.promises = []) (hpw : pw.val = .loc ⟨l, 0⟩ 0)
    (hwm : wm.val = .num m) (hm0 : m ≠ 0) (hwn : wn.val = .num n) (hx : ∀ x, Event.exit x ∉ s.trace) :
    ∃ th', (source P p).Run s [] { s with ths := s.ths.set! 0 th' } ∧ th'.stack = th.stack ∧
      PrintAt th.stack pw wn l n m 0 { s with ths := s.ths.set! 0 th' } := by
  have hr : LocalRunS p ⟨printBody, [("a", Hello1Src.sliceTy, [pw, wm, wn])], none⟩
      ⟨printLBody, topEnv [pw, cst (.num 0), subW wm (cst (.num 1)), cst (.num 0), wn, cst (.num 0)], none⟩ := by
    refine .step (localStepS_split rfl rfl rfl) ?_
    refine .step (localStepS_split rfl rfl rfl) ?_
    refine .step (localStepS_ifeq_ne rfl rfl rfl hwm rfl hm0) ?_
    refine .step (localStepS_sub rfl rfl rfl) ?_
    refine .step (localStepS_nameI rfl rfl) ?_
    refine .step (localStepS_nameI rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_atom rfl rfl) ?_
    refine .step (localStepS_atom rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    exact .single (localStepS_tail rfl hd rfl)
  have he1 : topEnv [pw, cst (.num 0), subW wm (cst (.num 1)), cst (.num 0), wn, cst (.num 0)] =
      topEnv (printArgs pw wn 0 (m - 1 - 0) 0 0) := by
    simp [topEnv, printArgs, subW, hwm]
  refine ⟨_, hr.run_source hT hi ht he hσ hst hp, rfl, _, 0, 0, set0 hi, rfl, he1, hσ, rfl, hp, rfl, by omega,
    by omega, hpw, hwn, hx⟩

/-- **`print` on an empty slice** returns silently. -/
theorem print_empty (hT : TraceThs P) {s : Cfg} {th : TTh} {pw wm wn : Word}
    (hi : s.ths[0]? = some th) (ht : th.term = printBody) (he : th.env = [("a", Hello1Src.sliceTy, [pw, wm, wn])])
    (hσ : th.σs = []) (hst : th.stack ≠ []) (hp : th.promises = []) (hwm : wm.val = .num 0) :
    ∃ env, (source P p).Run s [] { s with ths := s.ths.set! 0 { th with term := .ret .unit, env := env } } := by
  have hr : ∃ env, LocalRunS p ⟨printBody, [("a", Hello1Src.sliceTy, [pw, wm, wn])], none⟩
      ⟨.ret .unit, env, none⟩ :=
    ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
      .single (localStepS_ifeq_eq rfl rfl rfl hwm rfl)⟩
  obtain ⟨env, hr⟩ := hr
  exact ⟨env, hr.run_source hT hi ht he hσ hst hp⟩

/-- **Exit of the loop**: at `k = printN n m` the source returns silently from `printL`. -/
theorem print_done (hT : TraceThs P) {fs : List Frame} {pw wn : Word} {l n m : Nat} {s : Cfg} (hfs : fs ≠ [])
    (h : PrintAt fs pw wn l n m (printN n m) s) :
    ∃ th env, s.ths[0]? = some th ∧ th.stack = fs ∧ th.promises = [] ∧ th.σs = [] ∧
      (source P p).Run s [] { s with ths := s.ths.set! 0 { th with term := .ret .unit, env := env } } := by
  obtain ⟨th, i, j, hi, ht, he, hσ, hst, hp, hk, hj8, him, hpw, hwn, hx⟩ := h
  suffices H : ∃ env, (source P p).Run s []
      { s with ths := s.ths.set! 0 { th with term := .ret .unit, env := env } } by
    obtain ⟨env, H⟩ := H; exact ⟨th, env, hi, hst, hp, hσ, H⟩
  by_cases hkn : printN n m = n
  · have hr : ∃ env, LocalRunS p ⟨printLBody, topEnv (printArgs pw wn i (m - 1 - i) (printN n m) j), none⟩
        ⟨.ret .unit, env, none⟩ :=
      ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .single (localStepS_ifeq_eq rfl rfl rfl rfl (by rw [hwn, hkn]))⟩
    obtain ⟨env, hr⟩ := hr
    exact ⟨env, hr.run_source hT hi ht he hσ (hst ▸ hfs) hp⟩
  · have h8 : printN n m = 8 * m := by unfold printN at *; omega
    have hj : j = 8 := by omega
    have hiv : m - 1 - i = 0 := by omega
    subst hj
    have hr : ∃ env, LocalRunS p ⟨printLBody, topEnv (printArgs pw wn i (m - 1 - i) (printN n m) 8), none⟩
        ⟨.ret .unit, env, none⟩ :=
      ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .step (localStepS_ifeq_ne rfl rfl rfl rfl hwn hkn) <|
        .step (localStepS_ifeq_eq rfl rfl rfl rfl rfl) <|
        .single (localStepS_ifeq_eq rfl rfl rfl (by rw [hiv]; rfl) rfl)⟩
    obtain ⟨env, hr⟩ := hr
    exact ⟨env, hr.run_source hT hi ht he hσ (hst ▸ hfs) hp⟩

/-! ## The loop at the control level

The same runs as `LocalRunS` between controls (`Ctl`), for a caller that relates them to
target code (`LocalRunS.toLocalRun`). A byte from `PrintC k` is `printC_load` (local, with
the pending word advance), the element load (not local: it reads memory), `printC_lane`,
the `emit` (an extern step binding `r`) and `printC_next` back to `PrintC (k + 1)`. -/

/-- **The loop invariant on a control**: at the top of `printL` with `k` bytes emitted
(`k = 8 * i + j`, `j ≤ 8`, `i < m`), no hold, and `wn` holding `n`. -/
def PrintC (pw wn : Word) (n m k : Nat) (c : Ctl) : Prop :=
  ∃ i j, c.term = printLBody ∧ c.env = topEnv (printArgs pw wn i (m - 1 - i) k j) ∧ c.hold = none ∧
    k = 8 * i + j ∧ j ≤ 8 ∧ i < m ∧ wn.val = .num n

/-- The control at `printL`'s element load for byte `k`: word `k / 8`, lane `k % 8`. -/
def loadC (pw wn : Word) (m k : Nat) : Ctl :=
  ⟨printLoad, loadEnv pw (cst (.num (k / 8))) (cst (.num (m - 1 - k / 8))) (cst (.num k)) wn
    (cst (.num (k % 8))), none⟩

/-- The control after the element load bound the word `mw`. -/
def laneC (pw wn : Word) (m k : Nat) (mw : Word) : Ctl :=
  ⟨printLane, ("wd", .lanes false .w8, [mw]) :: (loadC pw wn m k).env, none⟩

/-- The control at the `emit` of byte `b`. -/
def emitC (pw wn : Word) (m k : Nat) (mw : Word) (b : Nat) : Ctl :=
  ⟨printEmit, ("x", .fix false .w8, [cst (.num b)]) :: (laneC pw wn m k mw).env, none⟩

/-- The control after the `emit` (it binds `r` to `()`). -/
def nextC (pw wn : Word) (m k : Nat) (mw : Word) (b : Nat) : Ctl :=
  ⟨printNext, ("r", .unit, []) :: (emitC pw wn m k mw b).env, none⟩

/-- **Entry of `print`, as a local run**: on a nonempty slice, `print`'s body runs to the
top of `printL` at word 0, byte 0. -/
theorem print_entry_run (hd : p.find? (·.name == "printL") = some printLD) {pw wm wn : Word} {m : Nat}
    (hwm : wm.val = .num m) (hm0 : m ≠ 0) :
    LocalRunS p ⟨printBody, [("a", Hello1Src.sliceTy, [pw, wm, wn])], none⟩
      ⟨printLBody, topEnv (printArgs pw wn 0 (m - 1) 0 0), none⟩ := by
  have hr : LocalRunS p ⟨printBody, [("a", Hello1Src.sliceTy, [pw, wm, wn])], none⟩
      ⟨printLBody, topEnv [pw, cst (.num 0), subW wm (cst (.num 1)), cst (.num 0), wn, cst (.num 0)], none⟩ := by
    refine .step (localStepS_split rfl rfl rfl) ?_
    refine .step (localStepS_split rfl rfl rfl) ?_
    refine .step (localStepS_ifeq_ne rfl rfl rfl hwm rfl hm0) ?_
    refine .step (localStepS_sub rfl rfl rfl) ?_
    refine .step (localStepS_nameI rfl rfl) ?_
    refine .step (localStepS_nameI rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_atom rfl rfl) ?_
    refine .step (localStepS_atom rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    exact .single (localStepS_tail rfl hd rfl)
  have he1 : topEnv [pw, cst (.num 0), subW wm (cst (.num 1)), cst (.num 0), wn, cst (.num 0)] =
      topEnv (printArgs pw wn 0 (m - 1) 0 0) := by
    simp [topEnv, printArgs, subW, hwm]
  rw [he1] at hr
  exact hr

/-- The top of `printL` at word 0, byte 0 is `PrintC 0` on a nonempty slice. -/
theorem printC_entry {pw wn : Word} {n m : Nat} (hwn : wn.val = .num n) (hm0 : m ≠ 0) :
    PrintC pw wn n m 0 ⟨printLBody, topEnv (printArgs pw wn 0 (m - 1) 0 0), none⟩ :=
  ⟨0, 0, rfl, by simp, rfl, rfl, by omega, by omega, hwn⟩

/-- **Exit of the loop, as a local run**: at `k = printN n m`, `printL` runs to `ret ()`. -/
theorem print_done_run {pw wn : Word} {n m : Nat} {c : Ctl}
    (h : PrintC pw wn n m (printN n m) c) : ∃ env, LocalRunS p c ⟨.ret .unit, env, none⟩ := by
  obtain ⟨i, j, ht, he, hh, hk, hj8, him, hwn⟩ := h
  obtain ⟨t, e, h'⟩ := c
  simp only at ht he hh
  subst ht he hh
  by_cases hkn : printN n m = n
  · exact ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .single (localStepS_ifeq_eq rfl rfl rfl rfl (by rw [hwn, hkn]))⟩
  · have h8 : printN n m = 8 * m := by unfold printN at *; omega
    have hj : j = 8 := by omega
    have hiv : m - 1 - i = 0 := by omega
    subst hj
    exact ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
        .step (localStepS_split rfl rfl rfl) <| .step (localStepS_ifeq_ne rfl rfl rfl rfl hwn hkn) <|
        .step (localStepS_ifeq_eq rfl rfl rfl rfl rfl) <|
        .single (localStepS_ifeq_eq rfl rfl rfl (by rw [hiv]; rfl) rfl)⟩

/-- **To the element load**: below `printN n m`, from `PrintC k` the thread runs locally
(through a pending word advance) to the load of word `k / 8`. -/
theorem printC_load (hd : p.find? (·.name == "printL") = some printLD) {pw wn : Word} {n m k : Nat} {c : Ctl}
    (h : PrintC pw wn n m k c) (hk : k < printN n m) :
    LocalRunS p c (loadC pw wn m k) := by
  obtain ⟨i, j, ht, he, hh, rfl, hj8, him, hwn⟩ := h
  obtain ⟨t, e, h'⟩ := c
  simp only at ht he hh
  subst ht he hh
  have hkn : 8 * i + j ≠ n := by unfold printN at hk; omega
  by_cases hj : j = 8
  · subst hj
    have hdv : m - 1 - i ≠ 0 := by unfold printN at hk; omega
    have r0 := adv_run (p := p) hd (pw := pw) (wiv := cst (.num i)) (wdv := cst (.num (m - 1 - i)))
      (wc := cst (.num (8 * i + 8))) (wn := wn) (wj := cst (.num 8)) rfl hwn hkn rfl rfl hdv
    have r1 := body_load (p := p) (w0 := pw) (w1 := addW (cst (.num i)) (cst (.num 1)))
      (w2 := subW (cst (.num (m - 1 - i))) (cst (.num 1))) (w3 := cst (.num (8 * i + 8))) (w4 := wn)
      (w5 := cst (.num 0)) (k := 8 * i + 8) (j := 0) rfl hwn hkn rfl (by decide)
    have e1 : (8 * i + 8) / 8 = i + 1 := by omega
    have e2 : (8 * i + 8) % 8 = 0 := by omega
    have e3 : m - 1 - i - 1 = m - 1 - (i + 1) := by omega
    have R := r0.trans r1
    simp only [addW, subW, cst, Promises.TVal.mk0] at R
    simp only [loadC, e1, e2, cst]
    simp only [e3] at R
    exact R
  · have r1 := body_load (p := p) (w0 := pw) (w1 := cst (.num i)) (w2 := cst (.num (m - 1 - i)))
      (w3 := cst (.num (8 * i + j))) (w4 := wn) (w5 := cst (.num j)) rfl hwn hkn rfl hj
    have e1 : (8 * i + j) / 8 = i := by omega
    have e2 : (8 * i + j) % 8 = j := by omega
    simp only [loadC, e1, e2]
    exact r1

/-- **The lane**: after the load bound a word of value `v`, the thread takes lane `k % 8`
of it. -/
theorem printC_lane {pw wn mw : Word} {m k v : Nat} (hv : mw.val = .num v) :
    LocalStepS p (laneC pw wn m k mw) (emitC pw wn m k mw (laneN .w8 v (k % 8))) := by
  have h := localStepS_lane (p := p) (c := laneC pw wn m k mw) (n := v) (jj := k % 8) rfl rfl
    (by simp [numOf, hv]) rfl (by simp [numOf, cst, Promises.TVal.mk0])
  have e : k % 8 % Wd.lanes .w8 = k % 8 := by show k % 8 % 8 = k % 8; omega
  rw [e] at h
  exact h

/-- **After the `emit`**: the thread runs locally back to the top of `printL`, at
`PrintC (k + 1)`. -/
theorem printC_next (hd : p.find? (·.name == "printL") = some printLD) {pw wn mw : Word} {n m k b : Nat}
    (hwn : wn.val = .num n) (hk : k < printN n m) :
    ∃ c', LocalRunS p (nextC pw wn m k mw b) c' ∧ PrintC pw wn n m (k + 1) c' := by
  refine ⟨_, next_run (p := p) hd, k / 8, k % 8 + 1, rfl, ?_, rfl, by omega, by omega, ?_, hwn⟩
  · simp only [topEnv, printArgs, addW, cst, Promises.TVal.mk0]
  · unfold printN at hk; omega

/-! ## One byte from the element load, against the source memory -/

/-- **One byte of `print` from its element load**, for any buffer location
`l` and any program running `printL`: thread 0 at the load of byte `k`
(`loadC`), inside a call with no promise and no exit yet, and the word of
byte `k` with a latest message `j` holding `w (k / 8)` (the premise
`PrintMem` asks of each byte below its count, `Spike/Lib/SrcCalls.lean`).
The source reads that message, takes lane `k % 8` and emits it, as the
one event `.out` of `laneN .w8 (w (k / 8)) (k % 8)` (the byte
`printBytes w k 1` lists); thread 0 lands at `nextC` with the word read (the
number `w (k / 8)`) and that byte, memory and pairs kept. The source side of the output row's byte
step at a load of `print` (`hlb` of `print_call_segW`). -/
theorem loadC_byte (hP : UsesWc P p) {s : Cfg} {th : TTh} {pw wn : Word} {l m k : Nat} {w : Nat → Nat}
    (hi : s.ths[0]? = some th) (ht : th.term = (loadC pw wn m k).term) (he : th.env = (loadC pw wn m k).env)
    (hσ : th.σs = []) (hst : th.stack ≠ []) (hp : th.promises = []) (hpw : pw.val = .loc ⟨l, 0⟩ 0)
    (hx : ∀ x, Event.exit x ∉ s.trace)
    (hM : ∃ j msg, SLatest s.mem ⟨l, k / 8⟩ j ∧ s.mem[j]? = some msg ∧ msg.val = .num (w (k / 8))) :
    ∃ th' mw, (source P p).Run s [.out ⟨laneN .w8 (w (k / 8)) (k % 8) % 256, Nat.mod_lt _ (by decide)⟩]
        { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out (laneN .w8 (w (k / 8)) (k % 8))] } ∧
      th'.term = (nextC pw wn m k mw (laneN .w8 (w (k / 8)) (k % 8))).term ∧
      th'.env = (nextC pw wn m k mw (laneN .w8 (w (k / 8)) (k % 8))).env ∧ th'.σs = [] ∧
      th'.stack = th.stack ∧ th'.promises = [] ∧ mw.val = .num (w (k / 8)) ∧ th'.nalloc = th.nalloc := by
  obtain ⟨jm, msg, hcell, hm, hv⟩ := hM
  have hT := traceThs_wc hP
  have hc' : SLatest s.mem (offs ⟨l, 0⟩ (k / 8)) jm := by simpa [offs] using hcell
  obtain ⟨th2, h2, ht2, he2, hp2, hσ2, hst2, hn2⟩ := src_loadAt_step (gOf p P.k P.arch _ 0) s.mem s.pairs th
    (x := "wd") (b := .var "b") (i := .var "iv") (e := printLane) (t := bufTy) (pw := pw)
    (iws := [cst (.num (k / 8))]) (μ := .own) (u := .lanes false .w8) (sa := ⟨l, 0⟩) (k := k / 8)
    ht (by rw [he]; rfl) (by rw [he]; rfl) hpw rfl rfl rfl hc' hm
  have step2 := tstep_source_mem hT hi h2 (hp2.trans hp) hst (hst2 ▸ hst)
  have hi2 := set0 (th' := th2) hi
  have l3 := localStepS_lane (p := p) (c := ⟨printLane, th2.env, none⟩) (n := w (k / 8)) (jj := k % 8) rfl
    (by rw [he2]; rfl) (by simp [numOf, hv]) (by rw [he2, he]; rfl) rfl
  have r3 := (LocalRunS.single l3).run_source hT hi2 ht2 rfl (hσ2.trans hσ) (hst2 ▸ hst) (hp2.trans hp)
  have hi3 := set0 (th' := { th2 with term := printEmit, env := (("x", .fix false .w8,
    [cst (.num (laneN .w8 (w (k / 8)) (k % 8 % Wd.lanes .w8)))]) :: th2.env) }) hi2
  have step4 := emit_src_stack hP hi3 rfl (hp2.trans hp) (hst2 ▸ hst) rfl rfl (noExit_hook hP hx)
  have R := LRun.step ⟨0, step2⟩ (r3.trans (LRun.step ⟨0, step4⟩ (LRun.refl _)))
  simp only [List.nil_append, List.append_nil] at R
  have e8 : k % 8 % Wd.lanes .w8 = k % 8 := by show k % 8 % 8 = k % 8; omega
  simp only [extCfg, set!_set!, ExtName.events, e8] at R
  refine ⟨_, ⟨msg.val, msg.view, jm⟩, R, rfl, ?_, hσ2.trans hσ, hst2, hp2.trans hp, hv, ?_⟩
  · simp only [nextC, emitC, laneC, he2, he, cst]
    rfl
  · exact hn2

end Spike.Lib.PrintSrc
