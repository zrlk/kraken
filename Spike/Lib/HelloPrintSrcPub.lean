/-
**Source steps of hello.w's published `print` loop** (C1, `PrintSrcPub`):
the twin of `Spike.Lib.PrintSrc` for `printL`/`print` on a **published**
slice, each word read by `let l = idx b iv in let wd = load l in …` (a
plain load of the element's locative) instead of `loadAt`, for the
worker, a thread `i ≠ 0` (`Spike.Lib.WorkerSrcStep`'s style: a thread
with an outstanding promise is certified after its steps).

The byte's memory premise is the word's latest message (the one
`SLatest`), as `PrintSrc.loadC_byte`'s; for the published buffer it holds
of the frozen source words (`Inv2Core.frzS`, `scov1`), a named premise
here.

- `bufTyP`, `printLTyP`, `printLoadP`, `printLBodyP`, `printLPD`, `printPD`:
  the declarations; the word and byte advances, the lane and the `emit`
  are `PrintSrc`'s terms (`printAdv`, `printNext`, `printLane`,
  `printEmit`), `print`'s body is `PrintSrc.printBody`; `printLPD_find`,
  `printPD_find`: they are `helloSrc`'s.
- `localStepS_idx`: `let x = idx b i in e` is a local step;
  `src_load_step`: `let x = load false l in e` on a one-word cell can read
  the latest message of the cell.
- `PrintCP`, `loadCP`, `ldCP`, `laneCP`, `emitCP`, `nextCP`: the loop
  between controls (`LocalRunS`), as `PrintSrc.PrintC` …; `printP_entry_run`,
  `printCP_entry`, `printP_done_run`, `printCP_load`, `printCP_idx`,
  `printCP_lane`, `printCP_next`.
- `loadCP_byte_i`: thread `i ≠ 0` at the element's `idx` (`loadCP`), the
  word's latest message holding `w (k / 8)`: the `idx`, the load, the lane
  and the `emit` are a source run whose trace is the byte, landing at
  `nextCP`, once that landing is certified.
- `call_printP_i`, `ret_i`: the worker's `call print` (to `print`'s body,
  then `printP_entry_run`) and the return out of it, at thread `i ≠ 0`.
-/
import Spike.Lib.WorkerSrcStep
import Spike.Lib.SrcCalls
import Spike.Lib.HelloRodataSrc

namespace Spike.Lib.HelloPrintSrcPub

open CoreLang CoreTerm TermRun TermExtStep
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Spike.Lib.PrintSrc (printAdv printNext printEmit printLane printBody printArgs printN)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self getElem?_set!_ne mainExit_eq localRunS_solo localRunS_run_source_i
  certified_of_solo emit_src_i tstep_source_i)
open Scc.Sem.MemRel (SLatest)

/-! ## The declarations -/

/-- The buffer type of `printL`'s argument: a published, initialised
byte-lane array of `(i + 1) + d` words. -/
def bufTyP : Ty :=
  .refine (.loc .pub (.array (.add (.add (.var 1) (.lit 1)) (.var 0)) (.lanes false .w8)))
    (.ini (.add (.add (.var 1) (.lit 1)) (.var 0)))

/-- The argument type of `printL`: `(((buffer, i), d), ((c, n), j))`. -/
def printLTyP : Ty :=
  .prod (.prod (.prod bufTyP (.intS (.var 1))) (.intS (.var 0))) (.prod (.prod .int .int) .int)

/-- `let l = idx b iv in let wd = load l in printLane`. -/
def printLoadP : Expr := .let_ "l" (.idx (.var "b") (.var "iv")) (.let_ "wd" (.load false (.var "l")) printLane)

/-- The body of `printL`, as `PrintSrc.printLBody` with the element read by
`idx` and a plain load. -/
def printLBodyP : Expr :=
  .split (.var "a") "w" "q" <| .split (.var "w") "bi" "dv" <| .split (.var "bi") "b" "iv" <|
  .split (.var "q") "cn" "j" <| .split (.var "cn") "c" "n" <|
  .ifeq (.var "c") (.var "n") (.ret .unit) <|
  .ifeq (.var "j") (.lit 8) (.ifeq (.var "dv") (.lit 0) (.ret .unit) printAdv) printLoadP

/-- hello.w's `printL`. -/
def printLPD : Decl :=
  { name := "printL", idx := ["i", "d"], arg := "a", argTy := printLTyP, retTy := .unit, body := printLBodyP }

/-- hello.w's `print`, on the published slice. -/
def printPD : Decl :=
  { name := "print", idx := ["m"], arg := "a", argTy := HelloRodataSrc.sliceTyP, retTy := .unit, body := printBody }

theorem printLPD_find : HelloSrc.helloSrc.find? (·.name == "printL") = some printLPD := rfl

theorem printPD_find : HelloSrc.helloSrc.find? (·.name == "print") = some printPD := rfl

/-! ## Steps -/

/-- **`idx` is a local step**: element `j` of the buffer word's locative. -/
theorem localStepS_idx {p : Prog} {c : Ctl} {x : String} {b i : At} {e : Expr} {t ti : Ty} {pw : Word}
    {iws : List Word} {μ : Mode} {u : Ty} {us : List Acc} {a : WeakMem.Address} {gg j : Nat}
    (ht : c.term = .let_ x (.idx b i) e) (hb : evalAt c.env b = some (t, [pw]))
    (hi : evalAt c.env i = some (ti, iws)) (hj : numOf iws = some j) (hbuf : bufElem t = some (μ, u))
    (hu : accs u = some us) (hpw : pw.val = .loc a gg) :
    LocalStepS p c ⟨e, (x, .loc μ u, [{ pw with val := .loc (offs a (j * nWords us)) gg }]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [tstep, ht', ht, evalOp, he, hb, hi, hj, hbuf, hu, hpw, ol, withS, stOf]

/-- **The source load of a one-word cell**: at `let x = load false l in e`
with `l` a locative of a lanes cell, the thread can read the latest message
`j` of the cell, binding its word; memory and pairs stay (and the thread's
promises, stack, allocation count and box label). -/
theorem src_load_step (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts) (th : TTh)
    {x : String} {l : At} {e : Expr} {μ : Mode} {sg : Bool} {w : Wd} {pw : Word} {a : WeakMem.Address} {gg : Nat}
    {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.load false l) e) (hel : evalAt th.env l = some (.loc μ (.lanes sg w), [pw]))
    (hpw : pw.val = .loc a gg) (hj : SLatest mem a j) (hm : mem[j]? = some m) :
    ∃ th', (mem, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, .lanes sg w, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = th.promises ∧
      th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc ∧ th'.tidLbl = th.tidLbl := by
  obtain ⟨vs, hl⟩ := Spike.Lib.SrcMem.loadUnits_one g.arch pw false (stOf mem pairs th) hj hm
  refine ⟨⟨e, (x, .lanes sg w, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs, th.promises, th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit, th.tys⟩, ?mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, hel, cellOf, addrOf, hpw, wordOf, accs, List.mem_map]
    exact ⟨_, ⟨_, hl, rfl⟩, rfl⟩
  all_goals rfl

/-! ## The loop at the control level -/

variable {p : Prog}

/-- The environment of `printL`'s body on entry: the argument words `ws`. -/
def topEnvP (ws : List Word) : Env := [("a", printLTyP, ws)]

/-- The environment of `printL`'s body after its five `split`s. -/
def loadEnvP (w0 w1 w2 w3 w4 w5 : Word) : Env :=
  [("n", .int, [w4]), ("c", .int, [w3]), ("j", .int, [w5]), ("cn", .prod .int .int, [w3, w4]),
   ("iv", .intS (.var 1), [w1]), ("b", bufTyP, [w0]), ("dv", .intS (.var 0), [w2]),
   ("bi", .prod bufTyP (.intS (.var 1)), [w0, w1]), ("q", .prod (.prod .int .int) .int, [w3, w4, w5]),
   ("w", .prod (.prod bufTyP (.intS (.var 1))) (.intS (.var 0)), [w0, w1, w2]),
   ("a", printLTyP, [w0, w1, w2, w3, w4, w5])]

/-- **Word advance**: from the top of `printL` at `c ≠ n`, `j = 8`, `d ≠ 0`,
back to the top with `i + 1`, `d - 1`, `j = 0`. -/
theorem adv_run (hd : p.find? (·.name == "printL") = some printLPD)
    {pw wiv wdv wc wn wj : Word} {k n dv : Nat}
    (hc : wc.val = .num k) (hn : wn.val = .num n) (hkn : k ≠ n) (hj : wj.val = .num 8)
    (hdv : wdv.val = .num dv) (hdv0 : dv ≠ 0) :
    LocalRunS p ⟨printLBodyP, topEnvP [pw, wiv, wdv, wc, wn, wj], none⟩
      ⟨printLBodyP, topEnvP [pw, addW wiv (cst (.num 1)), subW wdv (cst (.num 1)), wc, wn, cst (.num 0)], none⟩ := by
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

/-- **To the element's `idx`**: from the top of `printL` at `c ≠ n`,
`j ≠ 8`. -/
theorem body_load {w0 w1 w2 w3 w4 w5 : Word} {k n j : Nat}
    (hc : w3.val = .num k) (hn : w4.val = .num n) (hkn : k ≠ n) (hj : w5.val = .num j) (hj8 : j ≠ 8) :
    LocalRunS p ⟨printLBodyP, topEnvP [w0, w1, w2, w3, w4, w5], none⟩
      ⟨printLoadP, loadEnvP w0 w1 w2 w3 w4 w5, none⟩ := by
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_split rfl rfl rfl) ?_
  refine .step (localStepS_ifeq_ne rfl rfl rfl hc hn hkn) ?_
  exact .single (localStepS_ifeq_ne rfl rfl rfl hj rfl hj8)

/-- **The loop invariant on a control**: at the top of `printL` with `k`
bytes emitted (`k = 8 * i + j`, `j ≤ 8`, `i < m`), no hold, `wn` holding
`n`. -/
def PrintCP (pw wn : Word) (n m k : Nat) (c : Ctl) : Prop :=
  ∃ i j, c.term = printLBodyP ∧ c.env = topEnvP (printArgs pw wn i (m - 1 - i) k j) ∧ c.hold = none ∧
    k = 8 * i + j ∧ j ≤ 8 ∧ i < m ∧ wn.val = .num n

/-- The control at `printL`'s element `idx` for byte `k`: word `k / 8`,
lane `k % 8`. -/
def loadCP (pw wn : Word) (m k : Nat) : Ctl :=
  ⟨printLoadP, loadEnvP pw (cst (.num (k / 8))) (cst (.num (m - 1 - k / 8))) (cst (.num k)) wn
    (cst (.num (k % 8))), none⟩

/-- The control at the load, `l` bound to the element's locative `lw`. -/
def ldCP (pw wn : Word) (m k : Nat) (lw : Word) : Ctl :=
  ⟨.let_ "wd" (.load false (.var "l")) printLane, ("l", .loc .pub (.lanes false .w8), [lw]) :: (loadCP pw wn m k).env,
    none⟩

/-- The control after the load bound the word `mw`. -/
def laneCP (pw wn : Word) (m k : Nat) (lw mw : Word) : Ctl :=
  ⟨printLane, ("wd", .lanes false .w8, [mw]) :: (ldCP pw wn m k lw).env, none⟩

/-- The control at the `emit` of byte `b`. -/
def emitCP (pw wn : Word) (m k : Nat) (lw mw : Word) (b : Nat) : Ctl :=
  ⟨printEmit, ("x", .fix false .w8, [cst (.num b)]) :: (laneCP pw wn m k lw mw).env, none⟩

/-- The control after the `emit` (it binds `r` to `()`). -/
def nextCP (pw wn : Word) (m k : Nat) (lw mw : Word) (b : Nat) : Ctl :=
  ⟨printNext, ("r", .unit, []) :: (emitCP pw wn m k lw mw b).env, none⟩

/-- The element's locative: word `i` of the buffer at the start of `l`. -/
def elemW (pw : Word) (l : WeakMem.AllocLabel) (i : Nat) : Word := { pw with val := .loc ⟨l, i⟩ 0 }

/-- **Entry of `print`, as a local run**: on a nonempty slice, `print`'s
body runs to the top of `printL` at word 0, byte 0. -/
theorem printP_entry_run (hd : p.find? (·.name == "printL") = some printLPD) {pw wm wn : Word} {m : Nat}
    (hwm : wm.val = .num m) (hm0 : m ≠ 0) :
    LocalRunS p ⟨printBody, [("a", HelloRodataSrc.sliceTyP, [pw, wm, wn])], none⟩
      ⟨printLBodyP, topEnvP (printArgs pw wn 0 (m - 1) 0 0), none⟩ := by
  have hr : LocalRunS p ⟨printBody, [("a", HelloRodataSrc.sliceTyP, [pw, wm, wn])], none⟩
      ⟨printLBodyP, topEnvP [pw, cst (.num 0), subW wm (cst (.num 1)), cst (.num 0), wn, cst (.num 0)], none⟩ := by
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
  have he1 : topEnvP [pw, cst (.num 0), subW wm (cst (.num 1)), cst (.num 0), wn, cst (.num 0)] =
      topEnvP (printArgs pw wn 0 (m - 1) 0 0) := by
    simp [topEnvP, printArgs, subW, hwm]
  rw [he1] at hr
  exact hr

/-- **`print` on an empty slice**, as a local run, returns. -/
theorem printP_empty_run {pw wm wn : Word} (hwm : wm.val = .num 0) :
    ∃ env, LocalRunS p ⟨printBody, [("a", HelloRodataSrc.sliceTyP, [pw, wm, wn])], none⟩ ⟨.ret .unit, env, none⟩ :=
  ⟨_, .step (localStepS_split rfl rfl rfl) <| .step (localStepS_split rfl rfl rfl) <|
    .single (localStepS_ifeq_eq rfl rfl rfl hwm rfl)⟩

/-- The top of `printL` at word 0, byte 0 is `PrintCP 0` on a nonempty slice. -/
theorem printCP_entry {pw wn : Word} {n m : Nat} (hwn : wn.val = .num n) (hm0 : m ≠ 0) :
    PrintCP pw wn n m 0 ⟨printLBodyP, topEnvP (printArgs pw wn 0 (m - 1) 0 0), none⟩ :=
  ⟨0, 0, rfl, by simp, rfl, rfl, by omega, by omega, hwn⟩

/-- **Exit of the loop, as a local run**: at `k = printN n m`, `printL` runs
to `ret ()`. -/
theorem printP_done_run {pw wn : Word} {n m : Nat} {c : Ctl}
    (h : PrintCP pw wn n m (printN n m) c) : ∃ env, LocalRunS p c ⟨.ret .unit, env, none⟩ := by
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

/-- **To the element's `idx`**: below `printN n m`, from `PrintCP k` the
thread runs locally (through a pending word advance) to `loadCP k`. -/
theorem printCP_load (hd : p.find? (·.name == "printL") = some printLPD) {pw wn : Word} {n m k : Nat} {c : Ctl}
    (h : PrintCP pw wn n m k c) (hk : k < printN n m) :
    LocalRunS p c (loadCP pw wn m k) := by
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
    simp only [loadCP, e1, e2, cst]
    simp only [e3] at R
    exact R
  · have r1 := body_load (p := p) (w0 := pw) (w1 := cst (.num i)) (w2 := cst (.num (m - 1 - i)))
      (w3 := cst (.num (8 * i + j))) (w4 := wn) (w5 := cst (.num j)) rfl hwn hkn rfl hj
    have e1 : (8 * i + j) / 8 = i := by omega
    have e2 : (8 * i + j) % 8 = j := by omega
    simp only [loadCP, e1, e2]
    exact r1

/-- **The element's `idx`**: with the buffer word at the start of `l`, `l`
gets word `k / 8`'s locative. -/
theorem printCP_idx {pw wn : Word} {m k : Nat} {l : WeakMem.AllocLabel} (hpw : pw.val = .loc ⟨l, 0⟩ 0) :
    LocalStepS p (loadCP pw wn m k) (ldCP pw wn m k (elemW pw l (k / 8))) := by
  have h := localStepS_idx (p := p) (c := loadCP pw wn m k) (x := "l") (b := .var "b") (i := .var "iv")
    (e := .let_ "wd" (.load false (.var "l")) printLane) (us := [.one]) (j := k / 8) rfl rfl rfl rfl rfl rfl hpw
  have e : offs ⟨l, 0⟩ (k / 8 * nWords [Acc.one]) = ⟨l, k / 8⟩ := by
    simp [offs, nWords, Acc.size]
  rw [e] at h
  exact h

/-- **The lane**: after the load bound a word of value `v`, the thread
takes lane `k % 8` of it. -/
theorem printCP_lane {pw wn lw mw : Word} {m k v : Nat} (hv : mw.val = .num v) :
    LocalStepS p (laneCP pw wn m k lw mw) (emitCP pw wn m k lw mw (laneN .w8 v (k % 8))) := by
  have h := PrintSrc.localStepS_lane (p := p) (c := laneCP pw wn m k lw mw) (n := v) (jj := k % 8) rfl rfl
    (by simp [numOf, hv]) rfl (by simp [numOf, cst, Promises.TVal.mk0])
  have e : k % 8 % Wd.lanes .w8 = k % 8 := by show k % 8 % 8 = k % 8; omega
  rw [e] at h
  exact h

/-- **After the `emit`**: the thread runs locally back to the top of
`printL`, at `PrintCP (k + 1)`. -/
theorem printCP_next (hd : p.find? (·.name == "printL") = some printLPD) {pw wn lw mw : Word} {n m k b : Nat}
    (hwn : wn.val = .num n) (hk : k < printN n m) :
    ∃ c', LocalRunS p (nextCP pw wn m k lw mw b) c' ∧ PrintCP pw wn n m (k + 1) c' := by
  have r : LocalRunS p (nextCP pw wn m k lw mw b) ⟨printLBodyP, topEnvP [pw, cst (.num (k / 8)),
      cst (.num (m - 1 - k / 8)), addW (cst (.num k)) (cst (.num 1)), wn,
      addW (cst (.num (k % 8))) (cst (.num 1))], none⟩ := by
    refine .step (localStepS_add rfl rfl rfl) ?_
    refine .step (localStepS_add rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    refine .step (localStepS_pair rfl rfl rfl) ?_
    exact .single (localStepS_tail rfl hd rfl)
  refine ⟨_, r, k / 8, k % 8 + 1, rfl, ?_, rfl, by omega, by omega, ?_, hwn⟩
  · simp only [topEnvP, printArgs, addW, cst, Promises.TVal.mk0]
  · unfold printN at hk; omega

/-! ## One byte from the element's `idx`, at thread `i ≠ 0` -/

variable {P : SrcParams}

/-- Configuration `s` with thread `i` replaced by `th` and the byte `b`
appended to its trace. -/
def outCfgI (s : Cfg) (i : Nat) (th : TTh) (b : Nat) : Cfg :=
  { s with ths := s.ths.set! i th, trace := s.trace ++ [.out b] }

/-- **One byte of the published `print` at thread `i ≠ 0`**, from the
element's `idx` (`loadCP`), inside any frames, before `main` has returned
and before any exit event, the word of byte `k` with a latest message `j`
holding `w (k / 8)` (`hM`, the named premise): the `idx`, the load reading
that message, the lane and the `emit` are a source run whose trace is the
byte `laneN .w8 (w (k / 8)) (k % 8)`, landing at `nextCP` (memory and
pairs kept), once the landing is certified (`Certified` → the run). -/
theorem loadCP_byte_i (hP : UsesWc P p) {s : Cfg} {i : Nat} {th : TTh} {pw wn : Word}
    {l : WeakMem.AllocLabel} {m k : Nat} {w : Nat → Nat} (hi0 : i ≠ 0) (hi : s.ths[i]? = some th)
    (ht : th.term = (loadCP pw wn m k).term) (he : th.env = (loadCP pw wn m k).env) (hσ : th.σs = [])
    (hpr : th.promises = []) (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hex : mainExit s = []) (hx : ∀ c, Ev.exit c ∉ P.hooks.trace s)
    (hM : ∃ j msg, SLatest s.mem ⟨l, k / 8⟩ j ∧ s.mem[j]? = some msg ∧ msg.val = .num (w (k / 8))) :
    ∃ th' mw, th'.term = (nextCP pw wn m k (elemW pw l (k / 8)) mw (laneN .w8 (w (k / 8)) (k % 8))).term ∧
      th'.env = (nextCP pw wn m k (elemW pw l (k / 8)) mw (laneN .w8 (w (k / 8)) (k % 8))).env ∧
      th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = th.promises ∧ mw.val = .num (w (k / 8)) ∧
      th'.nalloc = th.nalloc ∧ th'.tidLbl = th.tidLbl ∧
      (Certified p P.k P.arch (outCfgI s i th' (laneN .w8 (w (k / 8)) (k % 8))) i →
        (source P p).Run s [.out ⟨laneN .w8 (w (k / 8)) (k % 8) % 256, Nat.mod_lt _ (by decide)⟩]
          (outCfgI s i th' (laneN .w8 (w (k / 8)) (k % 8)))) := by
  obtain ⟨jm, msg, hcell, hm, hv⟩ := hM
  -- the `idx`
  have l1 := printCP_idx (p := p) (wn := wn) (m := m) (k := k) hpw
  let lw := elemW pw l (k / 8)
  let th1 : TTh := { th with term := (ldCP pw wn m k lw).term, env := (ldCP pw wn m k lw).env }
  have hi1 : ({ s with ths := s.ths.set! i th1 } : Cfg).ths[i]? = some th1 := getElem?_set!_self hi th1
  -- the load
  obtain ⟨th2, h2, ht2, he2, hp2, hσ2, hst2, hn2, htl2⟩ := src_load_step (gOf p P.k P.arch _ i) s.mem s.pairs th1
    (x := "wd") (l := .var "l") (e := printLane) (μ := .pub) (sg := false) (w := .w8) (pw := elemW pw l (k / 8))
    (a := ⟨l, k / 8⟩) (gg := 0) rfl rfl rfl hcell hm
  let s2 : Cfg := { s with ths := s.ths.set! i th2 }
  have hm2 : s2 ∈ threadSteps p P.k P.arch { s with ths := s.ths.set! i th1 } i := by
    have := SrcMem.mem_threadSteps hi1 h2
    simpa [s2, set!_set!] using this
  have hi2 : s2.ths[i]? = some th2 := getElem?_set!_self hi th2
  -- the lane
  let mw : Word := ⟨msg.val, msg.view, jm⟩
  have l3 := printCP_lane (p := p) (pw := pw) (wn := wn) (lw := elemW pw l (k / 8)) (mw := mw) (m := m) (k := k)
    (v := w (k / 8)) hv
  have he2' : th2.env = (laneCP pw wn m k (elemW pw l (k / 8)) mw).env := by rw [he2]; rfl
  let b := laneN .w8 (w (k / 8)) (k % 8)
  let th3 : TTh := { th2 with term := (emitCP pw wn m k lw mw b).term, env := (emitCP pw wn m k lw mw b).env }
  let s3 : Cfg := { s with ths := s.ths.set! i th3 }
  have hi3 : s3.ths[i]? = some th3 := getElem?_set!_self hi th3
  -- the `emit` (with no promise outstanding)
  have hp3 : th3.promises = [] := by show th2.promises = []; rw [hp2]; exact hpr
  let s4 := extCfg s3 i th3 "r" .emit printNext [cst (.num b)] []
  have ht3 : th3.term = .let_ "r" (.ext .emit (.var "x")) printNext := rfl
  have ha3 : evalAt th3.env (.var "x") = some (.fix false .w8, [cst (.num b)]) := rfl
  have hi4 := extCfg_ths_self hi3 "r" .emit printNext [cst (.num b)] [] (by decide)
  let th' : TTh := { th3 with term := printNext, env := ("r", ExtName.emit.sig.2, []) :: th3.env }
  have e4 : s4 = outCfgI s i th' b := by
    simp [s4, s3, outCfgI, extCfg, ExtName.events, th']
  refine ⟨th', mw, rfl, ?_, hσ2.trans hσ, hst2, hp2, hv, hn2, htl2, fun hc => ?_⟩
  · show ("r", ExtName.emit.sig.2, []) :: th3.env = _
    rfl
  rw [← e4] at hc
  -- certificates backwards (no promise at the `emit`: the empty run)
  have hc3 : Certified p P.k P.arch s3 i := WorkerSrcStep.certified_nil hi3 hp3
  have hsolo3 := localRunS_solo (k := P.k) (arch := P.arch) (LocalRunS.single l3) hi2 ht2 he2' (hσ2.trans hσ)
  have hc2 : Certified p P.k P.arch s2 i := by
    refine certified_of_solo ?_ hc3
    simpa [s2, s3, th3, set!_set!] using hsolo3
  have hc1 : Certified p P.k P.arch { s with ths := s.ths.set! i th1 } i :=
    certified_of_solo (.thread hm2 (.refl _)) hc2
  -- the run
  have r1 := localRunS_run_source_i hP hi0 (LocalRunS.single l1) hi ht he hσ hex hc1
  have hex1 : mainExit { s with ths := s.ths.set! i th1 } = [] :=
    (mainExit_eq (by simp only [getElem?_set!_ne _ hi0])).trans hex
  have r2 : (source P p).step i { s with ths := s.ths.set! i th1 } [] s2 := by
    have h := tstep_source_i (mem' := s.mem) (pairs' := s.pairs) hP hi0 hi1 h2
      (by simpa [s2, set!_set!] using hc2) hex1
    simpa [s2, set!_set!] using h
  have hex2 : mainExit s2 = [] := (mainExit_eq (by simp only [s2, getElem?_set!_ne _ hi0])).trans hex
  have r3 : (source P p).Run s2 [] s3 := by
    have h := localRunS_run_source_i hP hi0 (LocalRunS.single l3) hi2 ht2 he2' (hσ2.trans hσ) hex2
      (by simpa [s2, s3, th3, set!_set!] using hc3)
    simpa [s2, s3, th3, set!_set!] using h
  have hex3 : mainExit s3 = [] := (mainExit_eq (by simp only [s3, getElem?_set!_ne _ hi0])).trans hex
  have hx3 : ∀ c, Ev.exit c ∉ P.hooks.trace s3 := by
    rw [traceThs_wc hP]; exact hx
  have r4 := emit_src_i hP hi0 hi3 ht3 hp3 ha3 rfl hc hex3 hx3
  have R := r1.trans (LRun.step ⟨i, r2⟩ (r3.trans (LRun.step ⟨i, r4⟩ (LRun.refl _))))
  simp only [List.nil_append, List.append_nil] at R
  rw [← e4]
  exact R

/-! ## The call and the return, at thread `i ≠ 0` -/

/-- Thread `th` in `print`'s body on the slice's words `ws`, the frame
returning into `x` and then `e` pushed. -/
def callTh (th : TTh) (x : String) (e : Expr) (ws : List Word) : TTh :=
  { th with term := printBody, env := [("a", HelloRodataSrc.sliceTyP, ws)],
            stack := ⟨x, e, th.env, [], .unit⟩ :: th.stack }

/-- **The call of `print` at thread `i ≠ 0`**: at `let x = call print is a
in e` (no type variables) with `a` the slice's words, the thread pushes the
frame returning into `x` and enters `print`'s body; a source step with the
empty trace once certified. -/
theorem call_printP_i (hP : UsesWc P p) (hdp : p.find? (·.name == "print") = some printPD) {s : Cfg} {i : Nat}
    {th : TTh} {x : String} {is : List String} {a : At} {e : Expr} {t : Ty} {pw wm wn : Word} (hi0 : i ≠ 0)
    (hi : s.ths[i]? = some th) (ht : th.term = .let_ x (.call "print" is a []) e) (hσ : th.σs = [])
    (ha : evalAt th.env a = some (t, [pw, wm, wn])) (hex : mainExit s = [])
    (hc : Certified p P.k P.arch { s with ths := s.ths.set! i (callTh th x e [pw, wm, wn]) } i) :
    (source P p).step i s [] { s with ths := s.ths.set! i (callTh th x e [pw, wm, wn]) } :=
  tstep_source_i (mem' := s.mem) (pairs' := s.pairs) hP hi0 hi
    (by rw [tstep_call_nil (g := gOf p P.k P.arch s i) ht hσ hdp ha]; exact List.mem_singleton.mpr rfl) hc hex

/-- **The return at thread `i ≠ 0`**: at `ret a` inside a call, the thread
pops the top frame `fr` (`SrcCalls.popTh`); a source step with the empty
trace once certified. -/
theorem ret_i (hP : UsesWc P p) {s : Cfg} {i : Nat} {th : TTh} {a : At} {fr : Frame} {rest : List Frame} {t : Ty}
    {ws : List Word} (hi0 : i ≠ 0) (hi : s.ths[i]? = some th) (ht : th.term = .ret a) (hst : th.stack = fr :: rest)
    (ha : evalAt th.env a = some (t, ws)) (hex : mainExit s = [])
    (hc : Certified p P.k P.arch { s with ths := s.ths.set! i (SrcCalls.popTh th fr rest ws) } i) :
    (source P p).step i s [] { s with ths := s.ths.set! i (SrcCalls.popTh th fr rest ws) } :=
  tstep_source_i (mem' := s.mem) (pairs' := s.pairs) hP hi0 hi
    (by rw [tstep_ret (g := gOf p P.k P.arch s i) ht hst ha]; exact List.mem_singleton.mpr rfl) hc hex

end Spike.Lib.HelloPrintSrcPub

/-- info: 'Spike.Lib.HelloPrintSrcPub.loadCP_byte_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPrintSrcPub.loadCP_byte_i

/-- info: 'Spike.Lib.HelloPrintSrcPub.printCP_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPrintSrcPub.printCP_load

/-- info: 'Spike.Lib.HelloPrintSrcPub.printP_entry_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPrintSrcPub.printP_entry_run
