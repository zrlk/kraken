/-
**Source steps of hello.w's published `print` loop** (x86-64 side; the twin
of `Spike/Lib/HelloPrintSrcPub.lean`): `printL`/`print` on a **published**
slice, each word read by `let l = idx b iv in let wd = load l in …` (a plain
load of the element's locative) instead of `loadAt`.

- `bufTyP`, `printLTyP`, `printLoadP`, `printLBodyP`, `printLPD`, `printPD`:
  the declarations; the word and byte advances, the lane and the `emit` are
  `PrintSrc`'s terms (`printAdv`, `printNext`, `printLane`, `printEmit`),
  `print`'s body is `PrintSrc.printBody`; `printLPD_find`, `printPD_find`:
  they are `X64HelloSrc.helloSrc`'s.
- `localStepS_idx`: `let x = idx b i in e` is a local step.
- `topEnvP`, `loadEnvP`, `adv_run`, `body_load`: `printL`'s body to the word
  advance and to the element's `idx`.
- `PrintCP`, `loadCP`, `ldCP`, `laneCP`, `emitCP`, `nextCP`, `elemW`: the
  loop between controls (`LocalRunS`); `printP_entry_run`, `printCP_entry`,
  `printP_done_run`, `printCP_load`, `printCP_idx`, `printCP_lane`,
  `printCP_next`.
- `outCfgI`, `callTh`: a configuration with a thread replaced and a byte
  emitted; a thread entering `print`'s body.

**Where this differs from AArch64**: the declarations are found in
`X64HelloSrc.helloSrc` and the slice type is `X64HelloRodataSrc.sliceTyP`
(the AArch64 modules reach AArch64's syntax, which cannot be imported next
to x86-64's); the terms and proofs are otherwise the same. The source load
`src_load_step`, the byte `loadCP_byte_i`, `printP_empty_run`, and the call
and return steps `call_printP_i`, `ret_i` are not twinned (unused by the
hello proof).
-/
import Spike.Lib.WorkerSrcStep
import Spike.Lib.SrcCalls
import Spike.Lib.X64HelloRodataSrc

namespace Spike.Lib.X64HelloPrintSrcPub

open CoreLang CoreTerm TermRun TermExtStep
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Spike.Lib.PrintSrc (printAdv printNext printEmit printLane printBody printArgs printN)

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
  { name := "print", idx := ["m"], arg := "a", argTy := X64HelloRodataSrc.sliceTyP, retTy := .unit, body := printBody }

theorem printLPD_find : X64HelloSrc.helloSrc.find? (·.name == "printL") = some printLPD := rfl

theorem printPD_find : X64HelloSrc.helloSrc.find? (·.name == "print") = some printPD := rfl

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
    LocalRunS p ⟨printBody, [("a", X64HelloRodataSrc.sliceTyP, [pw, wm, wn])], none⟩
      ⟨printLBodyP, topEnvP (printArgs pw wn 0 (m - 1) 0 0), none⟩ := by
  have hr : LocalRunS p ⟨printBody, [("a", X64HelloRodataSrc.sliceTyP, [pw, wm, wn])], none⟩
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

/-! ## The worker's configurations -/

/-- Configuration `s` with thread `i` replaced by `th` and the byte `b`
appended to its trace. -/
def outCfgI (s : Cfg) (i : Nat) (th : TTh) (b : Nat) : Cfg :=
  { s with ths := s.ths.set! i th, trace := s.trace ++ [.out b] }

/-- Thread `th` in `print`'s body on the slice's words `ws`, the frame
returning into `x` and then `e` pushed. -/
def callTh (th : TTh) (x : String) (e : Expr) (ws : List Word) : TTh :=
  { th with term := printBody, env := [("a", X64HelloRodataSrc.sliceTyP, ws)],
            stack := ⟨x, e, th.env, [], .unit⟩ :: th.stack }

end Spike.Lib.X64HelloPrintSrcPub

/-- info: 'Spike.Lib.X64HelloPrintSrcPub.printCP_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPrintSrcPub.printCP_load

/-- info: 'Spike.Lib.X64HelloPrintSrcPub.printP_entry_run' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPrintSrcPub.printP_entry_run

/-- info: 'Spike.Lib.X64HelloPrintSrcPub.printCP_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPrintSrcPub.printCP_next
