/-
The bridge spike, spinning-reader variant: the source program and its steps
in closed form.

The reader spins on the flag until it reads a non-zero value:

```
spin f = let r = load acq f in if r = 0 then spin f else ret r
```

written as the code block `spin` (`spinDecl`, the program `progL`) whose
body (`spinBody`) the reader starts in. The writer is unchanged
(`writerTerm`). The reader's configurations:

* `readerHead vs u`: at the loop head (the body, `f` bound), views `vs`;
* `readerMid vs w u`: after the load, `r` bound to `w`, at the test;
* `readerTail vs w u`: the test chose the loop: at the tail call;
* `readerExit vs w u`: the test chose the exit: at `ret r`.

The source steps (`head_read`, `mid_test`, `tail_enter`) are what the
simulation of `Spike/Bridge/Loop.lean` needs: the load of any message the
reader's views do not hide (with the views after it, `loadVS`), the test,
and the tail call back to the head (its argument is rebound at the same
type, so the head is reached again exactly).
-/
import Spike.Bridge.Common

namespace Spike.Bridge

open CoreLang CoreTerm
open WeakMem (Val Msg Memory Address VState)

/-! ## The program -/

/-- The loop body: `let r = load acq f in if r = 0 then spin f else ret r`. -/
def spinBody : Expr :=
  .let_ "r" (.load true (.var "f")) (.ifeq (.var "r") (.lit 0) (.tail "spin" [] (.var "f")) (.ret (.var "r")))

/-- The code block `spin`. -/
def spinDecl : Decl :=
  { name := "spin", idx := [], arg := "f", argTy := fTy, retTy := .int, body := spinBody }

/-- The program: the one code block. -/
def progL : CoreTerm.Prog := [spinDecl]

/-- The spinning reader at its start. -/
def readerL0 : TermRun.TTh := { term := spinBody, env := envF }

/-- The reader at the loop head, with views `vs` and undefined-read count `u`. -/
def readerHead (vs : VState) (u : Nat) : TermRun.TTh := { readerL0 with vs := vs, undefs := u }

/-- The test after the load. -/
def testTerm : Expr := .ifeq (.var "r") (.lit 0) (.tail "spin" [] (.var "f")) (.ret (.var "r"))

/-- The reader after its load of `w`, at the test. -/
def readerMid (vs : VState) (w : TermRun.Word) (u : Nat) : TermRun.TTh :=
  { readerL0 with term := testTerm, env := ("r", .int, [w]) :: envF, vs := vs, undefs := u }

/-- The reader at the tail call (the test chose the loop). -/
def readerTail (vs : VState) (w : TermRun.Word) (u : Nat) : TermRun.TTh :=
  { readerMid vs w u with term := .tail "spin" [] (.var "f") }

/-- The reader at `ret r` (the test chose the exit). -/
def readerExit (vs : VState) (w : TermRun.Word) (u : Nat) : TermRun.TTh :=
  { readerMid vs w u with term := .ret (.var "r") }

/-- The source start configuration of the variant. -/
def srcInitL : TermRun.Cfg := { mem := #[flagInit], ths := #[writerAt [], readerL0], lbase := 1 }

theorem readerL0_eq : readerL0 = readerHead VState.init 0 := rfl

/-- The views after an acquire load of the flag at `t` with message view
`mv` (`Promises.stepLoad`). -/
def loadVS (vs : VState) (pairs : List Nat) (t mv : Nat) : VState :=
  { vs with
    coh := fun b => if b = flagA then max (vs.coh flagA) t else vs.coh b
    vRd := max vs.vRd (Promises.rdV vs pairs t mv)
    vPreBase := max vs.vPreBase (Promises.acqV vs pairs t mv) }

/-! ## Source steps in closed form -/

section SrcSteps

variable {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- The head's step, as `Promises.stepLoad` of the flag, acquiring. -/
theorem tstep_head (g : TermRun.G) (mem : Memory) (pairs : List Nat) (vs : VState) (u : Nat) :
    TermRun.tstep g mem pairs (readerHead vs u) =
      (Promises.stepLoad g.arch mem pairs (TermRun.mth (TermRun.stOf mem pairs (readerHead vs u)) fW fW fW) 1 flagA
          [0] true).map
        fun th => (mem, pairs, readerMid th.vs (th.regs 1) (u + TermRun.countUndef [th.regs 1])) := by
  simp [TermRun.tstep, readerHead, readerL0, spinBody, TermRun.evalOp, envF, TermRun.evalAt, TermRun.lookupE, fTy,
    cellOf, TermRun.addrOf, fW, TermRun.cst, Promises.TVal.mk0, flagA, TermRun.accs, TermRun.loadUnits,
    TermRun.offs, TermRun.withS, TermRun.stOf, readerMid, testTerm]
  generalize Promises.stepLoad _ _ _ _ _ _ _ _ = L
  induction L <;> simp_all

/-- **The head reads**: the reader at the loop head can read any message of
the flag that its read bound does not hide; it is then at the test, with
`r` bound to the message's value, view and timestamp, and views `loadVS`. -/
theorem head_read (c : TermRun.Cfg) {vs : VState} {u : Nat} (h1 : c.ths[1]? = some (readerHead vs u)) {t : Nat}
    {m : Msg} (hm : c.mem[t]? = some m) (hl : m.loc = flagA)
    (hnh : WeakMem.hiddenFrom c.mem flagA t (Promises.readBoundOf arch vs 0 flagA) = false) :
    ∃ u', { c with ths := c.ths.set! 1 (readerMid (loadVS vs c.pairs t m.view) ⟨m.val, m.view, t⟩ u') } ∈
      TermRun.threadSteps progL k arch c 1 := by
  have ht : t < c.mem.size := by
    rcases Nat.lt_or_ge t c.mem.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hm
  have hm' : c.mem[t]! = m := by
    rw [getElem!_pos c.mem t ht]; exact Option.some.inj ((Array.getElem?_eq_getElem ht).symm.trans hm)
  have hdb : Promises.depBound (TermRun.mth (TermRun.stOf c.mem c.pairs (readerHead vs u)) fW fW fW).regs [0] = 0 := by
    simp [Promises.depBound, Promises.depView, Promises.depRts, TermRun.mth, TermRun.regsOf, fW, TermRun.cst,
      Promises.TVal.mk0]
  unfold TermRun.threadSteps
  rw [h1]
  simp only [tstep_head, List.map_map]
  unfold Promises.stepLoad
  simp only [List.map_map]
  refine ⟨u + TermRun.countUndef [⟨m.val, m.view, t⟩],
    List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨List.mem_range.mpr ht, ?_⟩, ?_⟩⟩
  · rw [hdb]
    simp only [WeakMem.readable, hm, hl, Option.elim, decide_true, Bool.true_and, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    exact hnh
  · simp only [hm', Function.comp, ite_true]
    rfl

/-- **The test**: the reader at the test with `r` bound to a number `n`
goes to the tail call if `n = 0`, to `ret r` otherwise. -/
theorem mid_test (c : TermRun.Cfg) {vs : VState} {w : TermRun.Word} {u n : Nat}
    (h1 : c.ths[1]? = some (readerMid vs w u)) (hw : w.val = .num n) :
    { c with ths := c.ths.set! 1 (if n = 0 then readerTail vs w u else readerExit vs w u) } ∈
      TermRun.threadSteps progL k arch c 1 := by
  unfold TermRun.threadSteps
  rw [h1]
  by_cases hn : n = 0
  · subst hn
    simp [TermRun.tstep, readerMid, testTerm, TermRun.evalAt, TermRun.lookupE, envF, hw, TermRun.cst,
      Promises.TVal.mk0, readerTail]
  · simp [TermRun.tstep, readerMid, testTerm, TermRun.evalAt, TermRun.lookupE, envF, hw, TermRun.cst,
      Promises.TVal.mk0, readerExit, hn]

/-- The flag reference's type is closed. -/
theorem close_fTy : TermRun.close [] fTy = fTy := rfl

/-- **The tail call**: the reader at the tail call enters `spin` again with
`f` rebound at the same type: it is at the loop head, views kept. -/
theorem tail_enter (c : TermRun.Cfg) {vs : VState} {w : TermRun.Word} {u : Nat}
    (h1 : c.ths[1]? = some (readerTail vs w u)) :
    { c with ths := c.ths.set! 1 (readerHead vs u) } ∈ TermRun.threadSteps progL k arch c 1 := by
  unfold TermRun.threadSteps
  rw [h1]
  simp [TermRun.tstep, readerTail, readerMid, TermRun.enter, TermRun.gOf, progL, spinDecl, TermRun.evalAt,
    TermRun.lookupE, envF, TermRun.ol, readerHead, readerL0]
  rw [close_fTy]

end SrcSteps

end Spike.Bridge
