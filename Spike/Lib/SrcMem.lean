/-
**The source side of the one-word memory rows**: the source thread's
memory steps (`TermRun.tstep`) that the `Out.load` and `Out.store` rows of
`Spike.Lib.Seg` and a slot swap pair with, at an untagged locative address
word to a one-word cell (`accs u = some [.one]`).

- `loadUnits_one`, `storeUnits_one`: one unit through the promise
  machine's rules (`Scc.Sem.stepLoad_latest`, `Scc.Sem.stepStore_append`).
- `src_load_step`: `let x = load acq a in e` can read the latest message to
  the address and bind its word (`loadTy`).
- `src_store_step`: `let x = store rel a b in e`, with no promise, appends
  the message of `b`'s value.
- `src_xchg_step`, `src_xchgAt_step`: `let x = xchg a v in e` on a
  one-word cell, `let x = xchgAt b i v in e` on a one-word element (a plain
  load of the latest message then a plain store, in one source step) bind
  the old word and append the new one; `src_swap_step_cfg`: either, at an
  exchange site (`XchgSite`).
- `src_newBuf_step`: `let x = newBuf a τ in e` allocates the buffer at
  the thread's next fresh label (`allocBuf`) and binds the locative to it.
- `mem_threadSteps` and the `_cfg` corollaries: the same as thread steps of
  a configuration.
-/
import Spike.Lib.Seg
import Scc.Sem.RowsSrc

namespace Spike.Lib.SrcMem

open CoreLang CoreTerm TermRun
open Scc.Sem.MemRel (SLatest)

theorem offs_zero (a : WeakMem.Address) : offs a 0 = a := by cases a; simp [offs]

/-- A data word stored through register `1` is stored with its value. -/
theorem rmwNewVal_dataE (r0 w : Word) : Promises.rmwNewVal (regsOf r0 w w) (dataE 1 w) = w.val := by
  unfold dataE; split <;> simp_all [Promises.rmwNewVal, regsOf]

/-! ## One unit -/

/-- **One unit's load can read the latest message** to the address. -/
theorem loadUnits_one (arch : WeakMem.Arch) (pw : Word) {a : WeakMem.Address} (acq : Bool) (s : St) {j : Nat}
    {m : WeakMem.Msg} (hj : SLatest s.mem a j) (hm : s.mem[j]? = some m) :
    ∃ vs, ({ s with vs := vs, undefs := s.undefs + countUndef [⟨m.val, m.view, j⟩] }, [⟨m.val, m.view, j⟩]) ∈
      loadUnits arch pw a acq [.one] 0 s := by
  obtain ⟨t1, ht1, hr⟩ := Scc.Sem.stepLoad_latest arch s.pairs (mth s pw pw pw) 1 [0] acq hj hm
  refine ⟨t1.vs, ?_⟩
  simp only [loadUnits, offs_zero, List.mem_flatMap, List.mem_map]
  exact ⟨t1, ht1, _, List.mem_singleton.mpr rfl, by rw [hr]⟩

/-- **One unit's store, with no promise, appends** the message of the
word's value; the promises stay empty. -/
theorem storeUnits_one (k : Promises.Knobs) (arch : WeakMem.Arch) (pw w : Word) (a : WeakMem.Address) (rel : Bool)
    (s : St) (hp : s.promises = []) :
    ∃ mv vs, { s with mem := s.mem.push ⟨a, w.val, mv⟩, vs := vs, promises := [] } ∈
      storeUnits k arch pw a rel [.one] [w] 0 s := by
  obtain ⟨t1, ht1⟩ := Scc.Sem.stepStore_append k arch s.mem (mth s pw w w) a (dataE 1 w) [0] rel
  obtain ⟨-, hp1⟩ := Scc.Sem.stepStore_noProm (x := (_, t1)) (by simpa [mth] using hp) ht1
  refine ⟨Promises.storeMview (mth s pw w w) (dataE 1 w) [0] rel, t1.vs, ?_⟩
  simp only [storeUnits, offs_zero, List.mem_flatMap]
  refine ⟨_, ht1, ?_⟩
  simp only [List.mem_singleton]
  rw [hp1]
  simp only [mth, rmwNewVal_dataE]

/-! ## Source steps -/

variable (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts) (th : TTh)

/-- **The source load of the latest message**: at `let x = load acq a in e`
with the address word an untagged locative to a one-word cell, the source
thread can read the latest message `j` to the address and bind its word;
memory, the paired timestamps, the promises, type arguments and frames are
unchanged. -/
theorem src_load_step {x : String} {acq : Bool} {a : At} {e : Expr} {ty : Ty} {pw : Word} {μ : Mode} {u : Ty}
    {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.load acq a) e) (hea : evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u)) (hu : accs u = some [.one])
    (hj : SLatest mem sa j) (hm : mem[j]? = some m) :
    ∃ th', (mem, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack := by
  obtain ⟨vs, hl⟩ := loadUnits_one g.arch pw acq (stOf mem pairs th) hj hm
  refine ⟨⟨e, (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs, th.promises, th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, ?mem, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, hea, hcell, addrOf, hpw, hu, List.mem_map]
    exact ⟨_, ⟨_, hl, rfl⟩, by simp [withS, stOf, loadTy, hcell]⟩
  all_goals simp [loadTy, hcell]

/-- **The source store appends**: at `let x = store rel a b none in e` with
the address word an untagged locative to a one-word cell and no promise,
the source thread appends the message of `b`'s value at the address and
binds `x` to `()`; the promises stay empty. -/
theorem src_store_step {x : String} {rel : Bool} {a b : At} {e : Expr} {ty tb : Ty} {pw wb : Word} {μ : Mode}
    {u : Ty} {sa : WeakMem.Address}
    (ht : th.term = .let_ x (.store rel a b none) e) (hea : evalAt th.env a = some (ty, [pw]))
    (heb : evalAt th.env b = some (tb, [wb])) (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u))
    (hu : accs u = some [.one]) (hp : th.promises = []) :
    ∃ th' mv, (mem.push ⟨sa, wb.val, mv⟩, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, .unit, []) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack := by
  obtain ⟨mv, vs, hs⟩ := storeUnits_one g.k g.arch pw wb sa rel (stOf mem pairs th) hp
  refine ⟨⟨e, (x, .unit, []) :: th.env, th.σs, th.stack, vs, [], th.nalloc, th.undefs, th.tidLbl, th.permit⟩, mv, ?mem, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, hea, heb, hcell, addrOf, hpw, hu, List.mem_map]
    exact ⟨_, ⟨_, hs, rfl⟩, rfl⟩
  all_goals rfl

/-- **The source slot swap**: at `let x = xchgAt b i v in e` on a buffer of
one-word elements, with the buffer word an untagged locative, index `k` and
no promise, the source thread reads the latest message `j` of element `k`
then appends the message of `v`'s value there, in one step, binding the old
word; the promises stay empty. -/
theorem src_xchgAt_step {x : String} {b i v : At} {e : Expr} {t ti tv : Ty} {pw : Word} {iws : List Word}
    {wv : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address} {k j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.xchgAt b i v) e) (heb : evalAt th.env b = some (t, [pw]))
    (hei : evalAt th.env i = some (ti, iws)) (hev : evalAt th.env v = some (tv, [wv]))
    (hpw : pw.val = .loc sa 0) (hbuf : bufElem t = some (μ, u)) (hu : accs u = some [.one])
    (hk : numOf iws = some k) (hp : th.promises = [])
    (hj : SLatest mem (offs sa k) j) (hm : mem[j]? = some m) :
    ∃ th' mv, (mem.push ⟨offs sa k, wv.val, mv⟩, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack := by
  have hk1 : offs sa (k * nWords [.one]) = offs sa k := by simp [nWords, Acc.size]
  obtain ⟨vs, hl⟩ := loadUnits_one g.arch pw false (stOf mem pairs th) hj hm
  obtain ⟨mv, vs', hs⟩ := storeUnits_one g.k g.arch pw wv (offs sa k) false
    { stOf mem pairs th with vs := vs, undefs := (stOf mem pairs th).undefs + countUndef [⟨m.val, m.view, j⟩] }
    hp
  refine ⟨⟨e, (x, u, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs', [], th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, mv, ?mem, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, heb, hei, hev, hbuf, hk, addrOf, hpw, hu, hk1, List.mem_map, List.mem_flatMap]
    exact ⟨_, ⟨_, hl, _, hs, rfl⟩, rfl⟩
  all_goals rfl

/-- **The source exchange of a one-word cell**: at `let x = xchg a v in e`
with the reference word an untagged locative to a one-word cell and no
promise, the source thread reads the latest message `j` of the cell then
appends the message of `v`'s value there, in one step, binding the old
word; the promises stay empty. -/
theorem src_xchg_step {x : String} {a v : At} {e : Expr} {t tv : Ty} {pw wv : Word} {μ : Mode} {u : Ty}
    {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.xchg a v) e) (hea : evalAt th.env a = some (t, [pw]))
    (hev : evalAt th.env v = some (tv, [wv])) (hpw : pw.val = .loc sa 0) (hcell : cellOf t = some (μ, u))
    (hu : accs u = some [.one]) (hp : th.promises = []) (hj : SLatest mem sa j) (hm : mem[j]? = some m) :
    ∃ th' mv, (mem.push ⟨sa, wv.val, mv⟩, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack := by
  obtain ⟨vs, hl⟩ := loadUnits_one g.arch pw false (stOf mem pairs th) hj hm
  obtain ⟨mv, vs', hs⟩ := storeUnits_one g.k g.arch pw wv sa false
    { stOf mem pairs th with vs := vs, undefs := (stOf mem pairs th).undefs + countUndef [⟨m.val, m.view, j⟩] }
    hp
  refine ⟨⟨e, (x, u, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs', [], th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, mv, ?mem, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, hea, hev, hcell, addrOf, hpw, hu, List.mem_map, List.mem_flatMap]
    exact ⟨_, ⟨_, hl, _, hs, rfl⟩, rfl⟩
  all_goals rfl

/-- **The source buffer allocation**: at `let x = newBuf a τ in e` with `a`
a number `k` and `τ` (closed under the type arguments) of words `us`, the
source thread allocates `k` elements at the fresh label of its next
allocation (`allocBuf`), binding `x` to the untagged locative to its first
word at the buffer's type; the paired timestamps, the promises, type
arguments and frames are unchanged, and the allocation count goes up by
one. -/
theorem src_newBuf_step {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat} {us : List Acc}
    (ht : th.term = .let_ x (.newBuf a τ) e) (hea : evalAt th.env a = some (ta, ws))
    (hk : numOf ws = some k) (hus : accs (close th.σs τ) = some us) :
    ∃ z ini th', ((allocBuf (freshLabel g.lbase g.n g.i th.nalloc) (k * nWords us) z (stOf mem pairs th)).1.mem,
        pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit k) (close th.σs τ))) (.ini (.lit ini)),
        [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 := by
  let τ' := close th.σs τ
  let z := if zeroableIn [] [] τ' then zeroWords τ' else none
  let ini := if z.isSome then k else 0
  let lbl := freshLabel g.lbase g.n g.i th.nalloc
  refine ⟨z, ini, withS { th with term := e, env := (x, .refine (.loc .own (.array (.lit k) τ')) (.ini (.lit ini)),
    [cst (.loc ⟨lbl, 0⟩ 0)]) :: th.env } (allocBuf lbl (k * nWords us) z (stOf mem pairs th)).1, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [tstep, ht, evalOp, hea, hus, ol, List.mem_map]
  refine ⟨((allocBuf lbl (k * nWords us) z (stOf mem pairs th)).1,
    .refine (.loc .own (.array (.lit k) τ')) (.ini (.lit ini)), [cst (.loc ⟨lbl, 0⟩ 0)]), ?_, rfl⟩
  simp only [hk, Option.toList, Option.bind, bind, pure, List.mem_singleton]; rfl

/-! ## As thread steps of a configuration -/

/-- **A `tstep` outcome of thread `i` is one of its thread steps.** -/
theorem mem_threadSteps {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th : TTh}
    (hi : c.ths[i]? = some th) {mem' : WeakMem.Memory} {pairs' : List WeakMem.Ts} {th' : TTh}
    (h : (mem', pairs', th') ∈ tstep (gOf p k arch c i) c.mem c.pairs th) :
    { c with mem := mem', pairs := pairs', ths := c.ths.set! i th' } ∈ threadSteps p k arch c i := by
  unfold threadSteps
  simp only [hi, List.mem_map]
  exact ⟨_, h, rfl⟩

/-- `src_xchgAt_step` with the thread's allocation count kept. -/
theorem src_xchgAt_step_n {x : String} {b i v : At} {e : Expr} {t ti tv : Ty} {pw : Word} {iws : List Word}
    {wv : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address} {k j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.xchgAt b i v) e) (heb : evalAt th.env b = some (t, [pw]))
    (hei : evalAt th.env i = some (ti, iws)) (hev : evalAt th.env v = some (tv, [wv]))
    (hpw : pw.val = .loc sa 0) (hbuf : bufElem t = some (μ, u)) (hu : accs u = some [.one])
    (hk : numOf iws = some k) (hp : th.promises = [])
    (hj : SLatest mem (offs sa k) j) (hm : mem[j]? = some m) :
    ∃ th' mv, (mem.push ⟨offs sa k, wv.val, mv⟩, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  have hk1 : offs sa (k * nWords [.one]) = offs sa k := by simp [nWords, Acc.size]
  obtain ⟨vs, hl⟩ := loadUnits_one g.arch pw false (stOf mem pairs th) hj hm
  obtain ⟨mv, vs', hs⟩ := storeUnits_one g.k g.arch pw wv (offs sa k) false
    { stOf mem pairs th with vs := vs, undefs := (stOf mem pairs th).undefs + countUndef [⟨m.val, m.view, j⟩] }
    hp
  refine ⟨⟨e, (x, u, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs', [], th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, mv, ?mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, heb, hei, hev, hbuf, hk, addrOf, hpw, hu, hk1, List.mem_map, List.mem_flatMap]
    exact ⟨_, ⟨_, hl, _, hs, rfl⟩, rfl⟩
  all_goals rfl

/-- `src_xchg_step` with the thread's allocation count kept. -/
theorem src_xchg_step_n {x : String} {a v : At} {e : Expr} {t tv : Ty} {pw wv : Word} {μ : Mode} {u : Ty}
    {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.xchg a v) e) (hea : evalAt th.env a = some (t, [pw]))
    (hev : evalAt th.env v = some (tv, [wv])) (hpw : pw.val = .loc sa 0) (hcell : cellOf t = some (μ, u))
    (hu : accs u = some [.one]) (hp : th.promises = []) (hj : SLatest mem sa j) (hm : mem[j]? = some m) :
    ∃ th' mv, (mem.push ⟨sa, wv.val, mv⟩, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨vs, hl⟩ := loadUnits_one g.arch pw false (stOf mem pairs th) hj hm
  obtain ⟨mv, vs', hs⟩ := storeUnits_one g.k g.arch pw wv sa false
    { stOf mem pairs th with vs := vs, undefs := (stOf mem pairs th).undefs + countUndef [⟨m.val, m.view, j⟩] }
    hp
  refine ⟨⟨e, (x, u, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs', [], th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, mv, ?mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, hea, hev, hcell, addrOf, hpw, hu, List.mem_map, List.mem_flatMap]
    exact ⟨_, ⟨_, hl, _, hs, rfl⟩, rfl⟩
  all_goals rfl

variable {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th : TTh}

/-- `src_load_step` as a thread step of thread `i`. -/
theorem src_load_step_cfg (hi : c.ths[i]? = some th) {x : String} {acq : Bool} {a : At} {e : Expr} {ty : Ty}
    {pw : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.load acq a) e) (hea : evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u)) (hu : accs u = some [.one])
    (hj : SLatest c.mem sa j) (hm : c.mem[j]? = some m) :
    ∃ th', { c with ths := c.ths.set! i th' } ∈ threadSteps p k arch c i ∧ th'.term = e ∧
      th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack := by
  obtain ⟨th', h, h1⟩ := src_load_step (gOf p k arch c i) c.mem c.pairs th ht hea hpw hcell hu hj hm
  exact ⟨th', mem_threadSteps hi h, h1⟩

/-- `src_store_step` as a thread step of thread `i`. -/
theorem src_store_step_cfg (hi : c.ths[i]? = some th) {x : String} {rel : Bool} {a b : At} {e : Expr}
    {ty tb : Ty} {pw wb : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address}
    (ht : th.term = .let_ x (.store rel a b none) e) (hea : evalAt th.env a = some (ty, [pw]))
    (heb : evalAt th.env b = some (tb, [wb])) (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u))
    (hu : accs u = some [.one]) (hp : th.promises = []) :
    ∃ th' mv, { c with mem := c.mem.push ⟨sa, wb.val, mv⟩, ths := c.ths.set! i th' } ∈ threadSteps p k arch c i ∧
      th'.term = e ∧ th'.env = (x, .unit, []) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack := by
  obtain ⟨th', mv, h, h1⟩ := src_store_step (gOf p k arch c i) c.mem c.pairs th ht hea heb hpw hcell hu hp
  exact ⟨th', mv, mem_threadSteps hi h, h1⟩

/-- `src_xchgAt_step` as a thread step of thread `i`. -/
theorem src_xchgAt_step_cfg (hi : c.ths[i]? = some th) {x : String} {b i' v : At} {e : Expr} {t ti tv : Ty}
    {pw : Word} {iws : List Word} {wv : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address} {kk j : Nat}
    {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.xchgAt b i' v) e) (heb : evalAt th.env b = some (t, [pw]))
    (hei : evalAt th.env i' = some (ti, iws)) (hev : evalAt th.env v = some (tv, [wv]))
    (hpw : pw.val = .loc sa 0) (hbuf : bufElem t = some (μ, u)) (hu : accs u = some [.one])
    (hk : numOf iws = some kk) (hp : th.promises = [])
    (hj : SLatest c.mem (offs sa kk) j) (hm : c.mem[j]? = some m) :
    ∃ th' mv, { c with mem := c.mem.push ⟨offs sa kk, wv.val, mv⟩, ths := c.ths.set! i th' } ∈
        threadSteps p k arch c i ∧ th'.term = e ∧ th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack := by
  obtain ⟨th', mv, h, h1⟩ :=
    src_xchgAt_step (gOf p k arch c i) c.mem c.pairs th ht heb hei hev hpw hbuf hu hk hp hj hm
  exact ⟨th', mv, mem_threadSteps hi h, h1⟩

/-- **The source exchange at an exchange site** (`XchgSite`: `xchg` or
`xchgAt`), as a thread step of thread `i`: reading the latest message `j` at
`sa` and appending the message of `v`'s value there, binding the old word. -/
theorem src_swap_step_cfg (hi : c.ths[i]? = some th) {x : String} {sa : WeakMem.Address} {u : Ty} {v : At}
    {e : Expr} {tv : Ty} {wv : Word} {j : Nat} {m : WeakMem.Msg}
    (hs : XchgSite ⟨th.term, th.env, none⟩ x sa u v e) (hev : evalAt th.env v = some (tv, [wv]))
    (hp : th.promises = []) (hj : SLatest c.mem sa j) (hm : c.mem[j]? = some m) :
    ∃ th' mv, { c with mem := c.mem.push ⟨sa, wv.val, mv⟩, ths := c.ths.set! i th' } ∈
        threadSteps p k arch c i ∧ th'.term = e ∧ th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack := by
  obtain ⟨hu, ⟨a, t, pw, μ, ht, hea, hpw, hcell⟩ | ⟨b, i', t, pw, ti, iws, μ, sb, kk, ht, heb, hpw, hbuf, hei, hk,
    rfl⟩⟩ := hs
  · obtain ⟨th', mv, h, h1⟩ :=
      src_xchg_step (gOf p k arch c i) c.mem c.pairs th ht hea hev hpw hcell hu hp hj hm
    exact ⟨th', mv, mem_threadSteps hi h, h1⟩
  · obtain ⟨th', mv, h, h1⟩ :=
      src_xchgAt_step (gOf p k arch c i) c.mem c.pairs th ht heb hei hev hpw hbuf hu hk hp hj hm
    exact ⟨th', mv, mem_threadSteps hi h, h1⟩

/-- `src_swap_step_cfg` with the thread's allocation count kept (an exchange allocates
nothing). -/
theorem src_swap_step_cfg_n (hi : c.ths[i]? = some th) {x : String} {sa : WeakMem.Address} {u : Ty} {v : At}
    {e : Expr} {tv : Ty} {wv : Word} {j : Nat} {m : WeakMem.Msg}
    (hs : XchgSite ⟨th.term, th.env, none⟩ x sa u v e) (hev : evalAt th.env v = some (tv, [wv]))
    (hp : th.promises = []) (hj : SLatest c.mem sa j) (hm : c.mem[j]? = some m) :
    ∃ th' mv, { c with mem := c.mem.push ⟨sa, wv.val, mv⟩, ths := c.ths.set! i th' } ∈
        threadSteps p k arch c i ∧ th'.term = e ∧ th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨hu, ⟨a, t, pw, μ, ht, hea, hpw, hcell⟩ | ⟨b, i', t, pw, ti, iws, μ, sb, kk, ht, heb, hpw, hbuf, hei, hk,
    rfl⟩⟩ := hs
  · obtain ⟨th', mv, h, h1⟩ :=
      src_xchg_step_n (gOf p k arch c i) c.mem c.pairs th ht hea hev hpw hcell hu hp hj hm
    exact ⟨th', mv, mem_threadSteps hi h, h1⟩
  · obtain ⟨th', mv, h, h1⟩ :=
      src_xchgAt_step_n (gOf p k arch c i) c.mem c.pairs th ht heb hei hev hpw hbuf hu hk hp hj hm
    exact ⟨th', mv, mem_threadSteps hi h, h1⟩

/-- `src_newBuf_step` as a thread step of thread `i`. -/
theorem src_newBuf_step_cfg (hi : c.ths[i]? = some th) {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List Word} {kk : Nat} {us : List Acc}
    (ht : th.term = .let_ x (.newBuf a τ) e) (hea : evalAt th.env a = some (ta, ws))
    (hk : numOf ws = some kk) (hus : accs (close th.σs τ) = some us) :
    ∃ z ini th', { c with mem := (allocBuf (freshLabel c.lbase c.n i th.nalloc) (kk * nWords us) z
        (stOf c.mem c.pairs th)).1.mem, ths := c.ths.set! i th' } ∈ threadSteps p k arch c i ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit kk) (close th.σs τ))) (.ini (.lit ini)),
        [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 := by
  obtain ⟨z, ini, th', h, h1⟩ := src_newBuf_step (gOf p k arch c i) c.mem c.pairs th ht hea hk hus
  exact ⟨z, ini, th', mem_threadSteps hi h, h1⟩

end Spike.Lib.SrcMem
