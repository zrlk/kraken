/-
**The one-word memory rows' source steps keep the allocation count**:
`Spike.Lib.SrcMem`'s load, store and exchange steps (statements unchanged
there) with `th'.nalloc = th.nalloc` added, for the consumers that carry
`AllocInv.FreshInv` at thread 0's allocation count.

- `src_load_stepN`, `src_store_stepN`, `src_xchg_stepN`, `src_xchgAt_stepN`:
  the `tstep` cases.
- `src_load_step_cfgN`, `src_store_step_cfgN`, `src_swap_step_cfgN`: as
  thread steps of a configuration.
-/
import Spike.Lib.SrcMem

namespace Spike.Lib.SrcMemN

open CoreLang CoreTerm TermRun
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.SrcMem (loadUnits_one storeUnits_one mem_threadSteps)

variable (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts) (th : TTh)

/-- `SrcMem.src_load_step`, the allocation count kept. -/
theorem src_load_stepN {x : String} {acq : Bool} {a : At} {e : Expr} {ty : Ty} {pw : Word} {μ : Mode} {u : Ty}
    {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.load acq a) e) (hea : evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u)) (hu : accs u = some [.one])
    (hj : SLatest mem sa j) (hm : mem[j]? = some m) :
    ∃ th', (mem, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨vs, hl⟩ := loadUnits_one g.arch pw acq (stOf mem pairs th) hj hm
  refine ⟨⟨e, (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env, th.σs, th.stack, vs, th.promises, th.nalloc,
    th.undefs + countUndef [⟨m.val, m.view, j⟩], th.tidLbl, th.permit⟩, ?mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, hea, hcell, addrOf, hpw, hu, List.mem_map]
    exact ⟨_, ⟨_, hl, rfl⟩, by simp [withS, stOf, loadTy, hcell]⟩
  all_goals simp [loadTy, hcell]

/-- `SrcMem.src_store_step`, the allocation count kept. -/
theorem src_store_stepN {x : String} {rel : Bool} {a b : At} {e : Expr} {ty tb : Ty} {pw wb : Word} {μ : Mode}
    {u : Ty} {sa : WeakMem.Address}
    (ht : th.term = .let_ x (.store rel a b none) e) (hea : evalAt th.env a = some (ty, [pw]))
    (heb : evalAt th.env b = some (tb, [wb])) (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u))
    (hu : accs u = some [.one]) (hp : th.promises = []) :
    ∃ th' mv, (mem.push ⟨sa, wb.val, mv⟩, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, .unit, []) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧
      th'.nalloc = th.nalloc := by
  obtain ⟨mv, vs, hs⟩ := storeUnits_one g.k g.arch pw wb sa rel (stOf mem pairs th) hp
  refine ⟨⟨e, (x, .unit, []) :: th.env, th.σs, th.stack, vs, [], th.nalloc, th.undefs, th.tidLbl, th.permit⟩, mv, ?mem, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  case mem =>
    simp only [tstep, ht, evalOp, hea, heb, hcell, addrOf, hpw, hu, List.mem_map]
    exact ⟨_, ⟨_, hs, rfl⟩, rfl⟩
  all_goals rfl

/-- `SrcMem.src_xchgAt_step`, the allocation count kept. -/
theorem src_xchgAt_stepN {x : String} {b i v : At} {e : Expr} {t ti tv : Ty} {pw : Word} {iws : List Word}
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

/-- `SrcMem.src_xchg_step`, the allocation count kept. -/
theorem src_xchg_stepN {x : String} {a v : At} {e : Expr} {t tv : Ty} {pw wv : Word} {μ : Mode} {u : Ty}
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

variable {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th}

/-- `src_load_stepN` as a thread step of thread `i`. -/
theorem src_load_step_cfgN (hi : c.ths[i]? = some th) {x : String} {acq : Bool} {a : At} {e : Expr} {ty : Ty}
    {pw : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (ht : th.term = .let_ x (.load acq a) e) (hea : evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u)) (hu : accs u = some [.one])
    (hj : SLatest c.mem sa j) (hm : c.mem[j]? = some m) :
    ∃ th', { c with ths := c.ths.set! i th' } ∈ threadSteps p k arch c i ∧ th'.term = e ∧
      th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨th', h, h1⟩ := src_load_stepN (gOf p k arch c i) c.mem c.pairs th ht hea hpw hcell hu hj hm
  exact ⟨th', mem_threadSteps hi h, h1⟩

/-- `src_store_stepN` as a thread step of thread `i`. -/
theorem src_store_step_cfgN (hi : c.ths[i]? = some th) {x : String} {rel : Bool} {a b : At} {e : Expr}
    {ty tb : Ty} {pw wb : Word} {μ : Mode} {u : Ty} {sa : WeakMem.Address}
    (ht : th.term = .let_ x (.store rel a b none) e) (hea : evalAt th.env a = some (ty, [pw]))
    (heb : evalAt th.env b = some (tb, [wb])) (hpw : pw.val = .loc sa 0) (hcell : cellOf ty = some (μ, u))
    (hu : accs u = some [.one]) (hp : th.promises = []) :
    ∃ th' mv, { c with mem := c.mem.push ⟨sa, wb.val, mv⟩, ths := c.ths.set! i th' } ∈ threadSteps p k arch c i ∧
      th'.term = e ∧ th'.env = (x, .unit, []) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨th', mv, h, h1⟩ := src_store_stepN (gOf p k arch c i) c.mem c.pairs th ht hea heb hpw hcell hu hp
  exact ⟨th', mv, mem_threadSteps hi h, h1⟩

/-- `SrcMem.src_swap_step_cfg`, the allocation count kept. -/
theorem src_swap_step_cfgN (hi : c.ths[i]? = some th) {x : String} {sa : WeakMem.Address} {u : Ty} {v : At}
    {e : Expr} {tv : Ty} {wv : Word} {j : Nat} {m : WeakMem.Msg}
    (hs : Spike.Lib.XchgSite ⟨th.term, th.env, none⟩ x sa u v e) (hev : evalAt th.env v = some (tv, [wv]))
    (hp : th.promises = []) (hj : SLatest c.mem sa j) (hm : c.mem[j]? = some m) :
    ∃ th' mv, { c with mem := c.mem.push ⟨sa, wv.val, mv⟩, ths := c.ths.set! i th' } ∈
        threadSteps p k arch c i ∧ th'.term = e ∧ th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc := by
  obtain ⟨hu, ⟨a, t, pw, μ, ht, hea, hpw, hcell⟩ | ⟨b, i', t, pw, ti, iws, μ, sb, kk, ht, heb, hpw, hbuf, hei, hk,
    rfl⟩⟩ := hs
  · obtain ⟨th', mv, h, h1⟩ :=
      src_xchg_stepN (gOf p k arch c i) c.mem c.pairs th ht hea hev hpw hcell hu hp hj hm
    exact ⟨th', mv, mem_threadSteps hi h, h1⟩
  · obtain ⟨th', mv, h, h1⟩ :=
      src_xchgAt_stepN (gOf p k arch c i) c.mem c.pairs th ht heb hei hev hpw hbuf hu hk hp hj hm
    exact ⟨th', mv, mem_threadSteps hi h, h1⟩

end Spike.Lib.SrcMemN
