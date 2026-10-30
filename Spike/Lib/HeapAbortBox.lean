/-
**The heap abort at a box allocation**, ISA-free: the source half of the
heap abort at `let x = new a in e` (a one-word value), beside the buffer
allocation's (`Spike/Lib/HeapAbort.lean`, which it leaves unchanged).

* `HeapReadyBox cells old c`: the control is at a box allocation `let x =
  new a in e` of a one-word value, whose two heap units (the word and the
  allocator's header; the box is not a thread-id box) take the heap use
  `old` from within `cells` to past it;
* `HeapReadyA`: `HeapReady` or `HeapReadyBox`;
* `abortJustified_heap_source_box`: a heap abort of thread 0 is justified at
  a configuration whose thread 0 is `HeapReadyBox` at the configuration's
  heap use, has no promises, whose next allocation label is fresh and whose
  thread-id boxes were counted by allocations: the `new` step
  (`NewRow.src_new_step_cfg`) grows the heap use by two
  (`NewRow.cellAlloc_new`, the box label kept), crossing the heap part;
* `abortJustified_heap_sourceA`: the same for `HeapReadyA`;
* an `example`: at `hello.w`'s `let o = new z`, `HeapReadyBox` holds at the
  overflowing heap uses;
* `AtAlloc`, `HeapAbortOblA`, `HeapCtrA`, `HeapAbortOblA.at_heapCtr`: the
  abort site's heap obligation and the relation's heap clause
  (`Spike/Lib/HeapObl.lean`) guarded on either allocation;
  `HeapAbortObl.toA`, `HeapCtrA.toHeapCtr`, `AllocInvAt.heapCtrA`.
-/
import Spike.Lib.HeapObl
import Spike.Lib.NewRow

namespace Spike.Lib

open CoreLang CoreTerm
open Scc.Sem (SrcSem AbortJustified Budget heapUse allocCount boxCount Fresh)
open Scc.Sem.SrcSem (mainExit)

/-- **The source thread's box allocation crosses the heap budget**: its
term is `let x = new a in e`, `a` a one-word value, and its two units (the
word and the header) take the heap use `old` from within `cells` to past
it. Only the term and the environment are read (not the hold). -/
def HeapReadyBox (cells old : Nat) (c : Ctl) : Prop :=
  ∃ (x : String) (a : At) (e : Expr) (t : Ty) (w : TermRun.Word),
    c.term = .let_ x (.new a) e ∧ TermRun.evalAt c.env a = some (t, [w]) ∧
      TermRun.accs t = some [.one] ∧ old ≤ cells ∧ cells < old + 2

/-- **A heap-crossing allocation**: a buffer's (`HeapReady`) or a box's
(`HeapReadyBox`). -/
def HeapReadyA (cells old : Nat) (c : Ctl) : Prop := HeapReady cells old c ∨ HeapReadyBox cells old c

/-- **The heap abort is justified for `SrcSem.source P p`** at a
configuration whose thread 0 is `HeapReadyBox` at the configuration's heap
use, has no promises (at any call depth), whose next allocation label is
fresh, and whose thread-id boxes were counted by allocations (`hbx`): the
`new` step (certified by the empty solo run) grows the heap use by two,
crossing the heap part (`AbortJustified.heap_of_crossing`). -/
theorem abortJustified_heap_source_box {P : SrcSem.SrcParams} {p : Prog} {B : Budget} {tr : List Scc.Sem.Ev}
    {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th)
    (hc : HeapReadyBox B.cells (heapUse s) (Ctl.of th)) (hp : th.promises = [])
    (hfresh : Fresh s (TermRun.freshLabel s.lbase s.n 0 th.nalloc)) (hbx : boxCount s ≤ allocCount s) :
    AbortJustified B (SrcSem.source P p) tr s 0 .heap := by
  obtain ⟨x, a, e, t, w, ht, ha, hu, hle, hlt⟩ := hc
  simp only [Ctl.of] at ht ha
  obtain ⟨mv, th', hm, -, -, hp', -, -, hn, htl⟩ :=
    NewRow.src_new_step_cfg (p := p) (kn := P.k) (arch := P.arch) hi ht ha hu hp
  have hlt0 : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine AbortJustified.heap_of_crossing (u := 2) ⟨?_, ⟨.inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), rfl⟩⟩ ?_ hle hlt
  · unfold mainExit
    rw [hi]
    simp only [ht]
  · simp [TermRun.noPromises, hlt0, hp']
  · show heapUse _ = heapUse s + _
    refine BoxCount.heapUse_add (NewRow.cellAlloc_new hi hfresh rfl rfl hn) ?_
      (BoxCount.boxCount_set hi rfl htl) hbx
    show allocCount s ≤ allocCount { s with ths := s.ths.set! 0 th' }
    rw [BoxCount.allocCount_succ (s' := { s with ths := s.ths.set! 0 th' }) hi rfl hn]
    exact Nat.le_succ _

/-- **The heap abort is justified** at a `HeapReadyA` configuration: by
`abortJustified_heap_source` at a buffer allocation (no type arguments) and
`abortJustified_heap_source_box` at a box allocation. -/
theorem abortJustified_heap_sourceA {P : SrcSem.SrcParams} {p : Prog} {B : Budget} {tr : List Scc.Sem.Ev}
    {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th)
    (hc : HeapReadyA B.cells (heapUse s) (Ctl.of th)) (hσ : th.σs = []) (hp : th.promises = [])
    (hfresh : Fresh s (TermRun.freshLabel s.lbase s.n 0 th.nalloc)) (hbx : boxCount s ≤ allocCount s) :
    AbortJustified B (SrcSem.source P p) tr s 0 .heap :=
  hc.elim (fun h => abortJustified_heap_source hi h hσ hp hfresh hbx)
    (fun h => abortJustified_heap_source_box hi h hp hfresh hbx)

/-- **Not vacuous at `hello.w`'s box** (`main`'s `let z = zero[Int]; let o =
new z`, `SpawnViewLtSteps.mZ`): with `z` bound to `zero[Int]`'s word, the
control at the `new` is `HeapReadyBox` at every heap use `old` that the
two units carry past `cells` from within them (`cells - 1` or `cells`).
On `wakeSrc` itself: `Spike/Test/HeapAbortBoxWake.lean`. -/
example {cells old : Nat} {e : Expr} {env : TermRun.Env} {h : Option (Nat × TermRun.Word)}
    (hle : old ≤ cells) (hlt : cells < old + 2) :
    HeapReadyBox cells old ⟨.let_ "o" (.new (.var "z")) e, ("z", .int, [TermRun.cst (.num 0)]) :: env, h⟩ :=
  ⟨"o", .var "z", e, .int, TermRun.cst (.num 0), rfl, by simp [TermRun.evalAt, TermRun.lookupE], rfl, hle, hlt⟩

/-! ## The abort site's heap obligation at either allocation

`HeapAbortObl`/`HeapCtr` (`Spike/Lib/HeapObl.lean`) guard on `AtNewBuf`: at
a box allocation their premise is vacuous, so they ask `HeapReady` at every
`old`. The `A` forms guard on `AtAlloc` and ask `HeapReadyA`. -/

/-- **The control is at an allocation**: a buffer's or a box's. -/
def AtAlloc (c : Ctl) : Prop := AtNewBuf c ∨ ∃ x a e, c.term = .let_ x (.new a) e

/-- **The heap disjunct of an abort site at either allocation**: for every
count `old` that the control allows at an allocation (within the cells, the
held counter word, if any, `old`), the control is `HeapReadyA`. -/
def HeapAbortOblA (cells ctr : Nat) (c : Ctl) : Prop :=
  ∀ old, (AtAlloc c → old ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num old)) →
    HeapReadyA cells old c

/-- **The relation's heap clause at either allocation**, at the source's
heap use `hu`: `hu` within the cells and the held counter word, if any,
`hu`. -/
def HeapCtrA (cells ctr hu : Nat) (c : Ctl) : Prop :=
  AtAlloc c → hu ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num hu)

/-- **The two meet at the source's heap use**, the premise of
`abortJustified_heap_sourceA`. -/
theorem HeapAbortOblA.at_heapCtr {cells ctr hu : Nat} {c : Ctl} (hab : HeapAbortOblA cells ctr c)
    (hctr : HeapCtrA cells ctr hu c) : HeapReadyA cells hu c :=
  hab hu hctr

/-- A buffer allocation's obligation gives the `A` one (its premise only
weakens, its conclusion the `.inl` disjunct). -/
theorem HeapAbortObl.toA {cells ctr : Nat} {c : Ctl} (hab : HeapAbortObl cells ctr c) :
    HeapAbortOblA cells ctr c :=
  fun old h => .inl (hab old fun hb => h (.inl hb))

/-- `HeapCtrA` gives `HeapCtr`. -/
theorem HeapCtrA.toHeapCtr {cells ctr hu : Nat} {c : Ctl} (h : HeapCtrA cells ctr hu c) : HeapCtr cells ctr hu c :=
  fun hb => h (.inl hb)

open Kraken Kraken.Promising in
/-- `AllocInvAt` gives the heap clause at either allocation (`AllocInvAt.heapCtr`). -/
theorem AllocInvAt.heapCtrA {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {t : Thread I} {tm : Memory}
    {heap cells ctr : Nat} {units off : Nat → Ty → Nat} {hu : Nat} {c : Ctl}
    (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c) : HeapCtrA cells ctr hu c := by
  intro _
  rcases h with ⟨hh, ex, -, ha⟩ | ⟨hn, -, ha⟩
  · refine ⟨ha.hu_le, fun w hw => ?_⟩
    rw [hh] at hw
    cases hw
    rfl
  · exact ⟨ha.hu_le, fun w hw => absurd hw (hn w)⟩

end Spike.Lib
