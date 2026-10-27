/-
**The heap abort at the consumers' source**, ISA-free: the source facts a
heap abort exit carries, and the justification they give for
`SrcSem.source P p` (`AbortJustified … .heap`, by
`AbortJustified.heap_of_crossing` of `Scc/Sem/Budget.lean`).

* `HeapReady cells old c`: the control is at a buffer allocation
  `let x = newBuf a τ in e` of `k` elements of `nWords us` words, whose
  source units `k · nWords us + 1` take the heap use `old` from within
  `cells` to past it;
* `abortJustified_heap_source`: a heap abort of thread 0 is justified at a
  configuration whose thread 0 is `HeapReady` at the configuration's heap
  use, has no type arguments and no promises, and whose next allocation
  label is fresh: the `newBuf` step crosses the heap part of the budget, at
  any call depth (no condition on the thread's stack).
-/
import Spike.Lib.OvfAbort
import Spike.Lib.AllocSrc
import Scc.Sem.Budget

namespace Spike.Lib

open CoreLang CoreTerm
open Scc.Sem (SrcSem AbortJustified Budget heapUse Fresh)
open Scc.Sem.SrcSem (mainExit)

/-- **The source thread's allocation crosses the heap budget**: its term is
`let x = newBuf a τ in e`, `a` the number `k`, the closed element type's
accesses `us`, and its units `k · nWords us + 1` take the heap use `old`
from within `cells` to past it. Only the term and the environment are
read (not the hold). -/
def HeapReady (cells old : Nat) (c : Ctl) : Prop :=
  ∃ (x : String) (a : At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List TermRun.Word) (k : Nat) (us : List TermRun.Acc),
    c.term = .let_ x (.newBuf a τ) e ∧ TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some k ∧
      TermRun.accs (TermRun.close [] τ) = some us ∧ old ≤ cells ∧ cells < old + (k * TermRun.nWords us + 1)

/-- **The heap abort is justified for `SrcSem.source P p`** at a
configuration whose thread 0 is `HeapReady` at the configuration's heap
use, has no type arguments and no promises (at any call depth), and whose
next allocation label (`freshLabel … 0 th.nalloc`) is fresh: the `newBuf` step
(`src_newBuf_stepZ_cfg`, certified by the empty solo run) grows the heap use
by the units (`heapUse_newBuf`), crossing the heap part
(`AbortJustified.heap_of_crossing`). -/
theorem abortJustified_heap_source {P : SrcSem.SrcParams} {p : Prog} {B : Budget} {tr : List Scc.Sem.Ev}
    {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th)
    (hc : HeapReady B.cells (heapUse s) (Ctl.of th)) (hσ : th.σs = []) (hp : th.promises = [])
    (hfresh : Fresh s (TermRun.freshLabel s.lbase s.n 0 th.nalloc)) :
    AbortJustified B (SrcSem.source P p) tr s 0 .heap := by
  obtain ⟨x, a, τ, e, ta, ws, k, us, ht, ha, hk, hus, hle, hlt⟩ := hc
  simp only [Ctl.of] at ht ha
  have hus' : TermRun.accs (TermRun.close th.σs τ) = some us := by rw [hσ]; exact hus
  obtain ⟨th', hm, -, -, hp', -, -, hn⟩ :=
    AllocSrc.src_newBuf_stepZ_cfg (p := p) (kn := P.k) (arch := P.arch) hi ht ha hk hus'
  have hlt0 : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hth : s.ths[0] = th := (Array.getElem?_eq_some_iff.mp hi).2
  refine AbortJustified.heap_of_crossing (u := k * TermRun.nWords us + 1) ⟨?_, ⟨.inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), rfl⟩⟩
    ?_ hle hlt
  · unfold mainExit
    rw [hi]
    simp only [ht]
  · simp [TermRun.noPromises, hlt0, hp', hp]
  · show heapUse _ = heapUse s + _
    refine Scc.Sem.heapUse_newBuf (st := TermRun.stOf s.mem s.pairs th) rfl rfl hfresh hlt0 ?_ (by rw [hn, hth])
    show (Array.set! s.ths 0 th') = _
    simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt0]

end Spike.Lib
