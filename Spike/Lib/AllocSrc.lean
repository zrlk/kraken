/-
**The source `newBuf` step lifted to the one-thread invariant**: the
`TermRun.tstep` case of `let x = newBuf a τ in e` (the fresh label
`freshLabel …` of the thread's next allocation, `k · w` words with the zero
words of the element type, `TermRun.allocBuf`) as a thread step of a
configuration, with `Scc.Sem.Inv1` placing that label at a target base.

- `newBufZero`: the zero words `newBuf` gives a buffer of element type `τ'`
  (`zeroWords τ'` when `τ'` is `Zeroable`, else none: every word `undef`).
- `src_newBuf_stepZ`, `src_newBuf_stepZ_cfg`: `Spike.Lib.SrcMem.src_newBuf_step`
  with the zero words and the initialised count exposed (`newBufZero`; `k`
  initialised elements when there are zero words, else 0).
- `zeroWords_rep_of_simple`, `newBufZero_lanes`: every zero word of a
  scalar element type (an integer, a fixed-width number, lanes) represents
  0; lanes are `Zeroable`.
- `Inv1.newBuf_src`: the lift. From `Inv1` over the configuration's memory,
  a thread at `newBuf` of `k` elements of `w` words each, and a base `b`
  for the fresh label meeting `Inv1.alloc`'s placement premises (aligned,
  in the heap arena, disjoint from every placed label, target messages
  there only outstanding promises, initial values zero), the thread steps
  to the continuation with `x` bound to the label's locative, and `Inv1`
  holds over the new memory with the label placed at `b` with `k · w`
  words.
-/
import Scc.Sem.RowsAlloc
import Spike.Lib.SrcMem

namespace Spike.Lib.AllocSrc

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (Inv1 ValRep Range lrange wordLoc)

/-! ## The zero words of a buffer -/

/-- **The zero words `newBuf` gives** a buffer of element type `τ'`: its
`zeroWords` when it is `Zeroable`, else none (each word born `undef`). -/
def newBufZero (τ' : Ty) : Option (List WeakMem.Val) :=
  if zeroableIn [] [] τ' then zeroWords τ' else none

/-- Lanes are `Zeroable`, with one zero word. -/
theorem newBufZero_lanes (sg : Bool) (w : Wd) : newBufZero (.lanes sg w) = some [.num 0] := by
  simp [newBufZero, zeroableIn, zeroWords]

/-- Every zero word of a scalar element type (an integer, a fixed-width
number, lanes) represents 0, under every placement. -/
theorem zeroWords_rep_of_simple {τ : Ty}
    (hτ : τ = .int ∨ (∃ n, τ = .intS n) ∨ (∃ sg w, τ = .fix sg w) ∨ (∃ sg w, τ = .lanes sg w))
    (lbl : WeakMem.AllocLabel → Option Nat) :
    ∀ vs, zeroWords τ = some vs → ∀ v ∈ vs, ValRep lbl v 0 := by
  intro vs hz v hv
  rcases hτ with rfl | ⟨n, rfl⟩ | ⟨sg, w, rfl⟩ | ⟨sg, w, rfl⟩ <;>
  · simp only [zeroWords, Option.some.injEq] at hz
    subst hz
    simp only [List.mem_singleton] at hv
    subst hv
    exact ⟨by decide, rfl⟩

/-- `newBufZero`'s words represent 0 when `zeroWords`' do. -/
theorem newBufZero_rep {τ' : Ty} {lbl : WeakMem.AllocLabel → Option Nat}
    (hz : ∀ vs, zeroWords τ' = some vs → ∀ v ∈ vs, ValRep lbl v 0) :
    ∀ vs, newBufZero τ' = some vs → ∀ v ∈ vs, ValRep lbl v 0 := by
  intro vs h
  unfold newBufZero at h
  split at h
  · exact hz vs h
  · cases h

/-! ## The source step -/

section Step

variable {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}

/-- **The source buffer allocation, zero words exposed**: at `let x =
newBuf a τ in e` with `a` the number `k` and the closed element type's
accesses `us`, the thread allocates `k · nWords us` words at the fresh label
of its next allocation with the zero words `newBufZero` of the element
type, binding `x` to the untagged locative to its first word at the
buffer's type (`k` elements initialised when there are zero words, else
none); the paired timestamps, promises, type arguments and frames are
unchanged, and the allocation count goes up by one. -/
theorem src_newBuf_stepZ {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat}
    {us : List Acc}
    (ht : th.term = .let_ x (.newBuf a τ) e) (hea : evalAt th.env a = some (ta, ws))
    (hk : numOf ws = some k) (hus : accs (close th.σs τ) = some us) :
    ∃ th', ((allocBuf (freshLabel g.lbase g.n g.i th.nalloc) (k * nWords us) (newBufZero (close th.σs τ))
        (stOf mem pairs th)).1.mem, pairs, th') ∈ tstep g mem pairs th ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit k) (close th.σs τ)))
          (.ini (.lit (if (newBufZero (close th.σs τ)).isSome then k else 0))),
        [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 := by
  let τ' := close th.σs τ
  let z := newBufZero τ'
  let ini := if z.isSome then k else 0
  let lbl := freshLabel g.lbase g.n g.i th.nalloc
  refine ⟨withS { th with term := e, env := (x, .refine (.loc .own (.array (.lit k) τ')) (.ini (.lit ini)),
    [cst (.loc ⟨lbl, 0⟩ 0)]) :: th.env } (allocBuf lbl (k * nWords us) z (stOf mem pairs th)).1, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [tstep, ht, evalOp, hea, hus, ol, List.mem_map]
  refine ⟨((allocBuf lbl (k * nWords us) z (stOf mem pairs th)).1,
    .refine (.loc .own (.array (.lit k) τ')) (.ini (.lit ini)), [cst (.loc ⟨lbl, 0⟩ 0)]), ?_, rfl⟩
  simp only [hk, Option.toList, Option.bind, bind, pure, List.mem_singleton]; rfl

end Step

section Cfg

variable {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th : TTh}

/-- `src_newBuf_stepZ` as a thread step of thread `i`. -/
theorem src_newBuf_stepZ_cfg (hi : c.ths[i]? = some th) {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List Word} {k : Nat} {us : List Acc}
    (ht : th.term = .let_ x (.newBuf a τ) e) (hea : evalAt th.env a = some (ta, ws))
    (hk : numOf ws = some k) (hus : accs (close th.σs τ) = some us) :
    ∃ th', { c with mem := (allocBuf (freshLabel c.lbase c.n i th.nalloc) (k * nWords us)
        (newBufZero (close th.σs τ)) (stOf c.mem c.pairs th)).1.mem, ths := c.ths.set! i th' } ∈
          threadSteps p kn arch c i ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit k) (close th.σs τ)))
          (.ini (.lit (if (newBufZero (close th.σs τ)).isSome then k else 0))),
        [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 := by
  obtain ⟨th', h, h1⟩ := src_newBuf_stepZ (g := gOf p kn arch c i) (mem := c.mem)
    (pairs := c.pairs) ht hea hk hus
  exact ⟨th', Spike.Lib.SrcMem.mem_threadSteps hi h, h1⟩

/-! ## The lift to `Inv1` -/

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}

/-- **The source `newBuf` step under the one-thread invariant**: thread `i`
of `c`, whose memory the invariant relates, at `let x = newBuf a τ in e`
(`a` the number `k`, the closed element type's accesses `us`, `n = k ·
nWords us` words), with the fresh label `l = freshLabel c.lbase c.n i
th.nalloc` not yet placed and a word-aligned base `b` in the heap arena,
disjoint from every placed label, where every target message is an
outstanding promise of the thread and every initial value is zero, and
the element type's zero words representing 0 (`hz`; `zeroWords_rep_of_simple`
for scalars): the thread steps to `e` with `x` bound to `l`'s locative, and
the invariant holds over the new memory with `l` placed at `b` with `n`
words, each new message imaged at the initial write. -/
theorem _root_.Scc.Sem.Inv1.newBuf_src (h : Inv1 Λ lbl lsize ts t tm c.mem) (hi : c.ths[i]? = some th)
    {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat} {us : List Acc} {b : Nat}
    (ht : th.term = .let_ x (.newBuf a τ) e) (hea : evalAt th.env a = some (ta, ws))
    (hk : numOf ws = some k) (hus : accs (close th.σs τ) = some us)
    (hfresh : lbl (freshLabel c.lbase c.n i th.nalloc) = none) (hb : b % 8 = 0)
    (hheap : (Range.mk b (8 * (k * nWords us))).Sub Λ.heap)
    (hdisj : ∀ l' b', lbl l' = some b' → (Range.mk b (8 * (k * nWords us))).Disjoint (lrange lsize l' b'))
    (hnone : ∀ k' w, tm.get? k' = some w → (Range.mk b (8 * (k * nWords us))).contains w.loc.addr.toNat →
      k' ∈ t.prom)
    (hinit : ∀ j < k * nWords us, tm.initVal (wordLoc (b + 8 * j)) = 0)
    (hz : ∀ vs, zeroWords (close th.σs τ) = some vs → ∀ v ∈ vs,
      ValRep (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then some b else lbl l') v 0) :
    ∃ th', { c with mem := (allocBuf (freshLabel c.lbase c.n i th.nalloc) (k * nWords us)
        (newBufZero (close th.σs τ)) (stOf c.mem c.pairs th)).1.mem, ths := c.ths.set! i th' } ∈
          threadSteps p kn arch c i ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit k) (close th.σs τ)))
          (.ini (.lit (if (newBufZero (close th.σs τ)).isSome then k else 0))),
        [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      Inv1 Λ (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then some b else lbl l')
        (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then k * nWords us else lsize l')
        (fun k' => if c.mem.size ≤ k' ∧ k' < c.mem.size + k * nWords us then some 0 else ts k') t tm
        (allocBuf (freshLabel c.lbase c.n i th.nalloc) (k * nWords us)
          (newBufZero (close th.σs τ)) (stOf c.mem c.pairs th)).1.mem := by
  obtain ⟨th', hs, h1⟩ := src_newBuf_stepZ_cfg (p := p) (kn := kn) (arch := arch) hi ht hea hk hus
  exact ⟨th', hs, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2,
    h.allocBuf_src hfresh hb hheap hdisj hnone hinit (newBufZero_rep hz) rfl⟩

end Cfg

end Spike.Lib.AllocSrc
