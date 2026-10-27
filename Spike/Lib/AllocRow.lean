/-
**The allocator's arena contract and the allocation row** (one thread,
promises never mirrored).

`scc_rt_alloc` (`Scc/Lower/Runtime.lean`, `allocF`; `Scc/Sem/HeapCtr.lean`)
hands out the arena `[heap, heap + 16 · cells)` in 16-byte cells from a
cursor: the source heap use `hu` (the counter `scc_rt_heap_use` once no
allocation is pending). The facts the allocation row of the memory
invariant needs about it (`Scc.Sem.Inv1.alloc`'s placement premises) are
not consequences of the code's rows alone; they are a **contract** on the
runtime, stated here as an invariant of the target memory, which a
consumer carries and every step keeps. It is not trusted text: a whole
program proof establishes it at load and keeps it.

**What the contract encodes** (`ArenaOK … heap cells hu ex`):

- **the cursor**: `hu ≤ cells`, and the arena lies in the layout's heap
  region, 16-aligned;
- **handed-out space below the cursor**: every placed label's range is
  disjoint from the free range `[heap + 16 · hu, heap + 16 · cells)`
  (`freeR`);
- **the zeroed arena**: every initial value in the free range is 0 (the
  arena is in `.bss`);
- **never written past the cursor**: every target message at an address of
  the free range is an outstanding promise of the thread, but at the
  addresses `ex` (the header word of an allocation in progress, stored by
  `scc_rt_alloc` before it returns).

The runtime facts behind it, for the consumer's node obligations: the
counter and every runtime word other than an allocation's header lie
outside the free range; the header of an allocation from cursor `old` is
at `heap + 16 · old + off - 8`, below the buffer `[heap + 16 · old + off,
… + 8 · n)`, and the object fits its cells (`off + 8 · n ≤ 16 · u`, the
lowering's check, `Scc.Sem.slot_sub_arena`).

Contents:

- `get?_append`: the messages of an appended memory.
- `freeR`, `ArenaOK`: the free range and the contract.
- `ArenaOK.init`: at load (no label placed, no message, `.bss` zero).
- `ArenaOK.keep`: kept by any memory change that adds no message at a free
  address off the exceptions, and keeps the promises there outstanding (a
  store to a placed label, a runtime store outside the free range, the
  counter's add, a promise); `ArenaOK.store_out`: an appended message
  outside the free range; `ArenaOK.store_ex`: the header store, recorded
  as an exception.
- `ArenaOK.buf`: the buffer range of an allocation from the cursor meets
  `Inv1.alloc`'s placement premises.
- `ArenaOK.place`: after the label is placed there and the cursor moved
  past the object's cells, the contract holds with no exception.
- `row_alloc`: **the allocation row**: from `Inv1` and the contract, a
  source thread at `newBuf` with the cursor at `old`, the base
  `A = heap + 16 · old + off` (the row `Out.alloc`'s): the source step at
  the fresh label, `Inv1` with the label placed at `A`, and the contract at
  `old + u`.
-/
import Spike.Lib.AllocSrc

namespace Spike.Lib.AllocRow

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (Inv1 ValRep Range lrange wordLoc)

/-! ## The contract -/

/-- A message of an appended memory: the new one at `|M| + 1`, else the old
one. -/
theorem get?_append (tm : Memory) (w : Msg) (k' : Nat) :
    (tm.append w).1.get? k' = if k' = tm.last + 1 then some w else tm.get? k' := by
  unfold Memory.get? Memory.append Memory.last
  by_cases h0 : k' = 0
  · subst h0; simp
  · simp only [h0, ite_false]
    rw [Array.getElem?_push]
    by_cases h1 : k' - 1 = tm.msgs.size
    · have h2 : k' = tm.msgs.size + 1 := by omega
      simp [h2]
    · have h2 : ¬ k' = tm.msgs.size + 1 := by omega
      simp [h1, h2]

/-- **The free range** of the arena at `heap` of `cells` 16-byte cells,
past the cursor `hu`. -/
def freeR (heap cells hu : Nat) : Range := ⟨heap + 16 * hu, 16 * (cells - hu)⟩

/-- **The arena contract** of a one-thread run (layout `Λ`, placement
`lbl`/`lsize`, thread `t`, target memory `tm`; the arena at `heap` of
`cells` cells, the cursor `hu`, the exceptions `ex`): see the module
docstring. -/
structure ArenaOK {I : ISA} (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (t : Thread I) (tm : Memory) (heap cells hu : Nat) (ex : Nat → Prop) :
    Prop where
  /-- The cursor is within the arena. -/
  hu_le : hu ≤ cells
  /-- The arena is in the heap region. -/
  sub : (Range.mk heap (16 * cells)).Sub Λ.heap
  /-- The arena is 16-aligned. -/
  align : heap % 16 = 0
  /-- Every placed label lies off the free range. -/
  disj : ∀ l b, lbl l = some b → (freeR heap cells hu).Disjoint (lrange lsize l b)
  /-- The free range is zero at the initial write. -/
  zero : ∀ a, (freeR heap cells hu).contains a → tm.initVal (wordLoc a) = 0
  /-- Every message in the free range off the exceptions is an outstanding
  promise. -/
  fresh : ∀ k' w, tm.get? k' = some w → (freeR heap cells hu).contains w.loc.addr.toNat →
    ¬ ex w.loc.addr.toNat → k' ∈ t.prom

namespace ArenaOK

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {t : Thread I} {tm : Memory} {heap cells hu : Nat} {ex : Nat → Prop}

/-- **The contract at load**: no label placed, no message, the arena zero
at the initial write, the cursor at 0. -/
theorem init (hsub : (Range.mk heap (16 * cells)).Sub Λ.heap) (hal : heap % 16 = 0)
    (hz : ∀ a, (freeR heap cells 0).contains a → tm.initVal (wordLoc a) = 0)
    (hm : ∀ k', tm.get? k' = none) :
    ArenaOK Λ (fun _ => none) lsize t tm heap cells 0 (fun _ => False) :=
  ⟨Nat.zero_le _, hsub, hal, (fun _ _ h => by cases h), hz, (fun k' w h => by rw [hm k'] at h; cases h)⟩

/-- **The contract is kept** by a change of memory and thread that keeps the
initial values of the free range, adds no message there (off the new
exceptions `ex'`) but old ones off the old exceptions, and keeps every
outstanding promise there outstanding; the placement and cursor
unchanged. -/
theorem keep (h : ArenaOK Λ lbl lsize t tm heap cells hu ex) {t' : Thread I} {tm' : Memory} {ex' : Nat → Prop}
    (hiv : ∀ a, (freeR heap cells hu).contains a → tm'.initVal (wordLoc a) = tm.initVal (wordLoc a))
    (hnew : ∀ k' w, tm'.get? k' = some w → (freeR heap cells hu).contains w.loc.addr.toNat →
      ¬ ex' w.loc.addr.toNat → (tm.get? k' = some w ∧ ¬ ex w.loc.addr.toNat) ∨ k' ∈ t'.prom)
    (hprom : ∀ k' w, tm.get? k' = some w → (freeR heap cells hu).contains w.loc.addr.toNat → k' ∈ t.prom →
      k' ∈ t'.prom) :
    ArenaOK Λ lbl lsize t' tm' heap cells hu ex' :=
  ⟨h.hu_le, h.sub, h.align, h.disj, fun a ha => (hiv a ha).trans (h.zero a ha), fun k' w hk ha hx =>
    (hnew k' w hk ha hx).elim (fun ⟨ho, hnx⟩ => hprom k' w ho ha (h.fresh k' w ho ha hnx)) id⟩

/-- **An appended message outside the free range** (a store to a placed
label, a runtime store off the arena, the counter's add) keeps the
contract, the promises unchanged. -/
theorem store_out (h : ArenaOK Λ lbl lsize t tm heap cells hu ex) {t' : Thread I} {w : Msg}
    (hw : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hp : t'.prom = t.prom) :
    ArenaOK Λ lbl lsize t' (tm.append w).1 heap cells hu ex := by
  refine h.keep (fun _ _ => rfl) (fun k' w' hk ha hx => ?_) (fun _ _ _ _ h => hp ▸ h)
  rw [get?_append] at hk
  split at hk
  · cases hk; exact absurd ha hw
  · exact .inl ⟨hk, hx⟩

/-- **The header store**: an appended message at address `x`, recorded as
an exception, keeps the contract, the promises unchanged. -/
theorem store_ex (h : ArenaOK Λ lbl lsize t tm heap cells hu ex) {t' : Thread I} {w : Msg}
    (hp : t'.prom = t.prom) :
    ArenaOK Λ lbl lsize t' (tm.append w).1 heap cells hu (fun a => ex a ∨ a = w.loc.addr.toNat) := by
  refine h.keep (fun _ _ => rfl) (fun k' w' hk ha hx => ?_) (fun _ _ _ _ h => hp ▸ h)
  rw [get?_append] at hk
  split at hk
  · cases hk; exact absurd (.inr rfl) hx
  · exact .inl ⟨hk, fun hx' => hx (.inl hx')⟩

/-- **The buffer of an allocation from the cursor** `[A, A + 8 n)`, with
`A = heap + 16 · hu + off` word-aligned, the object fitting `u` cells within
the arena (`off + 8 n ≤ 16 u`, `hu + u ≤ cells`) and every exception below
`A` (the header): `Inv1.alloc`'s placement premises (aligned, in the heap
region, disjoint from every placed label, every message there an
outstanding promise, zero at the initial write). -/
theorem buf (h : ArenaOK Λ lbl lsize t tm heap cells hu ex) {off n u : Nat} (hoff : off % 8 = 0)
    (hfit : off + 8 * n ≤ 16 * u) (hle : hu + u ≤ cells) (hex : ∀ a, ex a → a < heap + 16 * hu + off) :
    (heap + 16 * hu + off) % 8 = 0 ∧ (Range.mk (heap + 16 * hu + off) (8 * n)).Sub Λ.heap ∧
      (∀ l' b', lbl l' = some b' → (Range.mk (heap + 16 * hu + off) (8 * n)).Disjoint (lrange lsize l' b')) ∧
      (∀ k' w, tm.get? k' = some w → (Range.mk (heap + 16 * hu + off) (8 * n)).contains w.loc.addr.toNat →
        k' ∈ t.prom) ∧
      (∀ i < n, tm.initVal (wordLoc (heap + 16 * hu + off + 8 * i)) = 0) := by
  have hal := h.align
  have hsub := h.sub
  have hsubF : ∀ a, (Range.mk (heap + 16 * hu + off) (8 * n)).contains a → (freeR heap cells hu).contains a := by
    intro a ha
    simp only [Range.contains, freeR] at ha ⊢
    omega
  refine ⟨by omega, ?_, fun l' b' hl => ?_, fun k' w hk ha => ?_, fun i hi => h.zero _ (hsubF _ ?_)⟩
  · simp only [Range.Sub] at hsub ⊢; omega
  · have hd := h.disj l' b' hl
    simp only [Range.Disjoint, freeR] at hd ⊢
    omega
  · refine h.fresh k' w hk (hsubF _ ha) fun hx => ?_
    have := hex _ hx
    simp only [Range.contains] at ha
    omega
  · simp only [Range.contains]; omega

/-- **After the placement**: the label `l` (not placed) at `A = heap + 16 ·
hu + off` with `n` words, the object fitting `u` cells within the arena,
every exception below the new cursor: the contract at `hu + u` with no
exception, the label placed. -/
theorem place (h : ArenaOK Λ lbl lsize t tm heap cells hu ex) {l : WeakMem.AllocLabel} {off n u : Nat}
    (hfit : off + 8 * n ≤ 16 * u) (hle : hu + u ≤ cells) (hex : ∀ a, ex a → a < heap + 16 * (hu + u)) :
    ArenaOK Λ (fun l' => if l' = l then some (heap + 16 * hu + off) else lbl l')
      (fun l' => if l' = l then n else lsize l') t tm heap cells (hu + u) (fun _ => False) := by
  have hsh : ∀ a, (freeR heap cells (hu + u)).contains a → (freeR heap cells hu).contains a := by
    intro a ha
    simp only [Range.contains, freeR] at ha ⊢
    omega
  refine ⟨hle, h.sub, h.align, fun l' b' hl => ?_, fun a ha => h.zero a (hsh a ha), fun k' w hk ha _ => ?_⟩
  · by_cases he : l' = l
    · subst he
      simp only [ite_true, Option.some.injEq] at hl
      subst hl
      simp only [Range.Disjoint, freeR, lrange, ite_true]
      omega
    · simp only [he, ite_false] at hl
      have hd := h.disj l' b' hl
      simp only [Range.Disjoint, freeR, lrange, he, ite_false] at hd ⊢
      omega
  · refine h.fresh k' w hk (hsh _ ha) fun hx => ?_
    have := hex _ hx
    simp only [Range.contains, freeR] at ha
    omega

end ArenaOK

/-! ## The allocation row -/

section Row

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th : TTh}

/-- **The allocation row**: thread `i` of the source configuration `c`,
whose memory the one-thread invariant relates, at `let x = newBuf a τ in e`
(`k` elements of `us` accesses, `n = k · nWords us` words), its fresh label
not placed, the element type's zero words representing 0 (`hz`); the arena
contract at the cursor `old` with its exceptions below the base; the base
`A = heap + 16 · old + off` word-aligned, the object fitting the `u` cells
the allocation takes within the arena. Then the source steps to `e` with
`x` bound to the label's locative; the invariant holds with the label
placed at `A` with `n` words, over the new memory; and the contract holds
at `old + u` with the label placed and no exception. The target memory and
thread do not change (the row is the allocator's last instruction,
`Out.alloc`). -/
theorem row_alloc (h : Inv1 Λ lbl lsize ts t tm c.mem) {heap cells old : Nat} {ex : Nat → Prop}
    (ha : ArenaOK Λ lbl lsize t tm heap cells old ex) (hi : c.ths[i]? = some th)
    {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat} {us : List Acc}
    {off u : Nat}
    (ht : th.term = .let_ x (.newBuf a τ) e) (hea : evalAt th.env a = some (ta, ws))
    (hk : numOf ws = some k) (hus : accs (close th.σs τ) = some us)
    (hfresh : lbl (freshLabel c.lbase c.n i th.nalloc) = none)
    (hoff : off % 8 = 0) (hfit : off + 8 * (k * nWords us) ≤ 16 * u) (hle : old + u ≤ cells)
    (hex : ∀ a', ex a' → a' < heap + 16 * old + off)
    (hz : ∀ vs, zeroWords (close th.σs τ) = some vs → ∀ v ∈ vs,
      ValRep (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then some (heap + 16 * old + off) else lbl l')
        v 0) :
    ∃ th', { c with mem := (allocBuf (freshLabel c.lbase c.n i th.nalloc) (k * nWords us)
        (AllocSrc.newBufZero (close th.σs τ)) (stOf c.mem c.pairs th)).1.mem, ths := c.ths.set! i th' } ∈
          threadSteps p kn arch c i ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit k) (close th.σs τ)))
          (.ini (.lit (if (AllocSrc.newBufZero (close th.σs τ)).isSome then k else 0))),
        [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      Inv1 Λ (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then some (heap + 16 * old + off) else lbl l')
        (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then k * nWords us else lsize l')
        (fun k' => if c.mem.size ≤ k' ∧ k' < c.mem.size + k * nWords us then some 0 else ts k') t tm
        (allocBuf (freshLabel c.lbase c.n i th.nalloc) (k * nWords us)
          (AllocSrc.newBufZero (close th.σs τ)) (stOf c.mem c.pairs th)).1.mem ∧
      ArenaOK Λ (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then some (heap + 16 * old + off) else lbl l')
        (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then k * nWords us else lsize l') t tm heap cells
        (old + u) (fun _ => False) := by
  obtain ⟨hb, hheap, hdisj, hnone, hinit⟩ := ha.buf hoff hfit hle hex
  obtain ⟨th', hs, h1, h2, h3, h4, h5, h6, hinv⟩ :=
    h.newBuf_src (p := p) (kn := kn) (arch := arch) hi ht hea hk hus hfresh hb hheap hdisj hnone hinit hz
  exact ⟨th', hs, h1, h2, h3, h4, h5, h6, hinv,
    ha.place hfit hle fun a' hx => by have := hex a' hx; omega⟩

end Row

end Spike.Lib.AllocRow
