/-
**The box allocation's source side and row** (`let x = new a in e` of a
one-word value, the row `Out.newStore` of `Spike/Lib/Seg.lean`).

The source `new` (`TermRun.alloc`) of a one-word value at the thread's next
fresh label `l` pushes the cell's `undef` first message and then the
initialising store of the value, plain; `x` is bound to the untagged
locative to `⟨l, 0⟩` at `Ptr own τ`, the thread's allocation count goes up
by one, and its thread-id box (`tidLbl`) is untouched. The target pairs it
with the box word's store into the cell the allocator handed out (the
cursor `old` held, the base `A = heap + 16 · old + off`), the row
`Out.newStore`.

- `src_new_step`, `src_new_step_cfg`: the source step, as a `tstep`
  outcome and as a thread step of a configuration.
- `cellAlloc_new`, `tidLbls_new`: the source quantities heap use is built
  from: the words plus the allocations (`cellCount + allocCount`) grow by
  two (one word, one header), and no thread-id box changes. Stated without
  `heapUse` itself so that they hold whether or not `heapUse` excepts the
  thread-id boxes.
- `Inv1.new_src`: the memory relation after the placement of `l` at `b`
  (`Inv1.alloc`, the `undef` message imaged at the initial write) and the
  paired stores (`Inv1.store`).
- `row_newStore`: **the box row**: from `Inv1` and the arena contract
  (`ArenaOK`) at the cursor `old`, a source thread at `new` with no
  promise, the target's store of a value the word represents to `A`: the
  source step, `Inv1` with `l` placed at `A` (one word) after both sides,
  and the contract at `old + u` with `l` placed and no exception.
-/
import Spike.Lib.AllocRow
import Spike.Lib.HeapPresCore

namespace Spike.Lib.NewRow

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (Inv1 ValRep Range lrange wordLoc wordAddr cellCount allocCount Fresh)
open Spike.Lib.AllocRow (ArenaOK freeR get?_append)
open Spike.Lib.SrcMem (storeUnits_one mem_threadSteps)

/-! ## The source step -/

/-- **The source box allocation**: at `let x = new a in e` with `a` a
one-word value `w` (`accs t = some [.one]`) and no promise, the source
thread pushes the `undef` first message of the cell at its next fresh label
and then the store of `w`'s value there, binding `x` to the untagged
locative to the cell at `Ptr own t`; the paired timestamps, type arguments,
frames and thread-id box are unchanged, the promises stay empty, and the
allocation count goes up by one. -/
theorem src_new_step (g : G) (mem : WeakMem.Memory) (pairs : List WeakMem.Ts) (th : TTh)
    {x : String} {a : At} {e : Expr} {t : Ty} {w : Word}
    (ht : th.term = .let_ x (.new a) e) (hea : evalAt th.env a = some (t, [w]))
    (hu : accs t = some [.one]) (hp : th.promises = []) :
    ∃ mv th', ((mem.push ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, .undef, 0⟩).push
        ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, w.val, mv⟩, pairs, th') ∈ tstep g mem pairs th ∧
      th'.term = e ∧
      th'.env = (x, .ptr .own t, [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      th'.tidLbl = th.tidLbl := by
  simp only [tstep, ht, evalOp, hea, hu, alloc, List.mem_map]
  refine (storeUnits_one g.k g.arch _ w _ false _ ?hp).elim fun mv h => h.elim fun vs hs =>
    ⟨mv, _, ⟨_, ⟨_, ⟨_, hs, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  case hp => exact hp
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `src_new_step` as a thread step of thread `i`. -/
theorem src_new_step_cfg {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th : TTh}
    (hi : c.ths[i]? = some th) {x : String} {a : At} {e : Expr} {t : Ty} {w : Word}
    (ht : th.term = .let_ x (.new a) e) (hea : evalAt th.env a = some (t, [w]))
    (hu : accs t = some [.one]) (hp : th.promises = []) :
    ∃ mv th', { c with mem := ((c.mem.push ⟨⟨freshLabel c.lbase c.n i th.nalloc, 0⟩, .undef, 0⟩).push
        ⟨⟨freshLabel c.lbase c.n i th.nalloc, 0⟩, w.val, mv⟩), ths := c.ths.set! i th' } ∈
          threadSteps p kn arch c i ∧ th'.term = e ∧
      th'.env = (x, .ptr .own t, [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      th'.tidLbl = th.tidLbl := by
  obtain ⟨mv, th', h, h1⟩ := src_new_step (gOf p kn arch c i) c.mem c.pairs th ht hea hu hp
  exact ⟨mv, th', mem_threadSteps hi h, h1⟩

/-! ## The heap-use quantities -/

/-- **A box allocation's words and allocations**: the memory with the
`undef` first message and the store at a fresh label's word, the thread's
allocation count bumped: the distinct cells grow by one and the allocations
by one (`cellCount`, `allocCount`; `heapUse` is built from these). -/
theorem cellAlloc_new {c c' : Cfg} {i : Nat} {th th' : TTh} (hi : c.ths[i]? = some th) {l : WeakMem.AllocLabel}
    (hfresh : Fresh c l) {v : WeakMem.Val} {mv : Nat}
    (hmem : c'.mem = (c.mem.push ⟨⟨l, 0⟩, .undef, 0⟩).push ⟨⟨l, 0⟩, v, mv⟩) (hths : c'.ths = c.ths.set! i th')
    (hn : th'.nalloc = th.nalloc + 1) :
    cellCount c' + allocCount c' = cellCount c + allocCount c + 2 := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  have h1 : Scc.Sem.memCells (c.mem.push ⟨⟨l, 0⟩, .undef, 0⟩) = Scc.Sem.memCells c.mem + 1 :=
    Scc.Sem.memCells_allocBuf (n := 1) (zero := none) (st := stOf c.mem c.pairs c.ths[i]) hfresh
  have h2 : Scc.Sem.memCells ((c.mem.push ⟨⟨l, 0⟩, .undef, 0⟩).push ⟨⟨l, 0⟩, v, mv⟩) =
      Scc.Sem.memCells (c.mem.push ⟨⟨l, 0⟩, .undef, 0⟩) := by
    unfold Scc.Sem.memCells
    rw [Array.toList_push (xs := c.mem.push _), List.map_append, List.map_singleton,
      HeapPres.eraseDups_append_mem (List.mem_map.mpr ⟨_, Array.mem_toList_iff.mpr
        (Array.mem_push_self (xs := c.mem)), rfl⟩)]
  have hset : c.ths.set! i th' = c.ths.set i th' hlt := by
    simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
  rw [Scc.Sem.cellCount_eq, Scc.Sem.cellCount_eq, Scc.Sem.allocCount_eq, Scc.Sem.allocCount_eq, hmem, hths,
    h2, h1, hset, Scc.Sem.nallocSum_set hlt hn]
  omega

/-- **A thread replaced by one with the same thread-id box** keeps every
thread's box (so the count of thread-id boxes). -/
theorem tidLbls_new {c c' : Cfg} {i : Nat} {th th' : TTh} (hi : c.ths[i]? = some th)
    (hths : c'.ths = c.ths.set! i th') (htid : th'.tidLbl = th.tidLbl) :
    c'.ths.toList.map (·.tidLbl) = c.ths.toList.map (·.tidLbl) := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  rw [hths]
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, dite_true, Array.toList_set,
    List.map_set]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_set]
  split
  · subst_vars; simp [htid]
  · rfl

/-! ## The memory relation -/

/-- **The box row's memory relation**: placing the fresh label `l` at the
word-aligned `b` with one word (`Inv1.alloc`'s premises, the cell's
`undef` first message imaged at the initial write), and then the target's
store of `v` to `b` paired with the source's store to `⟨l, 0⟩` of a value
`v` represents (`Inv1.store`, fulfilling or appending): the invariant holds
of the thread after, over the source memory with both messages pushed. -/
theorem _root_.Scc.Sem.Inv1.new_src {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
    {sm : WeakMem.Memory} (h : Inv1 Λ lbl lsize ts t tm sm) {l : WeakMem.AllocLabel} {b : Nat}
    (hfresh : lbl l = none) (hb : b % 8 = 0) (hheap : (Range.mk b (8 * 1)).Sub Λ.heap)
    (hdisj : ∀ l' b', lbl l' = some b' → (Range.mk b (8 * 1)).Disjoint (lrange lsize l' b'))
    (hnone : ∀ k' w, tm.get? k' = some w → (Range.mk b (8 * 1)).contains w.loc.addr.toNat → k' ∈ t.prom)
    (hinit : ∀ i < 1, tm.initVal (wordLoc (b + 8 * i)) = 0)
    (A : Arch) {tid : Nat} {kr : StoreKind} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc b) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) {sv : WeakMem.Val} {mv : Nat}
    (hv : ValRep lbl sv v.toNat) :
    o.thread.st = s ∧ ∃ q, Inv1 Λ (fun l' => if l' = l then some b else lbl l')
      (fun l' => if l' = l then 1 else lsize l')
      (fun k => if k = sm.size + 1 then some q else if sm.size ≤ k ∧ k < sm.size + 1 then some 0 else ts k)
      o.thread o.mem ((sm.push ⟨⟨l, 0⟩, .undef, 0⟩).push ⟨⟨l, 0⟩, sv, mv⟩) := by
  have h1 := h.alloc (n := 1) (sm' := sm.push ⟨⟨l, 0⟩, .undef, 0⟩) hfresh hb hheap hdisj hnone hinit
    (by simp) (fun k hk => by rw [Array.getElem?_push_lt hk, Array.getElem?_eq_getElem hk]) fun i hi => by
      obtain rfl : i = 0 := by omega
      exact ⟨⟨⟨l, 0⟩, .undef, 0⟩, by simp, rfl, trivial⟩
  have hl : ∀ l' b', lbl l' = some b' → (if l' = l then some b else lbl l') = some b' := by
    intro l' b' hl'
    by_cases he : l' = l
    · subst he; rw [hfresh] at hl'; cases hl'
    · simpa [he] using hl'
  obtain ⟨hst, q, hi⟩ := h1.store A hex hstep ho (m := ⟨⟨l, 0⟩, sv, mv⟩) (by simp [wordAddr]) (by simp)
    (Scc.Sem.MemRel.valRep_mono hl hv)
  exact ⟨hst, q, by simpa using hi⟩

/-! ## The box row -/

section Row

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {c : Cfg} {i : Nat} {th : TTh}

/-- **The box row**: thread `i` of the source configuration `c`, whose
memory the one-thread invariant relates, at `let x = new a in e` with `a`
a one-word value `w` and no promise, its fresh label `l` not placed; the
arena contract at the cursor `old` with its exceptions below the base; the
base `A = heap + 16 · old + off` word-aligned, the cell's word fitting the
`u` cells the allocation takes within the arena; the target's store to `A`
of a value `w`'s word represents (the row `Out.newStore`). Then the source
steps to `e` with `x` bound to `l`'s locative; the invariant holds after
both sides with `l` placed at `A` with one word; and the contract holds of
the thread after at `old + u`, `l` placed, no exception. -/
theorem row_newStore (h : Inv1 Λ lbl lsize ts t tm c.mem) {heap cells old : Nat} {ex : Nat → Prop}
    (ha : ArenaOK Λ lbl lsize t tm heap cells old ex) (hi : c.ths[i]? = some th)
    {x : String} {a : At} {e : Expr} {ty : Ty} {w : Word}
    (ht : th.term = .let_ x (.new a) e) (hea : evalAt th.env a = some (ty, [w]))
    (hu : accs ty = some [.one]) (hp : th.promises = [])
    (hfresh : lbl (freshLabel c.lbase c.n i th.nalloc) = none)
    {off u : Nat} (hoff : off % 8 = 0) (hfit : off + 8 * 1 ≤ 16 * u) (hle : old + u ≤ cells)
    (hex : ∀ a', ex a' → a' < heap + 16 * old + off)
    (A : Arch) {tid : Nat} {kr : StoreKind} {v : Val} {s : I.State}
    (hexec : I.exec t.st = some (.store kr false (wordLoc (heap + 16 * old + off)) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hv : ValRep lbl w.val v.toNat) :
    ∃ mv th', { c with mem := ((c.mem.push ⟨⟨freshLabel c.lbase c.n i th.nalloc, 0⟩, .undef, 0⟩).push
        ⟨⟨freshLabel c.lbase c.n i th.nalloc, 0⟩, w.val, mv⟩), ths := c.ths.set! i th' } ∈
          threadSteps p kn arch c i ∧ th'.term = e ∧
      th'.env = (x, .ptr .own ty, [cst (.loc ⟨freshLabel c.lbase c.n i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      th'.tidLbl = th.tidLbl ∧ o.thread.st = s ∧
      (∃ q, Inv1 Λ (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then some (heap + 16 * old + off)
          else lbl l') (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then 1 else lsize l')
        (fun k => if k = c.mem.size + 1 then some q else if c.mem.size ≤ k ∧ k < c.mem.size + 1 then some 0
          else ts k)
        o.thread o.mem ((c.mem.push ⟨⟨freshLabel c.lbase c.n i th.nalloc, 0⟩, .undef, 0⟩).push
          ⟨⟨freshLabel c.lbase c.n i th.nalloc, 0⟩, w.val, mv⟩)) ∧
      ArenaOK Λ (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then some (heap + 16 * old + off)
          else lbl l') (fun l' => if l' = freshLabel c.lbase c.n i th.nalloc then 1 else lsize l')
        o.thread o.mem heap cells (old + u) (fun _ => False) := by
  obtain ⟨mv, th', hs, h1, h2, h3, h4, h5, h6, h7⟩ :=
    src_new_step_cfg (p := p) (kn := kn) (arch := arch) hi ht hea hu hp
  obtain ⟨hb, hheap, hdisj, hnone, hinit⟩ := ha.buf (n := 1) hoff hfit hle hex
  obtain ⟨hst, q, hinv⟩ := h.new_src hfresh hb hheap hdisj hnone hinit A hexec hstep ho (mv := mv) hv
  refine ⟨mv, th', hs, h1, h2, h3, h4, h5, h6, h7, hst, ⟨q, hinv⟩, ?_⟩
  -- The contract with `l` placed (no target change), then over the store.
  have hp1 := ha.place (l := freshLabel c.lbase c.n i th.nalloc) (n := 1) hfit hle fun a' hx => by
    have := hex a' hx; omega
  -- The stored word is below the new free range.
  have hA : ∀ (V : Val), ¬ (freeR heap cells (old + u)).contains
      (⟨wordLoc (heap + 16 * old + off), V, tid⟩ : Msg).loc.addr.toNat := by
    intro V hc
    simp only [Range.contains, freeR, wordLoc, BitVec.toNat_ofNat] at hc
    have := Nat.mod_le (heap + 16 * old + off) (2 ^ 64)
    omega
  obtain ⟨-, hc⟩ := Scc.Sem.stepOne_store_cases A hexec hstep ho fun p hp => (h.mem.tq_le p hp).2
  rcases hc with ⟨q', hq', hg, -, hm, hpr⟩ | ⟨hm, hpr⟩
  · refine hp1.keep (fun _ _ => by rw [hm]) (fun k' w' hk _ _ => .inl ⟨hm ▸ hk, id⟩) ?_
    intro k' w' hk hfr hk'
    rw [hpr]
    refine (List.mem_erase_of_ne fun he => ?_).mpr hk'
    subst he
    rw [hg] at hk
    cases hk
    exact hA v hfr
  · refine hp1.keep (fun _ _ => by rw [hm]; rfl) (fun k' w' hk hfr _ => ?_) fun _ _ _ _ h => hpr ▸ h
    rw [hm, get?_append] at hk
    split at hk
    · cases hk; exact absurd hfr (hA v)
    · exact .inl ⟨hk, id⟩

/-- **The box's locative is in its placement**: the word `row_newStore`
binds `x` to, the untagged locative to `⟨l, 0⟩`, is at an offset within the
one word the row places `l` with. -/
theorem newLoc_in {lsize : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel} :
    ∃ sa : WeakMem.Address, (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc sa 0 ∧
      sa.offset < (fun l' => if l' = l then 1 else lsize l') sa.label :=
  ⟨⟨l, 0⟩, rfl, by simp⟩

end Row

/-! ## Axioms -/

/-- info: 'Spike.Lib.NewRow.row_newStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms row_newStore

/-- info: 'Spike.Lib.NewRow.cellAlloc_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cellAlloc_new

/-- info: 'Spike.Lib.NewRow.tidLbls_new' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tidLbls_new

/-- info: 'Scc.Sem.Inv1.new_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Scc.Sem.Inv1.new_src

end Spike.Lib.NewRow
