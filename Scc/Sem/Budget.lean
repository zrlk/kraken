/-
**Abort budgets by exact runtime counters** (`Scc/DESIGN.md` §7.3, item 5,
option (c)): the source side of the heap and stack aborts, and the tie
between the budget and the layout.

The runtime counts in source units (planned shapes, §7.3): a global counter
`scc_rt_heap_use` that `scc_rt_alloc` bumps by an allocation's words plus
one, aborting exactly when the old count is within `B.cells` and the new one
is past it; a per-thread depth bumped around source non-tail calls, aborting
when the depth would pass `B.frames`. With the counter equal to the source
quantity (`heapUse`, the thread's `stack.length`), the abort happens at the
target step simulating the source step that crosses the part, which is what
`AbortJustified` asks:

- `memCells`, `memCells_allocBuf`: a `newBuf` of a fresh label adds its word
  count to the source's distinct cells (`cellCount`); `nallocSum_set`: one
  thread's allocation counter bumped adds one to `allocCount`;
  `heapUse_newBuf`: so `heapUse` grows by the words plus one, the `u` the
  runtime adds;
- `AbortJustified.heap_of_crossing`: a step of thread `i` that grows
  `heapUse` by `u` from within `B.cells` to past it justifies a heap abort;
  `AbortJustified.not_heap_past`: once past (another thread crossed), no
  heap abort is justified, so a later thread must wait (spin), not abort;
- `AbortJustified.stack_of_push`: a step of thread `i` that pushes one frame
  when its depth is `B.frames` justifies a stack abort;
- `Budget.ofArena`, `arena_fits`: the heap part derived from the arena,
  `B.cells = heap bytes / 16`, so that the arena check is unreachable while
  the part holds (`arena_covers`).

Not here: the runtime invariant that the counters equal the source
quantities (it needs the runtime's counter code), and the frame-size side
of the stack budget (the largest frame, the cap and the pool, which are the
runtime layout's).
-/
import Scc.Sem.RowsAlloc

namespace Scc.Sem

/-! ## Distinct cells after `newBuf` -/

/-- An array built by pushes lists as the old entries and then the pushed
ones. -/
theorem foldl_push_toList {α : Type} (f : Nat → α) (n : Nat) (a : Array α) :
    ((List.range n).foldl (fun m j => m.push (f j)) a).toList = a.toList ++ (List.range n).map f := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.foldl_append]

/-- Deduplicating a duplicate-free list changes nothing. -/
theorem eraseDups_of_nodup {α : Type} [DecidableEq α] : ∀ {l : List α}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.eraseDups_cons]
    have hf : (l.filter fun b => !b == a) = l := by
      rw [List.filter_eq_self]
      intro b hb
      have : b ≠ a := fun he => (List.nodup_cons.mp h).1 (he ▸ hb)
      simpa using this
    rw [hf, eraseDups_of_nodup (List.nodup_cons.mp h).2]

/-- The number of distinct cell addresses of a source memory. -/
def memCells (mem : WeakMem.Memory) : Nat := (mem.toList.map (·.loc)).eraseDups.length

/-- `cellCount` is `memCells` of the memory. -/
theorem cellCount_eq (s : TermRun.Cfg) : cellCount s = memCells s.mem := rfl

/-- **A `newBuf` of a fresh label adds its words**: `allocBuf l n` over a
memory with no message to `l` adds `n` distinct cells. -/
theorem memCells_allocBuf {l : WeakMem.AllocLabel} {n : Nat} {zero : Option (List WeakMem.Val)}
    {st : TermRun.St} (hfresh : ∀ m ∈ st.mem.toList, m.loc.label ≠ l) :
    memCells (TermRun.allocBuf l n zero st).1.mem = memCells st.mem + n := by
  unfold memCells
  rw [allocBuf_mem, foldl_push_toList, List.map_append, List.eraseDups_append, List.length_append,
    List.map_map]
  have hnew : ((List.range n).map ((·.loc) ∘ fun j => (⟨TermRun.offs ⟨l, 0⟩ j, allocBufVal zero j, 0⟩ :
      WeakMem.Msg))) = (List.range n).map fun j => (⟨l, j⟩ : WeakMem.Address) := by
    apply List.map_congr_left
    intro j _
    simp [TermRun.offs]
  rw [hnew]
  have hnd : ((List.range n).map fun j => (⟨l, j⟩ : WeakMem.Address)).Nodup :=
    List.Pairwise.map _ (fun a b h he => h (by simpa using he)) List.nodup_range
  have hrm : ((List.range n).map fun j => (⟨l, j⟩ : WeakMem.Address)).removeAll
      (st.mem.toList.map (·.loc)) = (List.range n).map fun j => (⟨l, j⟩ : WeakMem.Address) := by
    unfold List.removeAll
    rw [List.filter_eq_self]
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.elem_eq_mem, decide_eq_false_iff_not,
      List.mem_map, not_exists, not_and]
    intro m hm he
    exact hfresh m hm (by rw [he])
  rw [hrm, eraseDups_of_nodup hnd]
  simp

/-! ## Allocation counts -/

/-- The sum of the threads' allocation counters. -/
def nallocSum (ths : Array TermRun.TTh) : Nat := (ths.toList.map (·.nalloc)).sum

/-- `allocCount` is `nallocSum` of the threads. -/
theorem allocCount_eq (s : TermRun.Cfg) : allocCount s = nallocSum s.ths := rfl

theorem list_sum_set {l : List TermRun.TTh} {i : Nat} (hi : i < l.length) (th' : TermRun.TTh) :
    ((l.set i th').map (·.nalloc)).sum + l[i].nalloc = (l.map (·.nalloc)).sum + th'.nalloc := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      have := ih (i := i) (by simpa using hi)
      omega

/-- **One thread's allocation counter bumped** adds one to the sum. -/
theorem nallocSum_set {ths : Array TermRun.TTh} {i : Nat} (hi : i < ths.size) {th' : TermRun.TTh}
    (hn : th'.nalloc = ths[i].nalloc + 1) : nallocSum (ths.set i th') = nallocSum ths + 1 := by
  unfold nallocSum
  rw [Array.toList_set]
  have := list_sum_set (l := ths.toList) (by simpa using hi) th'
  simp only [Array.getElem_toList] at this
  omega

/-- **A `newBuf` step's heap use**: a source configuration `c'` whose
memory is `allocBuf l n` over `c`'s (a fresh label) and whose thread `i`
has its allocation counter bumped has heap use `heapUse c + (n + 1)`: the
words plus the header, the `u` the runtime's counter adds. -/
theorem heapUse_newBuf {c c' : TermRun.Cfg} {l : WeakMem.AllocLabel} {n : Nat}
    {zero : Option (List WeakMem.Val)} {st : TermRun.St} (hst : st.mem = c.mem)
    (hmem : c'.mem = (TermRun.allocBuf l n zero st).1.mem) (hfresh : Fresh c l) {i : Nat} (hi : i < c.ths.size)
    {th' : TermRun.TTh} (hths : c'.ths = c.ths.set i th') (hn : th'.nalloc = c.ths[i].nalloc + 1) :
    heapUse c' = heapUse c + (n + 1) := by
  unfold heapUse
  rw [cellCount_eq, cellCount_eq, allocCount_eq, allocCount_eq, hmem, hths,
    memCells_allocBuf (by rw [hst]; exact hfresh), nallocSum_set hi hn, hst]
  omega

/-! ## Justified aborts at the crossing -/

/-- **A heap abort at the crossing is justified**: a step of thread `i`
that grows the heap use by `u`, from within `B.cells` to past it. -/
theorem AbortJustified.heap_of_crossing {B : Budget} {S : SrcSem} {tr : List Ev} {s s' : S.Cfg} {i : Nat}
    {es : List Ev} (hstep : S.step i s es s') {u : Nat} (hu : heapUse (S.core s') = heapUse (S.core s) + u)
    (hle : heapUse (S.core s) ≤ B.cells) (hlt : B.cells < heapUse (S.core s) + u) :
    AbortJustified B S tr s i .heap :=
  ⟨es, s', hstep, hle, by show ¬ heapUse (S.core s') ≤ B.cells; omega⟩

/-- **Past the crossing no heap abort is justified**: when the heap use is
already past `B.cells` (another thread crossed), a heap abort is not
justified, so the runtime must not abort there (it waits for the crossing
thread's exit). -/
theorem AbortJustified.not_heap_past {B : Budget} {S : SrcSem} {tr : List Ev} {s : S.Cfg} {i : Nat}
    (hpast : B.cells < heapUse (S.core s)) : ¬ AbortJustified B S tr s i .heap :=
  AbortJustified.not_of_not_part (k := .heap) (by simp [EnvJustified])
    (by show ¬ heapUse (S.core s) ≤ B.cells; omega)

/-- **A stack abort at the crossing is justified**: a step of thread `i`
that pushes one frame when its depth is `B.frames`. -/
theorem AbortJustified.stack_of_push {B : Budget} {S : SrcSem} {tr : List Ev} {s s' : S.Cfg} {i : Nat}
    {es : List Ev} (hstep : S.step i s es s') {th th' : TermRun.TTh} (hth : (S.core s).ths[i]? = some th)
    (hth' : (S.core s').ths[i]? = some th') (hlen : th'.stack.length = th.stack.length + 1)
    (hat : th.stack.length = B.frames) : AbortJustified B S tr s i .stack := by
  refine ⟨es, s', hstep, ?_, ?_⟩
  · intro t ht
    rw [hth] at ht; cases ht; omega
  · intro h
    have := h th' hth'
    omega

/-! ## The budget from the layout -/

/-- **The budget derived from the layout**: as many heap cells as the
arena holds at 16 bytes each (`arena_margin`), and the given thread and
frame counts (the runtime layout's: the thread cap plus one, and the frames
the stack cap holds). -/
def Budget.ofArena (Λ : Layout) (threads frames : Nat) : Budget :=
  ⟨Λ.heap.size / 16, threads, frames⟩

/-- **The arena check is unreachable within the heap part**: with
`B.cells` derived from the arena, the arena bytes of the allocations
`arena_covers` accounts for fit the arena. -/
theorem arena_fits {s : TermRun.Cfg} {Λ : Layout} {threads frames : Nat} (as : List (Nat × Nat × Nat))
    (ht : ∀ a ∈ as, 2 * a.2.1 ≤ 3 * a.1) (hf : ∀ a ∈ as, a.2.2 ≤ 8)
    (hw : (as.map (·.1)).sum = cellCount s) (hn : as.length = allocCount s)
    (hB : heapUse s ≤ (Budget.ofArena Λ threads frames).cells) :
    (as.map fun a => objBytes a.2.1 a.2.2).sum ≤ Λ.heap.size := by
  have := arena_covers as ht hf hw hn hB
  simp only [Budget.ofArena] at this
  omega

end Scc.Sem
