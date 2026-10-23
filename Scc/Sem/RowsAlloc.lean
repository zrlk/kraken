/-
**The allocation row** of the one-thread invariant (`Scc/DESIGN.md` §9.0,
"Never-mirror for M1"; §8, *Operations*, "Fresh allocation").

The source's `newBuf` (`TermRun.allocBuf`) pushes one first message per word
of a fresh label; the target's `scc_rt_alloc` returns the base of zeroed,
never used arena words (its own writes, the cursor and the header, are
runtime writes outside every placed label: `Inv1.rtStore` and the RMW
rows). The row is the point where the label is placed at the returned
address: no target memory step, the source memory grows by the label's
messages, each imaged at the target's initial write (timestamp 0: the
zeroed arena). Under never-mirror no target promise is mirrored, so every
target message already in the new range must be an outstanding promise of
the thread (a promise to an address the allocator returns now).

- `foldl_push_size`, `foldl_push_old`, `foldl_push_new`: the shape of the
  memory a fold of pushes builds;
- `allocBuf_mem_size`, `allocBuf_mem_old`, `allocBuf_mem_new`: the source
  memory after `allocBuf`;
- `Inv1.alloc`: the invariant after placing a fresh label of `n` words at
  `b` over any source memory extending the old one by `n` first messages
  whose values represent 0 (`MemRelP.alloc`);
- `Inv1.allocBuf_src`: the same for the source memory `allocBuf` builds,
  the values given by `zero` (the zero of the element type, or `undef`);
- `Inv1.alloc_placed`, `Inv1.allocBuf_placed_src`: the same for a label
  placed in advance (`MemRelP.alloc_placed`): the placement maps do not
  change, so a relation with one fixed `lbl` (a deterministic one-thread
  allocator's addresses, known ahead) needs no row that grows `lbl`.

Not here: the lift through `TermRun.tstep`'s `newBuf` case (the label
`freshLabel …` and the word count `k · w`) and the `Out` row of
`Spike/Lib/Seg.lean`; `new` (`TermRun.alloc`: the same pushes followed by
initialising stores, the store rows); the runtime facts the hypotheses
name (the arena past the cursor is zeroed and unwritten, the returned base
is fresh and disjoint from every placed label).
-/
import Scc.Sem.RowsSrc

namespace Scc.Sem

open Kraken Kraken.Promising

/-! ## A fold of pushes -/

section FoldPush

variable {α : Type} (f : Nat → α)

/-- A fold of `n` pushes grows the array by `n`. -/
theorem foldl_push_size (n : Nat) (a : Array α) :
    ((List.range n).foldl (fun m j => m.push (f j)) a).size = a.size + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.foldl_append]

/-- A fold of pushes keeps the old entries. -/
theorem foldl_push_old (n : Nat) (a : Array α) {k : Nat} (hk : k < a.size) :
    ((List.range n).foldl (fun m j => m.push (f j)) a)[k]? = a[k]? := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Array.getElem?_push]
    split
    · rename_i h; rw [foldl_push_size] at h; omega
    · exact ih

/-- Entry `a.size + i` of a fold of `n` pushes is the `i`-th pushed. -/
theorem foldl_push_new (n : Nat) (a : Array α) {i : Nat} (hi : i < n) :
    ((List.range n).foldl (fun m j => m.push (f j)) a)[a.size + i]? = some (f i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Array.getElem?_push]
    split
    · rename_i h
      rw [foldl_push_size] at h
      have : i = n := by omega
      subst this; rfl
    · rename_i h
      rw [foldl_push_size] at h
      exact ih (by omega)

end FoldPush

/-! ## The source memory after `allocBuf` -/

/-- The value `allocBuf` gives word `j` of a buffer with zero words `zero`:
the zero of the element type cycled over the buffer, or `undef`. -/
def allocBufVal (zero : Option (List WeakMem.Val)) (j : Nat) : WeakMem.Val :=
  match zero with
  | some (z :: zs) => (z :: zs).getD (j % (z :: zs).length) .undef
  | _ => .undef

/-- `allocBuf`'s memory is a fold of pushes of `allocBufVal`'s messages. -/
theorem allocBuf_mem (lbl : WeakMem.AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val))
    (s : TermRun.St) :
    (TermRun.allocBuf lbl n zero s).1.mem =
      (List.range n).foldl (fun m j => m.push ⟨TermRun.offs ⟨lbl, 0⟩ j, allocBufVal zero j, 0⟩) s.mem := by
  unfold TermRun.allocBuf allocBufVal
  rfl

/-- `allocBuf` adds `n` messages. -/
theorem allocBuf_mem_size (lbl : WeakMem.AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val))
    (s : TermRun.St) : (TermRun.allocBuf lbl n zero s).1.mem.size = s.mem.size + n := by
  rw [allocBuf_mem, foldl_push_size]

/-- `allocBuf` keeps the old messages. -/
theorem allocBuf_mem_old (lbl : WeakMem.AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val))
    (s : TermRun.St) {k : Nat} (hk : k < s.mem.size) :
    (TermRun.allocBuf lbl n zero s).1.mem[k]? = s.mem[k]? := by
  rw [allocBuf_mem, foldl_push_old _ _ _ hk]

/-- `allocBuf`'s `i`-th new message: word `i` of the label, its value, view
0. -/
theorem allocBuf_mem_new (lbl : WeakMem.AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val))
    (s : TermRun.St) {i : Nat} (hi : i < n) :
    (TermRun.allocBuf lbl n zero s).1.mem[s.mem.size + i]? = some ⟨⟨lbl, i⟩, allocBufVal zero i, 0⟩ := by
  rw [allocBuf_mem, foldl_push_new _ _ _ hi]
  simp [TermRun.offs]

/-- Every value `allocBuf` gives represents 0 when every zero word does
(`undef` represents anything). -/
theorem allocBufVal_rep {lbl : WeakMem.AllocLabel → Option Nat} {zero : Option (List WeakMem.Val)}
    (hz : ∀ vs, zero = some vs → ∀ v ∈ vs, ValRep lbl v 0) (j : Nat) : ValRep lbl (allocBufVal zero j) 0 := by
  unfold allocBufVal
  rcases zero with _ | _ | ⟨z, zs⟩
  · trivial
  · trivial
  · have hlt : j % (z :: zs).length < (z :: zs).length := Nat.mod_lt _ (by simp)
    have hm : (z :: zs).getD (j % (z :: zs).length) .undef ∈ z :: zs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.getElem_mem hlt
    exact hz _ rfl _ hm

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- **The allocation row**: placing a fresh label `l` of `n` words at the
word-aligned base `b`, a range of the heap arena disjoint from every placed
label, whose target words are zero at the initial write (`hinit`: the
zeroed arena) and in which every target message is an outstanding promise
of the thread (`hnone`), keeps the invariant over a source memory that
extends the old one by `n` first messages to the label's words whose values
represent 0; each new message is imaged at the initial write (timestamp
0). No target step: the thread and the target memory are unchanged. -/
theorem alloc (h : Inv1 Λ lbl lsize ts t tm sm) {l : WeakMem.AllocLabel} {n b : Nat}
    (hfresh : lbl l = none) (hb : b % 8 = 0) (hheap : (Range.mk b (8 * n)).Sub Λ.heap)
    (hdisj : ∀ l' b', lbl l' = some b' → (Range.mk b (8 * n)).Disjoint (lrange lsize l' b'))
    (hnone : ∀ k' w, tm.get? k' = some w → (Range.mk b (8 * n)).contains w.loc.addr.toNat → k' ∈ t.prom)
    (hinit : ∀ i < n, tm.initVal (wordLoc (b + 8 * i)) = 0)
    {sm' : WeakMem.Memory} (hsize : sm'.size = sm.size + n) (hold : ∀ k < sm.size, sm'[k]? = sm[k]?)
    (hnew : ∀ i < n, ∃ m, sm'[sm.size + i]? = some m ∧ m.loc = ⟨l, i⟩ ∧
      ValRep (fun l' => if l' = l then some b else lbl l') m.val 0) :
    Inv1 Λ (fun l' => if l' = l then some b else lbl l') (fun l' => if l' = l then n else lsize l')
      (fun k => if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) t tm sm' :=
  ⟨h.mem.alloc hfresh hb hheap hdisj hnone hinit hsize hold hnew, h.coh, h.narrow⟩

/-- **The allocation row, source `newBuf`**: `alloc` for the memory
`TermRun.allocBuf l n zero` builds from a source state whose memory is the
related one, when every zero word of the element type represents 0 (a
number 0, `null`, `undef`). -/
theorem allocBuf_src (h : Inv1 Λ lbl lsize ts t tm sm) {l : WeakMem.AllocLabel} {n b : Nat}
    (hfresh : lbl l = none) (hb : b % 8 = 0) (hheap : (Range.mk b (8 * n)).Sub Λ.heap)
    (hdisj : ∀ l' b', lbl l' = some b' → (Range.mk b (8 * n)).Disjoint (lrange lsize l' b'))
    (hnone : ∀ k' w, tm.get? k' = some w → (Range.mk b (8 * n)).contains w.loc.addr.toNat → k' ∈ t.prom)
    (hinit : ∀ i < n, tm.initVal (wordLoc (b + 8 * i)) = 0)
    {zero : Option (List WeakMem.Val)}
    (hz : ∀ vs, zero = some vs → ∀ v ∈ vs, ValRep (fun l' => if l' = l then some b else lbl l') v 0)
    {s : TermRun.St} (hs : s.mem = sm) :
    Inv1 Λ (fun l' => if l' = l then some b else lbl l') (fun l' => if l' = l then n else lsize l')
      (fun k => if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) t tm
      (TermRun.allocBuf l n zero s).1.mem := by
  subst hs
  refine h.alloc hfresh hb hheap hdisj hnone hinit (allocBuf_mem_size l n zero s)
    (fun k hk => allocBuf_mem_old l n zero s hk) fun i hi => ?_
  exact ⟨_, allocBuf_mem_new l n zero s hi, rfl, allocBufVal_rep hz i⟩

/-- **The allocation row at a label placed in advance**: the label `l` is
placed at `b` with `n` words and has no source message yet; the invariant
holds with the same placement over a source memory extending the old one by
`n` first messages to `l`'s words whose values represent 0, each imaged at
the initial write (`hinit`: the zeroed arena). -/
theorem alloc_placed (h : Inv1 Λ lbl lsize ts t tm sm) {l : WeakMem.AllocLabel} {n b : Nat}
    (hl : lbl l = some b) (hn : lsize l = n) (hno : ∀ m ∈ sm.toList, m.loc.label ≠ l)
    (hinit : ∀ i < n, tm.initVal (wordLoc (b + 8 * i)) = 0)
    {sm' : WeakMem.Memory} (hsize : sm'.size = sm.size + n) (hold : ∀ k < sm.size, sm'[k]? = sm[k]?)
    (hnew : ∀ i < n, ∃ m, sm'[sm.size + i]? = some m ∧ m.loc = ⟨l, i⟩ ∧ ValRep lbl m.val 0) :
    Inv1 Λ lbl lsize (fun k => if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) t tm sm' :=
  ⟨h.mem.alloc_placed hl hn hno hinit hsize hold hnew, h.coh, h.narrow⟩

/-- **The allocation row at a label placed in advance, source `newBuf`**:
`alloc_placed` for the memory `TermRun.allocBuf l n zero` builds. -/
theorem allocBuf_placed_src (h : Inv1 Λ lbl lsize ts t tm sm) {l : WeakMem.AllocLabel} {n b : Nat}
    (hl : lbl l = some b) (hn : lsize l = n) (hno : ∀ m ∈ sm.toList, m.loc.label ≠ l)
    (hinit : ∀ i < n, tm.initVal (wordLoc (b + 8 * i)) = 0)
    {zero : Option (List WeakMem.Val)} (hz : ∀ vs, zero = some vs → ∀ v ∈ vs, ValRep lbl v 0)
    {s : TermRun.St} (hs : s.mem = sm) :
    Inv1 Λ lbl lsize (fun k => if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) t tm
      (TermRun.allocBuf l n zero s).1.mem := by
  subst hs
  refine h.alloc_placed hl hn hno hinit (allocBuf_mem_size l n zero s)
    (fun k hk => allocBuf_mem_old l n zero s hk) fun i hi => ?_
  exact ⟨_, allocBuf_mem_new l n zero s hi, rfl, allocBufVal_rep hz i⟩

end Inv1

end Scc.Sem
