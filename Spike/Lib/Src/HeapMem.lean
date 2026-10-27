import Scc.Sem.RowsAlloc
import Spike.Lib.SrcMem
import Spike.Lib.Consumer1

/-!
**Numbers in the source memory** (ISA-neutral; no lowering import, so it
builds on any tree with `Scc.Sem.RowsAlloc` and `Spike.Lib.Consumer1`).
`HeapLit sm L`: every message of the source memory at a label in `L` holds a
number below `2^64`; `HasCell sm sa`: the cell at `sa` has a message.

- `heapLit_empty`, `heapLit_push`, `HeapLit.mono`, `heapLit_allocBuf` (a
  fresh label, `FreshIn`, whose words are numbers);
- `HasCell.push`, `hasCell_allocBuf`, `HasCell.allocBuf`;
- `sLatest_unique`; `latest_num'`: a cell at a label in `L` has a latest
  message, a number;
- `cellNum sm sa`: that number (`0` off such cells), `cellNum_eq`;
  `bufWords sm l`: the numbers of label `l`'s words;
- `printMem_bufWords`: `print`'s memory premise
  (`Spike.Lib.SrcCalls.PrintMem sm l N w`, written out) at `w = bufWords sm l`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Sem.MemRel (SLatest)

/-! ## The invariant -/

/-- **The messages at labels in `L` hold numbers** below `2^64`. -/
def HeapLit (sm : WeakMem.Memory) (L : WeakMem.AllocLabel → Prop) : Prop :=
  ∀ (k : Nat) (m : WeakMem.Msg), sm[k]? = some m → L m.loc.label → ∃ n, m.val = .num n ∧ n < 2 ^ 64

theorem heapLit_empty (L : WeakMem.AllocLabel → Prop) : HeapLit #[] L := fun _ _ h => by simp at h

/-- **A push keeps `HeapLit`** when the message is at a label outside `L` or
holds a number. -/
theorem heapLit_push {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    {m : WeakMem.Msg} (hm : L m.loc.label → ∃ n, m.val = .num n ∧ n < 2 ^ 64) : HeapLit (sm.push m) L := by
  intro k m' hk hl
  rw [Array.getElem?_push] at hk
  split at hk
  · cases hk; exact hm hl
  · exact h k m' hk hl

/-- **A smaller set of labels keeps `HeapLit`.** -/
theorem HeapLit.mono {sm : WeakMem.Memory} {L L' : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    (hL : ∀ l, L' l → L l) : HeapLit sm L' := fun k m hk hl => h k m hk (hL _ hl)

/-- **No message of the memory is at label `lbl`** (a fresh label). -/
def FreshIn (sm : WeakMem.Memory) (lbl : WeakMem.AllocLabel) : Prop :=
  ∀ (k : Nat) (m : WeakMem.Msg), sm[k]? = some m → m.loc.label ≠ lbl

/-- **`allocBuf` keeps `HeapLit` and adds its label** when the label is
fresh or in `L` already and the buffer's words are numbers. -/
theorem heapLit_allocBuf {L : WeakMem.AllocLabel → Prop} {lbl : WeakMem.AllocLabel} {n : Nat}
    {zero : Option (List WeakMem.Val)} {s : TermRun.St} (h : HeapLit s.mem L)
    (hf : FreshIn s.mem lbl) (hz : ∀ j, ∃ v, Scc.Sem.allocBufVal zero j = .num v ∧ v < 2 ^ 64) :
    HeapLit (TermRun.allocBuf lbl n zero s).1.mem (fun l => L l ∨ l = lbl) := by
  intro k m hk hl
  by_cases hold : k < s.mem.size
  · rw [Scc.Sem.allocBuf_mem_old _ _ _ _ hold] at hk
    rcases hl with hl | hl
    · exact h k m hk hl
    · exact absurd hl (hf k m hk)
  · have hsz := Scc.Sem.allocBuf_mem_size lbl n zero s
    have hlt : k < s.mem.size + n := by
      rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨i, rfl⟩ : ∃ i, k = s.mem.size + i := ⟨k - s.mem.size, by omega⟩
    rw [Scc.Sem.allocBuf_mem_new _ _ _ _ (by omega)] at hk
    cases hk
    exact hz i

/-! ## Cells -/

/-- **The cell at `sa` has a message.** -/
def HasCell (sm : WeakMem.Memory) (sa : WeakMem.Address) : Prop :=
  ∃ (k : Nat) (m : WeakMem.Msg), sm[k]? = some m ∧ m.loc = sa

theorem HasCell.push {sm : WeakMem.Memory} {sa : WeakMem.Address} (h : HasCell sm sa) (m : WeakMem.Msg) :
    HasCell (sm.push m) sa := by
  obtain ⟨k, m', hk, hl⟩ := h
  refine ⟨k, m', ?_, hl⟩
  have := (Array.getElem?_eq_some_iff.mp hk).1
  rw [Array.getElem?_push]; split
  · omega
  · exact hk

/-- **`allocBuf` gives each word of its buffer a message.** -/
theorem hasCell_allocBuf (lbl : WeakMem.AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val))
    (s : TermRun.St) {i : Nat} (hi : i < n) : HasCell (TermRun.allocBuf lbl n zero s).1.mem ⟨lbl, i⟩ :=
  ⟨_, _, Scc.Sem.allocBuf_mem_new _ _ _ _ hi, rfl⟩

/-- **`allocBuf` keeps the old cells.** -/
theorem HasCell.allocBuf {s : TermRun.St} {sa : WeakMem.Address} (h : HasCell s.mem sa)
    (lbl : WeakMem.AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) :
    HasCell (TermRun.allocBuf lbl n zero s).1.mem sa := by
  obtain ⟨k, m, hk, hl⟩ := h
  exact ⟨k, m, by rw [Scc.Sem.allocBuf_mem_old _ _ _ _ (Array.getElem?_eq_some_iff.mp hk).1]; exact hk, hl⟩

/-- **The latest message of a cell is unique.** -/
theorem sLatest_unique {sm : WeakMem.Memory} {sa : WeakMem.Address} {j j' : Nat} (h : SLatest sm sa j)
    (h' : SLatest sm sa j') : j = j' := by
  obtain ⟨⟨m, hm, hml⟩, hl⟩ := h
  obtain ⟨⟨m', hm', hml'⟩, hl'⟩ := h'
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd hml' (hl j' m' hlt hm')
  · exact heq
  · exact absurd hml (hl' j m hgt hm)

/-- **A cell at a label in `L` has a latest message, a number.** -/
theorem latest_num' {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    {sa : WeakMem.Address} (hc : HasCell sm sa) (hl : L sa.label) :
    ∃ j m n, SLatest sm sa j ∧ sm[j]? = some m ∧ m.val = .num n ∧ n < 2 ^ 64 := by
  obtain ⟨j, hj⟩ := Spike.Lib.Consumer1.exists_sLatest hc
  obtain ⟨m, hm, hml⟩ := hj.1
  obtain ⟨n, hn, hlt⟩ := h j m hm (hml ▸ hl)
  exact ⟨j, m, n, hj, hm, hn, hlt⟩

/-! ## The numbers of a buffer -/

open Classical in
/-- **The number in the latest message of the cell at `sa`** (`0` if the
cell has none, or its latest message is not a number). -/
noncomputable def cellNum (sm : WeakMem.Memory) (sa : WeakMem.Address) : Nat :=
  if h : ∃ j m n, SLatest sm sa j ∧ sm[j]? = some m ∧ m.val = .num n
  then h.choose_spec.choose_spec.choose else 0

/-- `cellNum` is the number of the latest message. -/
theorem cellNum_eq {sm : WeakMem.Memory} {sa : WeakMem.Address} {j : Nat} {m : WeakMem.Msg} {n : Nat}
    (hj : SLatest sm sa j) (hm : sm[j]? = some m) (hn : m.val = .num n) : cellNum sm sa = n := by
  have hi : ∃ j m n, SLatest sm sa j ∧ sm[j]? = some m ∧ m.val = .num n := ⟨j, m, n, hj, hm, hn⟩
  have key : ∀ j' m' n', SLatest sm sa j' → sm[j']? = some m' → m'.val = .num n' → n' = n := by
    intro j' m' n' hj' hm' hn'
    have e := sLatest_unique hj' hj
    subst e
    rw [hm] at hm'; cases hm'
    rw [hn] at hn'; cases hn'; rfl
  unfold cellNum
  simp only [dite_eq_left_of_eq_true (eq_true hi)]
  obtain ⟨h1, h2, h3⟩ := hi.choose_spec.choose_spec.choose_spec
  exact key _ _ _ h1 h2 h3

/-- **The numbers of label `l`'s words**: word `i` is `cellNum sm ⟨l, i⟩`. -/
noncomputable def bufWords (sm : WeakMem.Memory) (l : WeakMem.AllocLabel) : Nat → Nat :=
  fun i => cellNum sm ⟨l, i⟩

/-- **`print`'s memory premise at `bufWords`**: a buffer at a label in `L`
whose first `⌈N/8⌉` words have messages
(`Spike.Lib.SrcCalls.PrintMem sm l N (bufWords sm l)`, written out). -/
theorem printMem_bufWords {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    {l N : Nat} (hl : L l) (hc : ∀ k < N, HasCell sm ⟨l, k / 8⟩) :
    ∀ k < N, ∃ j msg, SLatest sm ⟨l, k / 8⟩ j ∧ sm[j]? = some msg ∧ msg.val = .num (bufWords sm l (k / 8)) := by
  intro k hk
  obtain ⟨j, m, n, hj, hm, hn, -⟩ := latest_num' h (hc k hk) hl
  exact ⟨j, m, hj, hm, by rw [hn, bufWords, cellNum_eq hj hm hn]⟩

/-- `bufWords` are below `2^64` on cells at labels in `L`. -/
theorem bufWords_lt {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    {l : WeakMem.AllocLabel} {i : Nat} (hl : L l) (hc : HasCell sm ⟨l, i⟩) : bufWords sm l i < 2 ^ 64 := by
  obtain ⟨j, m, n, hj, hm, hn, hlt⟩ := latest_num' h hc hl
  rw [bufWords, cellNum_eq hj hm hn]; exact hlt

end Spike.Lib.LowerNode
