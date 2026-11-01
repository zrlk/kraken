/-
**hello.w: rodata's buffer words are not the last message at the spawn**
(B8; closes the strictness gap of `HelloFrzSrc.frzBuf_latest`). `rodata`'s
two lane stores append the buffer's words at `⟨l, 0⟩`, `⟨l, 1⟩`; at least
one message is appended after them before the clone (main's box `new z`
pushes its cell's `undef` message: `alloc_size_one`), so the latest message
to each buffer word is strictly below the last one, the shape `ClonePreH`'s
buffer conjunct (`HelloPreA.BufAtSpawn`) and `HelloFrz.FrzBufL` take.

- `PushB mem l w0 w1`: the memory just after rodata's two lane stores.
- `frzBufSz_latest`: `frzBuf_latest`'s hypotheses (`hpre`, `hnew`) and one
  more message (`hmore : (PushB mem l w0 w1).size < mem'.size`) give, for
  `i < 2`, the latest message at `⟨l, i⟩` holding `bufW i`, `j + 1 <
  mem'.size`: `BufAtSpawn`'s body.
- `bufAt_of_latest`: the same as `BufAtSpawn s l` at `s.mem = mem'`.
- `alloc_size_one`: a one-word `new` (main's box) makes the memory strictly
  larger (its `undef` message, its store appended or a promise fulfilled).
- `hmore_of_mid`: `hmore` from an intermediate memory `mid` (e.g. just past
  the box's `new`) that is larger than `PushB` and a prefix of `mem'`.
-/
import Spike.Lib.HelloFrzSrc
import Spike.Lib.A64HelloClonePreHOf

namespace Spike.Lib.HelloFrzSrcSz

open CoreLang CoreTerm TermRun
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)
open Spike.Lib.Hello1RodataMem (rd_latest)
open Spike.Lib.HelloFrzSrc (latest_ext)
open Spike.Lib.HelloPreA (bufW BufAtSpawn)

/-- **The memory just after rodata's two lane stores.** -/
abbrev PushB (mem : WeakMem.Memory) (l : WeakMem.AllocLabel) (w0 w1 : WeakMem.Ts) : WeakMem.Memory :=
  (mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩

/-- **rodata's buffer words are latest and not last** at any extension
`mem'` of `PushB` whose new messages are to other labels (`hpre`, `hnew`)
and which has at least one more message (`hmore`). -/
theorem frzBufSz_latest {mem mem' : WeakMem.Memory} {l : WeakMem.AllocLabel} {w0 w1 : WeakMem.Ts}
    (hpre : ∀ k, k < (PushB mem l w0 w1).size → mem'[k]? = (PushB mem l w0 w1)[k]?)
    (hnew : ∀ k m', (PushB mem l w0 w1).size ≤ k → mem'[k]? = some m' → m'.loc.label ≠ l)
    (hmore : (PushB mem l w0 w1).size < mem'.size) :
    ∀ i < 2, ∃ j m, SLatest mem' ⟨l, i⟩ j ∧ mem'[j]? = some m ∧ m.val = .num (bufW i) ∧ j + 1 < mem'.size := by
  obtain ⟨j0, j1, m0, m1, a0, b0, c0, a1, b1, c1⟩ := rd_latest mem l w0 w1
  have hm : ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩).size < mem'.size :=
    hmore
  intro i hi
  match i, hi with
  | 0, _ =>
    obtain ⟨h1, h2⟩ := latest_ext a0 b0 hpre hnew
    have := (Array.getElem?_eq_some_iff.mp b0).1
    exact ⟨j0, m0, h1, h2, by rw [c0]; rfl, by omega⟩
  | 1, _ =>
    obtain ⟨h1, h2⟩ := latest_ext a1 b1 hpre hnew
    have := (Array.getElem?_eq_some_iff.mp b1).1
    exact ⟨j1, m1, h1, h2, by rw [c1]; rfl, by omega⟩

/-- **`BufAtSpawn` at a source configuration** whose memory is such an
extension. -/
theorem bufAt_of_latest {s : TermRun.Cfg} {mem : WeakMem.Memory} {l : WeakMem.AllocLabel} {w0 w1 : WeakMem.Ts}
    (hpre : ∀ k, k < (PushB mem l w0 w1).size → s.mem[k]? = (PushB mem l w0 w1)[k]?)
    (hnew : ∀ k m', (PushB mem l w0 w1).size ≤ k → s.mem[k]? = some m' → m'.loc.label ≠ l)
    (hmore : (PushB mem l w0 w1).size < s.mem.size) : BufAtSpawn s l :=
  frzBufSz_latest hpre hnew hmore

/-- **A one-word `new` makes the memory strictly larger**: its cell's
`undef` message is pushed, and its store is appended or fulfils a
promise. -/
theorem alloc_size_one {k : Promises.Knobs} {arch : WeakMem.Arch} {lbl : WeakMem.AllocLabel} {ws : List Word}
    {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl [.one] ws s) : s.mem.size < s'.mem.size := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, -⟩ := h
  cases ws with
  | nil => simp [storeUnits] at hs2
  | cons w ws =>
    simp only [storeUnits, List.mem_flatMap, List.mem_singleton] at hs2
    obtain ⟨⟨mem', th⟩, hst, rfl⟩ := hs2
    obtain ⟨t, hc, -⟩ := TermStep.stepStore_casesC hst
    have hsz := TermMem.fold_size (fun j => (⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩ : WeakMem.Msg)) (nWords [.one]) s.mem
    have hn : nWords [Acc.one] = 1 := rfl
    rw [hn] at hsz
    show s.mem.size < mem'.size
    rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
    · simp only [Array.size_push, hn] at hsz ⊢
      omega
    · simp only [hn] at hsz ⊢
      omega

/-- **`hmore` from an intermediate memory**: `mid` (e.g. past the box's
`new`) larger than `PushB`, a prefix of `mem'`. -/
theorem hmore_of_mid {mem mid mem' : WeakMem.Memory} {l : WeakMem.AllocLabel} {w0 w1 : WeakMem.Ts}
    (hmid : (PushB mem l w0 w1).size < mid.size) (hext : mid.size ≤ mem'.size) :
    (PushB mem l w0 w1).size < mem'.size :=
  Nat.lt_of_lt_of_le hmid hext

end Spike.Lib.HelloFrzSrcSz

/-- info: 'Spike.Lib.HelloFrzSrcSz.bufAt_of_latest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloFrzSrcSz.bufAt_of_latest

/-- info: 'Spike.Lib.HelloFrzSrcSz.alloc_size_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloFrzSrcSz.alloc_size_one
