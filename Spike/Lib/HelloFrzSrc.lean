/-
**hello.w: `rodata`'s buffer words in source memory up to the clone** (for
`HelloFrz.frzBuf_start`): `rodata`'s two lane stores append the buffer's
words at `⟨l, 0⟩` and `⟨l, 1⟩` (`Hello1RodataMem.rd_latest`'s form); from
then to the clone every message appended is to another label (main's
`new z` allocates a fresh one; `publish`, the pairs and the `spawn` append
nothing), so each element's latest message is still rodata's.

- `latest_ext`: a latest message survives any extension of the memory whose
  new messages are to other labels;
- `frzBuf_latest`: the instance, in the form `print`'s byte reads take
  (`HelloPrintSrcPub.loadCP_byte_i`'s `hM`): for `i < 2` the latest message
  at `⟨l, i⟩` has value `w i`, `w 0 = rdK1`, `w 1 = rdK2`.
-/
import Spike.Lib.Hello1RodataMem

namespace Spike.Lib.HelloFrzSrc

open CoreLang CoreTerm TermRun
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)
open Spike.Lib.Hello1RodataMem (rd_latest)

/-- **A latest message survives an extension whose new messages are to other
labels.** -/
theorem latest_ext {mem mem' : WeakMem.Memory} {a : WeakMem.Address} {j : Nat} {m : WeakMem.Msg}
    (hj : SLatest mem a j) (hm : mem[j]? = some m) (hpre : ∀ k, k < mem.size → mem'[k]? = mem[k]?)
    (hnew : ∀ k m', mem.size ≤ k → mem'[k]? = some m' → m'.loc.label ≠ a.label) :
    SLatest mem' a j ∧ mem'[j]? = some m := by
  have hjs : j < mem.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hm' : mem'[j]? = some m := by rw [hpre j hjs, hm]
  refine ⟨⟨⟨m, hm', ?_⟩, fun k m' hk hk' => ?_⟩, hm'⟩
  · obtain ⟨⟨m0, h0, h1⟩, -⟩ := hj
    rw [hm] at h0
    cases h0
    exact h1
  · by_cases hks : k < mem.size
    · rw [hpre k hks] at hk'
      exact hj.2 k m' hk hk'
    · intro he
      exact hnew k m' (by omega) hk' (by rw [he])

/-- **`rodata`'s buffer words at the clone**: `mem1` is `mem` with
`rodata`'s two lane stores appended (`rdK1` at element `0`, `rdK2` at
element `1` of label `l`); `mem'` extends `mem1` by messages to other
labels only. Then for `i < 2` the latest message at `⟨l, i⟩` in `mem'` has
value `w i`. -/
theorem frzBuf_latest {mem mem' : WeakMem.Memory} {l : WeakMem.AllocLabel} {w0 w1 : WeakMem.Ts}
    {w : Nat → Nat} (hw0 : w 0 = rdK1) (hw1 : w 1 = rdK2)
    (hpre : ∀ k, k < ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩).size →
      mem'[k]? = ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩)[k]?)
    (hnew : ∀ k m', ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩).size ≤ k →
      mem'[k]? = some m' → m'.loc.label ≠ l) :
    ∀ i < 2, ∃ j m, SLatest mem' ⟨l, i⟩ j ∧ mem'[j]? = some m ∧ m.val = .num (w i) := by
  obtain ⟨j0, j1, m0, m1, a0, b0, c0, a1, b1, c1⟩ := rd_latest mem l w0 w1
  intro i hi
  match i, hi with
  | 0, _ =>
    obtain ⟨h1, h2⟩ := latest_ext a0 b0 hpre hnew
    exact ⟨j0, m0, h1, h2, by rw [c0, hw0]⟩
  | 1, _ =>
    obtain ⟨h1, h2⟩ := latest_ext a1 b1 hpre hnew
    exact ⟨j1, m1, h1, h2, by rw [c1, hw1]⟩

/-- info: 'Spike.Lib.HelloFrzSrc.frzBuf_latest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frzBuf_latest

end Spike.Lib.HelloFrzSrc
