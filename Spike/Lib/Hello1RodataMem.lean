/-
**`rodata`'s buffer words in source memory**: after the two lane
exchanges (`Spike/Lib/Hello1RodataSrc.lean`), each appending its word's
message (`SrcMem.src_swap_step_cfg`), the latest message of element `0` is
`rdK1`'s and of element `1` is `rdK2`'s.

- `SLatest_push_self`, `SLatest_push_ne`: an appended message is the
  latest at its address and leaves the latest at every other address;
- `pushAll`: appending a list of messages in order; `latest_pushAll_keep`,
  `latest_pushAll`: after appends at pairwise distinct addresses, the
  latest message at each is the one appended there (any memory before);
- `pushLanes`, `latest_pushLanes`: the stores of a buffer's elements at
  distinct indices (a buffer at label `l`, element `k` at `offs ⟨l, 0⟩ k`,
  as `xchgAt`'s site has it), each element's latest message its stored
  value;
- `rd_latest`: `rodata`'s instance, the two appends at `offs ⟨l, 0⟩ 0` and `offs ⟨l, 0⟩ 1`, in
  the form `print`'s byte reads take (`⟨l, 0⟩`, `⟨l, 1⟩`, the message and
  its value).
-/
import Spike.Lib.SrcMem
import Spike.Lib.Hello1RodataSrc

namespace Spike.Lib.Hello1RodataMem

open CoreLang CoreTerm TermRun
open Scc.Sem.MemRel (SLatest)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2)

/-- **An appended message is the latest at its address.** -/
theorem SLatest_push_self (mem : WeakMem.Memory) (a : WeakMem.Address) (v : WeakMem.Val) (w : WeakMem.Ts) :
    SLatest (mem.push ⟨a, v, w⟩) a mem.size := by
  refine ⟨⟨⟨a, v, w⟩, by simp, rfl⟩, fun k m hk hm => ?_⟩
  rw [Array.getElem?_push] at hm
  split at hm
  · omega
  · rw [Array.getElem?_eq_none (by omega)] at hm
    cases hm

/-- **An append at another address keeps the latest message.** -/
theorem SLatest_push_ne {mem : WeakMem.Memory} {a a' : WeakMem.Address} {j : Nat} (hj : SLatest mem a' j)
    (hne : a ≠ a') (v : WeakMem.Val) (w : WeakMem.Ts) : SLatest (mem.push ⟨a, v, w⟩) a' j := by
  obtain ⟨⟨m, hm, hl⟩, hlat⟩ := hj
  have hjs : j < mem.size := (Array.getElem?_eq_some_iff.mp hm).1
  refine ⟨⟨m, ?_, hl⟩, fun k m' hk hm' => ?_⟩
  · simp [Array.getElem?_push, show j ≠ mem.size by omega, hm]
  · rw [Array.getElem?_push] at hm'
    split at hm'
    · cases hm'; exact hne
    · exact hlat k m' hk hm'

/-- **Appending messages in order.** -/
def pushAll (mem : WeakMem.Memory) (ws : List (WeakMem.Address × WeakMem.Val × WeakMem.Ts)) : WeakMem.Memory :=
  ws.foldl (fun m x => m.push ⟨x.1, x.2.1, x.2.2⟩) mem

/-- **Appends elsewhere keep a latest message** and its value. -/
theorem latest_pushAll_keep {ws : List (WeakMem.Address × WeakMem.Val × WeakMem.Ts)} :
    ∀ {mem : WeakMem.Memory} {a : WeakMem.Address} {j : Nat} {m : WeakMem.Msg},
      a ∉ ws.map (·.1) → SLatest mem a j → mem[j]? = some m →
      SLatest (pushAll mem ws) a j ∧ (pushAll mem ws)[j]? = some m := by
  induction ws with
  | nil => intro mem a j m _ hj hm; exact ⟨hj, hm⟩
  | cons x ws ih =>
    intro mem a j m ha hj hm
    simp only [List.map_cons, List.mem_cons, not_or] at ha
    have hjs : j < mem.size := (Array.getElem?_eq_some_iff.mp hm).1
    exact ih ha.2 (SLatest_push_ne hj (Ne.symm ha.1) _ _)
      (by simp [Array.getElem?_push, show j ≠ mem.size by omega, hm])

/-- **After appends at pairwise distinct addresses, each address's latest
message is the one appended there.** -/
theorem latest_pushAll {ws : List (WeakMem.Address × WeakMem.Val × WeakMem.Ts)} (hnd : (ws.map (·.1)).Nodup) :
    ∀ {mem : WeakMem.Memory} {a : WeakMem.Address} {v : WeakMem.Val} {w : WeakMem.Ts}, (a, v, w) ∈ ws →
      ∃ j m, SLatest (pushAll mem ws) a j ∧ (pushAll mem ws)[j]? = some m ∧ m.val = v := by
  induction ws with
  | nil => intro _ _ _ _ h; cases h
  | cons x ws ih =>
    intro mem a v w h
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with rfl | h
    · have hk := latest_pushAll_keep (mem := mem.push ⟨a, v, w⟩) (m := ⟨a, v, w⟩) hnd.1
        (SLatest_push_self mem a v w) (by simp)
      exact ⟨mem.size, ⟨a, v, w⟩, hk.1, hk.2, rfl⟩
    · exact ih hnd.2 h

/-- **A buffer's element stores**: element `k` of the buffer at label `l`
stored with value `v`, in order. -/
def pushLanes (mem : WeakMem.Memory) (l : WeakMem.AllocLabel) (ks : List (Nat × WeakMem.Val × WeakMem.Ts)) :
    WeakMem.Memory :=
  pushAll mem (ks.map fun x => (offs ⟨l, 0⟩ x.1, x.2.1, x.2.2))

/-- **After a buffer's stores at distinct indices, each element's latest
message has its stored value**, at the bare address `⟨l, k⟩`. -/
theorem latest_pushLanes (mem : WeakMem.Memory) (l : WeakMem.AllocLabel)
    {ks : List (Nat × WeakMem.Val × WeakMem.Ts)} (hnd : (ks.map (·.1)).Nodup) {k : Nat} {v : WeakMem.Val}
    {w : WeakMem.Ts} (h : (k, v, w) ∈ ks) :
    ∃ j m, SLatest (pushLanes mem l ks) ⟨l, k⟩ j ∧ (pushLanes mem l ks)[j]? = some m ∧ m.val = v := by
  have ho : ∀ k : Nat, offs ⟨l, 0⟩ k = (⟨l, k⟩ : WeakMem.Address) := fun k => by simp [offs]
  have hnd' : ((ks.map fun x => (offs ⟨l, 0⟩ x.1, x.2.1, x.2.2)).map (·.1)).Nodup := by
    have he : ((ks.map fun x => (offs ⟨l, 0⟩ x.1, x.2.1, x.2.2)).map (·.1)) = (ks.map (·.1)).map (offs ⟨l, 0⟩) := by
      simp [List.map_map, Function.comp_def]
    rw [he]
    exact List.pairwise_map.mpr (List.Pairwise.imp (fun {a b} h e => h (by simpa [offs] using e)) hnd)
  have := latest_pushAll (mem := mem) hnd' (List.mem_map.mpr ⟨_, h, rfl⟩)
  rw [ho] at this
  exact this

/-- **`rodata`'s buffer words after its two lane exchanges**: in memory
`mem` with `rdK1`'s message appended at element `0` of label `l` and then
`rdK2`'s at element `1` (any views), the latest message of `⟨l, 0⟩` has
value `rdK1` and of `⟨l, 1⟩` value `rdK2` (`latest_pushLanes`). -/
theorem rd_latest (mem : WeakMem.Memory) (l : WeakMem.AllocLabel) (w0 w1 : WeakMem.Ts) :
    ∃ j0 j1 : Nat, ∃ m0 m1 : WeakMem.Msg,
      SLatest ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩) ⟨l, 0⟩ j0 ∧
      ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩)[j0]? = some m0 ∧
      m0.val = .num rdK1 ∧
      SLatest ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩) ⟨l, 1⟩ j1 ∧
      ((mem.push ⟨offs ⟨l, 0⟩ 0, .num rdK1, w0⟩).push ⟨offs ⟨l, 0⟩ 1, .num rdK2, w1⟩)[j1]? = some m1 ∧
      m1.val = .num rdK2 := by
  have hnd : (([(0, .num rdK1, w0), (1, .num rdK2, w1)] : List (Nat × WeakMem.Val × WeakMem.Ts)).map (·.1)).Nodup := by
    simp
  obtain ⟨j0, m0, a0, b0, c0⟩ := latest_pushLanes mem l hnd (k := 0) (v := .num rdK1) (w := w0) (by simp)
  obtain ⟨j1, m1, a1, b1, c1⟩ := latest_pushLanes mem l hnd (k := 1) (v := .num rdK2) (w := w1) (by simp)
  exact ⟨j0, j1, m0, m1, a0, b0, c0, a1, b1, c1⟩

end Spike.Lib.Hello1RodataMem
