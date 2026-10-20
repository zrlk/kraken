/-
Part 2: **the final law of `msqueue3.kl`**: the two
dequeuers receive `1` and `2`, one each.

msqueue2's final law (`EnvG/MsQueue2Final.lean`) does all the work: at a
final clean erasure in which the acquire id `0` of every queue word is
held, two non-initial messages of `head` are `n1` (the earlier) and `n2`
(the later) (`head_pair`), and a dequeue whose swing wrote `n1` (`n2`) read
`1` (`2`) (`deq_data`). A dequeue of thread `k` (`Deq3`) records its own
swing message with writer `k`, so the swings of the two dequeuers are at
different timestamps: **each node is dequeued exactly once**
(`final_values3`).

Also the identity-token exclusion for `tokD2` (`tokD2_pair_false`).
-/
import Kraken.Promising.SLR.EnvG.MsQueue3Ghost
import Kraken.Promising.SLR.EnvG.MsQueue2Final

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising

variable {I : ISA}

/-- **One dequeue of thread `k`** with result `x`: msqueue1's `DoneAt` (its
reads of `head`, of `[y3 + 8]` (`y5`) and of `[y5]`), and its own swing of
`head` at `V` to `y5` (writer `k`). -/
def Deq3 (m : Memory) (P : Params2) (k : Nat) (V : Time) (x : BitVec 64) : Prop :=
  ∃ y3 y5 vh, DoneAt m P.toParams y3 y5 x ∧ m.get? V = some ⟨P.head, vh, k⟩ ∧
    BitVec.setWidth 64 vh = BitVec.setWidth 64 y5

theorem Deq3.mono {m m' : Memory} (h : m.Prefix m') {P : Params2} {k : Nat} {V : Time} {x : BitVec 64}
    (hd : Deq3 m P k V x) : Deq3 m' P k V x :=
  let ⟨y3, y5, vh, h1, h2, h3⟩ := hd
  ⟨y3, y5, vh, h1.mono h, Memory.get?_of_prefix h.2 h2, h3⟩

theorem Deq3.deq {m : Memory} {P : Params2} {k : Nat} {V : Time} {x : BitVec 64} (hd : Deq3 m P k V x) :
    Deq m P V x :=
  let ⟨y3, y5, vh, h1, h2, h3⟩ := hd
  ⟨y3, y5, vh, k, h1, h2, h3⟩

/-- **Thread `k` is done**: one dequeue of thread `k` with result `x`. -/
def DoneK (m : Memory) (P : Params2) (k : Nat) (x : BitVec 64) : Prop := ∃ V, Deq3 m P k V x

theorem DoneK.mono {m m' : Memory} (h : m.Prefix m') {P : Params2} {k : Nat} {x : BitVec 64}
    (hd : DoneK m P k x) : DoneK m' P k x :=
  let ⟨V, hV⟩ := hd
  ⟨V, hV.mono h⟩

section Final

variable {P : Params2} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- **The two dequeuers' values** at a final clean erasure: `1` and `2`, one
each. -/
theorem final_values3 (E : Erase rF g TT c) (hW : GW2 P g) (hL : QLocs2 P) (hi : InitV2 c.mem P)
    (htot : ∀ x, P.IsW x → (total rF g c).acq x 0 = 1) (hno : ∀ ts, ¬ Outstanding c ts) {x1 x2 : BitVec 64}
    (hd1 : DoneK c.mem P 1 x1) (hd2 : DoneK c.mem P 2 x2) :
    (x1 = 1 ∧ x2 = 2) ∨ (x1 = 2 ∧ x2 = 1) := by
  obtain ⟨V1, hq1⟩ := hd1
  obtain ⟨V2, hq2⟩ := hd2
  obtain ⟨y1, w1, hg1, h1a, h1b⟩ := deq_data E hW hL hi htot hno hq1.deq
  obtain ⟨y2, w2, hg2, h2a, h2b⟩ := deq_data E hW hL hi htot hno hq2.deq
  have hg1' : ∃ vh, c.mem.get? V1 = some ⟨P.head, vh, 1⟩ := let ⟨_, _, vh, _, h, _⟩ := hq1; ⟨vh, h⟩
  have hg2' : ∃ vh, c.mem.get? V2 = some ⟨P.head, vh, 2⟩ := let ⟨_, _, vh, _, h, _⟩ := hq2; ⟨vh, h⟩
  rcases Nat.lt_trichotomy V1 V2 with h | h | h
  · obtain ⟨hv1, hv2⟩ := head_pair E hW hL hi htot h hg1 hg2
    exact .inl ⟨h1a hv1, h2b hv2⟩
  · subst h
    obtain ⟨_, ha⟩ := hg1'
    obtain ⟨_, hb⟩ := hg2'
    rw [ha] at hb
    cases hb
  · obtain ⟨hv2, hv1⟩ := head_pair E hW hL hi htot h hg2 hg1
    exact .inr ⟨h1b hv1, h2a hv2⟩

end Final

/-- **Two threads cannot both hold `tokD2` whole.** -/
theorem tokD2_pair_false {P : Params2} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    (h1 : 1 ≤ ((rF i).wr (tokD2 P)).q) (h2 : 1 ≤ ((rF j).wr (tokD2 P)).q) : False :=
  wr_pair_false E hi hj hij h1 h2

end Kraken.Promising.SLR.EnvG.MsQueue
