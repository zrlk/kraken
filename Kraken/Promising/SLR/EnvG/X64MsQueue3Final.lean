/-
**Msqueue3 part 2: the final clean erasure of
the x64 queue of `msqueue3.kl`** gives the `.kl`'s five outcomes. ISA-neutral.

At a final configuration with a clean erasure in which the acquire id `0` of
every queue word is held, at parameters tracking the `head` swings
(`P.trk = true`), `X64MsQueue2Final`'s history applies unchanged (`hist`,
`head_msg`, `head_pair`), and:

- a `head` message of thread `w` is a dequeuer's (`w ∈ {1, 2}`) and its slot
  holds `w`'s pop token whole (`msg_pop`);
- **a dequeuer's record** (`DoneD3`): it returned `0` still holding its pop
  token, or the value of its own `head` message (`Deq3`, the message's thread
  is `w`). Given a `head` message of thread `w`, `w`'s record is that message
  (`done_of_msg`: the pop token is in one place only);
- **the outcomes** (`final_values3`): two non-zero results are two
  messages of different threads, so `n1` and `n2` (`head_pair`); a result
  `n2` overwrote an `n1` `head` message, which is the other dequeuer's, whose
  result it is.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue3Ghost

namespace Kraken.Promising.X64.EnvG.MsQueue3X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read?)
open Kraken.Promising.X64.EnvG.Treiber2X (get?_ne_zero)

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The dequeuers' records -/

/-- **Dequeuer `w`'s dequeue** with result `x`: a message of `head` at `V`
of thread `w` and 64-bit value `x`. -/
def Deq3 (m : Memory) (P : Params) (w : Nat) (V : Time) (x : BitVec 64) : Prop :=
  ∃ vh, m.get? V = some ⟨P.head, vh, w⟩ ∧ BitVec.setWidth 64 vh = x

theorem Deq3.mono {m m' : Memory} (h : m.Prefix m') {P : Params} {w : Nat} {V : Time} {x : BitVec 64}
    (hd : Deq3 m P w V x) : Deq3 m' P w V x :=
  let ⟨vh, h1, h2⟩ := hd
  ⟨vh, Memory.get?_of_prefix h.2 h1, h2⟩

/-- **Dequeuer `w` done** with result `x`, holding `r`: `0` with its pop token
whole, or its own dequeue. -/
def DoneD3 (m : Memory) (P : Params) (w : Nat) (r : Res) (x : BitVec 64) : Prop :=
  (x = 0 ∧ TokFrozen (P.popTok w) r) ∨ ∃ V, Deq3 m P w V x

theorem DoneD3.mono {m m' : Memory} (h : m.Prefix m') {P : Params} {w : Nat} {r : Res} {x : BitVec 64}
    (hd : DoneD3 m P w r x) : DoneD3 m' P w r x :=
  hd.imp id fun ⟨V, hV⟩ => ⟨V, hV.mono h⟩

/-! ## The final law -/

section Final

variable {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}
variable (E : Erase rF g TT c) (hW : GW P g) (hL : QLocs P) (hi : InitV c.mem P)
  (htot : ∀ x, P.IsW x → (total rF g c).acq x 0 = 1) (htrk : P.trk = true)
include E hW hL hi htot htrk

/-- **A `head` message of thread `w`** is a dequeuer's, and its slot holds
`w`'s pop token whole. -/
theorem msg_pop {V : Time} {v : Val} {w : Nat} (hg : c.mem.get? V = some ⟨P.head, v, w⟩) :
    (w = 1 ∨ w = 2) ∧ ∃ s ∈ g.u, s.key = (P.head, V) ∧ TokFrozen (P.popTok w) s.res := by
  have hxw : P.IsW P.head := .inl rfl
  have hrd : c.mem.read? (P.head, V).1 (P.head, V).2 = some v := read?_of_get? hg
  obtain ⟨s, hs, hk, -, hP⟩ := slot_of_held E (htot _ hxw) hrd (hW.impure hxw v)
  rw [hW.acqPred_zero] at hP
  obtain ⟨x', w', hg', -, -, -, h4⟩ := hP (get?_ne_zero hg)
  rw [hg] at hg'
  cases hg'
  have H := hist E hW hL hi htot
  rcases h4 rfl with ht | ht | ⟨hw, ht⟩
  · exact absurd ht (head_not_tailLoc hL (fun V' _ => H V') (Nat.le_refl _))
  · rw [htrk] at ht; cases ht
  · exact ⟨hw, s, hs, hk, ht⟩

/-- **A `head` message of thread `w` is `w`'s record**: if thread `k` holds
`w`'s record `x`, then `x` is the message's value. -/
theorem done_of_msg {k : Nat} (hk : k < c.threads.size) {w : Nat} {x : BitVec 64}
    (hd : DoneD3 c.mem P w (rF k) x) {V : Time} {v : Val} (hg : c.mem.get? V = some ⟨P.head, v, w⟩) :
    x = BitVec.setWidth 64 v := by
  obtain ⟨-, s, hs, hks, hts⟩ := msg_pop E hW hL hi htot htrk hg
  rcases hd with ⟨-, htk⟩ | ⟨V', vh, hg', rfl⟩
  · have := E.q_add_le_one_slot hk hs (P.popTok w)
    unfold TokFrozen at htk hts
    grind
  · obtain ⟨-, s', hs', hks', hts'⟩ := msg_pop E hW hL hi htot htrk hg'
    by_cases hVV : V' = V
    · subst hVV; rw [hg] at hg'; cases hg'; rfl
    · exact (tok_unique E hs hs' (by rw [hks, hks']; intro h; exact hVV (congrArg Prod.snd h)) hts hts').elim

omit htrk in
/-- A dequeue's value is `n1` or `n2`. -/
theorem deq3_val {w : Nat} {V : Time} {x : BitVec 64} (hd : Deq3 c.mem P w V x) : x = P.n1 ∨ x = P.n2 := by
  obtain ⟨vh, hg, rfl⟩ := hd
  obtain ⟨_, _, _, _, _, h⟩ := head_msg E hW hL hi htot hg
  exact h.imp (fun h => h.1) (fun h => h.1)

/-- **A dequeue of `n2`** overwrote an `n1` `head` message of the other
dequeuer `w'`. -/
theorem deq3_n2 {w : Nat} {V : Time} (hd : Deq3 c.mem P w V P.n2) :
    ∃ V' v' w', V' < V ∧ c.mem.get? V' = some ⟨P.head, v', w'⟩ ∧ BitVec.setWidth 64 v' = P.n1 ∧ w' ≠ w := by
  obtain ⟨vh, hg, hv⟩ := hd
  obtain ⟨tr, z, htr, hrz, -, h⟩ := head_msg E hW hL hi htot hg
  have hz : BitVec.setWidth 64 z = P.n1 := by
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (hv.symm.trans h1) (Ne.symm hL.n12)
    · exact h2
  have htr0 : tr ≠ 0 := by
    rintro rfl
    simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hrz
    subst hrz
    exact hL.s1 (hi.head.symm.trans hz)
  obtain ⟨wm, hgm, hl, hvm⟩ := get?_of_read? htr0 hrz
  obtain ⟨x', v', w'⟩ := wm
  simp only at hl hvm
  subst hl hvm
  refine ⟨tr, v', w', htr, hgm, hz, fun hw => ?_⟩
  subst hw
  obtain ⟨-, s, hs, hks, hts⟩ := msg_pop E hW hL hi htot htrk hgm
  obtain ⟨-, s', hs', hks', hts'⟩ := msg_pop E hW hL hi htot htrk hg
  exact tok_unique E hs hs' (by rw [hks, hks']; intro h; have := congrArg Prod.snd h; simp at this; omega_t)
    hts hts'

/-- **The `.kl`'s five outcomes**, from the two dequeuers' records (held by
threads `k1`, `k2`). -/
theorem final_values3 {k1 k2 : Nat} (hk1 : k1 < c.threads.size) (hk2 : k2 < c.threads.size)
    {x1 x2 : BitVec 64} (hd1 : DoneD3 c.mem P 1 (rF k1) x1) (hd2 : DoneD3 c.mem P 2 (rF k2) x2) :
    (x1 = P.n1 ∧ x2 = P.n2) ∨ (x1 = P.n2 ∧ x2 = P.n1) ∨ (x1 = P.n1 ∧ x2 = 0) ∨ (x1 = 0 ∧ x2 = P.n1) ∨
      (x1 = 0 ∧ x2 = 0) := by
  -- a result `n2` of `w` forces the other's result `n1`
  have other : ∀ {w w' k k' : Nat} {x x' : BitVec 64}, k' < c.threads.size → (w = 1 ∧ w' = 2 ∨ w = 2 ∧ w' = 1) →
      DoneD3 c.mem P w (rF k) x → DoneD3 c.mem P w' (rF k') x' → x = P.n2 → x' = P.n1 := by
    intro w w' k k' x x' hk' hww hd hd' hx
    subst hx
    rcases hd with ⟨h0, -⟩ | ⟨V, hV⟩
    · exact absurd h0 hL.n2z
    obtain ⟨V', v', w'', -, hg', hv', hne⟩ := deq3_n2 E hW hL hi htot htrk hV
    obtain ⟨hw'', -⟩ := msg_pop E hW hL hi htot htrk hg'
    have : w'' = w' := by omega
    subst this
    rw [done_of_msg E hW hL hi htot htrk hk' hd' hg', hv']
  have val : ∀ {w k : Nat} {x : BitVec 64}, DoneD3 c.mem P w (rF k) x → x = 0 ∨ x = P.n1 ∨ x = P.n2 := by
    intro w k x hd
    rcases hd with ⟨h, -⟩ | ⟨V, hV⟩
    · exact .inl h
    · exact .inr (deq3_val E hW hL hi htot hV)
  have pop : ∀ {w k : Nat} {x : BitVec 64}, DoneD3 c.mem P w (rF k) x → x ≠ 0 → ∃ V, Deq3 c.mem P w V x := by
    intro w k x hd hx
    rcases hd with ⟨h, -⟩ | h
    · exact absurd h hx
    · exact h
  have o12 : x1 = P.n2 → x2 = P.n1 := other hk2 (.inl ⟨rfl, rfl⟩) hd1 hd2
  have o21 : x2 = P.n2 → x1 = P.n1 := other hk1 (.inr ⟨rfl, rfl⟩) hd2 hd1
  -- two non-zero results differ
  have dist : x1 ≠ 0 → x1 = x2 → False := by
    intro hx he
    obtain ⟨V1, vh1, hg1, hv1⟩ := pop hd1 hx
    obtain ⟨V2, vh2, hg2, hv2⟩ := pop hd2 (he ▸ hx)
    rcases Nat.lt_trichotomy V1 V2 with h | rfl | h
    · obtain ⟨h1, h2⟩ := head_pair E hW hL hi htot h hg1 hg2
      exact hL.n12 (h1.symm.trans (hv1.trans (he.trans (hv2.symm.trans h2))))
    · rw [hg1] at hg2; cases hg2
    · obtain ⟨h1, h2⟩ := head_pair E hW hL hi htot h hg2 hg1
      exact hL.n12 (h1.symm.trans (hv2.trans (he.symm.trans (hv1.symm.trans h2))))
  rcases val hd1 with rfl | rfl | rfl <;> rcases val hd2 with h2 | h2 | h2
  · exact .inr (.inr (.inr (.inr ⟨rfl, h2⟩)))
  · exact .inr (.inr (.inr (.inl ⟨rfl, h2⟩)))
  · exact absurd (o21 h2).symm hL.n1z
  · exact .inr (.inr (.inl ⟨rfl, h2⟩))
  · exact (dist hL.n1z h2.symm).elim
  · exact .inl ⟨rfl, h2⟩
  · exact absurd (h2.symm.trans (o12 rfl)).symm hL.n1z
  · exact .inr (.inl ⟨rfl, h2⟩)
  · exact (dist hL.n2z h2.symm).elim

end Final

end Kraken.Promising.X64.EnvG.MsQueue3X
