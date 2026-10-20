/-
Part 2: **the final clean erasure of the queue**
`msqueue1.kl` gives the dequeuer's value. ISA-neutral.

At a final configuration (no outstanding promise) with a clean erasure in
which the acquire id `0` of every queue word is held (the dequeuer's):

- every non-initial message of a queue word has an id-`0` slot satisfying
  `form` (`msg_form`);
- **values** (`hd_vals`, strong induction on the timestamp): every message of
  `head` or `tail` has a 64-bit value `d` or `n1`. A `form` message's value
  is `n1`, or by provenance the non-zero value of a link word's message
  (`[y + 8]` with `y ∈ {d, n1}` by induction), which is `n1` (`link_val`:
  a link's non-initial message holds `n1`, its initial value is `0`);
- **the dequeuer's last iteration** (`DoneD`: its `ldar` of `head` read `y3`,
  its `ldar` of `[y3 + 8]` read `y5 ≠ 0` at `tr0`, its `ldr` of `[y5]` read
  `u` with no write to `[y5]` after it up to `tr0`): `y3 ∈ {d, n1}`, so
  `[y3 + 8]` is a link word, its message at `tr0` is `n1`'s, whose slot holds
  the data word frozen (`NodeFrozen`; validity empties the junk part `J`), so
  `slot_read` (`EnvG/Treiber2Final.lean`) reads `D`: `X10 = 1`
  (`final_value`).
-/
import Kraken.Promising.SLR.EnvG.MsQueueGhost

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber (read?_of_get? get?_of_read? initVal_eq)

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The ghost facts -/

/-- **The ghost facts** the threads rely on: the release predicates of
`ghost₀`, an acquire table extending `[form]`. -/
def GW (P : Params) (g : Ghost) : Prop :=
  g.rel = (ghost₀ P).rel ∧ (ghost₀ P).acqTab <+: g.acqTab

namespace GW

variable {P : Params} {g g' : Ghost}

theorem mono (h : GW P g) (hle : g.Le g') : GW P g' :=
  ⟨hle.rel.trans h.1, h.2.trans hle.acqTab⟩

theorem rel_q (h : GW P g) {x : Loc} (hx : P.IsQ x) : g.rel x = form P := by rw [h.1]; exact ghost₀_rel_q hx

theorem rel_ne (h : GW P g) {x : Loc} (hx : ¬ P.IsQ x) : g.rel x = Pred.emp := by rw [h.1]; exact ghost₀_rel_ne hx

theorem acqPred_zero (h : GW P g) : g.acqPred 0 = form P :=
  Ghost.acqPred_of_prefix h.2 (by simp [ghost₀])

theorem impure (h : GW P g) {x : Loc} (hx : P.IsQ x) (v : Val) : ¬ Pred.Pure (g.rel x) v := by
  rw [h.rel_q hx]; exact form_not_pure P v

end GW

theorem ghost₀_gw (P : Params) : GW P (ghost₀ P) := ⟨rfl, List.prefix_refl _⟩

/-! ## The dequeuer's final facts -/

/-- **The dequeuer's last iteration** in memory `m` with `X10 = x10`: its
`ldar` of `head` read `y3`; its `ldar` of `[y3 + 8]` read `y5` (64 bits
non-zero) at `tr0`; its `ldr` of `[y5]` (4 bytes) read `u` with no write to
`[y5]` after it up to `tr0`; `x10` is `u`'s zero-extended low 32 bits. -/
def DoneD (m : Memory) (P : Params) (x10 : BitVec 64) : Prop :=
  ∃ (a : Time) (y3 : Val) (tr0 : Time) (y5 : Val) (tl : Time) (u : Val), m.read? P.head a = some y3 ∧
    m.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ BitVec.setWidth 64 y5 ≠ 0 ∧
    m.read? ⟨BitVec.setWidth 64 y5, 4⟩ tl = some u ∧
    (∀ p wm, tl < p → p ≤ tr0 → m.get? p = some wm → wm.loc ≠ ⟨BitVec.setWidth 64 y5, 4⟩) ∧
    x10 = BitVec.setWidth 64 (BitVec.setWidth 32 u)

theorem DoneD.mono {m m' : Memory} (h : m.Prefix m') {P : Params} {x : BitVec 64} (hd : DoneD m P x) :
    DoneD m' P x := by
  obtain ⟨a, y3, tr0, y5, tl, u, h1, h2, h3, h4, h5, h6⟩ := hd
  have hle := TreiberCommon.read?_le_last h2
  refine ⟨a, y3, tr0, y5, tl, u, Treiber2.read?_mono h h1, Treiber2.read?_mono h h2, h3, Treiber2.read?_mono h h4,
    fun p wm a b hg => h5 p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg), h6⟩

/-- The initial values: `head = tail = d`, the links `0` (64 bits). -/
structure InitV (m : Memory) (P : Params) : Prop where
  head : BitVec.setWidth 64 (m.initVal P.head) = P.d
  tail : BitVec.setWidth 64 (m.initVal P.tail) = P.d
  dn : BitVec.setWidth 64 (m.initVal P.dn) = 0
  nn : BitVec.setWidth 64 (m.initVal P.nn) = 0

theorem InitV.of_init {m m' : Memory} (h : m'.init = m.init) {P : Params} (hi : InitV m P) : InitV m' P :=
  ⟨by rw [initVal_eq h]; exact hi.1, by rw [initVal_eq h]; exact hi.2, by rw [initVal_eq h]; exact hi.3,
    by rw [initVal_eq h]; exact hi.4⟩

/-! ## The final law -/

section Final

variable {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- **Every non-initial message of a queue word has an id-`0` slot in
`form`.** -/
theorem msg_form (E : Erase rF g TT c) (hW : GW P g) {x : Loc} (hx : P.IsQ x)
    (htot : (total rF g c).acq x 0 = 1) {V : Time} {v : Val} {w : Nat} (hV : c.mem.get? V = some ⟨x, v, w⟩) :
    ∃ s ∈ g.u, s.key = (x, V) ∧ (P.IsN x → BitVec.setWidth 64 v = P.n1 ∧ NodeFrozen P s.res V) ∧
      (¬ P.IsN x → BitVec.setWidth 64 v = P.n1 ∨ Prov P c.mem V v) := by
  have hrd : c.mem.read? (x, V).1 (x, V).2 = some v := read?_of_get? hV
  obtain ⟨s, hs, hk, -, hP⟩ := slot_of_held E htot hrd (hW.impure hx v)
  rw [hW.acqPred_zero] at hP
  obtain ⟨x', w', hg, h1, h2⟩ := hP (Treiber2.get?_ne_zero hV)
  rw [hV] at hg
  cases hg
  exact ⟨s, hs, hk, h1, h2⟩

/-- **A link word's non-zero value is `n1`**, with the node frozen in the
message's slot. -/
theorem link_val (E : Erase rF g TT c) (hW : GW P g) (hi : InitV c.mem P) {x : Loc} (hx : P.IsN x)
    (htot : (total rF g c).acq x 0 = 1) {b : Time} {z : Val} (hr : c.mem.read? x b = some z)
    (hz : BitVec.setWidth 64 z ≠ 0) :
    BitVec.setWidth 64 z = P.n1 ∧ ∃ s ∈ g.u, s.key = (x, b) ∧ NodeFrozen P s.res b := by
  by_cases hb : b = 0
  · subst hb
    simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
    subst hr
    rcases hx with rfl | rfl
    · exact absurd hi.dn hz
    · exact absurd hi.nn hz
  · obtain ⟨wm, hg, hl, hv⟩ := get?_of_read? hb hr
    have hg' : c.mem.get? b = some ⟨x, z, wm.tid⟩ := by rw [hg, ← hl, ← hv]
    obtain ⟨s, hs, hk, h1, -⟩ := msg_form E hW (isQ_of_isN P hx) htot hg'
    obtain ⟨h2, h3⟩ := h1 hx
    exact ⟨h2, s, hs, hk, h3⟩

/-- `[y + 8]` for `y ∈ {d, n1}` is a link word. -/
theorem isN_of_val {y : BitVec 64} (hy : y = P.d ∨ y = P.n1) : P.IsN ⟨y + 8, 8⟩ := by
  rcases hy with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

/-- **The values of `head` and `tail`** are `d` and `n1`. -/
theorem hd_vals (E : Erase rF g TT c) (hW : GW P g) (hL : QLocs P) (hi : InitV c.mem P)
    (htot : ∀ x, P.IsQ x → (total rF g c).acq x 0 = 1) :
    ∀ V x y, (x = P.head ∨ x = P.tail) → c.mem.read? x V = some y →
      BitVec.setWidth 64 y = P.d ∨ BitVec.setWidth 64 y = P.n1 := by
  intro V
  induction V using Nat.strongRecOn with
  | _ V ih =>
    intro x y hx hr
    have hxq : P.IsQ x := by
      rcases hx with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
    have hxn : ¬ P.IsN x := by
      rcases hx with rfl | rfl
      · exact hL.not_isN_head
      · exact hL.not_isN_tail
    by_cases hV : V = 0
    · subst hV
      simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rcases hx with rfl | rfl
      · exact .inl hi.head
      · exact .inl hi.tail
    obtain ⟨wm, hg, hl, hv⟩ := get?_of_read? hV hr
    have hg' : c.mem.get? V = some ⟨x, y, wm.tid⟩ := by rw [hg, ← hl, ← hv]
    obtain ⟨s, -, -, -, h2⟩ := msg_form E hW hxq (htot x hxq) hg'
    rcases h2 hxn with h | ⟨hnz, x', a, y', b, y'', hx', ha, hr', hb, hr'', hyy⟩
    · exact .inr h
    · have hn := isN_of_val (ih a ha x' y' hx' hr')
      obtain ⟨h, -⟩ := link_val E hW hi hn (htot _ (isQ_of_isN P hn)) hr'' (by rw [hyy]; exact hnz)
      exact .inr (by rw [← hyy, h])

/-- **The dequeuer's value**: `X10 = 1`. -/
theorem final_value (E : Erase rF g TT c) (hW : GW P g) (hL : QLocs P) (hi : InitV c.mem P)
    (hno : ∀ ts, ¬ Outstanding c ts) (htot : ∀ x, P.IsQ x → (total rF g c).acq x 0 = 1) {x10 : BitVec 64}
    (hd : DoneD c.mem P x10) : x10 = 1 := by
  obtain ⟨a, y3, tr0, y5, tl, u, h1, h2, h3, h4, h5, rfl⟩ := hd
  have hn := isN_of_val (hd_vals E hW hL hi htot a P.head y3 (.inl rfl) h1)
  obtain ⟨hv, s, hs, -, O, J, hOJ, hOq, d, td, hX, hmax, htd, hD⟩ :=
    link_val E hW hi hn (htot _ (isQ_of_isN P hn)) h2 h3
  -- validity empties the junk part
  have hle : (s.res.wr P.dat).q ≤ 1 :=
    Rat.le_trans ((sub_total_slot (rF := rF) (c := c) hs).q_le P.dat) (E.valid.1 P.dat)
  have hJ : J.q = 0 := by
    rw [hOJ] at hle
    have := J.nonneg
    change O.q + J.q ≤ 1 at hle
    grind
  have hq : (s.res.wr P.dat).q = 1 := by rw [hOJ]; change O.q + J.q = 1; rw [hOq, hJ]; exact Rat.add_zero 1
  have hXs : ∀ p, (s.res.wr P.dat).X p ↔ O.X p := by
    intro p; rw [hOJ]
    exact ⟨fun h => h.resolve_right (J.zero hJ p), .inl⟩
  have hl : (⟨BitVec.setWidth 64 y5, 4⟩ : Loc) = P.dat := by rw [hv]; rfl
  rw [hl] at h4 h5
  have hu := Treiber2.slot_read E hno hs hq ((hXs _).mpr hX) (fun p hp => hmax p ((hXs p).mp hp)) h4 h5
    (Nat.le_of_lt htd)
  subst hu
  unfold D at hD
  rw [hD]; rfl

end Final

end Kraken.Promising.SLR.EnvG.MsQueue
