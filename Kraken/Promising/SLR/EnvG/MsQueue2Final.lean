/-
Msqueue2 part 2: **the final clean erasure of the
queue of `msqueue2.kl`** gives FIFO: the dequeuer's two values are `1` and
`2`. ISA-neutral.

At a final configuration (no outstanding promise) with a clean erasure in
which the acquire id `0` of every queue word is held (the dequeuer's):

- every non-initial message of a queue word has an id-`0` slot in `form2`
  (`msg_form2`);
- **the history** (`hist`, strong induction on the timestamp): a value of
  `head`/`tail` at `V` is `d`, or `n1` with `n1`'s link message at `[d + 8]`
  below `V` (`L1At`), or `n2` with `n2`'s link message at `[n1 + 8]` below `V`
  (`L2At`, itself above an `L1At`); a non-initial link message at `V` is `n1`
  at `[d + 8]`, or `n2` at `[n1 + 8]` above an `L1At` (`LK`). A link message's
  address is a value of `tail` plus `8` (`TailLoc`), so a link word; two
  messages freezing the same data word contradict validity
  (`frozen_unique`), and a second message at `[d + 8]` overwrote a non-zero
  adjacent message (`AdjZero`);
- **the `head` chain** (`head_msg`, `head_pair`): a non-initial message of
  `head` overwrote an adjacent `d` and is `n1`, or overwrote `n1` and is
  `n2`; so of two of them, the earlier is `n1` and the later `n2`;
- **the dequeuer's two iterations** (`DoneD2`: two `Deq`s whose `head`
  swings are at `V1 < V2`): their values are `n1`, `n2`, the link messages
  they read freeze `n1`'s and `n2`'s data words, so `slot_read` reads `1` and
  `2` (`final_values2`).
-/
import Kraken.Promising.SLR.EnvG.MsQueue2Ghost
import Kraken.Promising.SLR.EnvG.MsQueueVC

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber (read?_of_get? get?_of_read? initVal_eq)

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The ghost facts -/

/-- `form2` is impure at every value: it needs the message. -/
theorem form2_not_pure (P : Params2) (v : Val) : ¬ Pred.Pure (form2 P) v := by
  intro h
  obtain ⟨x, w, hg, -⟩ := h { init := [], msgs := #[] } 1 (by decide)
  simp [Memory.get?] at hg

/-- **The ghost facts** of `msqueue2.kl`. -/
def GW2 (P : Params2) (g : Ghost) : Prop :=
  g.rel = (ghost2 P).rel ∧ (ghost2 P).acqTab <+: g.acqTab

namespace GW2

variable {P : Params2} {g g' : Ghost}

theorem mono (h : GW2 P g) (hle : g.Le g') : GW2 P g' :=
  ⟨hle.rel.trans h.1, h.2.trans hle.acqTab⟩

theorem rel_w (h : GW2 P g) {x : Loc} (hx : P.IsW x) : g.rel x = form2 P := by rw [h.1]; exact ghost2_rel_w hx

theorem rel_ne (h : GW2 P g) {x : Loc} (hx : ¬ P.IsW x) : g.rel x = Pred.emp := by
  rw [h.1]; exact ghost2_rel_ne hx

theorem acqPred_zero (h : GW2 P g) : g.acqPred 0 = form2 P :=
  Ghost.acqPred_of_prefix h.2 (by simp [ghost2])

theorem impure (h : GW2 P g) {x : Loc} (hx : P.IsW x) (v : Val) : ¬ Pred.Pure (g.rel x) v := by
  rw [h.rel_w hx]; exact form2_not_pure P v

end GW2

theorem ghost2_gw (P : Params2) : GW2 P (ghost2 P) := ⟨rfl, List.prefix_refl _⟩

/-- The initial values: msqueue1's, and `n2`'s link `0`. -/
structure InitV2 (m : Memory) (P : Params2) : Prop where
  v1 : InitV m P.toParams
  nn2 : BitVec.setWidth 64 (m.initVal P.nn2) = 0

theorem InitV2.of_init {m m' : Memory} (h : m'.init = m.init) {P : Params2} (hi : InitV2 m P) : InitV2 m' P :=
  ⟨hi.1.of_init h, by rw [initVal_eq h]; exact hi.2⟩

/-! ## The dequeuer's facts -/

/-- **One dequeue** with result `x`: msqueue1's `DoneAt` (its reads of
`head`, of `[y3 + 8]` (`y5`) and of `[y5]`), and its swing of `head` at `V`
to `y5`. -/
def Deq (m : Memory) (P : Params2) (V : Time) (x : BitVec 64) : Prop :=
  ∃ y3 y5 vh w, DoneAt m P.toParams y3 y5 x ∧ m.get? V = some ⟨P.head, vh, w⟩ ∧
    BitVec.setWidth 64 vh = BitVec.setWidth 64 y5

theorem Deq.mono {m m' : Memory} (h : m.Prefix m') {P : Params2} {V : Time} {x : BitVec 64} (hd : Deq m P V x) :
    Deq m' P V x :=
  let ⟨y3, y5, vh, w, h1, h2, h3⟩ := hd
  ⟨y3, y5, vh, w, h1.mono h, Memory.get?_of_prefix h.2 h2, h3⟩

/-- **The dequeuer's two dequeues**, the first `head` swing below the
second. -/
def DoneD2 (m : Memory) (P : Params2) (x10 x11 : BitVec 64) : Prop :=
  ∃ V1 V2, V1 < V2 ∧ Deq m P V1 x10 ∧ Deq m P V2 x11

theorem DoneD2.mono {m m' : Memory} (h : m.Prefix m') {P : Params2} {x y : BitVec 64} (hd : DoneD2 m P x y) :
    DoneD2 m' P x y :=
  let ⟨V1, V2, h1, h2, h3⟩ := hd
  ⟨V1, V2, h1, h2.mono h, h3.mono h⟩

/-! ## The final law -/

section Final

variable {P : Params2} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- **Every non-initial message of a queue word has an id-`0` slot in
`form2`.** -/
theorem msg_form2 (E : Erase rF g TT c) (hW : GW2 P g) {x : Loc} (hx : P.IsW x)
    (htot : (total rF g c).acq x 0 = 1) {V : Time} {v : Val} {w : Nat} (hV : c.mem.get? V = some ⟨x, v, w⟩) :
    ∃ s ∈ g.u, s.key = (x, V) ∧ (P.IsL x → LinkF P c.mem V s.res x v) ∧
      (x = P.head → HeadF P c.mem V v ∨ TailLoc P c.mem V x) ∧
      (x = P.tail → SwingF P c.mem V v ∨ Prov P.toParams c.mem V v ∨ TailLoc P c.mem V x) := by
  have hrd : c.mem.read? (x, V).1 (x, V).2 = some v := read?_of_get? hV
  obtain ⟨s, hs, hk, -, hP⟩ := slot_of_held E htot hrd (hW.impure hx v)
  rw [hW.acqPred_zero] at hP
  obtain ⟨x', w', hg, h1, h2, h3⟩ := hP (Treiber2.get?_ne_zero hV)
  rw [hV] at hg
  cases hg
  exact ⟨s, hs, hk, h1, h2, h3⟩

theorem NodeFrozenAt.one_le {δ : Loc} {Dp : Val → Prop} {R : Res} {V : View} (h : NodeFrozenAt δ Dp R V) :
    1 ≤ (R.wr δ).q := by
  obtain ⟨O, J, hOJ, hOq, -⟩ := h
  rw [hOJ]; exact q_op_ge_one (by rw [hOq]; exact Rat.le_refl)

/-- **Two slots cannot freeze the same data word.** -/
theorem frozen_unique (E : Erase rF g TT c) {s s' : Slot} (hs : s ∈ g.u) (hs' : s' ∈ g.u) (hne : s'.key ≠ s.key)
    {δ : Loc} {D1 D2 : Val → Prop} {V V' : View} (h1 : NodeFrozenAt δ D1 s.res V)
    (h2 : NodeFrozenAt δ D2 s'.res V') : False := by
  have := E.q_add_le_one_slots hs hs' (fun h => hne (by rw [h])) δ
  have := h1.one_le
  have := h2.one_le
  grind

/-- **A frozen data word is read with its property**: a read of `δ` at
`tl` with no write to `δ` after it up to `B ≥ V`. -/
theorem frozen_read (E : Erase rF g TT c) (hno : ∀ ts, ¬ Outstanding c ts) {s : Slot} (hs : s ∈ g.u) {δ : Loc}
    {Dp : Val → Prop} {V : View} (hf : NodeFrozenAt δ Dp s.res V) {tl B : Time} {u : Val}
    (hrd : c.mem.read? δ tl = some u) (hwin : ∀ p wm, tl < p → p ≤ B → c.mem.get? p = some wm → wm.loc ≠ δ)
    (hVB : V ≤ B) : Dp u := by
  obtain ⟨O, J, hOJ, hOq, d, td, hX, hmax, htd, hD⟩ := hf
  have hle : (s.res.wr δ).q ≤ 1 := Rat.le_trans ((sub_total_slot (rF := rF) (c := c) hs).q_le δ) (E.valid.1 δ)
  have hJ : J.q = 0 := by
    rw [hOJ] at hle
    have := J.nonneg
    change O.q + J.q ≤ 1 at hle
    grind
  have hq : (s.res.wr δ).q = 1 := by rw [hOJ]; change O.q + J.q = 1; rw [hOq, hJ]; exact Rat.add_zero 1
  have hXs : ∀ p, (s.res.wr δ).X p ↔ O.X p := by
    intro p; rw [hOJ]
    exact ⟨fun h => h.resolve_right (J.zero hJ p), .inl⟩
  have hu := Treiber2.slot_read E hno hs hq ((hXs _).mpr hX) (fun p hp => hmax p ((hXs p).mp hp)) hrd hwin
    (by omega_t)
  subst hu; exact hD

/-! ### The history -/

/-- `n1`'s link message at `[d + 8]` at `b`. -/
def L1At (P : Params2) (m : Memory) (b : Time) : Prop :=
  ∃ v w, m.get? b = some ⟨P.dn, v, w⟩ ∧ BitVec.setWidth 64 v = P.n1

/-- `n2`'s link message at `[n1 + 8]` at `b`, above an `L1At`. -/
def L2At (P : Params2) (m : Memory) (b : Time) : Prop :=
  ∃ v w, m.get? b = some ⟨P.nn, v, w⟩ ∧ BitVec.setWidth 64 v = P.n2 ∧ ∃ b1 < b, L1At P m b1

/-- The value `y` of `head`/`tail` at `V`. -/
def HT (P : Params2) (m : Memory) (V : Time) (y : BitVec 64) : Prop :=
  y = P.d ∨ (y = P.n1 ∧ ∃ b < V, L1At P m b) ∨ (y = P.n2 ∧ ∃ b < V, L2At P m b)

/-- The non-initial link message `(x, y)` at `V`. -/
def LK (P : Params2) (m : Memory) (V : Time) (x : Loc) (y : BitVec 64) : Prop :=
  (x = P.dn ∧ y = P.n1) ∨ (x = P.nn ∧ y = P.n2 ∧ ∃ b1 < V, L1At P m b1)

/-- The history at `V`. -/
def Hist (P : Params2) (m : Memory) (V : Time) : Prop :=
  (∀ x y, (x = P.head ∨ x = P.tail) → m.read? x V = some y → HT P m V (BitVec.setWidth 64 y)) ∧
    ∀ x v w, P.IsL x → m.get? V = some ⟨x, v, w⟩ → LK P m V x (BitVec.setWidth 64 v)

theorem isL_of_HT {m : Memory} {V : Time} {y : BitVec 64} (h : HT P m V y) : P.IsL ⟨y + 8, 8⟩ := by
  rcases h with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem HT_of_LK {m : Memory} {b V : Time} {x : Loc} {v : Val} {w : Nat} (hg : m.get? b = some ⟨x, v, w⟩)
    (hk : LK P m b x (BitVec.setWidth 64 v)) (hb : b < V) : HT P m V (BitVec.setWidth 64 v) := by
  rcases hk with ⟨rfl, h⟩ | ⟨rfl, h, b1, hb1, h1⟩
  · exact .inr (.inl ⟨h, b, hb, v, w, hg, h⟩)
  · exact .inr (.inr ⟨h, b, hb, v, w, hg, h, b1, hb1, h1⟩)

theorem initVal_link (hi : InitV2 c.mem P) {x : Loc} (hx : P.IsL x) : BitVec.setWidth 64 (c.mem.initVal x) = 0 := by
  rcases hx with rfl | rfl | rfl
  · exact hi.1.dn
  · exact hi.1.nn
  · exact hi.2

theorem msg_of_read {x : Loc} {b : Time} {y : Val} (hb : b ≠ 0) (hr : c.mem.read? x b = some y) :
    ∃ w, c.mem.get? b = some ⟨x, y, w⟩ := by
  obtain ⟨wm, hg, hl, hv⟩ := get?_of_read? hb hr
  exact ⟨wm.tid, by rw [hg, ← hl, ← hv]⟩

theorem ne_zero_of_link (hi : InitV2 c.mem P) {x : Loc} (hx : P.IsL x) {b : Time} {y : Val}
    (hr : c.mem.read? x b = some y) (hy : BitVec.setWidth 64 y ≠ 0) : b ≠ 0 := by
  rintro rfl
  simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
  subst hr; exact hy (initVal_link hi hx)

variable (E : Erase rF g TT c) (hW : GW2 P g) (hL : QLocs2 P) (hi : InitV2 c.mem P)
  (htot : ∀ x, P.IsW x → (total rF g c).acq x 0 = 1)
include E hW hL hi htot

omit hi in
/-- A link message's slot freezes `n1`'s data word if its value is `n1`. -/
theorem frozen1 {x : Loc} (hx : P.IsL x) {V : Time} {v : Val} {w : Nat} (hg : c.mem.get? V = some ⟨x, v, w⟩)
    (hv : BitVec.setWidth 64 v = P.n1) : ∃ s ∈ g.u, s.key = (x, V) ∧ NodeFrozenAt P.dat D s.res V := by
  obtain ⟨s, hs, hk, h1, -⟩ := msg_form2 E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
  rcases (h1 hx).1 with ⟨-, hf⟩ | ⟨hv', -⟩
  · exact ⟨s, hs, hk, hf⟩
  · exact absurd (hv.symm.trans hv') hL.n12

omit hi in
/-- A link message's slot freezes `n2`'s data word if its value is `n2`. -/
theorem frozen2 {x : Loc} (hx : P.IsL x) {V : Time} {v : Val} {w : Nat} (hg : c.mem.get? V = some ⟨x, v, w⟩)
    (hv : BitVec.setWidth 64 v = P.n2) : ∃ s ∈ g.u, s.key = (x, V) ∧ NodeFrozenAt P.dat2 D2 s.res V := by
  obtain ⟨s, hs, hk, h1, -⟩ := msg_form2 E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
  rcases (h1 hx).1 with ⟨hv', -⟩ | ⟨-, hf, -⟩
  · exact absurd (hv'.symm.trans hv) hL.n12
  · exact ⟨s, hs, hk, hf⟩

omit hi in
/-- Two `n_i` link messages at different times contradict validity. -/
theorem two_n1 {x x' : Loc} (hx : P.IsL x) (hx' : P.IsL x') {V V' : Time} {v v' : Val} {w w' : Nat}
    (hg : c.mem.get? V = some ⟨x, v, w⟩) (hg' : c.mem.get? V' = some ⟨x', v', w'⟩)
    (hv : BitVec.setWidth 64 v = P.n1) (hv' : BitVec.setWidth 64 v' = P.n1) (hne : V ≠ V') : False := by
  obtain ⟨s, hs, hk, hf⟩ := frozen1 E hW hL htot hx hg hv
  obtain ⟨s', hs', hk', hf'⟩ := frozen1 E hW hL htot hx' hg' hv'
  exact frozen_unique E hs hs' (by rw [hk, hk']; intro h; exact hne (congrArg Prod.snd h).symm) hf hf'

omit hi in
theorem two_n2 {x x' : Loc} (hx : P.IsL x) (hx' : P.IsL x') {V V' : Time} {v v' : Val} {w w' : Nat}
    (hg : c.mem.get? V = some ⟨x, v, w⟩) (hg' : c.mem.get? V' = some ⟨x', v', w'⟩)
    (hv : BitVec.setWidth 64 v = P.n2) (hv' : BitVec.setWidth 64 v' = P.n2) (hne : V ≠ V') : False := by
  obtain ⟨s, hs, hk, hf⟩ := frozen2 E hW hL htot hx hg hv
  obtain ⟨s', hs', hk', hf'⟩ := frozen2 E hW hL htot hx' hg' hv'
  exact frozen_unique E hs hs' (by rw [hk, hk']; intro h; exact hne (congrArg Prod.snd h).symm) hf hf'

section Step

variable {V : Time} (ih : ∀ V' < V, Hist P c.mem V')
include ih

omit E hW hL htot in
/-- A non-zero read of a link word below `V` is a link message with `LK`. -/
theorem link_read {x : Loc} (hx : P.IsL x) {b : Time} (hb : b < V) {y : Val} (hr : c.mem.read? x b = some y)
    (hy : BitVec.setWidth 64 y ≠ 0) : ∃ w, c.mem.get? b = some ⟨x, y, w⟩ ∧ LK P c.mem b x (BitVec.setWidth 64 y) := by
  obtain ⟨w, hg⟩ := msg_of_read (ne_zero_of_link hi hx hr hy) hr
  exact ⟨w, hg, (ih b hb).2 x y w hx hg⟩

omit E hW hL hi htot in
/-- A `TailLoc` address below `V` is a link word. -/
theorem isL_of_tailLoc {V' : Time} (hV : V' ≤ V) {x : Loc} (ht : TailLoc P c.mem V' x) : P.IsL x := by
  obtain ⟨a, y, ha, hr, rfl⟩ := ht
  exact isL_of_HT ((ih a (by omega_t)).1 _ _ (.inr rfl) hr)

omit E hW hL hi htot in
/-- **A `LinkMsg` below `V`** is a link message with `LK`. -/
theorem linkMsg_LK {V0 : Time} (hV : V0 ≤ V) {n : BitVec 64} (hl : LinkMsg P c.mem V0 n) :
    ∃ b < V0, ∃ x v w, c.mem.get? b = some ⟨x, v, w⟩ ∧ BitVec.setWidth 64 v = n ∧ LK P c.mem b x n := by
  obtain ⟨b, x, v, w, hb, hg, hv, ht⟩ := hl
  have hx := isL_of_tailLoc ih (by omega_t) ht
  exact ⟨b, hb, x, v, w, hg, hv, hv ▸ (ih b (by omega_t)).2 x v w hx hg⟩

omit E hW hL htot in
/-- `HT` of a value read by provenance below `V` (`Prov`'s and `HeadF`'s
second read). -/
theorem HT_of_link {z : Val} (hz : HT P c.mem V (BitVec.setWidth 64 z)) {b : Time} (hb : b < V) {y5 : Val}
    (hr : c.mem.read? ⟨BitVec.setWidth 64 z + 8, 8⟩ b = some y5) (hy : BitVec.setWidth 64 y5 ≠ 0) :
    HT P c.mem V (BitVec.setWidth 64 y5) := by
  obtain ⟨w, hg, hk⟩ := link_read hi ih (isL_of_HT hz) hb hr hy
  exact HT_of_LK hg hk hb

/-- **The history step.** -/
theorem hist_step : Hist P c.mem V := by
  -- a value of `head`/`tail` below `V` is in `HT` at `V`
  have hlow : ∀ a < V, ∀ x y, (x = P.head ∨ x = P.tail) → c.mem.read? x a = some y →
      HT P c.mem V (BitVec.setWidth 64 y) := by
    intro a ha x y hx hr
    rcases (ih a ha).1 x y hx hr with h | ⟨h, b, hb, hb'⟩ | ⟨h, b, hb, hb'⟩
    · exact .inl h
    · exact .inr (.inl ⟨h, b, by omega_t, hb'⟩)
    · exact .inr (.inr ⟨h, b, by omega_t, hb'⟩)
  refine ⟨fun x y hx hr => ?_, fun x v w hx hg => ?_⟩
  · by_cases hV : V = 0
    · subst hV
      simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rcases hx with rfl | rfl
      · exact .inl hi.1.head
      · exact .inl hi.1.tail
    obtain ⟨w, hg⟩ := msg_of_read hV hr
    have hxw : P.IsW x := by rcases hx with rfl | rfl <;> simp [Params2.IsW]
    obtain ⟨s, -, -, -, h2, h3⟩ := msg_form2 E hW hxw (htot x hxw) hg
    have hnl : ¬ P.IsL x := by rcases hx with rfl | rfl; exact hL.not_isL_head; exact hL.not_isL_tail
    have htl : ¬ TailLoc P c.mem V x := fun ht => hnl (isL_of_tailLoc ih (Nat.le_refl _) ht)
    rcases hx with rfl | rfl
    · rcases h2 rfl with ⟨hnz, tr, z, b, y5, htr, hrz, -, hb, hr5, hyy⟩ | ht
      · rw [← hyy] at hnz ⊢
        exact HT_of_link hi ih (hlow tr htr _ _ (.inl rfl) hrz) hb hr5 hnz
      · exact absurd ht htl
    · rcases h3 rfl with ⟨n, hn, hv, hl⟩ | ⟨hnz, x', a, y', b, y'', hx', ha, hr', hb, hr'', hyy⟩ | ht
      · obtain ⟨b, hb, x', v', w', hg', hv', hk⟩ := linkMsg_LK ih (Nat.le_refl _) hl
        rw [hv]
        rw [← hv'] at hk ⊢
        exact HT_of_LK hg' hk hb
      · rw [← hyy] at hnz ⊢
        exact HT_of_link hi ih (hlow a ha _ _ hx' hr') hb hr'' hnz
      · exact absurd ht htl
  · obtain ⟨s, hs, hk, h1, -⟩ := msg_form2 E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
    obtain ⟨hnode, ⟨a, y3, ha, hr3, rfl⟩, tr, z, htr, hrz, hz0, hnm⟩ := h1 hx
    rcases hlow a ha _ _ (.inr rfl) hr3 with hy | ⟨hy, b, hb, v1, w1, hg1, hv1⟩ |
        ⟨hy, b, hb, v2, w2, hg2, hv2, b1, hb1, v1, w1, hg1, hv1⟩
    · -- `[d + 8]`
      rcases hnode with ⟨hv, -⟩ | ⟨hv, -, hl⟩
      · exact .inl ⟨by rw [hy]; rfl, hv⟩
      · exfalso
        obtain ⟨b, hb, x', v', w', hg', hv', hk⟩ := linkMsg_LK ih (Nat.le_refl _) hl
        have hx' : x' = P.dn := by
          rcases hk with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact h
          · exact absurd h hL.n12
        subst hx'
        have hloc : (⟨BitVec.setWidth 64 y3 + 8, 8⟩ : Loc) = P.dn := by rw [hy]; rfl
        rw [hloc] at hrz hnm
        by_cases htb : tr < b
        · exact hnm b _ htb hb hg' rfl
        have htr0 : tr ≠ 0 := by have := Treiber2.get?_ne_zero hg'; omega_t
        obtain ⟨wz, hgz⟩ := msg_of_read htr0 hrz
        rcases (ih tr htr).2 _ z wz (.inl rfl) hgz with ⟨-, h⟩ | ⟨-, h, -⟩
        · exact hL.n1z (h.symm.trans hz0)
        · exact hL.n2z (h.symm.trans hz0)
    · -- `[n1 + 8]`
      have hloc : (⟨BitVec.setWidth 64 y3 + 8, 8⟩ : Loc) = P.nn := by rw [hy]; rfl
      rcases hnode with ⟨hv, -⟩ | ⟨hv, -, hl⟩
      · exact (two_n1 E hW hL htot (.inl rfl) hx hg1 hg hv1 hv (by omega_t)).elim
      · obtain ⟨b', hb', x', v', w', hg', hv', hk⟩ := linkMsg_LK ih (Nat.le_refl _) hl
        have hx' : x' = P.dn := by
          rcases hk with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact h
          · exact absurd h hL.n12
        subst hx'
        exact .inr ⟨hloc, hv, b', hb', v', w', hg', hv'⟩
    · -- `[n2 + 8]`
      rcases hnode with ⟨hv, -⟩ | ⟨hv, -, -⟩
      · exact (two_n1 E hW hL htot (.inl rfl) hx hg1 hg hv1 hv (by omega_t)).elim
      · exact (two_n2 E hW hL htot (.inr (.inl rfl)) hx hg2 hg hv2 hv (by omega_t)).elim

end Step

/-- **The history**, at every time. -/
theorem hist : ∀ V, Hist P c.mem V := by
  intro V
  induction V using Nat.strongRecOn with
  | _ V ih => exact hist_step E hW hL hi htot ih

/-- **A non-initial message of `head`** overwrote an adjacent `d` and is
`n1`, or overwrote an adjacent `n1` and is `n2`. -/
theorem head_msg {V : Time} {y : Val} {w : Nat} (hg : c.mem.get? V = some ⟨P.head, y, w⟩) :
    ∃ tr z, tr < V ∧ c.mem.read? P.head tr = some z ∧ NoMsgIn c.mem P.head tr V ∧
      ((BitVec.setWidth 64 y = P.n1 ∧ BitVec.setWidth 64 z = P.d) ∨
        (BitVec.setWidth 64 y = P.n2 ∧ BitVec.setWidth 64 z = P.n1)) := by
  have hxw : P.IsW P.head := .inl rfl
  obtain ⟨s, -, -, -, h2, -⟩ := msg_form2 E hW hxw (htot _ hxw) hg
  have H := hist E hW hL hi htot
  rcases h2 rfl with ⟨hnz, tr, z, b, y5, htr, hrz, hnm, hb, hr5, hyy⟩ | ⟨a, y3, ha, hr3, hloc⟩
  · refine ⟨tr, z, htr, hrz, hnm, ?_⟩
    have hz := (H tr).1 _ _ (.inl rfl) hrz
    obtain ⟨w5, hg5, hk⟩ := link_read hi (fun V' _ => H V') (isL_of_HT hz) hb hr5 (by rw [hyy]; exact hnz)
    rw [hyy] at hk
    rcases hk with ⟨h, hv⟩ | ⟨h, hv, -⟩
    · simp only [Params.dn, Loc.mk.injEq, and_true] at h
      exact .inl ⟨hv, by bv_omega⟩
    · simp only [Params.nn, Loc.mk.injEq, and_true] at h
      exact .inr ⟨hv, by bv_omega⟩
  · exact absurd (hloc ▸ isL_of_HT ((H a).1 _ _ (.inr rfl) hr3)) hL.not_isL_head

/-- **Two non-initial messages of `head`**: the earlier is `n1`, the later
`n2`. -/
theorem head_pair {V V' : Time} (hVV : V < V') {y y' : Val} {w w' : Nat} (hg : c.mem.get? V = some ⟨P.head, y, w⟩)
    (hg' : c.mem.get? V' = some ⟨P.head, y', w'⟩) :
    BitVec.setWidth 64 y = P.n1 ∧ BitVec.setWidth 64 y' = P.n2 := by
  have hd1 := hL.q1.dn1
  have hd2 := hL.dn2
  have hV0 := Treiber2.get?_ne_zero hg
  -- a non-initial message of `head` at or above `V` is not `d`
  have hnd : ∀ t z, V ≤ t → c.mem.read? P.head t = some z → BitVec.setWidth 64 z ≠ P.d := by
    intro t z ht hr hz
    obtain ⟨wt, hgt⟩ := msg_of_read (by omega_t) hr
    obtain ⟨_, _, _, _, _, h⟩ := head_msg E hW hL hi htot hgt
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hd1 (hz.symm.trans h)
    · exact hd2 (hz.symm.trans h)
  obtain ⟨tr, z, htr, hrz, hnm, h⟩ := head_msg E hW hL hi htot hg'
  have hVtr : V ≤ tr := Classical.byContradiction fun hc => hnm V _ (by omega_t) hVV hg rfl
  rcases h with ⟨-, hz⟩ | ⟨hy', hz⟩
  · exact absurd hz (hnd tr z hVtr hrz)
  refine ⟨?_, hy'⟩
  rcases Nat.eq_or_lt_of_le hVtr with heq | hlt
  · subst heq
    rw [read?_of_get? hg] at hrz
    cases hrz; exact hz
  · obtain ⟨wt, hgt⟩ := msg_of_read (by omega_t) hrz
    obtain ⟨tr', z', htr', hrz', hnm', h'⟩ := head_msg E hW hL hi htot hgt
    have hVtr' : V ≤ tr' := Classical.byContradiction fun hc => hnm' V _ (by omega_t) hlt hg rfl
    rcases h' with ⟨-, hz'⟩ | ⟨h', -⟩
    · exact absurd hz' (hnd tr' z' hVtr' hrz')
    · exact absurd (hz.symm.trans h') hL.n12

/-- **One dequeue's value**: `1` if its swing wrote `n1`, `2` if `n2`. -/
theorem deq_data (hno : ∀ ts, ¬ Outstanding c ts) {V : Time} {x : BitVec 64} (hd : Deq c.mem P V x) :
    ∃ yh w, c.mem.get? V = some ⟨P.head, yh, w⟩ ∧
      (BitVec.setWidth 64 yh = P.n1 → x = 1) ∧ (BitVec.setWidth 64 yh = P.n2 → x = 2) := by
  obtain ⟨y3, y5, vh, w, ⟨a, tr0, tl, u, h1, h2, h3, h4, h5, rfl⟩, hg, hvh⟩ := hd
  have H := hist E hW hL hi htot
  have hx := isL_of_HT ((H a).1 _ _ (.inl rfl) h1)
  obtain ⟨w5, hg5⟩ := msg_of_read (ne_zero_of_link hi hx h2 h3) h2
  refine ⟨vh, w, hg, fun hv => ?_, fun hv => ?_⟩
  · rw [hvh] at hv
    obtain ⟨s, hs, -, hf⟩ := frozen1 E hW hL htot hx hg5 hv
    have hl : (⟨BitVec.setWidth 64 y5, 4⟩ : Loc) = P.dat := by rw [hv]; rfl
    rw [hl] at h4 h5
    have hD := frozen_read E hno hs hf h4 h5 (Nat.le_refl _)
    unfold D at hD; rw [hD]; rfl
  · rw [hvh] at hv
    obtain ⟨s, hs, -, hf⟩ := frozen2 E hW hL htot hx hg5 hv
    have hl : (⟨BitVec.setWidth 64 y5, 4⟩ : Loc) = P.dat2 := by rw [hv]; rfl
    rw [hl] at h4 h5
    have hD := frozen_read E hno hs hf h4 h5 (Nat.le_refl _)
    unfold D2 at hD; rw [hD]; rfl

/-- **The dequeuer's values**: `X10 = 1` and `X11 = 2`. -/
theorem final_values2 (hno : ∀ ts, ¬ Outstanding c ts) {x10 x11 : BitVec 64} (hd : DoneD2 c.mem P x10 x11) :
    x10 = 1 ∧ x11 = 2 := by
  obtain ⟨V1, V2, h12, hd1, hd2⟩ := hd
  obtain ⟨y1, w1, hg1, h1, -⟩ := deq_data E hW hL hi htot hno hd1
  obtain ⟨y2, w2, hg2, -, h2⟩ := deq_data E hW hL hi htot hno hd2
  obtain ⟨hv1, hv2⟩ := head_pair E hW hL hi htot h12 hg1 hg2
  exact ⟨h1 hv1, h2 hv2⟩

end Final

end Kraken.Promising.SLR.EnvG.MsQueue
