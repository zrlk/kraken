/-
**Part 2: the final clean erasure of the x64
queue of `msqueue2.kl`** gives FIFO: the dequeuer's two values are `n1` and
`n2`. ISA-neutral.

A copy of the MS queue proof's `EnvG/MsQueue2Final.lean` for the x64 layout
(`EnvG/X64MsQueue2Ghost.lean`), with one new argument: x64's dequeuer swings
`head` whenever `head ≠ tail`, without AArch64's `next ≠ 0` test, so the
link value it writes is shown non-zero globally.

At a final configuration with a clean erasure in which the acquire id `0` of
every queue word is held (the dequeuer's):

- every non-initial message of a queue word has an id-`0` slot in `form`
  (`msg_form`);
- **the history** (`hist`, strong induction on the timestamp):
  - a value of `head`/`tail` at `V` is `s`, or `n1` with `n1`'s link message
    at `[s]` below `V` (`L1At`), or `n2` with `n2`'s link message at `[n1]`
    below `V` (`L2At`, itself above an `L1At`) (`HT`);
  - a non-initial link message at `V` is `n1` at `[s]`, or `n2` at `[n1]`
    above an `L1At` (`LK`); two link messages giving the same token
    contradict validity (`tok_unique`), and a second message at `[s]`
    overwrote a non-zero adjacent message (`AdjZero`);
  - **new**: a value of `head` at `V` has rank at most that of a value of
    `tail` at or below `V` (`HH`; `rk s = 0`, `rk n1 = 1`, `rk n2 = 2`). The
    rank of `tail` only grows (`tail_mono`: a `tail` message is `TailF`, one
    link past its adjacent predecessor). At the dequeuer's swing (`head_step`)
    `head` read `h` at `tA`, `tail` read `t ≠ h` at `tB`: by `HH` at `tA`,
    `tail_mono` and the `tail` read's window, `rk h < rk t`, so `[h]`'s link
    message is below `tB`, the window of the `[h]` read covers it, and the
    value read is the link: non-zero and of rank `rk h + 1 ≤ rk t`;
- **the `head` chain** (`head_msg`, `head_pair`): a non-initial message of
  `head` overwrote an adjacent `s` and is `n1`, or overwrote `n1` and is
  `n2`; so of two of them, the earlier is `n1` and the later `n2`;
- **the dequeuer's two dequeues** (`DoneD2`: two `Deq`s, `head` messages at
  `V1 < V2`) are `n1` and `n2` (`final_values`).
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2Ghost
import Kraken.Promising.SLR.EnvG.X64Treiber2Final

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq)
open Kraken.Promising.X64.EnvG.Treiber2X (get?_ne_zero)

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The ghost facts -/

/-- **The ghost facts**: the release predicates of `ghost₀`, an acquire table
extending `[form]`. -/
def GW (P : Params) (g : Ghost) : Prop :=
  g.rel = (ghost₀ P).rel ∧ (ghost₀ P).acqTab <+: g.acqTab

namespace GW

variable {P : Params} {g g' : Ghost}

theorem mono (h : GW P g) (hle : g.Le g') : GW P g' :=
  ⟨hle.rel.trans h.1, h.2.trans hle.acqTab⟩

theorem rel_w (h : GW P g) {x : Loc} (hx : P.IsW x) : g.rel x = form P := by rw [h.1]; exact ghost₀_rel_w hx

theorem rel_ne (h : GW P g) {x : Loc} (hx : ¬ P.IsW x) : g.rel x = Pred.emp := by
  rw [h.1]; exact ghost₀_rel_ne hx

theorem acqPred_zero (h : GW P g) : g.acqPred 0 = form P :=
  Ghost.acqPred_of_prefix h.2 (by simp [ghost₀])

theorem impure (h : GW P g) {x : Loc} (hx : P.IsW x) (v : Val) : ¬ Pred.Pure (g.rel x) v := by
  rw [h.rel_w hx]; exact form_not_pure P v

end GW

theorem ghost₀_gw (P : Params) : GW P (ghost₀ P) := ⟨rfl, List.prefix_refl _⟩

/-- The initial values: `head = tail = s`, the links `0`. -/
structure InitV (m : Memory) (P : Params) : Prop where
  head : BitVec.setWidth 64 (m.initVal P.head) = P.s
  tail : BitVec.setWidth 64 (m.initVal P.tail) = P.s
  ls : BitVec.setWidth 64 (m.initVal P.ls) = 0
  l1 : BitVec.setWidth 64 (m.initVal P.l1) = 0
  l2 : BitVec.setWidth 64 (m.initVal P.l2) = 0

theorem InitV.of_init {m m' : Memory} (h : m'.init = m.init) {P : Params} (hi : InitV m P) : InitV m' P :=
  ⟨by rw [initVal_eq h]; exact hi.head, by rw [initVal_eq h]; exact hi.tail, by rw [initVal_eq h]; exact hi.ls,
    by rw [initVal_eq h]; exact hi.l1, by rw [initVal_eq h]; exact hi.l2⟩

/-! ## The dequeuer's facts -/

/-- **One dequeue** with result `x`: a message of `head` at `V` of 64-bit
value `x` (the dequeuer's own swing). -/
def Deq (m : Memory) (P : Params) (V : Time) (x : BitVec 64) : Prop :=
  ∃ vh w, m.get? V = some ⟨P.head, vh, w⟩ ∧ BitVec.setWidth 64 vh = x

theorem Deq.mono {m m' : Memory} (h : m.Prefix m') {P : Params} {V : Time} {x : BitVec 64} (hd : Deq m P V x) :
    Deq m' P V x :=
  let ⟨vh, w, h1, h2⟩ := hd
  ⟨vh, w, Memory.get?_of_prefix h.2 h1, h2⟩

/-- **The dequeuer's two dequeues**, the first swing below the second. -/
def DoneD2 (m : Memory) (P : Params) (x12 x13 : BitVec 64) : Prop :=
  ∃ V1 V2, V1 < V2 ∧ Deq m P V1 x12 ∧ Deq m P V2 x13

theorem DoneD2.mono {m m' : Memory} (h : m.Prefix m') {P : Params} {x y : BitVec 64} (hd : DoneD2 m P x y) :
    DoneD2 m' P x y :=
  let ⟨V1, V2, h1, h2, h3⟩ := hd
  ⟨V1, V2, h1, h2.mono h, h3.mono h⟩

/-! ## Ranks and the history predicates -/

/-- The rank of a queue value: `n2 ↦ 2`, `n1 ↦ 1`, otherwise (`s`) `0`. -/
def rk (P : Params) (y : BitVec 64) : Nat := if y = P.n2 then 2 else if y = P.n1 then 1 else 0

/-- `n1`'s link message at `[s]` at `b`. -/
def L1At (P : Params) (m : Memory) (b : Time) : Prop :=
  ∃ v w, m.get? b = some ⟨P.ls, v, w⟩ ∧ BitVec.setWidth 64 v = P.n1

/-- `n2`'s link message at `[n1]` at `b`, above an `L1At`. -/
def L2At (P : Params) (m : Memory) (b : Time) : Prop :=
  ∃ v w, m.get? b = some ⟨P.l1, v, w⟩ ∧ BitVec.setWidth 64 v = P.n2 ∧ ∃ b1 < b, L1At P m b1

/-- The value `y` of `head`/`tail` at `V`. -/
def HT (P : Params) (m : Memory) (V : Time) (y : BitVec 64) : Prop :=
  y = P.s ∨ (y = P.n1 ∧ ∃ b < V, L1At P m b) ∨ (y = P.n2 ∧ ∃ b < V, L2At P m b)

/-- The non-initial link message `(x, y)` at `V`. -/
def LK (P : Params) (m : Memory) (V : Time) (x : Loc) (y : BitVec 64) : Prop :=
  (x = P.ls ∧ y = P.n1) ∨ (x = P.l1 ∧ y = P.n2 ∧ ∃ b1 < V, L1At P m b1)

/-- **`head` is not ahead of `tail`**: a value of `head` at `V` has rank at
most that of a value of `tail` at or below `V`. -/
def HH (P : Params) (m : Memory) (V : Time) : Prop :=
  ∀ y, m.read? P.head V = some y →
    ∃ b ≤ V, ∃ y', m.read? P.tail b = some y' ∧ rk P (BitVec.setWidth 64 y) ≤ rk P (BitVec.setWidth 64 y')

/-- The history at `V`. -/
def Hist (P : Params) (m : Memory) (V : Time) : Prop :=
  (∀ x y, (x = P.head ∨ x = P.tail) → m.read? x V = some y → HT P m V (BitVec.setWidth 64 y)) ∧
    (∀ x v w, P.IsL x → m.get? V = some ⟨x, v, w⟩ → LK P m V x (BitVec.setWidth 64 v)) ∧ HH P m V

section Ranks

variable {P : Params}

theorem isL_of_HT {m : Memory} {V : Time} {y : BitVec 64} (h : HT P m V y) : P.IsL ⟨y, 8⟩ := by
  rcases h with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem HT_of_LK {m : Memory} {b V : Time} {x : Loc} {v : Val} {w : Nat} (hg : m.get? b = some ⟨x, v, w⟩)
    (hk : LK P m b x (BitVec.setWidth 64 v)) (hb : b < V) : HT P m V (BitVec.setWidth 64 v) := by
  rcases hk with ⟨rfl, h⟩ | ⟨rfl, h, b1, hb1, h1⟩
  · exact .inr (.inl ⟨h, b, hb, v, w, hg, h⟩)
  · exact .inr (.inr ⟨h, b, hb, v, w, hg, h, b1, hb1, h1⟩)

theorem rk_s (hL : QLocs P) : rk P P.s = 0 := by simp [rk, hL.s1, hL.s2]
theorem rk_n1 (hL : QLocs P) : rk P P.n1 = 1 := by simp [rk, hL.n12]
theorem rk_n2 : rk P P.n2 = 2 := by simp [rk]

/-- The three values of `HT` and their ranks. -/
theorem rk_cases (hL : QLocs P) {m : Memory} {V : Time} {y : BitVec 64} (h : HT P m V y) :
    (y = P.s ∧ rk P y = 0) ∨ (y = P.n1 ∧ rk P y = 1) ∨ (y = P.n2 ∧ rk P y = 2) := by
  rcases h with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact .inl ⟨rfl, rk_s hL⟩
  · exact .inr (.inl ⟨rfl, rk_n1 hL⟩)
  · exact .inr (.inr ⟨rfl, rk_n2⟩)

/-- The rank is injective on `HT` values. -/
theorem rk_inj (hL : QLocs P) {m : Memory} {V V' : Time} {y y' : BitVec 64} (h : HT P m V y) (h' : HT P m V' y')
    (he : rk P y = rk P y') : y = y' := by
  rcases rk_cases hL h with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
    rcases rk_cases hL h' with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;> first | rfl | omega

end Ranks

/-! ## The final law -/

section Final

variable {P : Params} {rF : Nat → Res} {g : Ghost} {TT : Nat → Prop} {c : Config I}

/-- **Every non-initial message of a queue word has an id-`0` slot in
`form`.** -/
theorem msg_form (E : Erase rF g TT c) (hW : GW P g) {x : Loc} (hx : P.IsW x)
    (htot : (total rF g c).acq x 0 = 1) {V : Time} {v : Val} {w : Nat} (hV : c.mem.get? V = some ⟨x, v, w⟩) :
    ∃ s ∈ g.u, s.key = (x, V) ∧ (P.IsL x → LinkF P c.mem V s.res x v) ∧
      (x = P.head → HeadF P c.mem V v ∨ TailLoc P c.mem V x) ∧
      (x = P.tail → TailF P c.mem V v ∨ TailLoc P c.mem V x) := by
  have hrd : c.mem.read? (x, V).1 (x, V).2 = some v := read?_of_get? hV
  obtain ⟨s, hs, hk, -, hP⟩ := slot_of_held E htot hrd (hW.impure hx v)
  rw [hW.acqPred_zero] at hP
  obtain ⟨x', w', hg, h1, h2, h3, -⟩ := hP (get?_ne_zero hV)
  rw [hV] at hg
  cases hg
  exact ⟨s, hs, hk, h1, h2, h3⟩

/-- **Two slots cannot hold the same token whole.** -/
theorem tok_unique (E : Erase rF g TT c) {s s' : Slot} (hs : s ∈ g.u) (hs' : s' ∈ g.u) (hne : s'.key ≠ s.key)
    {tok : Loc} (h1 : TokFrozen tok s.res) (h2 : TokFrozen tok s'.res) : False := by
  have := E.q_add_le_one_slots hs hs' (fun h => hne (by rw [h])) tok
  unfold TokFrozen at h1 h2
  grind

theorem initVal_link (hi : InitV c.mem P) {x : Loc} (hx : P.IsL x) : BitVec.setWidth 64 (c.mem.initVal x) = 0 := by
  rcases hx with rfl | rfl | rfl
  · exact hi.ls
  · exact hi.l1
  · exact hi.l2

theorem msg_of_read {x : Loc} {b : Time} {y : Val} (hb : b ≠ 0) (hr : c.mem.read? x b = some y) :
    ∃ w, c.mem.get? b = some ⟨x, y, w⟩ := by
  obtain ⟨wm, hg, hl, hv⟩ := get?_of_read? hb hr
  exact ⟨wm.tid, by rw [hg, ← hl, ← hv]⟩

theorem ne_zero_of_link (hi : InitV c.mem P) {x : Loc} (hx : P.IsL x) {b : Time} {y : Val}
    (hr : c.mem.read? x b = some y) (hy : BitVec.setWidth 64 y ≠ 0) : b ≠ 0 := by
  rintro rfl
  simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
  subst hr; exact hy (initVal_link hi hx)

/-- A message at `x` between `a` and `b` contradicts `NoMsgIn`. -/
theorem noMsgIn_read {x : Loc} {a b p : Time} (hn : NoMsgIn c.mem x a b) (h1 : a < p) (h2 : p < b) {y : Val}
    (hr : c.mem.read? x p = some y) : False := by
  obtain ⟨w, hg⟩ := msg_of_read (by omega_t) hr
  exact hn p _ h1 h2 hg rfl

variable (E : Erase rF g TT c) (hW : GW P g) (hL : QLocs P) (hi : InitV c.mem P)
  (htot : ∀ x, P.IsW x → (total rF g c).acq x 0 = 1)
include E hW hL hi htot

omit hi in
/-- A link message's slot holds `n1`'s token if its value is `n1`. -/
theorem tok1_of {x : Loc} (hx : P.IsL x) {V : Time} {v : Val} {w : Nat} (hg : c.mem.get? V = some ⟨x, v, w⟩)
    (hv : BitVec.setWidth 64 v = P.n1) : ∃ s ∈ g.u, s.key = (x, V) ∧ TokFrozen P.tok1 s.res := by
  obtain ⟨s, hs, hk, h1, -⟩ := msg_form E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
  rcases (h1 hx).1 with ⟨-, hf⟩ | ⟨hv', -⟩
  · exact ⟨s, hs, hk, hf⟩
  · exact absurd (hv.symm.trans hv') hL.n12

omit hi in
/-- A link message's slot holds `n2`'s token if its value is `n2`. -/
theorem tok2_of {x : Loc} (hx : P.IsL x) {V : Time} {v : Val} {w : Nat} (hg : c.mem.get? V = some ⟨x, v, w⟩)
    (hv : BitVec.setWidth 64 v = P.n2) : ∃ s ∈ g.u, s.key = (x, V) ∧ TokFrozen P.tok2 s.res := by
  obtain ⟨s, hs, hk, h1, -⟩ := msg_form E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
  rcases (h1 hx).1 with ⟨hv', -⟩ | ⟨-, hf, -⟩
  · exact absurd (hv'.symm.trans hv) hL.n12
  · exact ⟨s, hs, hk, hf⟩

omit hi in
/-- Two `n1` link messages at different times contradict validity. -/
theorem two_n1 {x x' : Loc} (hx : P.IsL x) (hx' : P.IsL x') {V V' : Time} {v v' : Val} {w w' : Nat}
    (hg : c.mem.get? V = some ⟨x, v, w⟩) (hg' : c.mem.get? V' = some ⟨x', v', w'⟩)
    (hv : BitVec.setWidth 64 v = P.n1) (hv' : BitVec.setWidth 64 v' = P.n1) (hne : V ≠ V') : False := by
  obtain ⟨s, hs, hk, hf⟩ := tok1_of E hW hL htot hx hg hv
  obtain ⟨s', hs', hk', hf'⟩ := tok1_of E hW hL htot hx' hg' hv'
  exact tok_unique E hs hs' (by rw [hk, hk']; intro h; exact hne (congrArg Prod.snd h).symm) hf hf'

omit hi in
/-- Two `n2` link messages at different times contradict validity. -/
theorem two_n2 {x x' : Loc} (hx : P.IsL x) (hx' : P.IsL x') {V V' : Time} {v v' : Val} {w w' : Nat}
    (hg : c.mem.get? V = some ⟨x, v, w⟩) (hg' : c.mem.get? V' = some ⟨x', v', w'⟩)
    (hv : BitVec.setWidth 64 v = P.n2) (hv' : BitVec.setWidth 64 v' = P.n2) (hne : V ≠ V') : False := by
  obtain ⟨s, hs, hk, hf⟩ := tok2_of E hW hL htot hx hg hv
  obtain ⟨s', hs', hk', hf'⟩ := tok2_of E hW hL htot hx' hg' hv'
  exact tok_unique E hs hs' (by rw [hk, hk']; intro h; exact hne (congrArg Prod.snd h).symm) hf hf'

section Step

variable {V : Time} (ih : ∀ V' < V, Hist P c.mem V')
include ih

omit E hW hL htot in
/-- A non-zero read of a link word below `V` is a link message with `LK`. -/
theorem link_read {x : Loc} (hx : P.IsL x) {b : Time} (hb : b < V) {y : Val} (hr : c.mem.read? x b = some y)
    (hy : BitVec.setWidth 64 y ≠ 0) : ∃ w, c.mem.get? b = some ⟨x, y, w⟩ ∧ LK P c.mem b x (BitVec.setWidth 64 y) := by
  obtain ⟨w, hg⟩ := msg_of_read (ne_zero_of_link hi hx hr hy) hr
  exact ⟨w, hg, (ih b hb).2.1 x y w hx hg⟩

omit E hW hL hi htot in
/-- A `TailLoc` address at or below `V` is a link word. -/
theorem isL_of_tailLoc {V' : Time} (hV : V' ≤ V) {x : Loc} (ht : TailLoc P c.mem V' x) : P.IsL x := by
  obtain ⟨a, y, ha, hr, rfl⟩ := ht
  exact isL_of_HT ((ih a (by omega_t)).1 _ _ (.inr rfl) hr)

omit E hW hL hi htot in
/-- **A `LinkMsg` at or below `V`** is a link message with `LK`. -/
theorem linkMsg_LK {V0 : Time} (hV : V0 ≤ V) {n : BitVec 64} (hl : LinkMsg P c.mem V0 n) :
    ∃ b < V0, ∃ x v w, c.mem.get? b = some ⟨x, v, w⟩ ∧ BitVec.setWidth 64 v = n ∧ LK P c.mem b x n := by
  obtain ⟨b, x, v, w, hb, hg, hv, ht⟩ := hl
  have hx := isL_of_tailLoc ih hV ht
  exact ⟨b, hb, x, v, w, hg, hv, hv ▸ (ih b (by omega_t)).2.1 x v w hx hg⟩

omit E hW htot in
/-- **One link past**: a non-zero read below `V` of `[z]`, `z` an `HT` value,
is a link message, an `HT` value at `V` of rank `rk z + 1`. -/
theorem link_succ {V0 : Time} {z : BitVec 64} (hz : HT P c.mem V0 z) {b : Time} (hb : b < V) {y5 : Val}
    (hr : c.mem.read? ⟨z, 8⟩ b = some y5) (hy : BitVec.setWidth 64 y5 ≠ 0) :
    ∃ w, c.mem.get? b = some ⟨⟨z, 8⟩, y5, w⟩ ∧ HT P c.mem V (BitVec.setWidth 64 y5) ∧
      rk P (BitVec.setWidth 64 y5) = rk P z + 1 := by
  obtain ⟨w, hg, hk⟩ := link_read hi ih (isL_of_HT hz) hb hr hy
  refine ⟨w, hg, HT_of_LK hg hk hb, ?_⟩
  rcases hk with ⟨h, hv⟩ | ⟨h, hv, -⟩
  · simp only [Params.ls, Loc.mk.injEq, and_true] at h
    rw [hv, h, rk_n1 hL, rk_s hL]
  · simp only [Params.l1, Loc.mk.injEq, and_true] at h
    rw [hv, h, rk_n2, rk_n1 hL]

omit E hW hi htot in
/-- A `tail` message is not at a `TailLoc` address. -/
theorem tail_not_tailLoc {V' : Time} (hV : V' ≤ V) : ¬ TailLoc P c.mem V' P.tail := fun ht =>
  hL.not_isL_tail (isL_of_tailLoc ih hV ht)

omit E hW hi htot in
theorem head_not_tailLoc {V' : Time} (hV : V' ≤ V) : ¬ TailLoc P c.mem V' P.head := fun ht =>
  hL.not_isL_head (isL_of_tailLoc ih hV ht)

/-- **The rank of `tail` only grows** below `V`. -/
theorem tail_mono : ∀ c' < V, ∀ b ≤ c', ∀ y y', c.mem.read? P.tail b = some y → c.mem.read? P.tail c' = some y' →
    rk P (BitVec.setWidth 64 y) ≤ rk P (BitVec.setWidth 64 y') := by
  intro c'
  induction c' using Nat.strongRecOn with
  | _ c' ihc =>
    intro hc b hb y y' hr hr'
    rcases Nat.eq_or_lt_of_le hb with rfl | hlt
    · rw [hr] at hr'; cases hr'; exact Nat.le_refl _
    obtain ⟨w, hg⟩ := msg_of_read (by omega_t) hr'
    have hxw : P.IsW P.tail := .inr (.inl rfl)
    obtain ⟨s, -, -, -, -, h3⟩ := msg_form E hW hxw (htot _ hxw) hg
    rcases h3 rfl with ⟨hnz, tr, z, b', y'', htr, hrz, hnm, hb', hr'', hyy⟩ | ht
    · have hz := (ih tr (by omega_t)).1 _ _ (.inr rfl) hrz
      obtain ⟨-, -, hrk⟩ := link_succ hL hi ih hz (by omega_t : b' < V) hr'' (by rw [hyy]; exact hnz)
      rw [hyy] at hrk
      have hbt : b ≤ tr := Nat.le_of_not_lt fun h => noMsgIn_read hnm h hlt hr
      have := ihc tr htr (by omega_t) b hbt y z hr hrz
      omega
    · exact absurd ht (tail_not_tailLoc hL ih (by omega_t))

/-- **The dequeuer's swing below `V`'s step**: `[z]`'s link message is the
value written, one rank past `z`, at most the rank of a `tail` value read
below `V`. -/
theorem head_step {v : Val} (hh : HeadF P c.mem V v) :
    ∃ tr z, tr < V ∧ c.mem.read? P.head tr = some z ∧ NoMsgIn c.mem P.head tr V ∧
      HT P c.mem V (BitVec.setWidth 64 v) ∧ rk P (BitVec.setWidth 64 v) = rk P (BitVec.setWidth 64 z) + 1 ∧
      ∃ tB yt, tB < V ∧ c.mem.read? P.tail tB = some yt ∧
        rk P (BitVec.setWidth 64 v) ≤ rk P (BitVec.setWidth 64 yt) := by
  obtain ⟨tr, z, htr, hrz, hnm, tA, y3, tB, yt, tl, u, htA, hr3, h3z, htB, hrt, htz, hwin, htl, hru, huv, hnl⟩ :=
    hh
  have hHz : HT P c.mem tA (BitVec.setWidth 64 z) := h3z ▸ (ih tA htA).1 _ _ (.inl rfl) hr3
  have hHt : HT P c.mem tB (BitVec.setWidth 64 yt) := (ih tB htB).1 _ _ (.inr rfl) hrt
  -- `rk z ≤ rk t`: `HH` at `tA`, the rank of `tail` grows, the `tail` window
  have hle : rk P (BitVec.setWidth 64 z) ≤ rk P (BitVec.setWidth 64 yt) := by
    obtain ⟨b, hb, y', hrb, hrk⟩ := (ih tA htA).2.2 y3 hr3
    rw [h3z] at hrk
    by_cases hbt : b ≤ tB
    · exact Nat.le_trans hrk (tail_mono E hW hL hi htot ih tB htB b hbt y' yt hrb hrt)
    · exact (noMsgIn_read (hwin (by omega_t)) (by omega_t) (by omega_t) hrb).elim
  have hlt : rk P (BitVec.setWidth 64 z) < rk P (BitVec.setWidth 64 yt) := by
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (rk_inj hL hHz hHt h).symm htz
  -- `[z]`'s link message is below `tB`
  have hbl : ∃ bl < tB, ∃ vl wl, c.mem.get? bl = some ⟨⟨BitVec.setWidth 64 z, 8⟩, vl, wl⟩ := by
    rcases rk_cases hL hHz with ⟨hz, hrz0⟩ | ⟨hz, hrz1⟩ | ⟨hz, hrz2⟩
    · rcases hHt with ht | ⟨-, b1, hb1, v1, w1, hg1, -⟩ | ⟨-, b2, hb2, -, -, -, -, b1, hb1, v1, w1, hg1, -⟩
      · rw [ht, rk_s hL] at hlt; omega
      · exact ⟨b1, hb1, v1, w1, by rw [hz]; exact hg1⟩
      · exact ⟨b1, by omega_t, v1, w1, by rw [hz]; exact hg1⟩
    · rcases hHt with ht | ⟨ht, -⟩ | ⟨-, b2, hb2, v2, w2, hg2, -⟩
      · rw [ht, rk_s hL] at hlt; omega
      · rw [ht, rk_n1 hL] at hlt; omega
      · exact ⟨b2, hb2, v2, w2, by rw [hz]; exact hg2⟩
    · rcases rk_cases hL hHt with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨bl, hbl, vl, wl, hgl⟩ := hbl
  have htl' : bl ≤ tl := Nat.le_of_not_lt fun h => hnl bl _ h (by omega_t) hgl rfl
  have hbl0 := get?_ne_zero hgl
  obtain ⟨wu, hgu⟩ := msg_of_read (by omega_t) hru
  have hk := (ih tl htl).2.1 _ u wu (isL_of_HT hHz) hgu
  refine ⟨tr, z, htr, hrz, hnm, huv ▸ HT_of_LK hgu hk htl, ?_, tB, yt, htB, hrt, ?_⟩
  · rw [← huv]
    rcases hk with ⟨h, hv⟩ | ⟨h, hv, -⟩
    · simp only [Params.ls, Loc.mk.injEq, and_true] at h
      rw [hv, h, rk_n1 hL, rk_s hL]
    · simp only [Params.l1, Loc.mk.injEq, and_true] at h
      rw [hv, h, rk_n2, rk_n1 hL]
  · have : rk P (BitVec.setWidth 64 u) = rk P (BitVec.setWidth 64 z) + 1 := by
      rcases hk with ⟨h, hv⟩ | ⟨h, hv, -⟩
      · simp only [Params.ls, Loc.mk.injEq, and_true] at h
        rw [hv, h, rk_n1 hL, rk_s hL]
      · simp only [Params.l1, Loc.mk.injEq, and_true] at h
        rw [hv, h, rk_n2, rk_n1 hL]
    rw [← huv]; omega

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
  refine ⟨fun x y hx hr => ?_, fun x v w hx hg => ?_, fun y hr => ?_⟩
  · by_cases hV : V = 0
    · subst hV
      simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rcases hx with rfl | rfl
      · exact .inl hi.head
      · exact .inl hi.tail
    obtain ⟨w, hg⟩ := msg_of_read hV hr
    have hxw : P.IsW x := by rcases hx with rfl | rfl <;> simp [Params.IsW]
    obtain ⟨s, -, -, -, h2, h3⟩ := msg_form E hW hxw (htot x hxw) hg
    rcases hx with rfl | rfl
    · rcases h2 rfl with hh | ht
      · obtain ⟨-, -, -, -, -, hHT, -⟩ := head_step E hW hL hi htot ih hh
        exact hHT
      · exact absurd ht (head_not_tailLoc hL ih (Nat.le_refl _))
    · rcases h3 rfl with ⟨hnz, tr, z, b, y5, htr, hrz, -, hb, hr5, hyy⟩ | ht
      · rw [← hyy] at hnz ⊢
        obtain ⟨-, -, hHT, -⟩ := link_succ hL hi ih ((ih tr htr).1 _ _ (.inr rfl) hrz) hb hr5 hnz
        exact hHT
      · exact absurd ht (tail_not_tailLoc hL ih (Nat.le_refl _))
  · obtain ⟨s, hs, hk, h1, -⟩ := msg_form E hW (isW_of_isL P hx) (htot _ (isW_of_isL P hx)) hg
    obtain ⟨hnode, ⟨a, y3, ha, hr3, rfl⟩, tr, z, htr, hrz, hz0, hnm⟩ := h1 hx
    rcases hlow a ha _ _ (.inr rfl) hr3 with hy | ⟨hy, b, hb, v1, w1, hg1, hv1⟩ |
        ⟨hy, b, hb, v2, w2, hg2, hv2, b1, hb1, v1, w1, hg1, hv1⟩
    · -- `[s]`
      rcases hnode with ⟨hv, -⟩ | ⟨hv, -, hl⟩
      · exact .inl ⟨by rw [hy]; rfl, hv⟩
      · exfalso
        obtain ⟨b, hb, x', v', w', hg', hv', hk⟩ := linkMsg_LK ih (Nat.le_refl _) hl
        have hx' : x' = P.ls := by
          rcases hk with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact h
          · exact absurd h hL.n12
        subst hx'
        have hloc : (⟨BitVec.setWidth 64 y3, 8⟩ : Loc) = P.ls := by rw [hy]; rfl
        rw [hloc] at hrz hnm
        by_cases htb : tr < b
        · exact hnm b _ htb hb hg' rfl
        have htr0 : tr ≠ 0 := by have := get?_ne_zero hg'; omega_t
        obtain ⟨wz, hgz⟩ := msg_of_read htr0 hrz
        rcases (ih tr htr).2.1 _ z wz (.inl rfl) hgz with ⟨-, h⟩ | ⟨-, h, -⟩
        · exact hL.n1z (h.symm.trans hz0)
        · exact hL.n2z (h.symm.trans hz0)
    · -- `[n1]`
      have hloc : (⟨BitVec.setWidth 64 y3, 8⟩ : Loc) = P.l1 := by rw [hy]; rfl
      rcases hnode with ⟨hv, -⟩ | ⟨hv, -, hl⟩
      · exact (two_n1 E hW hL htot (.inl rfl) hx hg1 hg hv1 hv (by omega_t)).elim
      · obtain ⟨b', hb', x', v', w', hg', hv', hk⟩ := linkMsg_LK ih (Nat.le_refl _) hl
        have hx' : x' = P.ls := by
          rcases hk with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact h
          · exact absurd h hL.n12
        subst hx'
        exact .inr ⟨hloc, hv, b', hb', v', w', hg', hv'⟩
    · -- `[n2]`
      rcases hnode with ⟨hv, -⟩ | ⟨hv, -, -⟩
      · exact (two_n1 E hW hL htot (.inl rfl) hx hg1 hg hv1 hv (by omega_t)).elim
      · exact (two_n2 E hW hL htot (.inr (.inl rfl)) hx hg2 hg hv2 hv (by omega_t)).elim
  · by_cases hV : V = 0
    · subst hV
      refine ⟨0, Nat.le_refl _, c.mem.initVal P.tail, by simp [Memory.read?], ?_⟩
      simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rw [hi.head, hi.tail]
      exact Nat.le_refl _
    obtain ⟨w, hg⟩ := msg_of_read hV hr
    have hxw : P.IsW P.head := .inl rfl
    obtain ⟨s, -, -, -, h2, -⟩ := msg_form E hW hxw (htot _ hxw) hg
    rcases h2 rfl with hh | ht
    · obtain ⟨-, -, -, -, -, -, -, tB, yt, htB, hrt, hrk⟩ := head_step E hW hL hi htot ih hh
      exact ⟨tB, Nat.le_of_lt htB, yt, hrt, hrk⟩
    · exact absurd ht (head_not_tailLoc hL ih (Nat.le_refl _))

end Step

/-- **The history**, at every time. -/
theorem hist : ∀ V, Hist P c.mem V := by
  intro V
  induction V using Nat.strongRecOn with
  | _ V ih => exact hist_step E hW hL hi htot ih

/-- **A non-initial message of `head`** overwrote an adjacent `s` and is
`n1`, or overwrote an adjacent `n1` and is `n2`. -/
theorem head_msg {V : Time} {y : Val} {w : Nat} (hg : c.mem.get? V = some ⟨P.head, y, w⟩) :
    ∃ tr z, tr < V ∧ c.mem.read? P.head tr = some z ∧ NoMsgIn c.mem P.head tr V ∧
      ((BitVec.setWidth 64 y = P.n1 ∧ BitVec.setWidth 64 z = P.s) ∨
        (BitVec.setWidth 64 y = P.n2 ∧ BitVec.setWidth 64 z = P.n1)) := by
  have hxw : P.IsW P.head := .inl rfl
  obtain ⟨s, -, -, -, h2, -⟩ := msg_form E hW hxw (htot _ hxw) hg
  have H := hist E hW hL hi htot
  rcases h2 rfl with hh | ht
  · obtain ⟨tr, z, htr, hrz, hnm, hHy, hrk, -⟩ := head_step E hW hL hi htot (fun V' _ => H V') hh
    have hHz := (H tr).1 _ _ (.inl rfl) hrz
    refine ⟨tr, z, htr, hrz, hnm, ?_⟩
    rcases rk_cases hL hHy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases rk_cases hL hHz with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      first | omega | exact .inl ⟨h1, h3⟩ | exact .inr ⟨h1, h3⟩
  · exact absurd ht (head_not_tailLoc hL (fun V' _ => H V') (Nat.le_refl _))

/-- **Two non-initial messages of `head`**: the earlier is `n1`, the later
`n2`. -/
theorem head_pair {V V' : Time} (hVV : V < V') {y y' : Val} {w w' : Nat} (hg : c.mem.get? V = some ⟨P.head, y, w⟩)
    (hg' : c.mem.get? V' = some ⟨P.head, y', w'⟩) :
    BitVec.setWidth 64 y = P.n1 ∧ BitVec.setWidth 64 y' = P.n2 := by
  have hd1 := hL.s1
  have hd2 := hL.s2
  have hV0 := get?_ne_zero hg
  -- a non-initial message of `head` at or above `V` is not `s`
  have hnd : ∀ t z, V ≤ t → c.mem.read? P.head t = some z → BitVec.setWidth 64 z ≠ P.s := by
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

/-- **The dequeuer's values**: `r12 = n1` and `r13 = n2`. -/
theorem final_values {x12 x13 : BitVec 64} (hd : DoneD2 c.mem P x12 x13) : x12 = P.n1 ∧ x13 = P.n2 := by
  obtain ⟨V1, V2, h12, ⟨vh1, w1, hg1, rfl⟩, ⟨vh2, w2, hg2, rfl⟩⟩ := hd
  exact head_pair E hW hL hi htot h12 hg1 hg2

end Final

end Kraken.Promising.X64.EnvG.MsQueueX
